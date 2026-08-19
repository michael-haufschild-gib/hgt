import GaloisForLFunctions.RHTower.ProjectiveFisherBlindness
import GaloisForLFunctions.RHTower.AnderssonTheoremTwo
import GaloisForLFunctions.HTGeometry.HelsonCharacterLSeries
import Mathlib

/-!
# The prime Fisher superspace is blind to unimodular Euler phases

The Dirichlet coherent state of a completely multiplicative unimodular coefficient family has Born
probabilities, expectations and Fisher variance independent of the phases: they are the normalized
`n^{-2σ}/ζ(2σ)` law of the untwisted state.  The scalar Helson zeta value, by contrast, is a
distributional projection against the constant vector, which is not square summable, and by the
corpus divisor-surjectivity theorem it can carry prescribed zeros to the right of the critical
line.  Hence Fisher geometry cannot localize the zero divisor.
-/

open Complex Filter GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The Dirichlet coherent state of a unimodular completely multiplicative phase. -/
def dirichletCoherentState (u : ℕ → ℂ) (s : ℂ) (n : ℕ+) : ℂ :=
  phaseChar u (n : ℕ) * ((n : ℕ) : ℂ) ^ (-s)

theorem norm_phaseChar_pnat {u : ℕ → ℂ} (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) (n : ℕ+) :
    ‖phaseChar u (n : ℕ)‖ = 1 :=
  norm_phaseChar_eq_one hu (by exact_mod_cast n.ne_zero)

theorem dirichletCoherentState_eq_twist (u : ℕ → ℂ) (s : ℂ) :
    dirichletCoherentState u s
      = fun n : ℕ+ => phaseChar u (n : ℕ) * dirichletCoherentState (fun _ => 1) s n := by
  funext n
  rw [dirichletCoherentState, dirichletCoherentState]
  have hone : phaseChar (fun _ : ℕ => (1 : ℂ)) (n : ℕ) = 1 := by
    rw [phaseChar_apply_of_ne_zero _ (by exact_mod_cast n.ne_zero)]
    exact Finset.prod_eq_one fun p _ => one_pow _
  rw [hone, one_mul]

/-- **Born blindness of the Dirichlet coherent state.**  Every Born probability of a twisted state
equals that of the untwisted one. -/
theorem bornProbability_dirichletCoherentState {u : ℕ → ℂ}
    (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) (s : ℂ) (n : ℕ+) :
    bornProbability (dirichletCoherentState u s) n
      = bornProbability (dirichletCoherentState (fun _ => 1) s) n := by
  rw [dirichletCoherentState_eq_twist u s]
  exact bornProbability_phase_twist _ _ (fun m => norm_phaseChar_pnat hu m) n

/-- The Fisher variance of a twisted Dirichlet coherent state is that of the untwisted one. -/
theorem bornVariance_dirichletCoherentState {u : ℕ → ℂ}
    (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) (s : ℂ) (E : ℕ+ → ℝ) :
    bornVariance (dirichletCoherentState u s) E
      = bornVariance (dirichletCoherentState (fun _ => 1) s) E := by
  rw [dirichletCoherentState_eq_twist u s]
  exact bornVariance_phase_twist _ _ E (fun m => norm_phaseChar_pnat hu m)

/-- The coordinate weights of the coherent state are the phase-free powers. -/
theorem norm_sq_dirichletCoherentState {u : ℕ → ℂ}
    (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) (s : ℂ) (n : ℕ+) :
    ‖dirichletCoherentState u s n‖ ^ 2 = ((n : ℕ) : ℝ) ^ (-(2 * s.re)) := by
  have hn0 : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  rw [dirichletCoherentState, norm_mul, norm_phaseChar_pnat hu n, one_mul,
    Complex.norm_natCast_cpow_of_pos n.pos]
  rw [← Real.rpow_natCast (((n : ℕ) : ℝ) ^ (-s).re) 2, ← Real.rpow_mul hn0.le]
  congr 1
  simp
  ring

/-- **The constant vector is not a state.**  The scalar Dirichlet projection is not a bounded
Hilbert observable of the coherent-state geometry. -/
theorem not_summable_constant_state :
    ¬ Summable (fun _ : ℕ+ => ‖(1 : ℂ)‖ ^ 2) := by
  intro hsum
  have h1 : (fun _ : ℕ+ => ‖(1 : ℂ)‖ ^ 2) = fun _ : ℕ+ => (1 : ℝ) := by
    funext n
    simp
  rw [h1] at hsum
  have hzero := hsum.tendsto_cofinite_zero
  have hone : Filter.Tendsto (fun _ : ℕ+ => (1 : ℝ)) Filter.cofinite (nhds 1) :=
    tendsto_const_nhds
  haveI : (Filter.cofinite : Filter ℕ+).NeBot := Filter.cofinite_neBot
  have heq : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
  norm_num at heq

/-- The completely multiplicative coefficient family attached to a prime phase. -/
def phaseCoefficients (χ : PhaseTorus) : ℕ → ℂ :=
  fun n => if h : n.Prime then (χ ⟨n, h⟩ : ℂ) else 1

theorem norm_phaseCoefficients (χ : PhaseTorus) {p : ℕ} (hp : Nat.Prime p) :
    ‖phaseCoefficients χ p‖ = 1 := by
  rw [phaseCoefficients, dif_pos hp]
  exact (χ ⟨p, hp⟩).2

/-- The prescribed zero sequence: a single point `ρ` together with a vertical escape. -/
def offLineZeroSequence (ρ : ℂ) : ℕ → ℂ := fun n => ρ - (n : ℂ) * Complex.I

/-- The prescribed pole sequence, kept away from the marked point. -/
def offLinePoleSequence : ℕ → ℂ := fun n => -1 - ((n : ℂ) + 1) * Complex.I

theorem tendsto_norm_offLineZeroSequence (ρ : ℂ) :
    Tendsto (fun n => ‖offLineZeroSequence ρ n‖) atTop atTop := by
  have hlower : ∀ n : ℕ, (n : ℝ) - ‖ρ‖ ≤ ‖offLineZeroSequence ρ n‖ := by
    intro n
    have h1 : ‖((n : ℂ)) * Complex.I‖ = (n : ℝ) := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast]
    have h2 : ‖((n : ℂ)) * Complex.I‖ - ‖ρ‖ ≤ ‖ρ - (n : ℂ) * Complex.I‖ := by
      have := norm_sub_norm_le ((n : ℂ) * Complex.I) ρ
      calc ‖((n : ℂ)) * Complex.I‖ - ‖ρ‖ ≤ ‖(n : ℂ) * Complex.I - ρ‖ := this
        _ = ‖ρ - (n : ℂ) * Complex.I‖ := by rw [norm_sub_rev]
    rw [h1] at h2
    exact h2
  refine tendsto_atTop_mono hlower ?_
  exact tendsto_atTop_add_const_right _ (-‖ρ‖) tendsto_natCast_atTop_atTop

theorem tendsto_norm_offLinePoleSequence :
    Tendsto (fun n => ‖offLinePoleSequence n‖) atTop atTop := by
  have hlower : ∀ n : ℕ, (n : ℝ) ≤ ‖offLinePoleSequence n‖ := by
    intro n
    have him : (offLinePoleSequence n).im = -((n : ℝ) + 1) := by
      simp [offLinePoleSequence]
    have habs := Complex.abs_im_le_norm (offLinePoleSequence n)
    rw [him] at habs
    have : (n : ℝ) ≤ |(-((n : ℝ) + 1))| := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      linarith
    linarith
  exact tendsto_atTop_mono hlower tendsto_natCast_atTop_atTop

theorem offLineZeroSequence_ne_zero {ρ : ℂ} (hρ : 0 < ρ.re) (n : ℕ) :
    offLineZeroSequence ρ n ≠ 0 := by
  intro hcon
  have hre : (offLineZeroSequence ρ n).re = ρ.re := by
    simp [offLineZeroSequence]
  rw [hcon] at hre
  simp at hre
  linarith [hρ, hre]

theorem offLinePoleSequence_ne_zero (n : ℕ) : offLinePoleSequence n ≠ 0 := by
  intro hcon
  have hre : (offLinePoleSequence n).re = -1 := by
    simp [offLinePoleSequence]
  rw [hcon] at hre
  simp at hre

theorem re_offLineZeroSequence_lt_one {ρ : ℂ} (hρ : ρ.re < 1) (n : ℕ) :
    (offLineZeroSequence ρ n).re < 1 := by
  have hre : (offLineZeroSequence ρ n).re = ρ.re := by
    simp [offLineZeroSequence]
  rw [hre]
  exact hρ

theorem re_offLinePoleSequence_lt_one (n : ℕ) : (offLinePoleSequence n).re < 1 := by
  have hre : (offLinePoleSequence n).re = -1 := by
    simp [offLinePoleSequence]
  rw [hre]
  norm_num

theorem zeroMultiplicity_offLineZeroSequence (ρ : ℂ) :
    GaloisForLFunctions.zeroMultiplicity (offLineZeroSequence ρ) ρ = 1 := by
  have hset : {n : ℕ | offLineZeroSequence ρ n = ρ} = {0} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, offLineZeroSequence]
    constructor
    · intro h
      have hzero : ((n : ℂ)) * Complex.I = 0 := by
        have := h
        linear_combination -this
      have hn : ((n : ℂ)) = 0 := by
        rcases mul_eq_zero.mp hzero with h1 | h2
        · exact h1
        · exact absurd h2 Complex.I_ne_zero
      exact_mod_cast hn
    · rintro rfl
      simp
  rw [GaloisForLFunctions.zeroMultiplicity, hset]
  simp

theorem zeroMultiplicity_offLinePoleSequence {ρ : ℂ} (hρ : 0 < ρ.re) :
    GaloisForLFunctions.zeroMultiplicity offLinePoleSequence ρ = 0 := by
  have hset : {n : ℕ | offLinePoleSequence n = ρ} = ∅ := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hcon
    have hre : (offLinePoleSequence n).re = -1 := by
      simp [offLinePoleSequence]
    rw [hcon] at hre
    linarith
  rw [GaloisForLFunctions.zeroMultiplicity, hset]
  simp

/-- **The Fisher superspace does not determine the zero divisor.**  For every point to the right of
the imaginary axis and to the left of the line `Re = 1` there is a completely multiplicative
unimodular phase whose Helson zeta continuation has a simple zero there, while every Born
probability and every Fisher variance of its Dirichlet coherent state coincides with those of the
untwisted state. -/
theorem exists_phase_fisher_blind_with_prescribed_zero {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ∃ (χ : PhaseTorus) (F : ℂ → ℂ),
      MeromorphicOn F Set.univ ∧
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun p : Nat.Primes => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) (F s)) ∧
      meromorphicOrderAt F ρ = ((1 : ℤ) : WithTop ℤ) ∧
      (∀ (s : ℂ) (n : ℕ+),
        bornProbability (dirichletCoherentState (phaseCoefficients χ) s) n
          = bornProbability (dirichletCoherentState (fun _ => 1) s) n) ∧
      (∀ (s : ℂ) (E : ℕ+ → ℝ),
        bornVariance (dirichletCoherentState (phaseCoefficients χ) s) E
          = bornVariance (dirichletCoherentState (fun _ => 1) s) E) := by
  obtain ⟨χ, -, F, hFmero, hFprod, hFord⟩ :=
    exists_continuable_phase_with_prescribed_multiplicities
      (tendsto_norm_offLineZeroSequence ρ) (offLineZeroSequence_ne_zero hρ0)
      tendsto_norm_offLinePoleSequence offLinePoleSequence_ne_zero
      (re_offLineZeroSequence_lt_one hρ1) re_offLinePoleSequence_lt_one
  refine ⟨χ, F, hFmero, hFprod, ?_, ?_, ?_⟩
  · rw [hFord ρ, zeroMultiplicity_offLineZeroSequence ρ, zeroMultiplicity_offLinePoleSequence hρ0]
    simp
  · intro s n
    exact bornProbability_dirichletCoherentState
      (fun p hp => norm_phaseCoefficients χ hp) s n
  · intro s E
    exact bornVariance_dirichletCoherentState
      (fun p hp => norm_phaseCoefficients χ hp) s E

/-! ### The quartet multiplier and the conformal cancellation -/

/-- The even, reality-symmetric quartet multiplier of the card. -/
def quartetMultiplier (a z : ℂ) : ℂ := (z ^ 2 - a ^ 2) * (z ^ 2 - ((starRingEnd ℂ) a) ^ 2)

theorem quartetMultiplier_even (a z : ℂ) : quartetMultiplier a (-z) = quartetMultiplier a z := by
  rw [quartetMultiplier, quartetMultiplier]
  ring

theorem quartetMultiplier_conj (a z : ℂ) :
    quartetMultiplier a ((starRingEnd ℂ) z) = (starRingEnd ℂ) (quartetMultiplier a z) := by
  rw [quartetMultiplier, quartetMultiplier]
  simp only [map_mul, map_sub, map_pow, Complex.conj_conj]
  ring

theorem quartetMultiplier_eq_zero_iff (a z : ℂ) :
    quartetMultiplier a z = 0 ↔ z = a ∨ z = -a ∨ z = (starRingEnd ℂ) a ∨ z = -(starRingEnd ℂ) a := by
  rw [quartetMultiplier, mul_eq_zero, sub_eq_zero, sub_eq_zero, sq_eq_sq_iff_eq_or_eq_neg,
    sq_eq_sq_iff_eq_or_eq_neg]
  tauto

/-- The scalar Laplacian of a two-dimensional conformal metric with scale factor `G`. -/
def conformalLaplacian (G : ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  (G x)⁻¹ * (deriv (fun t => deriv (fun r => f (r, x.2)) t) x.1
    + deriv (fun t => deriv (fun r => f (x.1, r)) t) x.2)

/-- **Conformal cancellation in dimension two.**  The massless equation of a conformal metric does
not see the scale factor: it is the flat Laplace equation. -/
theorem conformalLaplacian_eq_zero_iff {G : ℝ × ℝ → ℝ} (hG : ∀ x, G x ≠ 0)
    (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    conformalLaplacian G f x = 0
      ↔ deriv (fun t => deriv (fun r => f (r, x.2)) t) x.1
        + deriv (fun t => deriv (fun r => f (x.1, r)) t) x.2 = 0 := by
  rw [conformalLaplacian, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd (inv_eq_zero.mp h) (hG x)
    · exact h
  · intro h
    exact Or.inr h

/-- The massless equation of a conformal metric agrees with that of the flat metric. -/
theorem conformalLaplacian_eq_zero_iff_flat {G : ℝ × ℝ → ℝ} (hG : ∀ x, G x ≠ 0)
    (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    conformalLaplacian G f x = 0 ↔ conformalLaplacian (fun _ => (1 : ℝ)) f x = 0 := by
  rw [conformalLaplacian_eq_zero_iff hG, conformalLaplacian_eq_zero_iff (fun _ => one_ne_zero)]

/-- **The coherent-state norm is the phase-free zeta value.** -/
theorem tsum_norm_sq_dirichletCoherentState {u : ℕ → ℂ}
    (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    ((∑' n : ℕ+, ‖dirichletCoherentState u s n‖ ^ 2 : ℝ) : ℂ)
      = riemannZeta (2 * (s.re : ℂ)) := by
  have hre : (1 : ℝ) < (2 * (s.re : ℂ)).re := by
    simp
    linarith
  have hzeta := zeta_eq_tsum_one_div_nat_cpow hre
  have hterm : ∀ n : ℕ+, ((‖dirichletCoherentState u s n‖ ^ 2 : ℝ) : ℂ)
      = 1 / ((n : ℕ) : ℂ) ^ (2 * (s.re : ℂ)) := by
    intro n
    rw [norm_sq_dirichletCoherentState hu s n]
    have hn0 : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    rw [Complex.ofReal_cpow hn0.le, Complex.ofReal_neg, Complex.cpow_neg, ← one_div]
    congr 2
    push_cast
    ring
  have hzeroterm : ∀ n : ℕ, n ∉ Set.range (fun m : ℕ+ => (m : ℕ)) →
      1 / ((n : ℕ) : ℂ) ^ (2 * (s.re : ℂ)) = 0 := by
    intro n hn
    have hn0 : n = 0 := by
      by_contra hcon
      exact hn ⟨⟨n, Nat.pos_of_ne_zero hcon⟩, rfl⟩
    subst hn0
    rw [Nat.cast_zero, Complex.zero_cpow (by
      intro hcon
      have : (2 * (s.re : ℂ)).re = 0 := by rw [hcon]; simp
      simp at this
      linarith), div_zero]
  have hsupp : Function.support (fun n : ℕ => 1 / ((n : ℕ) : ℂ) ^ (2 * (s.re : ℂ)))
      ⊆ Set.range (fun m : ℕ+ => (m : ℕ)) := by
    intro n hn
    by_contra hmem
    exact hn (hzeroterm n hmem)
  have hinj : Function.Injective (fun m : ℕ+ => (m : ℕ)) := fun m₁ m₂ h => PNat.coe_injective h
  rw [hzeta, ← hinj.tsum_eq hsupp, Complex.ofReal_tsum]
  exact tsum_congr hterm

/-- **The Born law of the coherent state is the phase-free zeta law.** -/
theorem bornProbability_dirichletCoherentState_eq {u : ℕ → ℂ}
    (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) {s : ℂ} (hs : 1 / 2 < s.re) (n : ℕ+) :
    ((bornProbability (dirichletCoherentState u s) n : ℝ) : ℂ)
      = (((n : ℕ) : ℝ) ^ (-(2 * s.re)) : ℝ) / riemannZeta (2 * (s.re : ℂ)) := by
  rw [bornProbability, norm_sq_dirichletCoherentState hu s n]
  rw [Complex.ofReal_div, ← tsum_norm_sq_dirichletCoherentState hu hs]

end

end RHTower
