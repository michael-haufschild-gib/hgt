import GaloisForLFunctions.HTGeometry.GeometricThetaUnbounded
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The standard twist of the zeta function and its spectrum

The twisted series `∑_{n ≥ 1} e^{2πiαn} n^{-s}` has a meromorphic continuation in
`s` for every real `α`, and the continuation is entire exactly when `α` is not an
integer: on the integers the twist collapses to the zeta function, whose pole at
`s = 1` obstructs differentiability there.

So the singular set of the twist family is the integers, its shift spectrum is the
positive integers, and from any singular point the nearest other singular point is
at distance one.  That distance is the cusp gap of the zeta function.
-/

open Filter Topology Complex HurwitzZeta
open GaloisForLFunctions.HTGeometry

namespace RHTower

section StandardTwist

/-- The standard twist of the zeta function at a real shift. -/
noncomputable def zetaStandardTwist (α : ℝ) (s : ℂ) : ℂ :=
  expZeta ((α : ℝ) : UnitAddCircle) s

/-- **The twist is the theta series.**  On the half plane of absolute convergence
the continued twist agrees with the theta series of the constant family in degree
one evaluated at the real point `α`. -/
theorem thetaSeries_eq_zetaStandardTwist (α : ℝ) {s : ℂ} (hs : 1 < s.re) :
    thetaSeries oneCoeff 1 s (α : ℂ) = zetaStandardTwist α s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp only [Complex.zero_re] at hs
    linarith
  have hsum := hasSum_expZeta_of_one_lt_re α hs
  have hcongr : ∀ n : ℕ, thetaTerm oneCoeff 1 s (α : ℂ) n
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ) * (n : ℂ)) / (n : ℂ) ^ s := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [thetaTerm_zero, Nat.cast_zero, Complex.zero_cpow hs0, div_zero]
    · have hd : ((n : ℝ)) ^ (1 / (1 : ℝ)) = (n : ℝ) := by
        rw [one_div_one, Real.rpow_one]
      rw [thetaTerm, if_neg hn.ne', oneCoeff, one_mul, hd, Complex.cpow_neg,
        div_eq_mul_inv, Complex.ofReal_natCast]
      ring
  rw [thetaSeries, (hsum.congr_fun hcongr).tsum_eq, zetaStandardTwist]

/-- The zeta function is not differentiable at its pole. -/
theorem not_differentiableAt_riemannZeta_one : ¬ DifferentiableAt ℂ riemannZeta 1 := by
  intro hd
  have hlin : ContinuousAt (fun s : ℂ => s - 1) 1 :=
    (continuous_id.sub continuous_const).continuousAt
  have hcont : ContinuousAt (fun s : ℂ => (s - 1) * riemannZeta s) 1 :=
    hlin.mul hd.continuousAt
  have h0 : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have h : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] (1 : ℂ))
        (𝓝 ((1 - 1) * riemannZeta 1)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h
  exact zero_ne_one (tendsto_nhds_unique h0 riemannZeta_residue_one)

/-- The untwisted series is the zeta function, so it is not entire. -/
theorem not_differentiable_expZeta_zero :
    ¬ Differentiable ℂ (expZeta (0 : UnitAddCircle)) := by
  rw [expZeta_zero]
  intro h
  exact not_differentiableAt_riemannZeta_one (h 1)

/-- **The spectral dichotomy for the exponential zeta function.**  The twist is
entire exactly off the spectrum. -/
theorem differentiable_expZeta_iff (a : UnitAddCircle) :
    Differentiable ℂ (expZeta a) ↔ a ≠ 0 := by
  constructor
  · intro h hne
    rw [hne] at h
    exact not_differentiable_expZeta_zero h
  · exact differentiable_expZeta_of_ne_zero

/-- A real shift is spectral exactly when it is an integer. -/
theorem coe_unitAddCircle_eq_zero_iff (α : ℝ) :
    ((α : ℝ) : UnitAddCircle) = 0 ↔ ∃ m : ℤ, (m : ℝ) = α := by
  rw [AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := α)]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by simpa using hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by simpa using hm⟩

/-- **The spectral dichotomy in the shift variable.**  The standard twist of the
zeta function fails to be entire exactly at the integers. -/
theorem not_differentiable_zetaStandardTwist_iff (α : ℝ) :
    ¬ Differentiable ℂ (zetaStandardTwist α) ↔ ∃ m : ℤ, (m : ℝ) = α := by
  have h := differentiable_expZeta_iff ((α : ℝ) : UnitAddCircle)
  rw [show zetaStandardTwist α = expZeta ((α : ℝ) : UnitAddCircle) from rfl,
    not_congr h, not_not, coe_unitAddCircle_eq_zero_iff]

/-- The singular set of the standard twist family. -/
def zetaTwistSingularSet : Set ℝ := {α : ℝ | ¬ Differentiable ℂ (zetaStandardTwist α)}

theorem mem_zetaTwistSingularSet (α : ℝ) :
    α ∈ zetaTwistSingularSet ↔ ∃ m : ℤ, (m : ℝ) = α :=
  not_differentiable_zetaStandardTwist_iff α

/-- **The shift spectrum consists of singular shifts.** -/
theorem shiftSpectrum_subset_singular :
    shiftSpectrum oneCoeff 1 1 ⊆ zetaTwistSingularSet := by
  rintro x ⟨m, hm, -, rfl⟩
  refine (mem_zetaTwistSingularSet _).mpr ⟨(m : ℤ), ?_⟩
  simp only [div_one, Real.rpow_one, one_mul]
  push_cast
  ring

/-- **Every singular shift is a spectral point translated by the shift lattice.** -/
theorem singular_iff_spectrum_translate (α : ℝ) :
    α ∈ zetaTwistSingularSet
      ↔ ∃ x ∈ shiftSpectrum oneCoeff 1 1, ∃ m : ℤ, α = x + (m : ℝ) := by
  rw [mem_zetaTwistSingularSet]
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨1, ⟨1, one_pos, ?_, ?_⟩, m - 1, ?_⟩
    · rw [oneCoeff]; exact one_ne_zero
    · simp only [Nat.cast_one, div_one, Real.rpow_one, one_mul]
    · push_cast; ring
  · rintro ⟨x, ⟨k, hk, -, rfl⟩, m, rfl⟩
    refine ⟨(k : ℤ) + m, ?_⟩
    simp only [div_one, Real.rpow_one, one_mul]
    push_cast
    ring

end StandardTwist

section CuspGap

/-- **The cusp gap of the zeta function is one.**  From any singular shift the
nearest other singular shift is at distance exactly one. -/
theorem infDist_zetaTwistSingularSet_sdiff {α : ℝ} (hα : α ∈ zetaTwistSingularSet) :
    Metric.infDist α (zetaTwistSingularSet \ {α}) = 1 := by
  obtain ⟨k, rfl⟩ := (mem_zetaTwistSingularSet α).mp hα
  have hmem : ((k : ℝ) + 1) ∈ zetaTwistSingularSet \ {(k : ℝ)} := by
    refine ⟨(mem_zetaTwistSingularSet _).mpr ⟨k + 1, by push_cast; ring⟩, ?_⟩
    simp
  have hne : (zetaTwistSingularSet \ {(k : ℝ)}).Nonempty := ⟨_, hmem⟩
  refine le_antisymm ?_ ?_
  · have hle := Metric.infDist_le_dist_of_mem (x := ((k : ℤ) : ℝ)) hmem
    rw [Real.dist_eq] at hle
    simpa using hle
  · refine (Metric.le_infDist hne).mpr fun β hβ => ?_
    obtain ⟨hsing, hne'⟩ := hβ
    obtain ⟨m, rfl⟩ := (mem_zetaTwistSingularSet β).mp hsing
    have hmk : m ≠ k := by
      intro h
      exact hne' (by simp [h])
    have h1 : (1 : ℤ) ≤ |m - k| := by
      rcases lt_or_gt_of_ne (sub_ne_zero.mpr hmk) with h | h
      · rw [abs_of_neg h]; omega
      · rw [abs_of_pos h]; omega
    have h2 : (1 : ℝ) ≤ |(m : ℝ) - (k : ℝ)| := by
      have h3 := (Int.cast_le (R := ℝ)).mpr h1
      rwa [Int.cast_one, Int.cast_abs, Int.cast_sub] at h3
    rw [Real.dist_eq, abs_sub_comm]
    exact h2

end CuspGap

end RHTower
