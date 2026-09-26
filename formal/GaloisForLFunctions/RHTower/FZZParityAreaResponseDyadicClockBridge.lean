import GaloisForLFunctions.RHTower.FZZCigarParityLinearReplicaAreaHolonomySelector
import GaloisForLFunctions.RHTower.XiLineUnimodularClockExcessCriterion
import GaloisForLFunctions.RHTower.SeamStripRamification

/-!
# The FZZ parity area response is the orbit average of the dyadic prime clock

At the canonical parity-Mellin twist `τ(ρ) = −(log 2/2π)·i·(ρ − 1/2)` the normalized linear
replica-area response of the FZZ cigar is

`R(ρ) = 3/4 + (‖2^{ρ−1/2}‖² + ‖2^{(1−conj ρ)−1/2}‖²)/8`,

the average over the reflection orbit `{ρ, 1 − conj ρ}` of the squared modulus of the dyadic
prime clock `Λ(s) = 2^{s−1/2}`.  Hence at every point passivity `R ≤ 1` is exactly unimodularity
`‖Λ(ρ)‖ = 1`.

Consequently the FZZ-P source premise (divisor-mode passivity) is equivalent to: for every strip
window, the Cesàro energy of the dyadic divisor pencil `Σ_ρ m_ρ Λ(ρ)^n` minus its local squares is
eventually bounded.  The physical premise is therefore a statement about the prime-`2` clock
pencil of the zeros, the object classified by `XiLineUnimodularClockExcessCriterion`: an off-line
zero makes that energy grow exponentially, and no sub-unit passivity margin exists.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- The dyadic prime clock `2^{s−1/2}`. -/
def dyadicPrimeClock (s : ℂ) : ℂ := burnolPrimeCharacter 2 s

theorem norm_dyadicPrimeClock (s : ℂ) :
    ‖dyadicPrimeClock s‖ = (2 : ℝ) ^ (s.re - 1 / 2) :=
  norm_burnolPrimeCharacter_eq_rpow (by norm_num) s

theorem differentiable_dyadicPrimeClock : Differentiable ℂ dyadicPrimeClock := by
  intro s
  unfold dyadicPrimeClock burnolPrimeCharacter
  have h : DifferentiableAt ℂ (fun s : ℂ => s - 1 / 2) s :=
    differentiableAt_id.sub (differentiableAt_const _)
  simpa using h.const_cpow (Or.inl (by norm_num : ((2 : ℝ) : ℂ) ≠ 0))

theorem norm_dyadicPrimeClock_criticalLine (t : ℝ) :
    ‖dyadicPrimeClock ((1 / 2 : ℂ) + t * I)‖ = 1 := by
  rw [norm_dyadicPrimeClock]
  simp

theorem norm_dyadicPrimeClock_eq_one_iff (s : ℂ) :
    ‖dyadicPrimeClock s‖ = 1 ↔ s.re = 1 / 2 := by
  rw [norm_dyadicPrimeClock]
  constructor
  · intro h
    have h2 : Real.logb 2 ((2 : ℝ) ^ (s.re - 1 / 2)) = Real.logb 2 1 := by rw [h]
    rw [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_one] at h2
    linarith
  · intro h
    rw [h, sub_self, Real.rpow_zero]

/-- **Orbit-average form.**  The canonical-twist FZZ area response is the average of the squared
dyadic clock moduli over the reflection orbit, shifted by `3/4`. -/
theorem fzzAreaResponse_mellinTwist_eq_dyadicClockOrbitAverage (rho : ℂ) :
    fzzLinearReplicaAreaNormalizedResponse 1 (fzzCigarParityMellinTorusTwist rho).im =
      3 / 4 + (‖dyadicPrimeClock rho‖ ^ 2 + ‖dyadicPrimeClock (lineReflect rho)‖ ^ 2) / 8 := by
  rw [fzzLinearReplicaAreaNormalizedResponse_closedForm, fzzCigarParityMellinTorusTwist_im,
    norm_dyadicPrimeClock, norm_dyadicPrimeClock, lineReflect_re]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : -4 * Real.pi * ((1 : ℤ) : ℝ) * (-(Real.log 2 / (2 * Real.pi)) * (rho.re - 1 / 2)) =
      Real.log 2 * (2 * (rho.re - 1 / 2)) := by
    push_cast
    field_simp
    ring
  have h2 : 4 * Real.pi * ((1 : ℤ) : ℝ) * (-(Real.log 2 / (2 * Real.pi)) * (rho.re - 1 / 2)) =
      Real.log 2 * (2 * (1 - rho.re - 1 / 2)) := by
    push_cast
    field_simp
    ring
  rw [h1, h2, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  push_cast
  ring_nf

/-- Pointwise: area passivity is dyadic-clock unimodularity. -/
theorem fzzAreaResponse_mellinTwist_le_one_iff_dyadicClock_unimodular (rho : ℂ) :
    fzzLinearReplicaAreaNormalizedResponse 1 (fzzCigarParityMellinTorusTwist rho).im ≤ 1 ↔
      ‖dyadicPrimeClock rho‖ = 1 := by
  rw [fzzLinearReplicaAreaNormalizedResponse_mellinTorusTwist_le_one_iff,
    norm_dyadicPrimeClock_eq_one_iff]

/-- A nontrivial zeta zero of the open strip, or its conjugate, lies in some strip window of Xi
zeros. -/
theorem exists_window_mem_of_riemannZeta_eq_zero {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1)
    (hz : riemannZeta rho = 0) :
    ∃ z : ℂ, z.re = rho.re ∧ z ∈ (stripZeros_finite (|rho.im| + 1)).toFinset := by
  have hxi : xi rho = 0 := (xi_zero_iff_zeta_zero_of_mem_strip h0 h1).2 hz
  by_cases him : 0 ≤ rho.im
  · refine ⟨rho, rfl, ?_⟩
    rw [Set.Finite.mem_toFinset]
    refine ⟨⟨h0, h1, him, ?_⟩, hxi⟩
    rw [abs_of_nonneg him]
    linarith
  · push Not at him
    refine ⟨starRingEnd ℂ rho, by simp, ?_⟩
    rw [Set.Finite.mem_toFinset]
    refine ⟨⟨by simpa using h0, by simpa using h1, by simp; linarith, ?_⟩, ?_⟩
    · simp only [Complex.conj_im]
      rw [abs_of_neg him]
      linarith
    · rw [xi_conj, hxi, map_zero]

/-- **FZZ-P premise = bounded dyadic clock energy.**  Divisor-mode passivity of the FZZ linear
replica-area response holds exactly when, on every strip window, the Cesàro energy of the dyadic
divisor pencil minus local squares is eventually bounded. -/
theorem fzzLinearReplicaAreaDivisorPassive_iff_forall_dyadicClockExcess_bounded :
    FZZLinearReplicaAreaDivisorPassive ↔
      ∀ T : ℝ, ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, xiClockExcess dyadicPrimeClock T N ≤ C := by
  constructor
  · intro hpass T
    have hunit : ∀ rho ∈ (stripZeros_finite T).toFinset, ‖dyadicPrimeClock rho‖ = 1 := by
      intro rho hrho
      have hmem := (stripZeros_finite T).mem_toFinset.mp hrho
      have h0 := hmem.1.1
      have h1 := hmem.1.2.1
      have hz : riemannZeta rho = 0 := (xi_zero_iff_zeta_zero_of_mem_strip h0 h1).1 hmem.2
      have hmode : FZZCigarParityMellinMode rho :=
        (fzzCigarParityMellin_eq_zero_iff_riemannZeta_eq_zero h0 h1).2 hz
      exact (fzzAreaResponse_mellinTwist_le_one_iff_dyadicClock_unimodular rho).1
        (hpass rho h0 h1 hmode)
    have hlim := tendsto_xiClockExcess_aliasingCharge hunit
    exact ⟨xiClockAliasingCharge dyadicPrimeClock T + 1,
      hlim.eventually (eventually_le_nhds (by linarith))⟩
  · intro hbound rho h0 h1 hmode
    have hz : riemannZeta rho = 0 :=
      (fzzCigarParityMellin_eq_zero_iff_riemannZeta_eq_zero h0 h1).1 hmode
    obtain ⟨z, hzre, hzmem⟩ := exists_window_mem_of_riemannZeta_eq_zero h0 h1 hz
    have hunit : ∀ w ∈ (stripZeros_finite (|rho.im| + 1)).toFinset,
        ‖dyadicPrimeClock w‖ = 1 := by
      by_contra hcon
      push Not at hcon
      exact not_eventually_bounded_xiClockExcess differentiable_dyadicPrimeClock
        norm_dyadicPrimeClock_criticalLine hcon (hbound _)
    have hre : z.re = 1 / 2 := (norm_dyadicPrimeClock_eq_one_iff z).1 (hunit z hzmem)
    rw [fzzLinearReplicaAreaNormalizedResponse_mellinTorusTwist_le_one_iff, ← hzre, hre]

end

end RHTower
