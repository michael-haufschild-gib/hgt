import GaloisForLFunctions.HTGeometry.HillOscillatorBounds

/-!
# The energy bound in both time directions

The Grönwall estimate was proved forward in time. A probe has to be nonvanishing on a *two-sided*
neighbourhood of an event, so the same bound is needed for negative times.

Nothing about the oscillator needs redoing: reversing the time variable in the energy function alone
turns the backward estimate into the forward one, because the differential inequality
`|E'| ≤ 2K E` is invariant under `t ↦ -t`.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

section TwoSided

variable {ω dω u du ddu : ℝ → ℝ} {K b : ℝ}

/-- **The energy bound for negative times.** -/
theorem hillEnergy_le_of_logDeriv_le_neg
    (hω : ∀ t, HasDerivAt ω (dω t) t) (hu : ∀ t, HasDerivAt u (du t) t)
    (hdu : ∀ t, HasDerivAt du (ddu t) t) (heq : ∀ t, ddu t + ω t ^ (2 : ℕ) * u t = 0)
    (hωpos : ∀ t, 0 < ω t) (hK : ∀ t, |dω t| ≤ K * ω t) {t : ℝ} (ht : t ∈ Icc (-b) 0) :
    hillEnergy ω u du t ≤ hillEnergy ω u du 0 * Real.exp (2 * K * (-t)) := by
  set F : ℝ → ℝ := fun s => hillEnergy ω u du (-s) with hF
  have hFderiv : ∀ s : ℝ, HasDerivAt F (-(2 * (ω (-s) * dω (-s)) * u (-s) ^ (2 : ℕ))) s := by
    intro s
    have hbase := hasDerivAt_hillEnergy hω hu hdu heq (-s)
    have hcomp := hbase.comp s (hasDerivAt_neg s)
    have hval : 2 * (ω (-s) * dω (-s)) * u (-s) ^ (2 : ℕ) * -1
        = -(2 * (ω (-s) * dω (-s)) * u (-s) ^ (2 : ℕ)) := by ring
    rw [hval] at hcomp
    exact hcomp
  have hFnonneg : ∀ s : ℝ, 0 ≤ F s := fun s => hillEnergy_nonneg ω u du (-s)
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dω 0| := abs_nonneg _
    have h1 := hK 0
    have h2 := hωpos 0
    nlinarith
  have hbound : ∀ s ∈ Ico (0 : ℝ) b,
      ‖-(2 * (ω (-s) * dω (-s)) * u (-s) ^ (2 : ℕ))‖ ≤ 2 * K * ‖F s‖ + 0 := by
    intro s _
    have hωs : 0 < ω (-s) := hωpos (-s)
    have habs : |dω (-s)| ≤ K * ω (-s) := hK (-s)
    have hnorm : ‖-(2 * (ω (-s) * dω (-s)) * u (-s) ^ (2 : ℕ))‖
        = 2 * (ω (-s) * |dω (-s)|) * u (-s) ^ (2 : ℕ) := by
      rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_pos hωs,
        abs_of_nonneg (sq_nonneg (u (-s)))]
    have hFs : ‖F s‖ = F s := Real.norm_of_nonneg (hFnonneg s)
    rw [hnorm, hFs, add_zero]
    have hstep : 2 * (ω (-s) * |dω (-s)|) * u (-s) ^ (2 : ℕ)
        ≤ 2 * (ω (-s) * (K * ω (-s))) * u (-s) ^ (2 : ℕ) := by
      have := mul_le_mul_of_nonneg_left habs (le_of_lt hωs)
      nlinarith [sq_nonneg (u (-s))]
    refine hstep.trans ?_
    have hdu2 : (0 : ℝ) ≤ du (-s) ^ (2 : ℕ) := sq_nonneg _
    have hval : 2 * (ω (-s) * (K * ω (-s))) * u (-s) ^ (2 : ℕ)
        = 2 * K * (ω (-s) ^ (2 : ℕ) * u (-s) ^ (2 : ℕ)) := by ring
    have hFval : F s = du (-s) ^ (2 : ℕ) + ω (-s) ^ (2 : ℕ) * u (-s) ^ (2 : ℕ) := rfl
    rw [hval, hFval]
    nlinarith
  have hcont : ContinuousOn F (Icc 0 b) := fun s _ =>
    ((hFderiv s).continuousAt).continuousWithinAt
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s _ => (hFderiv s).hasDerivWithinAt)
    (le_of_eq (Real.norm_of_nonneg (hFnonneg 0))) hbound (-t) ⟨by linarith [ht.2], by
      have := ht.1
      linarith⟩
  rw [gronwallBound_ε0] at hgron
  have hFt : ‖F (-t)‖ = F (-t) := Real.norm_of_nonneg (hFnonneg (-t))
  rw [hFt] at hgron
  have hval : F (-t) = hillEnergy ω u du t := by
    rw [hF]
    simp
  have hzero : F 0 = hillEnergy ω u du 0 := by
    rw [hF]
    simp
  rw [hval, hzero] at hgron
  simpa using hgron

/-- **The energy bound in both directions.** -/
theorem hillEnergy_le_abs (hω : ∀ t, HasDerivAt ω (dω t) t) (hu : ∀ t, HasDerivAt u (du t) t)
    (hdu : ∀ t, HasDerivAt du (ddu t) t) (heq : ∀ t, ddu t + ω t ^ (2 : ℕ) * u t = 0)
    (hωpos : ∀ t, 0 < ω t) (hK : ∀ t, |dω t| ≤ K * ω t) (t : ℝ) :
    hillEnergy ω u du t ≤ hillEnergy ω u du 0 * Real.exp (2 * K * |t|) := by
  rcases le_or_gt 0 t with htpos | htneg
  · have h := hillEnergy_le_of_logDeriv_le (a := 0) (b := t) hω hu hdu heq hωpos hK
      (t := t) ⟨htpos, le_rfl⟩
    rw [sub_zero] at h
    rwa [abs_of_nonneg htpos]
  · have h := hillEnergy_le_of_logDeriv_le_neg (b := -t) hω hu hdu heq hωpos hK
      (t := t) ⟨by simp, le_of_lt htneg⟩
    rwa [abs_of_neg htneg]

end TwoSided

end GaloisForLFunctions.HTGeometry
