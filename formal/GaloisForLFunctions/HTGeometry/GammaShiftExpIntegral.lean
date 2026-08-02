import GaloisForLFunctions.HTGeometry.GammaShiftShape

/-!
# Shifting Gamma by a real amount

Equation (14) of the shifted law compares two Gamma translates.  The exact relation behind it is
that the shift is the exponential of the integrated digamma:

`Γ(z + λ) = Γ(z)·exp(∫₀^λ ψ(z+u) du)`,

which holds whenever the segment `z + [0, λ]` stays in the right half plane.  It is the differential
equation `Γ′ = Γ·ψ` integrated along the segment: the function `u ↦ Γ(z+u)·exp(−∫₀^u ψ)` has zero
derivative.

With the vertical asymptotic `ψ(σ+it) = log s + o(1)` this is what turns the ratio of two translates
into the real power `s^λ`.
-/

open Filter Set Topology Function intervalIntegral

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Gamma has no zeros on the open right half plane. -/
theorem gamma_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : Complex.Gamma z ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m => ?_
  intro h
  rw [h] at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hz
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- Gamma is differentiable on the open right half plane. -/
theorem differentiableAt_gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  refine Complex.differentiableAt_Gamma z fun m => ?_
  intro h
  rw [h] at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hz
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- The right half plane is open. -/
theorem isOpen_rePos : IsOpen {z : ℂ | 0 < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- The derivative of Gamma is the digamma times Gamma. -/
theorem deriv_gamma_eq {z : ℂ} (hz : 0 < z.re) :
    deriv Complex.Gamma z = Complex.Gamma z * Complex.digamma z := by
  have hne : Complex.Gamma z ≠ 0 := gamma_ne_zero_of_re_pos hz
  rw [Complex.digamma_def, logDeriv_apply]
  field_simp

/-- The digamma is continuous on the open right half plane. -/
theorem continuousOn_digamma_rePos :
    ContinuousOn Complex.digamma {z : ℂ | 0 < z.re} := by
  have hΓ : AnalyticOnNhd ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_rePos
    intro z hz
    exact (differentiableAt_gamma_of_re_pos hz).differentiableWithinAt
  have hderiv : ContinuousOn (deriv Complex.Gamma) {z : ℂ | 0 < z.re} :=
    hΓ.deriv.continuousOn
  have hcont : ContinuousOn Complex.Gamma {z : ℂ | 0 < z.re} := hΓ.continuousOn
  intro z hz
  have hne : Complex.Gamma z ≠ 0 := gamma_ne_zero_of_re_pos hz
  have hdiv := (hderiv z hz).div (hcont z hz) hne
  refine hdiv.congr (fun w _ => ?_) ?_
  · rw [Complex.digamma_def, logDeriv_apply]
    rfl
  · rw [Complex.digamma_def, logDeriv_apply]
    rfl

/-- The real shifts of a point of the right half plane that stay in it. -/
theorem isOpen_shiftSet (z : ℂ) : IsOpen {v : ℝ | -z.re < v} :=
  isOpen_lt continuous_const continuous_id

/-- Along a real shift that stays in the right half plane, the digamma is continuous. -/
theorem continuousOn_digamma_shift (z : ℂ) :
    ContinuousOn (fun v : ℝ => Complex.digamma (z + (v : ℂ))) {v : ℝ | -z.re < v} := by
  intro v hv
  have hre : 0 < (z + (v : ℂ)).re := by
    have : (z + (v : ℂ)).re = z.re + v := by simp
    rw [this]
    have hv' : -z.re < v := hv
    linarith
  have hmap : ContinuousAt (fun v : ℝ => z + (v : ℂ)) v := by fun_prop
  have hout : ContinuousAt Complex.digamma (z + (v : ℂ)) :=
    (continuousOn_digamma_rePos.continuousAt (isOpen_rePos.mem_nhds hre))
  have hcomp : ContinuousAt (fun v : ℝ => Complex.digamma (z + (v : ℂ))) v :=
    ContinuousAt.comp (g := Complex.digamma) (f := fun v : ℝ => z + (v : ℂ)) (x := v) hout hmap
  exact hcomp.continuousWithinAt

/-- **Gamma shifts by the exponential of the integrated digamma.**  On the right half plane the
translate `Γ(z+λ)` is `Γ(z)` times `exp` of the digamma integrated along the segment. -/
theorem gamma_shift_exp_integral {z : ℂ} (hz : 0 < z.re) {lam : ℝ} (hlam : 0 ≤ lam) :
    Complex.Gamma (z + (lam : ℂ))
      = Complex.Gamma z * Complex.exp (∫ u in (0 : ℝ)..lam, Complex.digamma (z + (u : ℂ))) := by
  classical
  set S : Set ℝ := {v : ℝ | -z.re < v} with hS
  have hSopen : IsOpen S := isOpen_shiftSet z
  have hcontS : ContinuousOn (fun v : ℝ => Complex.digamma (z + (v : ℂ))) S :=
    continuousOn_digamma_shift z
  have hsub : Set.uIcc (0 : ℝ) lam ⊆ S := by
    intro v hv
    rw [Set.uIcc_of_le hlam] at hv
    have h0 : (0 : ℝ) ≤ v := hv.1
    have : -z.re < 0 := by linarith
    exact lt_of_lt_of_le this h0
  have hcontI : ContinuousOn (fun v : ℝ => Complex.digamma (z + (v : ℂ))) (Set.uIcc 0 lam) :=
    hcontS.mono hsub
  have hint : IntervalIntegrable (fun v : ℝ => Complex.digamma (z + (v : ℂ)))
      MeasureTheory.volume 0 lam := hcontI.intervalIntegrable
  set Ψ : ℝ → ℂ := fun u => ∫ v in (0 : ℝ)..u, Complex.digamma (z + (v : ℂ)) with hΨ
  -- the fundamental theorem of calculus along the segment
  have hderivΨ : ∀ u ∈ Set.uIcc (0 : ℝ) lam,
      HasDerivAt Ψ (Complex.digamma (z + (u : ℂ))) u := by
    intro u hu
    have huS : u ∈ S := hsub hu
    have hsubu : Set.uIcc (0 : ℝ) u ⊆ Set.uIcc (0 : ℝ) lam := by
      rw [Set.uIcc_of_le hlam]
      rw [Set.uIcc_of_le (by rw [Set.uIcc_of_le hlam] at hu; exact hu.1)]
      rw [Set.uIcc_of_le hlam] at hu
      exact Set.Icc_subset_Icc le_rfl hu.2
    refine intervalIntegral.integral_hasDerivAt_right (hint.mono_set hsubu) ?_ ?_
    · exact (hcontS.stronglyMeasurableAtFilter hSopen u huS)
    · exact (hcontS.continuousAt (hSopen.mem_nhds huS))
  -- the derivative of the normalized translate vanishes
  have hzero : ∀ u ∈ Set.uIcc (0 : ℝ) lam,
      HasDerivAt (fun y : ℝ => Complex.Gamma (z + (y : ℂ)) * Complex.exp (-Ψ y)) 0 u := by
    intro u hu
    have huS : u ∈ S := hsub hu
    have hre : 0 < (z + (u : ℂ)).re := by
      have hval : (z + (u : ℂ)).re = z.re + u := by simp
      have hu' : -z.re < u := huS
      rw [hval]
      linarith
    have hinner : HasDerivAt (fun w : ℂ => z + w) 1 ((u : ℝ) : ℂ) :=
      (hasDerivAt_id _).const_add z
    have houter : HasDerivAt Complex.Gamma (deriv Complex.Gamma (z + (u : ℂ))) (z + (u : ℂ)) :=
      (differentiableAt_gamma_of_re_pos hre).hasDerivAt
    have hcomp : HasDerivAt (fun w : ℂ => Complex.Gamma (z + w))
        (deriv Complex.Gamma (z + (u : ℂ)) * 1) ((u : ℝ) : ℂ) := houter.comp _ hinner
    have hΓ : HasDerivAt (fun y : ℝ => Complex.Gamma (z + (y : ℂ)))
        (Complex.Gamma (z + (u : ℂ)) * Complex.digamma (z + (u : ℂ))) u := by
      have h := hcomp.comp_ofReal
      rw [mul_one, deriv_gamma_eq hre] at h
      exact h
    have hexp : HasDerivAt (fun y : ℝ => Complex.exp (-Ψ y))
        (Complex.exp (-Ψ u) * -Complex.digamma (z + (u : ℂ))) u := ((hderivΨ u hu).neg).cexp
    have hprod := hΓ.mul hexp
    have hval : Complex.Gamma (z + (u : ℂ)) * Complex.digamma (z + (u : ℂ))
          * Complex.exp (-Ψ u)
        + Complex.Gamma (z + (u : ℂ))
          * (Complex.exp (-Ψ u) * -Complex.digamma (z + (u : ℂ))) = 0 := by
      ring
    rw [hval] at hprod
    exact hprod
  -- hence the normalized translate is constant on the segment
  have hΨ0 : Ψ 0 = 0 := by
    rw [hΨ]
    simp
  have heq : Complex.Gamma (z + (lam : ℂ)) * Complex.exp (-Ψ lam) = Complex.Gamma z := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hzero
      (intervalIntegrable_const (c := (0 : ℂ)))
    rw [intervalIntegral.integral_zero] at h
    have hstep := sub_eq_zero.mp h.symm
    have h0 : Complex.Gamma (z + (((0 : ℝ) : ℂ))) * Complex.exp (-Ψ 0) = Complex.Gamma z := by
      rw [hΨ0, neg_zero, Complex.exp_zero, mul_one]
      norm_num
    rw [h0] at hstep
    exact hstep
  rw [← heq, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

end

end GaloisForLFunctions.HTGeometry
