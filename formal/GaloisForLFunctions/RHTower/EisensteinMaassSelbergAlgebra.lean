import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinLineInvariance
import GaloisForLFunctions.RHTower.EisensteinLineConstantTerm

/-!
# The Maass–Selberg right-hand side: algebra, derivative at the diagonal, and the diagonal limit

With `A(u) = Λ(1+2u)`, `B(u) = Λ(2u)` (`Λ = reflectedCompletedLambda`), the completed Eisenstein
series `E*(·, ½+u)` has Weyl constant part `c_u(Y) = B(u) Y^{½−u} + A(u) Y^{½+u}`.  The cleared
Maass–Selberg right-hand side is

`R(u, v, Y) = (u−v) A(u)A(v) Y^{u+v} + (u+v) [A(u)B(v) Y^{u−v} − B(u)A(v) Y^{v−u}] − (u−v) B(u)B(v) Y^{−u−v}`,

so that `(u−v)(u+v)·⟨Λ^Y E_u, Λ^Y E_v⟩ = R(u, v, Y)`.  This module proves: `R(u, u, Y) = 0`, the
`v`-derivative of `R` at `v = u` is `msDiag u Y`, and the limit lemma: if `P` is continuous at `u`
and `(u−v)(u+v) P(v) = R(u, v, Y)` for `v ≠ u` near `u`, then `P(u) = −msDiag u Y / (2u)`.  On the
line `u = it` the derivative functional equation `Λ'(2it) = −Λ'(1−2it)` turns the diagonal value into
`[A²Y^{2it} − B²Y^{−2it}]/(2it) + 2A·Λ'(1−2it) + 2B·Λ'(1+2it) + 2AB·log Y`.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- `A(u) = Λ(1 + 2u)`, the coefficient of `Y^{½+u}`. -/
def msA (u : ℂ) : ℂ := reflectedCompletedLambda (1 + 2 * u)

/-- `B(u) = Λ(2u)`, the coefficient of `Y^{½−u}`. -/
def msB (u : ℂ) : ℂ := reflectedCompletedLambda (2 * u)

/-- The cleared Maass–Selberg right-hand side. -/
def msRight (u v : ℂ) (Y : ℝ) : ℂ :=
  ((u - v) * (msA u * msA v)) * (Y : ℂ) ^ (u + v) +
    (u + v) * ((msA u * msB v) * (Y : ℂ) ^ (u - v) - (msB u * msA v) * (Y : ℂ) ^ (v - u)) -
    ((u - v) * (msB u * msB v)) * (Y : ℂ) ^ (-u - v)

/-- The `v`-derivative of `msRight u v Y` at `v = u`. -/
def msDiag (u : ℂ) (Y : ℝ) : ℂ :=
  -(msA u) ^ 2 * (Y : ℂ) ^ (u + u) + (msB u) ^ 2 * (Y : ℂ) ^ (-u - u) +
    (u + u) * (msA u * (2 * deriv reflectedCompletedLambda (2 * u)) -
      msB u * (2 * deriv reflectedCompletedLambda (1 + 2 * u)) -
      2 * (msA u * msB u) * Complex.log (Y : ℂ))

theorem msRight_self (u : ℂ) (Y : ℝ) : msRight u u Y = 0 := by
  unfold msRight
  simp only [sub_self, Complex.cpow_zero, zero_mul]
  ring

/-! ## The Weyl constant part in terms of `A`, `B` -/

theorem cuspConstantCoefficient_true (u : ℂ) :
    d4BMCompletedEisensteinCuspConstantCoefficient u true = msA u := rfl

theorem cuspConstantCoefficient_false (u : ℂ) :
    d4BMCompletedEisensteinCuspConstantCoefficient u false = msB u := rfl

theorem cuspWeylExponent_true (u : ℂ) :
    d4BMCompletedEisensteinCuspWeylExponent u true = 1 / 2 + u := by
  unfold d4BMCompletedEisensteinCuspWeylExponent d4BMCuspSign
  simp

theorem cuspWeylExponent_false (u : ℂ) :
    d4BMCompletedEisensteinCuspWeylExponent u false = 1 / 2 - u := by
  unfold d4BMCompletedEisensteinCuspWeylExponent d4BMCuspSign
  simp
  ring

/-- `c_u(Y) = B(u) Y^{½−u} + A(u) Y^{½+u}`. -/
theorem cuspConstantPart_eq_msAB (u : ℂ) (Y : ℝ) :
    d4BMCompletedEisensteinCuspConstantPart .scalar u Y =
      msB u * (Y : ℂ) ^ (1 / 2 - u) + msA u * (Y : ℂ) ^ (1 / 2 + u) := by
  unfold d4BMCompletedEisensteinCuspConstantPart d4BMCompletedEisensteinCuspConstantTerm
    d4BMCompletedEisensteinCuspConstantMaassFactor
  rw [cuspConstantCoefficient_true, cuspConstantCoefficient_false, cuspWeylExponent_true,
    cuspWeylExponent_false]
  simp

/-! ## Derivatives of `A`, `B` on the parameter domain -/

theorem im_one_add_two_mul (u : ℂ) : (1 + 2 * u).im = 2 * u.im := by simp

theorem im_two_mul (u : ℂ) : (2 * u).im = 2 * u.im := by simp

theorem hasDerivAt_msA {u : ℂ} (hu : u ∈ eisensteinLineDomain) :
    HasDerivAt msA (2 * deriv reflectedCompletedLambda (1 + 2 * u)) u := by
  have him : (1 + 2 * u).im ≠ 0 := by rw [im_one_add_two_mul]; exact by linarith [hu.2]
  have h := (differentiableAt_reflectedCompletedLambda him).hasDerivAt
  have h2 : HasDerivAt (fun v : ℂ => 1 + 2 * v) 2 u := by
    simpa using ((hasDerivAt_id u).const_mul (2 : ℂ)).const_add (1 : ℂ)
  have := h.comp u h2
  refine this.congr_deriv ?_
  ring

theorem hasDerivAt_msB {u : ℂ} (hu : u ∈ eisensteinLineDomain) :
    HasDerivAt msB (2 * deriv reflectedCompletedLambda (2 * u)) u := by
  have him : (2 * u).im ≠ 0 := by rw [im_two_mul]; exact by linarith [hu.2]
  have h := (differentiableAt_reflectedCompletedLambda him).hasDerivAt
  have h2 : HasDerivAt (fun v : ℂ => 2 * v) 2 u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℂ)
  have := h.comp u h2
  refine this.congr_deriv ?_
  ring

/-- **The `v`-derivative of the right-hand side at the diagonal.** -/
theorem hasDerivAt_msRight {u : ℂ} (hu : u ∈ eisensteinLineDomain) {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (fun v => msRight u v Y) (msDiag u Y) u := by
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hA := hasDerivAt_msA hu
  have hB := hasDerivAt_msB hu
  have hadd : HasDerivAt (fun v : ℂ => u + v) 1 u := (hasDerivAt_id u).const_add u
  have hsub : HasDerivAt (fun v : ℂ => u - v) (-1) u := (hasDerivAt_id u).const_sub u
  have hsub' : HasDerivAt (fun v : ℂ => v - u) 1 u := (hasDerivAt_id u).sub_const u
  have hneg : HasDerivAt (fun v : ℂ => -u - v) (-1) u := (hasDerivAt_id u).const_sub (-u)
  have h1 := hadd.const_cpow (c := (Y : ℂ)) (Or.inl hYne)
  have h2 := hsub.const_cpow (c := (Y : ℂ)) (Or.inl hYne)
  have h3 := hsub'.const_cpow (c := (Y : ℂ)) (Or.inl hYne)
  have h4 := hneg.const_cpow (c := (Y : ℂ)) (Or.inl hYne)
  have hAA : HasDerivAt (fun v => msA u * msA v)
      (msA u * (2 * deriv reflectedCompletedLambda (1 + 2 * u))) u := hA.const_mul (msA u)
  have hAB : HasDerivAt (fun v => msA u * msB v)
      (msA u * (2 * deriv reflectedCompletedLambda (2 * u))) u := hB.const_mul (msA u)
  have hBA : HasDerivAt (fun v => msB u * msA v)
      (msB u * (2 * deriv reflectedCompletedLambda (1 + 2 * u))) u := hA.const_mul (msB u)
  have hBB : HasDerivAt (fun v => msB u * msB v)
      (msB u * (2 * deriv reflectedCompletedLambda (2 * u))) u := hB.const_mul (msB u)
  have T1 := (hsub.mul hAA).mul h1
  have T2 := hadd.mul ((hAB.mul h2).sub (hBA.mul h3))
  have T3 := (hsub.mul hBB).mul h4
  have H := (T1.add T2).sub T3
  refine H.congr_deriv ?_
  unfold msDiag
  simp only [Pi.mul_apply, Pi.sub_apply, sub_self, Complex.cpow_zero, mul_one,
    one_mul, mul_neg, neg_mul, zero_mul, add_zero]
  ring

/-! ## The diagonal limit -/

theorem ne_zero_of_mem_eisensteinLineDomain {u : ℂ} (hu : u ∈ eisensteinLineDomain) : u ≠ 0 := by
  intro h
  have := hu.2
  rw [h] at this
  simp at this

/-- **Diagonal limit.**  If `P` is continuous at `u` and `(u−v)(u+v) P v = R(u,v,Y)` for `v ≠ u`
near `u`, then `P u = −msDiag u Y / (2u)`. -/
theorem eq_neg_msDiag_div_of_cleared {P : ℂ → ℂ} {u : ℂ} (hu : u ∈ eisensteinLineDomain)
    {Y : ℝ} (hY : 0 < Y) (hP : ContinuousAt P u)
    (h : ∀ᶠ v in 𝓝[≠] u, (u - v) * (u + v) * P v = msRight u v Y) :
    P u = -msDiag u Y / (2 * u) := by
  have hu0 : u ≠ 0 := ne_zero_of_mem_eisensteinLineDomain hu
  have huu : u + u ≠ 0 := by
    intro h0
    apply hu0
    have : (2 : ℂ) * u = 0 := by rw [two_mul]; exact h0
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  have hslope : Tendsto (slope (fun v => msRight u v Y) u) (𝓝[≠] u) (𝓝 (msDiag u Y)) :=
    hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_msRight hu hY)
  have hden : Tendsto (fun v : ℂ => u + v) (𝓝[≠] u) (𝓝 (u + u)) :=
    tendsto_nhdsWithin_of_tendsto_nhds ((continuous_const.add continuous_id).tendsto u)
  have hlim : Tendsto (fun v => (-(slope (fun v => msRight u v Y) u v)) / (u + v)) (𝓝[≠] u)
      (𝓝 (-(msDiag u Y) / (u + u))) :=
    hslope.neg.div hden huu
  have hP' : Tendsto P (𝓝[≠] u) (𝓝 (P u)) := tendsto_nhdsWithin_of_tendsto_nhds hP.tendsto
  have hne : ∀ᶠ v in 𝓝[≠] u, u + v ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((continuous_const.add continuous_id).continuousAt.eventually_ne huu)
  have hne' : ∀ᶠ v in 𝓝[≠] u, v ≠ u := self_mem_nhdsWithin
  have heq : (fun v => (-(slope (fun v => msRight u v Y) u v)) / (u + v)) =ᶠ[𝓝[≠] u] P := by
    filter_upwards [h, hne, hne'] with v hv hv1 hv2
    rw [slope_def_field, msRight_self, sub_zero]
    have hvu : v - u ≠ 0 := sub_ne_zero.mpr hv2
    have huv : u - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv2)
    rw [← hv]
    field_simp
    ring
  have := hlim.congr' heq
  have hval := tendsto_nhds_unique hP' this
  rw [hval]
  congr 1
  ring

/-! ## The line: the derivative functional equation -/

theorem reflectedCompletedLambda_eventuallyEq_completed {s : ℂ} (hs : s.im ≠ 0) :
    reflectedCompletedLambda =ᶠ[𝓝 s] completedRiemannZeta := by
  have hG : ∀ᶠ w in 𝓝 s, w.Gammaℝ ≠ 0 := by
    have hcont : ContinuousAt Complex.Gammaℝ s := by
      have hd : DifferentiableAt ℂ Complex.Gammaℝ s := by
        have hG : Complex.Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) :=
          funext Complex.Gammaℝ_def
        rw [hG]
        refine DifferentiableAt.mul ?_ ?_
        · refine DifferentiableAt.const_cpow ?_ (Or.inl (by exact_mod_cast Real.pi_ne_zero))
          fun_prop
        · refine DifferentiableAt.comp s ?_ (by fun_prop)
          refine Complex.differentiableAt_Gamma _ fun m => ?_
          intro h
          have him := congrArg Complex.im h
          simp at him
          exact hs (by linarith)
      exact hd.continuousAt
    exact hcont.eventually_ne (Gammaℝ_ne_zero_of_im_ne_zero hs)
  have hne : ∀ᶠ w in 𝓝 s, w ≠ 0 := by
    have : s ≠ 0 := by
      intro h; apply hs; rw [h]; simp
    exact continuousAt_id.eventually_ne this
  filter_upwards [hG, hne] with w hw1 hw2
  exact reflectedCompletedLambda_eq_completed hw2 hw1

theorem differentiableAt_completedRiemannZeta' {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s := by
  have : completedRiemannZeta = fun s => completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
    funext completedRiemannZeta_eq
  rw [this]
  refine ((differentiable_completedZeta₀ s).sub ?_).sub ?_
  · exact (differentiableAt_const _).div differentiableAt_id h0
  · refine (differentiableAt_const _).div ((differentiableAt_const _).sub differentiableAt_id) ?_
    exact sub_ne_zero.mpr (Ne.symm h1)

/-- `Λ'(s) = −Λ'(1 − s)` off the real axis. -/
theorem deriv_reflectedCompletedLambda_one_sub {s : ℂ} (hs : s.im ≠ 0) :
    deriv reflectedCompletedLambda s = -deriv reflectedCompletedLambda (1 - s) := by
  have hs' : (1 - s).im ≠ 0 := by simp [hs]
  have h0 : s ≠ 0 := by intro h; apply hs; rw [h]; simp
  have h1 : s ≠ 1 := by intro h; apply hs; rw [h]; simp
  have h0' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1' : 1 - s ≠ 1 := by
    intro h; apply h0; linear_combination -h
  rw [(reflectedCompletedLambda_eventuallyEq_completed hs).deriv_eq,
    (reflectedCompletedLambda_eventuallyEq_completed hs').deriv_eq]
  have hd := (differentiableAt_completedRiemannZeta' h0' h1').hasDerivAt
  have hcomp : HasDerivAt (fun w => completedRiemannZeta (1 - w))
      (deriv completedRiemannZeta (1 - s) * (-1)) s :=
    hd.comp s ((hasDerivAt_id s).const_sub 1)
  have hfe : (fun w => completedRiemannZeta (1 - w)) = completedRiemannZeta :=
    funext completedRiemannZeta_one_sub
  rw [hfe] at hcomp
  rw [hcomp.deriv]
  ring

/-- The diagonal value on the line, in the symmetric form. -/
def msLineValue (t Y : ℝ) : ℂ :=
  ((msA ((t : ℂ) * I)) ^ 2 * (Y : ℂ) ^ (2 * ((t : ℂ) * I)) -
      (msB ((t : ℂ) * I)) ^ 2 * (Y : ℂ) ^ (-(2 * ((t : ℂ) * I)))) / (2 * ((t : ℂ) * I)) +
    2 * msA ((t : ℂ) * I) * deriv reflectedCompletedLambda (1 - 2 * ((t : ℂ) * I)) +
    2 * msB ((t : ℂ) * I) * deriv reflectedCompletedLambda (1 + 2 * ((t : ℂ) * I)) +
    2 * (msA ((t : ℂ) * I) * msB ((t : ℂ) * I)) * Complex.log (Y : ℂ)

theorem neg_msDiag_div_line {t : ℝ} (ht : 0 < t) (Y : ℝ) :
    -msDiag ((t : ℂ) * I) Y / (2 * ((t : ℂ) * I)) = msLineValue t Y := by
  have him : (2 * ((t : ℂ) * I)).im ≠ 0 := by simp; exact ht.ne'
  have hfe := deriv_reflectedCompletedLambda_one_sub him
  unfold msDiag msLineValue
  rw [hfe]
  have h2 : (2 * ((t : ℂ) * I)) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ht.ne' this
  have e1 : (t : ℂ) * I + (t : ℂ) * I = 2 * ((t : ℂ) * I) := by ring
  have e2 : -((t : ℂ) * I) - (t : ℂ) * I = -(2 * ((t : ℂ) * I)) := by ring
  rw [e1, e2]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp
  ring

end

end RHTower
