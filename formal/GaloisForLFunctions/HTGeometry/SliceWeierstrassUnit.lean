import GaloisForLFunctions.HTGeometry.SliceWeierstrassJoint
import GaloisForLFunctions.HTGeometry.CircleIntegralParamOpen

/-!
# The unit factor of Weierstrass' preparation theorem

Dividing a function by the monic polynomial of the roots of its slice leaves, on each slice, a
holomorphic nowhere vanishing factor.  That factor is recovered from its boundary values by
Cauchy's integral formula, and the resulting contour integral is holomorphic in *all* the
variables at once — the integrand is holomorphic on the open set where the circle avoids both the
evaluation point and the zeros of the Weierstrass polynomial.

* `HTGeometry.unitIntegrand`, `HTGeometry.sliceUnit`;
* `HTGeometry.factorization_sliceUnit`;
* `HTGeometry.differentiableOn_sliceUnit`;
* `HTGeometry.weierstrass_preparation`.
-/

open Complex Metric
open scoped Real Topology

namespace HTGeometry

variable {n : ℕ}

/-- The Cauchy integrand producing the unit factor: the first variable is the contour variable, the
second the evaluation point, the rest the parameters. -/
noncomputable def unitIntegrand (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (v : Fin (n + 2) → ℂ) : ℂ :=
  (v 0 - (Fin.tail v) 0)⁻¹ *
    (f (Fin.cons (v 0) (Fin.tail (Fin.tail v)))
      / sliceWeierstrass f t (Fin.cons (v 0) (Fin.tail (Fin.tail v))))

@[simp]
theorem unitIntegrand_cons (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (ζ : ℂ) (w : Fin (n + 1) → ℂ) :
    unitIntegrand f t (Fin.cons ζ w)
      = (ζ - w 0)⁻¹ *
        (f (Fin.cons ζ (Fin.tail w)) / sliceWeierstrass f t (Fin.cons ζ (Fin.tail w))) := by
  rw [unitIntegrand, Fin.cons_zero, Fin.tail_cons]

/-- The unit factor of Weierstrass' preparation theorem. -/
noncomputable def sliceUnit (f : (Fin (n + 1) → ℂ) → ℂ) (t : ℝ) (w : Fin (n + 1) → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ ζ in C(0, t), unitIntegrand f t (Fin.cons ζ w)

/-- **The unit factor is the boundary factor of the slice.**  On the disc it equals the nowhere
vanishing factor of the slice factorization, so the function is the Weierstrass polynomial times
the unit, and the unit does not vanish. -/
theorem factorization_sliceUnit {f : (Fin (n + 1) → ℂ) → ℂ} {t : ℝ} (ht : 0 < t)
    {y : Fin n → ℂ} (hy : SliceAdmissible f t y) {z : ℂ} (hz : ‖z‖ < t) :
    f (Fin.cons z y) = sliceWeierstrass f t (Fin.cons z y) * sliceUnit f t (Fin.cons z y) ∧
      sliceUnit f t (Fin.cons z y) ≠ 0 := by
  obtain ⟨t₁, g, ht₁, hgd, hgne, hfact⟩ := exists_slice_factorization ht hy
  have hclosed : closedBall (0 : ℂ) t ⊆ ball (0 : ℂ) t₁ := closedBall_subset_ball ht₁
  -- on the circle the integrand is the Cauchy kernel against `g`
  have hcircle : ∀ ζ ∈ sphere (0 : ℂ) t,
      unitIntegrand f t (Fin.cons ζ (Fin.cons z y)) = (ζ - z)⁻¹ • g ζ := by
    intro ζ hζ
    have hζt : ‖ζ‖ = t := by simpa using mem_sphere_iff_norm.1 hζ
    have hζball : ζ ∈ ball (0 : ℂ) t₁ := hclosed (by simp [hζt])
    have hWne : sliceWeierstrass f t (Fin.cons ζ y) ≠ 0 :=
      sliceWeierstrass_ne_zero_of_norm_eq ht hy hζt
    have hfz : f (Fin.cons ζ y) = sliceWeierstrass f t (Fin.cons ζ y) * g ζ := by
      rw [sliceWeierstrass_cons]
      exact hfact ζ hζball
    rw [unitIntegrand_cons, Fin.tail_cons, Fin.cons_zero, hfz, smul_eq_mul]
    field_simp
  -- Cauchy's integral formula
  have hzball : z ∈ ball (0 : ℂ) t := by
    rw [mem_ball_zero_iff]
    exact hz
  have hcauchy : (∮ ζ in C(0, t), (ζ - z)⁻¹ • g ζ)
      = (2 * (Real.pi : ℂ) * Complex.I) • g z := by
    refine Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hzball ?_ ?_
    · exact (hgd.mono hclosed).continuousOn
    · intro w hw
      have hwb : w ∈ ball (0 : ℂ) t₁ := hclosed (ball_subset_closedBall hw.1)
      exact hgd.differentiableAt (isOpen_ball.mem_nhds hwb)
  have hne0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hunit : sliceUnit f t (Fin.cons z y) = g z := by
    rw [sliceUnit, circleIntegral.integral_congr ht.le hcircle, hcauchy, smul_eq_mul]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hunit, sliceWeierstrass_cons]
    exact hfact z (hclosed (ball_subset_closedBall hzball))
  · rw [hunit]
    exact hgne z (hclosed (ball_subset_closedBall hzball))

/-- Keeping the first coordinate and dropping the second is linear, hence holomorphic. -/
theorem differentiable_consDropSecond :
    Differentiable ℂ (fun v : Fin (n + 2) → ℂ =>
      (Fin.cons (v 0) (Fin.tail (Fin.tail v)) : Fin (n + 1) → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  induction i using Fin.cases with
  | zero =>
      simp only [Fin.cons_zero]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 2) => ℂ) 0).differentiable
  | succ j =>
      simp only [Fin.cons_succ, Fin.tail]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 2) => ℂ)
        j.succ.succ).differentiable

/-- **The unit factor is holomorphic in all the variables.**  It is a contour integral whose
integrand is holomorphic on the open set where the contour variable avoids both the evaluation
point and the zeros of the Weierstrass polynomial. -/
theorem differentiableOn_sliceUnit {f : (Fin (n + 1) → ℂ) → ℂ} {U : Set (Fin (n + 1) → ℂ)}
    {V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U)
    {t : ℝ} (ht : 0 < t)
    (hdisc : ∀ y ∈ V, ∀ z : ℂ, ‖z‖ ≤ t → (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U)
    (hnez : ∀ y ∈ V, ∀ ζ : ℂ, ‖ζ‖ = t → f (Fin.cons ζ y) ≠ 0)
    (hadm : ∀ y ∈ V, SliceAdmissible f t y) (hVconn : IsPreconnected V)
    {y₀ : Fin n → ℂ} (hy₀ : y₀ ∈ V) :
    DifferentiableOn ℂ (sliceUnit f t)
      {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V ∧ ‖w 0‖ < t} := by
  classical
  set A : (Fin (n + 2) → ℂ) → (Fin (n + 1) → ℂ) :=
    fun v => Fin.cons (v 0) (Fin.tail (Fin.tail v)) with hA
  have hAdiff : Differentiable ℂ A := differentiable_consDropSecond
  have hAtail : ∀ v : Fin (n + 2) → ℂ, Fin.tail (A v) = Fin.tail (Fin.tail v) := by
    intro v
    rw [hA, Fin.tail_cons]
  -- the open set of parameters where the Weierstrass polynomial is defined and nonzero
  set Wv : Set (Fin (n + 1) → ℂ) := {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V} with hWv
  have hWvopen : IsOpen Wv := by
    have hcont : Continuous fun w : Fin (n + 1) → ℂ => Fin.tail w :=
      (tailLin : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ)).continuous
    exact hV.preimage hcont
  have hWdiff : DifferentiableOn ℂ (sliceWeierstrass f t) Wv :=
    differentiableOn_sliceWeierstrass hU hV hf ht hdisc hnez hadm hVconn hy₀
  set N : Set (Fin (n + 1) → ℂ) := Wv ∩ (sliceWeierstrass f t) ⁻¹' {(0 : ℂ)}ᶜ with hN
  have hNopen : IsOpen N :=
    hWdiff.continuousOn.isOpen_inter_preimage hWvopen isOpen_compl_singleton
  -- the open set carrying the integrand
  set D : (Fin (n + 2) → ℂ) → ℂ := fun v => v 0 - (Fin.tail v) 0 with hD
  have hDdiff : Differentiable ℂ D := by
    refine Differentiable.sub ?_ ?_
    · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 2) => ℂ) 0).differentiable
    · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 2) => ℂ)
        (0 : Fin (n + 1)).succ).differentiable
  set Ω : Set (Fin (n + 2) → ℂ) := A ⁻¹' (U ∩ N) ∩ D ⁻¹' {(0 : ℂ)}ᶜ with hΩ
  have hΩopen : IsOpen Ω :=
    ((hU.inter hNopen).preimage hAdiff.continuous).inter
      (isOpen_compl_singleton.preimage hDdiff.continuous)
  have hintdiff : DifferentiableOn ℂ (unitIntegrand f t) Ω := by
    intro v hv
    have hDv : D v ≠ 0 := hv.2
    have hAU : A v ∈ U := hv.1.1
    have hAN : A v ∈ N := hv.1.2
    have h1 : DifferentiableAt ℂ (fun v : Fin (n + 2) → ℂ => (D v)⁻¹) v :=
      (hDdiff v).inv hDv
    have h2 : DifferentiableAt ℂ (fun v : Fin (n + 2) → ℂ => f (A v)) v :=
      (hf.differentiableAt (hU.mem_nhds hAU)).comp v (hAdiff v)
    have h3 : DifferentiableAt ℂ (fun v : Fin (n + 2) → ℂ => sliceWeierstrass f t (A v)) v :=
      (hWdiff.differentiableAt (hWvopen.mem_nhds hAN.1)).comp v (hAdiff v)
    have h4 : sliceWeierstrass f t (A v) ≠ 0 := hAN.2
    have hmul : DifferentiableAt ℂ (fun v : Fin (n + 2) → ℂ =>
        (D v)⁻¹ * (f (A v) * (sliceWeierstrass f t (A v))⁻¹)) v :=
      h1.mul (h2.mul (h3.inv h4))
    refine (hmul.congr_of_eventuallyEq ?_).differentiableWithinAt
    refine Filter.Eventually.of_forall fun u => ?_
    rw [unitIntegrand, div_eq_mul_inv]
  -- the parameter set
  set P : Set (Fin (n + 1) → ℂ) := {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V ∧ ‖w 0‖ < t} with hP
  have hPopen : IsOpen P := by
    have h1 : IsOpen {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V} := hWvopen
    have h2 : IsOpen {w : Fin (n + 1) → ℂ | ‖w 0‖ < t} := by
      have hcont : Continuous fun w : Fin (n + 1) → ℂ => w 0 :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) 0).continuous
      exact isOpen_lt (hcont.norm) continuous_const
    exact h1.inter h2
  have hmem : ∀ (θ : ℝ) (w : Fin (n + 1) → ℂ), w ∈ P →
      (Fin.cons (circleMap 0 t θ) w : Fin (n + 2) → ℂ) ∈ Ω := by
    intro θ w hw
    have hζt : ‖circleMap 0 t θ‖ = t := by simpa using abs_of_pos ht
    have hAv : A (Fin.cons (circleMap 0 t θ) w) = Fin.cons (circleMap 0 t θ) (Fin.tail w) := by
      simp [hA, Fin.tail_cons]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hAv]
      exact hdisc (Fin.tail w) hw.1 _ (le_of_eq hζt)
    · rw [hWv, Set.mem_setOf_eq, hAv, Fin.tail_cons]
      exact hw.1
    · rw [Set.mem_preimage, hAv]
      exact sliceWeierstrass_ne_zero_of_norm_eq ht (hadm (Fin.tail w) hw.1) hζt
    · have hval : D (Fin.cons (circleMap 0 t θ) w) = circleMap 0 t θ - w 0 := by
        simp [hD, Fin.tail_cons]
      rw [Set.mem_preimage, hval]
      intro hcon
      have heq0 : circleMap 0 t θ - w 0 = 0 := hcon
      have hce : circleMap 0 t θ = w 0 := sub_eq_zero.mp heq0
      rw [hce] at hζt
      exact absurd hw.2 (by rw [hζt]; exact lt_irrefl t)
  intro w hw
  have hcirc := differentiableAt_circleIntegral_slice_open hΩopen hPopen hintdiff ht
    (fun _ => (1 : ℂ)) (by fun_prop) hmem hw
  have hcongr : (fun w : Fin (n + 1) → ℂ =>
      ∮ ζ in C(0, t), (1 : ℂ) • unitIntegrand f t (Fin.cons ζ w))
      = fun w : Fin (n + 1) → ℂ => ∮ ζ in C(0, t), unitIntegrand f t (Fin.cons ζ w) := by
    funext w'
    simp
  rw [hcongr] at hcirc
  exact ((hcirc.const_mul (2 * (Real.pi : ℂ) * Complex.I)⁻¹)).differentiableWithinAt

/-- **Weierstrass' preparation theorem.**  Near a point where the slices do not vanish on a fixed
circle, a holomorphic function of several complex variables is the product of a monic polynomial in
the distinguished variable — whose coefficients are holomorphic in the remaining variables and
whose roots are exactly the zeros of the slice inside the circle — and a holomorphic nowhere
vanishing unit. -/
theorem weierstrass_preparation {f : (Fin (n + 1) → ℂ) → ℂ} {U : Set (Fin (n + 1) → ℂ)}
    {V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U)
    {t : ℝ} (ht : 0 < t)
    (hdisc : ∀ y ∈ V, ∀ z : ℂ, ‖z‖ ≤ t → (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U)
    (hnez : ∀ y ∈ V, ∀ ζ : ℂ, ‖ζ‖ = t → f (Fin.cons ζ y) ≠ 0)
    (hadm : ∀ y ∈ V, SliceAdmissible f t y) (hVconn : IsPreconnected V)
    {y₀ : Fin n → ℂ} (hy₀ : y₀ ∈ V) :
    DifferentiableOn ℂ (sliceWeierstrass f t) {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V} ∧
      DifferentiableOn ℂ (sliceUnit f t)
        {w : Fin (n + 1) → ℂ | Fin.tail w ∈ V ∧ ‖w 0‖ < t} ∧
      ∀ y ∈ V, ∀ z : ℂ, ‖z‖ < t →
        f (Fin.cons z y) = sliceWeierstrass f t (Fin.cons z y) * sliceUnit f t (Fin.cons z y) ∧
          sliceUnit f t (Fin.cons z y) ≠ 0 :=
  ⟨differentiableOn_sliceWeierstrass hU hV hf ht hdisc hnez hadm hVconn hy₀,
    differentiableOn_sliceUnit hU hV hf ht hdisc hnez hadm hVconn hy₀,
    fun y hy _ hz => factorization_sliceUnit ht (hadm y hy) hz⟩

end HTGeometry
