import GaloisForLFunctions.RHTower.GaussianPoleFilter
import GaloisForLFunctions.RHTower.ModularArcLineModelBlind

/-!
# Pole-filtered arc generators

For a point `u ∈ [−½, ½]` of the modular bottom arc, with `y = √(1 − u²)`, let
`φ_u(x) = (y / ((x − u)² + y²))^{1/2}` (`arcPointVector`) be the `s = ½` Poisson vector of `z = u + iy`,
and `ψ_u = φ_u + φ_{−u}` (`arcPairVector`). Its log-scale profile is
`Q_u(v) = e^{v/2} ψ_u(e^v) = (y/2)^{1/2} [(cosh v + u)^{−1/2} + (cosh v − u)^{−1/2}]`
(`exp_half_mul_arcPairVector`). It is even and strictly positive definite, and decays only like
`e^{−|v|/2}` (the logarithmic edge).

With the pole filter `ǧ_K` of `GaussianPoleFilter`, the **filtered generator** is

`h_{K,u}(x) = ψ_u(x) − ∫ ǧ_K(w) e^{−w/2} ψ_u(x e^{−w}) dw`  (`filteredArcVector`).

In the variable `w` the subtracted term is a superposition of Poisson vectors at the points
`e^w(±u + iy)` of the two rays through `±u + iy`, with the signed density `ǧ_K`.

* `h_{K,u}` is differentiable with derivative `filteredArcDeriv` (`hasDerivAt_filteredArcVector`), even
  (`filteredArcVector_neg`) and inversion invariant: `h(1/x) = |x| h(x)` (`filteredArcVector_inv`).
* Its profile is `e^{v/2} h(e^v) = Q_u(v) − (ǧ_K ⋆ Q_u)(v)` (`exp_half_mul_filteredArcVector`).
* **Strict positive definiteness** (`integral_cos_mul_filteredArcProfile_pos`): the cosine transform is
  `(1 − e^{−K(τ²+¼)})² Q̂_u(τ) > 0` for every real `τ`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The `s = ½` Poisson vector `φ_u(x) = (y/((x − u)² + y²))^{1/2}` of the arc point `u + iy`. -/
def arcPointVector (u : ArcParam) (x : ℝ) : ℝ :=
  (modularArcHeight u / ((x - u) ^ 2 + modularArcHeight u ^ 2)) ^ (1 / 2 : ℝ)

/-- The symmetric pair `ψ_u = φ_u + φ_{−u}`. -/
def arcPairVector (u : ArcParam) (x : ℝ) : ℝ := arcPointVector u x + arcPointVector (arcNeg u) x

/-- The derivative of `ψ_u`. -/
def arcPairDeriv (u : ArcParam) (x : ℝ) : ℝ := -(arcLineKernel x u + arcLineKernel x (arcNeg u))

/-- The log-scale profile `Q_u(v) = e^{v/2} ψ_u(e^v)`. -/
def arcPairProfile (u : ArcParam) (v : ℝ) : ℝ := Real.exp (v / 2) * arcPairVector u (Real.exp v)

theorem modularArcHeight_ge_half (u : ArcParam) : 1 / 2 ≤ modularArcHeight u := by
  have hy := modularArcHeight_pos u.2
  have h2 := modularArcHeight_sq u.2
  nlinarith [u.2.1, u.2.2]

theorem modularArcHeight_le_one (u : ArcParam) : modularArcHeight u ≤ 1 := by
  unfold modularArcHeight; rw [Real.sqrt_le_one]; nlinarith [sq_nonneg (u : ℝ)]

theorem continuous_arcPointVector (u : ArcParam) : Continuous (arcPointVector u) := by
  have hy := modularArcHeight_pos u.2
  unfold arcPointVector
  exact Continuous.rpow_const (by
    refine Continuous.div continuous_const (by fun_prop) fun x => ?_
    exact (sub_sq_add_modularArcHeight_sq_pos u x).ne') fun _ => Or.inr (by norm_num)

theorem continuous_arcPairVector (u : ArcParam) : Continuous (arcPairVector u) :=
  (continuous_arcPointVector u).add (continuous_arcPointVector _)

theorem continuous_arcPairDeriv (u : ArcParam) : Continuous (arcPairDeriv u) := by
  have h1 : Continuous fun x => arcLineKernel x u :=
    continuous_arcLineKernel.comp (continuous_id.prodMk continuous_const)
  have h2 : Continuous fun x => arcLineKernel x (arcNeg u) :=
    continuous_arcLineKernel.comp (continuous_id.prodMk continuous_const)
  exact (h1.add h2).neg

theorem arcPointVector_nonneg (u : ArcParam) (x : ℝ) : 0 ≤ arcPointVector u x :=
  Real.rpow_nonneg (div_nonneg (modularArcHeight_pos u.2).le
    (sub_sq_add_modularArcHeight_sq_pos u x).le) _

theorem arcPointVector_le_two (u : ArcParam) (x : ℝ) : arcPointVector u x ≤ 2 := by
  have hy := modularArcHeight_pos u.2
  have hy2 := modularArcHeight_ge_half u
  have hA := sub_sq_add_modularArcHeight_sq_pos u x
  have hb : modularArcHeight u / ((x - u) ^ 2 + modularArcHeight u ^ 2) ≤ 4 := by
    rw [div_le_iff₀ hA]; nlinarith [sq_nonneg (x - u)]
  unfold arcPointVector
  rw [← Real.sqrt_eq_rpow]
  calc Real.sqrt (modularArcHeight u / ((x - u) ^ 2 + modularArcHeight u ^ 2))
      ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hb
    _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem abs_arcPairVector_le (u : ArcParam) (x : ℝ) : |arcPairVector u x| ≤ 4 := by
  unfold arcPairVector
  rw [abs_of_nonneg (add_nonneg (arcPointVector_nonneg _ _) (arcPointVector_nonneg _ _))]
  linarith [arcPointVector_le_two u x, arcPointVector_le_two (arcNeg u) x]

theorem abs_arcPairDeriv_le (u : ArcParam) (x : ℝ) : |arcPairDeriv u x| ≤ 64 * (1 + x ^ 2)⁻¹ := by
  unfold arcPairDeriv
  rw [abs_neg]
  calc |arcLineKernel x u + arcLineKernel x (arcNeg u)|
      ≤ |arcLineKernel x u| + |arcLineKernel x (arcNeg u)| := abs_add_le _ _
    _ ≤ 32 * (1 + x ^ 2)⁻¹ + 32 * (1 + x ^ 2)⁻¹ :=
        add_le_add (abs_arcLineDeriv_kernel_le u x) (abs_arcLineDeriv_kernel_le _ x)
    _ = 64 * (1 + x ^ 2)⁻¹ := by ring

theorem abs_arcPairDeriv_le_const (u : ArcParam) (x : ℝ) : |arcPairDeriv u x| ≤ 64 := by
  calc |arcPairDeriv u x| ≤ 64 * (1 + x ^ 2)⁻¹ := abs_arcPairDeriv_le u x
    _ ≤ 64 * 1 := by gcongr; exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
    _ = 64 := mul_one _

theorem hasDerivAt_arcPairVector (u : ArcParam) (x : ℝ) :
    HasDerivAt (arcPairVector u) (arcPairDeriv u x) x := by
  have h := (hasDerivAt_arcPoisson u x).add (hasDerivAt_arcPoisson (arcNeg u) x)
  refine h.congr_deriv ?_
  unfold arcPairDeriv; ring

theorem arcPointVector_arcNeg (u : ArcParam) (x : ℝ) :
    arcPointVector (arcNeg u) x = arcPointVector u (-x) := by
  simp only [arcPointVector, arcNeg, modularArcHeight_neg]
  congr 2
  ring

theorem arcPairVector_neg (u : ArcParam) (x : ℝ) : arcPairVector u (-x) = arcPairVector u x := by
  unfold arcPairVector
  rw [arcPointVector_arcNeg, arcPointVector_arcNeg, neg_neg, add_comm]

/-- **Inversion for one arc point.** -/
theorem arcPointVector_inv (u : ArcParam) {x : ℝ} (hx : x ≠ 0) :
    arcPointVector u (1 / x) = |x| * arcPointVector u x := by
  have hy := modularArcHeight_pos u.2
  have hA := sub_sq_add_modularArcHeight_sq_pos u x
  have e : (1 / x - u) ^ 2 + modularArcHeight u ^ 2 =
      ((x - u) ^ 2 + modularArcHeight u ^ 2) / x ^ 2 := by
    rw [sub_sq_add_modularArcHeight_sq, sub_sq_add_modularArcHeight_sq]
    field_simp
    ring
  unfold arcPointVector
  rw [e, div_div_eq_mul_div, mul_div_right_comm, Real.mul_rpow (by positivity) (by positivity)]
  have hx2 : (x ^ 2) ^ (1 / 2 : ℝ) = |x| := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  rw [hx2, mul_comm]

theorem arcPairVector_inv (u : ArcParam) {x : ℝ} (hx : x ≠ 0) :
    arcPairVector u (1 / x) = |x| * arcPairVector u x := by
  unfold arcPairVector
  rw [arcPointVector_inv u hx, arcPointVector_inv _ hx, mul_add]

/-- `e^{v/2} φ_u(e^v) = (y/2)^{1/2} (cosh v − u)^{−1/2}`. -/
theorem exp_half_mul_arcPointVector (u : ArcParam) (v : ℝ) :
    Real.exp (v / 2) * arcPointVector u (Real.exp v) = arcPoissonKernel u v := by
  have hy := modularArcHeight_pos u.2
  have hc := cosh_sub_arc_pos u v
  have e1 : (Real.exp v - u) ^ 2 + modularArcHeight u ^ 2 =
      Real.exp v * (2 * (Real.cosh v - u)) := by
    rw [sub_sq_add_modularArcHeight_sq, Real.cosh_eq]
    have h1 : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
    linear_combination (-1 : ℝ) * h1
  unfold arcPointVector arcPoissonKernel
  rw [e1, Real.div_rpow hy.le (by positivity), Real.mul_rpow (Real.exp_pos v).le (by positivity),
    Real.mul_rpow (by norm_num) hc.le, Real.sqrt_eq_rpow, Real.div_rpow hy.le (by norm_num)]
  have hneg : (Real.cosh v - u) ^ (-1 / 2 : ℝ) = ((Real.cosh v - u) ^ (1 / 2 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hc.le]; norm_num
  rw [hneg]
  have he : Real.exp (v / 2) = Real.exp v ^ (1 / 2 : ℝ) := by
    rw [← Real.exp_mul]; ring_nf
  rw [he]
  have hev : 0 < Real.exp v ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (Real.exp_pos v) _
  have h2 : 0 < (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos two_pos _
  have hcr : 0 < (Real.cosh v - u) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hc _
  field_simp

/-- `Q_u(v) = (y/2)^{1/2} [(cosh v + u)^{−1/2} + (cosh v − u)^{−1/2}]`. -/
theorem arcPairProfile_eq (u : ArcParam) (v : ℝ) :
    arcPairProfile u v = Real.sqrt (modularArcHeight u / 2) * symCoshKernel u v := by
  unfold arcPairProfile arcPairVector
  rw [mul_add, exp_half_mul_arcPointVector, exp_half_mul_arcPointVector, arcPoissonKernel_add_neg]

theorem continuous_arcPairProfile (u : ArcParam) : Continuous (arcPairProfile u) := by
  unfold arcPairProfile
  exact (by fun_prop : Continuous fun v : ℝ => Real.exp (v / 2)).mul
    ((continuous_arcPairVector u).comp Real.continuous_exp)

theorem arcPairProfile_neg (u : ArcParam) (v : ℝ) : arcPairProfile u (-v) = arcPairProfile u v := by
  rw [arcPairProfile_eq, arcPairProfile_eq]
  simp [symCoshKernel, Real.cosh_neg]

theorem abs_arcPairProfile_le (u : ArcParam) (v : ℝ) :
    |arcPairProfile u v| ≤ 4 * Real.cosh v ^ (-(1 / 2) : ℝ) := by
  have h : arcPairProfile u v = arcPoissonKernel u v + arcPoissonKernel (arcNeg u) v := by
    unfold arcPairProfile arcPairVector
    rw [mul_add, exp_half_mul_arcPointVector, exp_half_mul_arcPointVector]
  rw [h]
  calc |arcPoissonKernel u v + arcPoissonKernel (arcNeg u) v|
      ≤ |arcPoissonKernel u v| + |arcPoissonKernel (arcNeg u) v| := abs_add_le _ _
    _ ≤ 2 * Real.cosh v ^ (-(1 / 2) : ℝ) + 2 * Real.cosh v ^ (-(1 / 2) : ℝ) :=
        add_le_add (arcPoissonKernel_le _ _) (arcPoissonKernel_le _ _)
    _ = 4 * Real.cosh v ^ (-(1 / 2) : ℝ) := by ring

theorem integrable_arcPairProfile (u : ArcParam) : Integrable (arcPairProfile u) := by
  have hI := _root_.HTGeometry.integrable_cosh_rpow_neg (s := 1 / 2) (by norm_num)
  refine (hI.const_mul 4).mono' (continuous_arcPairProfile u).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs]
  have := abs_arcPairProfile_le u v
  simpa [show (-(1 / 2) : ℝ) = -(1 / 2 : ℝ) by norm_num] using this

/-! ### The filtered generator -/

/-- The filtered generator `h_{K,u}(x) = ψ_u(x) − ∫ ǧ_K(w) e^{−w/2} ψ_u(x e^{−w}) dw`. -/
def filteredArcVector (K : ℝ) (u : ArcParam) (x : ℝ) : ℝ :=
  arcPairVector u x -
    ∫ w, poleFilter K w * (Real.exp (-(w / 2)) * arcPairVector u (x * Real.exp (-w)))

/-- Its derivative. -/
def filteredArcDeriv (K : ℝ) (u : ArcParam) (x : ℝ) : ℝ :=
  arcPairDeriv u x -
    ∫ w, poleFilter K w * (Real.exp (-(3 * w / 2)) * arcPairDeriv u (x * Real.exp (-w)))

/-- The filtered profile `Q_u − ǧ_K ⋆ Q_u`. -/
def filteredArcProfile (K : ℝ) (u : ArcParam) (v : ℝ) : ℝ :=
  arcPairProfile u v - ∫ w, poleFilter K w * arcPairProfile u (v - w)

theorem integrable_abs_poleFilter_mul_rexp {K : ℝ} (hK : 0 < K) (c : ℝ) :
    Integrable fun w => |poleFilter K w * Real.exp (w * c)| :=
  (integrable_poleFilter_mul_rexp hK c).abs

theorem integrable_filteredArcVector_integrand {K : ℝ} (hK : 0 < K) (u : ArcParam) (x : ℝ) :
    Integrable fun w =>
      poleFilter K w * (Real.exp (-(w / 2)) * arcPairVector u (x * Real.exp (-w))) := by
  refine ((integrable_abs_poleFilter_mul_rexp hK (-(1 / 2))).const_mul 4).mono'
    (((continuous_poleFilter K).mul ((by fun_prop : Continuous fun w : ℝ => Real.exp (-(w / 2))).mul
      ((continuous_arcPairVector u).comp (by fun_prop)))).aestronglyMeasurable)
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
    abs_of_pos (Real.exp_pos _), show w * -(1 / 2) = -(w / 2) by ring]
  have := abs_arcPairVector_le u (x * Real.exp (-w))
  have h0 := abs_nonneg (poleFilter K w)
  have h1 := Real.exp_pos (-(w / 2))
  nlinarith [mul_nonneg h0 h1.le]

theorem hasDerivAt_filteredArcVector {K : ℝ} (hK : 0 < K) (u : ArcParam) (x : ℝ) :
    HasDerivAt (filteredArcVector K u) (filteredArcDeriv K u x) x := by
  have hcont : ∀ x', Continuous fun w : ℝ =>
      poleFilter K w * (Real.exp (-(w / 2)) * arcPairVector u (x' * Real.exp (-w))) := fun x' =>
    (continuous_poleFilter K).mul ((by fun_prop : Continuous fun w : ℝ => Real.exp (-(w / 2))).mul
      ((continuous_arcPairVector u).comp (by fun_prop)))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (x' w : ℝ) =>
      poleFilter K w * (Real.exp (-(w / 2)) * arcPairVector u (x' * Real.exp (-w))))
    (F' := fun (x' w : ℝ) =>
      poleFilter K w * (Real.exp (-(3 * w / 2)) * arcPairDeriv u (x' * Real.exp (-w))))
    (x₀ := x) (bound := fun w => 64 * |poleFilter K w * Real.exp (w * (-(3 / 2)))|)
    (s := univ) Filter.univ_mem
    (Eventually.of_forall fun x' => (hcont x').aestronglyMeasurable)
    (integrable_filteredArcVector_integrand hK u x)
    (((continuous_poleFilter K).mul ((by fun_prop : Continuous fun w : ℝ =>
      Real.exp (-(3 * w / 2))).mul ((continuous_arcPairDeriv u).comp
        (by fun_prop)))).aestronglyMeasurable)
    (Eventually.of_forall fun w x' _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
        abs_of_pos (Real.exp_pos _), show w * -(3 / 2) = -(3 * w / 2) by ring]
      have := abs_arcPairDeriv_le_const u (x' * Real.exp (-w))
      have h0 := abs_nonneg (poleFilter K w)
      have h1 := Real.exp_pos (-(3 * w / 2))
      nlinarith [mul_nonneg h0 h1.le])
    ((integrable_abs_poleFilter_mul_rexp hK (-(3 / 2))).const_mul 64)
    (Eventually.of_forall fun w x' _ => by
      have hc : HasDerivAt (fun x'' : ℝ => x'' * Real.exp (-w)) (Real.exp (-w)) x' := by
        simpa using (hasDerivAt_id x').mul_const (Real.exp (-w))
      have h := ((hasDerivAt_arcPairVector u (x' * Real.exp (-w))).comp x' hc).const_mul
        (Real.exp (-(w / 2))) |>.const_mul (poleFilter K w)
      refine h.congr_deriv ?_
      have he : Real.exp (-(w / 2)) * Real.exp (-w) = Real.exp (-(3 * w / 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [← he]; ring)
  exact (hasDerivAt_arcPairVector u x).sub key.2

theorem filteredArcVector_neg (K : ℝ) (u : ArcParam) (x : ℝ) :
    filteredArcVector K u (-x) = filteredArcVector K u x := by
  unfold filteredArcVector
  rw [arcPairVector_neg]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [neg_mul, arcPairVector_neg]

/-- **Inversion invariance**: `h(1/x) = |x| h(x)`. -/
theorem filteredArcVector_inv (K : ℝ) (u : ArcParam) {x : ℝ} (hx : x ≠ 0) :
    filteredArcVector K u (1 / x) = |x| * filteredArcVector K u x := by
  unfold filteredArcVector
  rw [arcPairVector_inv u hx, mul_sub]
  congr 1
  have hinv : ∀ w : ℝ, poleFilter K w * (Real.exp (-(w / 2)) *
      arcPairVector u (1 / x * Real.exp (-w))) =
      |x| * (poleFilter K (-w) * (Real.exp (-(-w / 2)) *
        arcPairVector u (x * Real.exp (-(-w))))) := by
    intro w
    have hxe : x * Real.exp w ≠ 0 := mul_ne_zero hx (Real.exp_pos w).ne'
    have e1 : 1 / x * Real.exp (-w) = 1 / (x * Real.exp w) := by
      rw [Real.exp_neg]; field_simp
    rw [e1, arcPairVector_inv u hxe, abs_mul, abs_of_pos (Real.exp_pos w), poleFilter_neg, neg_neg]
    have e2 : Real.exp (-(w / 2)) * Real.exp w = Real.exp (-(-w / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← e2]; ring
  simp_rw [hinv]
  rw [integral_const_mul]
  congr 1
  exact integral_neg_eq_self (fun w => poleFilter K w * (Real.exp (-(w / 2)) *
    arcPairVector u (x * Real.exp (-w)))) volume

/-- **The profile of the filtered generator** is `Q_u − ǧ_K ⋆ Q_u`. -/
theorem exp_half_mul_filteredArcVector (K : ℝ) (u : ArcParam) (v : ℝ) :
    Real.exp (v / 2) * filteredArcVector K u (Real.exp v) = filteredArcProfile K u v := by
  unfold filteredArcVector filteredArcProfile
  rw [mul_sub, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [arcPairProfile]
  have e1 : Real.exp v * Real.exp (-w) = Real.exp (v - w) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (v / 2) * Real.exp (-(w / 2)) = Real.exp ((v - w) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, ← e2]; ring

theorem integral_cos_mul_arcPairProfile_shift (u : ArcParam) (τ w : ℝ) :
    ∫ v, Real.cos (τ * v) * arcPairProfile u (v - w) =
      Real.cos (τ * w) * ∫ v, Real.cos (τ * v) * arcPairProfile u v := by
  have hQ := integrable_arcPairProfile u
  have hc : Integrable fun v => Real.cos (τ * v) * arcPairProfile u v :=
    hQ.bdd_mul (by fun_prop) (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hs : Integrable fun v => Real.sin (τ * v) * arcPairProfile u v :=
    hQ.bdd_mul (by fun_prop) (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hodd : ∫ v, Real.sin (τ * v) * arcPairProfile u v = 0 := by
    have h := integral_neg_eq_self (fun v => Real.sin (τ * v) * arcPairProfile u v) volume
    have e : (fun v => Real.sin (τ * -v) * arcPairProfile u (-v)) =
        fun v => -(Real.sin (τ * v) * arcPairProfile u v) := by
      funext v; rw [arcPairProfile_neg, mul_neg, Real.sin_neg]; ring
    rw [e, integral_neg] at h
    linarith
  rw [← integral_add_right_eq_self (μ := volume)
    (fun v => Real.cos (τ * v) * arcPairProfile u (v - w)) w]
  have e : ∀ v, Real.cos (τ * (v + w)) * arcPairProfile u (v + w - w) =
      Real.cos (τ * w) * (Real.cos (τ * v) * arcPairProfile u v) -
        Real.sin (τ * w) * (Real.sin (τ * v) * arcPairProfile u v) := by
    intro v
    rw [add_sub_cancel_right, mul_add, Real.cos_add]; ring
  simp_rw [e]
  rw [integral_sub (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul, hodd,
    mul_zero, sub_zero]

/-- **The cosine transform of the filtered profile** is `(1 − ∫ ǧ_K cos(τ·)) Q̂_u(τ)`. -/
theorem integral_cos_mul_filteredArcProfile {K : ℝ} (hK : 0 < K) (u : ArcParam) (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * filteredArcProfile K u v =
      (1 - ∫ w, poleFilter K w * Real.cos (τ * w)) *
        ∫ v, Real.cos (τ * v) * arcPairProfile u v := by
  have hQ := integrable_arcPairProfile u
  have hconv : Integrable (fun p : ℝ × ℝ => poleFilter K p.2 * arcPairProfile u (p.1 - p.2))
      (volume.prod volume) :=
    (integrable_poleFilter hK).convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hQ
  have hF : Integrable (fun p : ℝ × ℝ =>
      Real.cos (τ * p.1) * (poleFilter K p.2 * arcPairProfile u (p.1 - p.2)))
      (volume.prod volume) :=
    hconv.bdd_mul (by fun_prop) (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hc : Integrable fun v => Real.cos (τ * v) * arcPairProfile u v :=
    hQ.bdd_mul (by fun_prop) (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hconvI : Integrable fun v =>
      Real.cos (τ * v) * ∫ w, poleFilter K w * arcPairProfile u (v - w) := by
    refine hF.integral_prod_left.congr (Eventually.of_forall fun v => ?_)
    simp only
    rw [← integral_const_mul]
  have hswap := integral_integral_swap (f := fun v w =>
    Real.cos (τ * v) * (poleFilter K w * arcPairProfile u (v - w))) hF
  unfold filteredArcProfile
  simp_rw [mul_sub]
  rw [integral_sub hc hconvI]
  have h2 : ∫ v, Real.cos (τ * v) * ∫ w, poleFilter K w * arcPairProfile u (v - w) =
      (∫ w, poleFilter K w * Real.cos (τ * w)) * ∫ v, Real.cos (τ * v) * arcPairProfile u v := by
    have e1 : ∀ v, Real.cos (τ * v) * ∫ w, poleFilter K w * arcPairProfile u (v - w) =
        ∫ w, Real.cos (τ * v) * (poleFilter K w * arcPairProfile u (v - w)) := fun v => by
      rw [← integral_const_mul]
    simp_rw [e1]
    rw [hswap]
    have e2 : ∀ w, ∫ v, Real.cos (τ * v) * (poleFilter K w * arcPairProfile u (v - w)) =
        poleFilter K w * Real.cos (τ * w) * ∫ v, Real.cos (τ * v) * arcPairProfile u v := by
      intro w
      have e3 : ∀ v, Real.cos (τ * v) * (poleFilter K w * arcPairProfile u (v - w)) =
          poleFilter K w * (Real.cos (τ * v) * arcPairProfile u (v - w)) := fun v => by ring
      simp_rw [e3]
      rw [integral_const_mul, integral_cos_mul_arcPairProfile_shift]; ring
    simp_rw [e2]
    rw [integral_mul_const]
  rw [h2]; ring

/-- **The filtered generator is strictly positive definite.** -/
theorem integral_cos_mul_filteredArcProfile_pos {K : ℝ} (hK : 0 < K) (u : ArcParam) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * filteredArcProfile K u v := by
  rw [integral_cos_mul_filteredArcProfile hK]
  refine mul_pos (one_sub_integral_poleFilter_mul_cos_pos hK τ) ?_
  have hc : |(u : ℝ)| < 1 := by rw [abs_lt]; constructor <;> linarith [u.2.1, u.2.2]
  have e : (fun v => Real.cos (τ * v) * arcPairProfile u v) = fun v =>
      Real.sqrt (modularArcHeight u / 2) * (Real.cos (τ * v) * symCoshKernel u v) := by
    funext v; rw [arcPairProfile_eq]; ring
  rw [e, integral_const_mul]
  exact mul_pos (Real.sqrt_pos.mpr (by have := modularArcHeight_pos u.2; positivity))
    (integral_cos_mul_symCoshKernel_pos hc τ)

end

end RHTower
