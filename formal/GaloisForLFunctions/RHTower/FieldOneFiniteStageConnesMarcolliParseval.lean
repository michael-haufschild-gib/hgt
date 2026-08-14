import GaloisForLFunctions.RHTower.FieldOneFiniteStageFiniteFourierParseval
import Mathlib.MeasureTheory.Group.Integral

/-!
# Full finite-stage additive-adele Fourier--Parseval theorem

Exact source Fourier kernel splitting, pure-tensor factorization, integrability,
polarization, and Parseval on the algebraic Bruhat--Schwartz tensor core.
-/

namespace GaloisForLFunctions.RHTower
noncomputable section
open Function IsDedekindDomain MeasureTheory Set TopologicalSpace
open scoped BigOperators ComplexConjugate TensorProduct FourierTransform

theorem fieldOneFiniteStageCircleAddChar_neg_mul_split
    (S : Finset (HeightOneSpectrum ℤ))
    (a w : FieldOneFiniteStageAdele S) :
    ((fieldOneFiniteStageCircleAddChar S (-(a * w)) : Circle) : ℂ) =
      (Real.fourierChar (a.1 * w.1) : ℂ) *
        fieldOneFiniteStageFiniteStandardAddChar S
          (fun v => -(a.2 v * w.2 v)) := by
  classical
  rw [fieldOneFiniteStageCircleAddChar,
    AddChar.compAddMonoidHom_apply]
  change
    ((AddCircle.toCircle
      (-((((-(a * w)).1 : ℝ) : UnitAddCircle)) +
        ∑ v ∈ S, fieldOneFiniteStageLocalTerm S (-(a * w)) v) : Circle) : ℂ) = _
  rw [AddCircle.toCircle_add, Circle.coe_mul]
  congr 1
  · have harg : -((((-(a * w)).1 : ℝ) : UnitAddCircle)) =
        ((a.1 * w.1 : ℝ) : UnitAddCircle) := by
      change ((-(-((a.1 * w.1 : ℝ))) : ℝ) : UnitAddCircle) = _
      simp
    have hcircle : AddCircle.toCircle
          ((a.1 * w.1 : ℝ) : UnitAddCircle) =
        Real.fourierChar (a.1 * w.1) := by
      rw [AddCircle.toCircle_apply_mk, Real.fourierChar_apply']
      congr 1
      ring
    exact congrArg (fun z : Circle => (z : ℂ))
      ((congrArg AddCircle.toCircle harg).trans hcircle)
  · have htoCircle : ∀ (T : Finset (HeightOneSpectrum ℤ))
        (u : HeightOneSpectrum ℤ → UnitAddCircle),
        ((AddCircle.toCircle (∑ v ∈ T, u v) : Circle) : ℂ) =
          ∏ v ∈ T, ((AddCircle.toCircle (u v) : Circle) : ℂ) := by
      intro T u
      induction T using Finset.induction_on with
      | empty => simp
      | @insert v T hv ih =>
          simp only [Finset.sum_insert hv, Finset.prod_insert hv,
            AddCircle.toCircle_add, Circle.coe_mul, ih]
    rw [htoCircle]
    rw [← Finset.prod_coe_sort]
    rw [fieldOneFiniteStageFiniteStandardAddChar]
    apply Fintype.prod_congr
    intro v
    simp only [fieldOneFiniteStageLocalTerm, dif_pos v.2]
    rfl

theorem fieldOneFiniteStageBruhatFourierEval_tmul
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (w : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageBruhatFourierEval S (f ⊗ₜ[ℂ] phi) w =
      (𝓕 f (-w.1)) *
        fieldOneFiniteStageFiniteBruhatFourier S phi w.2 := by
  rw [fieldOneFiniteStageBruhatFourierEval_apply]
  change
    (∫ a : FieldOneFiniteStageAdele S,
      ((fieldOneFiniteStageCircleAddChar S (-(a * w)) : Circle) : ℂ) *
        (f a.1 * phi.1 a.2)
      ∂((volume : Measure ℝ).prod
        (Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1))) = _
  simp_rw [fieldOneFiniteStageCircleAddChar_neg_mul_split]
  rw [show (fun a : FieldOneFiniteStageAdele S =>
      ((Real.fourierChar (a.1 * w.1) : Circle) : ℂ) *
          fieldOneFiniteStageFiniteStandardAddChar S
            (fun v => -(a.2 v * w.2 v)) *
        (f a.1 * phi.1 a.2)) =
      fun a =>
        (((Real.fourierChar (a.1 * w.1) : Circle) : ℂ) * f a.1) *
          (fieldOneFiniteStageFiniteStandardAddChar S
            (fun v => -(a.2 v * w.2 v)) * phi.1 a.2) by
    funext a
    ring]
  let F : ℝ → ℂ := fun x =>
    ((Real.fourierChar (x * w.1) : Circle) : ℂ) * f x
  let G : FieldOneFiniteStageFinitePart S → ℂ := fun y =>
    fieldOneFiniteStageFiniteStandardAddChar S
      (fun v => -(y v * w.2 v)) * phi.1 y
  change (∫ a : ℝ × FieldOneFiniteStageFinitePart S,
      F a.1 * G a.2
      ∂((volume : Measure ℝ).prod
        (Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1))) = _
  rw [integral_prod_mul]
  congr 1
  · rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [F]
    congr 2
    rw [Real.inner_apply]
    congr 1
    ring

@[simp] theorem fieldOneFiniteStageBruhatFourierEval_zero
    (S : Finset (HeightOneSpectrum ℤ))
    (w : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageBruhatFourierEval S 0 w = 0 := by
  change (fieldOneFiniteStageBruhatFourierLinear S 0) w = 0
  rw [map_zero]
  rfl

@[simp] theorem fieldOneFiniteStageBruhatFourierEval_add
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S)
    (w : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageBruhatFourierEval S (x + y) w =
      fieldOneFiniteStageBruhatFourierEval S x w +
        fieldOneFiniteStageBruhatFourierEval S y w := by
  change (fieldOneFiniteStageBruhatFourierLinear S (x + y)) w = _
  rw [map_add]
  rfl

def fieldOneFiniteStageBruhatSelfDualPair
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) : ℂ :=
  ∫ a, star (fieldOneFiniteStageBruhatEval S x a) *
      fieldOneFiniteStageBruhatEval S y a
    ∂fieldOneFiniteStageSelfDualAddHaar S

def fieldOneFiniteStageBruhatFourierSelfDualPair
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) : ℂ :=
  ∫ w, star (fieldOneFiniteStageBruhatFourierEval S x w) *
      fieldOneFiniteStageBruhatFourierEval S y w
    ∂fieldOneFiniteStageSelfDualAddHaar S

theorem fieldOneFiniteStageBruhatRealPair_integrable
    (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun x => star (f x) * g x) := by
  apply g.integrable.bdd_mul
  · exact (continuous_star.comp f.continuous).aestronglyMeasurable
  · filter_upwards [] with x
    simpa using SchwartzMap.norm_le_seminorm ℝ f x

theorem fieldOneFiniteStageBruhatFinitePair_integrable
    (S : Finset (HeightOneSpectrum ℤ))
    (phi psi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    Integrable (fun y => star (phi.1 y) * psi.1 y)
      (Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_star.comp phi.1.continuous).mul psi.1.continuous
  · exact psi.2.mul_left

theorem fieldOneFiniteStageBruhatSelfDualPair_integrable
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    Integrable (fun a => star (fieldOneFiniteStageBruhatEval S x a) *
        fieldOneFiniteStageBruhatEval S y a)
      (fieldOneFiniteStageSelfDualAddHaar S) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [fieldOneFiniteStageBruhatEval]
  | tmul f phi =>
      induction y using TensorProduct.induction_on with
      | zero => simp [fieldOneFiniteStageBruhatEval]
      | tmul g psi =>
          have h := (fieldOneFiniteStageBruhatRealPair_integrable f g).mul_prod
            (fieldOneFiniteStageBruhatFinitePair_integrable S phi psi)
          exact h.congr (Filter.Eventually.of_forall fun a => by
            simp only [fieldOneFiniteStageBruhatEval_tmul, star_mul]
            ring)
      | add y z hy hz =>
          exact (hy.add hz).congr (Filter.Eventually.of_forall fun a => by
            simp only [map_add, Pi.add_apply, mul_add])
  | add x z hx hz =>
      exact (hx.add hz).congr (Filter.Eventually.of_forall fun a => by
        simp only [map_add, Pi.add_apply, star_add, add_mul])

theorem fieldOneFiniteStageBruhatRealFourierReflectedPair_integrable
    (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun x => star ((𝓕 f) (-x)) * (𝓕 g) (-x)) := by
  exact (fieldOneFiniteStageBruhatRealPair_integrable (𝓕 f) (𝓕 g)).comp_neg

theorem fieldOneFiniteStageBruhatFourierSelfDualPair_integrable
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    Integrable (fun w => star (fieldOneFiniteStageBruhatFourierEval S x w) *
        fieldOneFiniteStageBruhatFourierEval S y w)
      (fieldOneFiniteStageSelfDualAddHaar S) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f phi =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul g psi =>
          have h := (fieldOneFiniteStageBruhatRealFourierReflectedPair_integrable f g).mul_prod
            (fieldOneFiniteStageBruhatFinitePair_integrable S
              (fieldOneFiniteStageFiniteBruhatFourierBruhat S phi)
              (fieldOneFiniteStageFiniteBruhatFourierBruhat S psi))
          have h' : Integrable (fun w : FieldOneFiniteStageAdele S =>
              (star ((𝓕 f) (-w.1)) * (𝓕 g) (-w.1)) *
                (star ((fieldOneFiniteStageFiniteBruhatFourierBruhat S phi).1 w.2) *
                  (fieldOneFiniteStageFiniteBruhatFourierBruhat S psi).1 w.2))
              (fieldOneFiniteStageSelfDualAddHaar S) := h
          exact h'.congr (Filter.Eventually.of_forall fun w => by
            change (star ((𝓕 f) (-w.1)) * (𝓕 g) (-w.1)) *
                (star ((fieldOneFiniteStageFiniteBruhatFourierBruhat S phi).1 w.2) *
                  (fieldOneFiniteStageFiniteBruhatFourierBruhat S psi).1 w.2) =
              star (fieldOneFiniteStageBruhatFourierEval S (f ⊗ₜ[ℂ] phi) w) *
                fieldOneFiniteStageBruhatFourierEval S (g ⊗ₜ[ℂ] psi) w
            rw [fieldOneFiniteStageBruhatFourierEval_tmul, fieldOneFiniteStageBruhatFourierEval_tmul]
            simp only [fieldOneFiniteStageFiniteBruhatFourierBruhat_apply,
              star_mul]
            ring)
      | add y z hy hz =>
          exact (hy.add hz).congr (Filter.Eventually.of_forall fun w => by
            change star (fieldOneFiniteStageBruhatFourierEval S (f ⊗ₜ[ℂ] phi) w) *
                  fieldOneFiniteStageBruhatFourierEval S y w +
                star (fieldOneFiniteStageBruhatFourierEval S (f ⊗ₜ[ℂ] phi) w) *
                  fieldOneFiniteStageBruhatFourierEval S z w =
              star (fieldOneFiniteStageBruhatFourierEval S (f ⊗ₜ[ℂ] phi) w) *
                fieldOneFiniteStageBruhatFourierEval S (y + z) w
            rw [fieldOneFiniteStageBruhatFourierEval_add]
            ring)
  | add x z hx hz =>
      exact (hx.add hz).congr (Filter.Eventually.of_forall fun w => by
        change star (fieldOneFiniteStageBruhatFourierEval S x w) *
                fieldOneFiniteStageBruhatFourierEval S y w +
              star (fieldOneFiniteStageBruhatFourierEval S z w) *
                fieldOneFiniteStageBruhatFourierEval S y w =
            star (fieldOneFiniteStageBruhatFourierEval S (x + z) w) *
              fieldOneFiniteStageBruhatFourierEval S y w
        rw [fieldOneFiniteStageBruhatFourierEval_add]
        simp only [star_add]
        ring)

theorem fieldOneFiniteStageBruhatRealFourierReflectedPair_parseval
    (f g : SchwartzMap ℝ ℂ) :
    (∫ x, star ((𝓕 f) (-x)) * (𝓕 g) (-x)) =
      ∫ x, star (f x) * g x := by
  calc
    (∫ x, star ((𝓕 f) (-x)) * (𝓕 g) (-x)) =
        ∫ x, star ((𝓕 f) x) * (𝓕 g) x :=
      integral_neg_eq_self
        (fun x : ℝ => star ((𝓕 f) x) * (𝓕 g) x) volume
    _ = ∫ x, star (f x) * g x := by
      simpa only [RCLike.inner_apply', starRingEnd_apply] using
        SchwartzMap.integral_inner_fourier_fourier f g

theorem fieldOneFiniteStageBruhatSelfDualPair_add_right
    (S : Finset (HeightOneSpectrum ℤ))
    (x y z : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatSelfDualPair S x (y + z) =
      fieldOneFiniteStageBruhatSelfDualPair S x y + fieldOneFiniteStageBruhatSelfDualPair S x z := by
  unfold fieldOneFiniteStageBruhatSelfDualPair
  simp_rw [map_add, Pi.add_apply, mul_add]
  rw [integral_add (fieldOneFiniteStageBruhatSelfDualPair_integrable S x y)
    (fieldOneFiniteStageBruhatSelfDualPair_integrable S x z)]

theorem fieldOneFiniteStageBruhatSelfDualPair_add_left
    (S : Finset (HeightOneSpectrum ℤ))
    (x y z : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatSelfDualPair S (x + y) z =
      fieldOneFiniteStageBruhatSelfDualPair S x z + fieldOneFiniteStageBruhatSelfDualPair S y z := by
  unfold fieldOneFiniteStageBruhatSelfDualPair
  simp_rw [map_add, Pi.add_apply, star_add, add_mul]
  rw [integral_add (fieldOneFiniteStageBruhatSelfDualPair_integrable S x z)
    (fieldOneFiniteStageBruhatSelfDualPair_integrable S y z)]

theorem fieldOneFiniteStageBruhatFourierSelfDualPair_add_right
    (S : Finset (HeightOneSpectrum ℤ))
    (x y z : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatFourierSelfDualPair S x (y + z) =
      fieldOneFiniteStageBruhatFourierSelfDualPair S x y + fieldOneFiniteStageBruhatFourierSelfDualPair S x z := by
  unfold fieldOneFiniteStageBruhatFourierSelfDualPair
  simp_rw [fieldOneFiniteStageBruhatFourierEval_add, mul_add]
  rw [integral_add (fieldOneFiniteStageBruhatFourierSelfDualPair_integrable S x y)
    (fieldOneFiniteStageBruhatFourierSelfDualPair_integrable S x z)]

theorem fieldOneFiniteStageBruhatFourierSelfDualPair_add_left
    (S : Finset (HeightOneSpectrum ℤ))
    (x y z : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatFourierSelfDualPair S (x + y) z =
      fieldOneFiniteStageBruhatFourierSelfDualPair S x z + fieldOneFiniteStageBruhatFourierSelfDualPair S y z := by
  unfold fieldOneFiniteStageBruhatFourierSelfDualPair
  simp_rw [fieldOneFiniteStageBruhatFourierEval_add, star_add, add_mul]
  rw [integral_add (fieldOneFiniteStageBruhatFourierSelfDualPair_integrable S x z)
    (fieldOneFiniteStageBruhatFourierSelfDualPair_integrable S y z)]

theorem fieldOneFiniteStageBruhatSelfDualPair_tmul
    (S : Finset (HeightOneSpectrum ℤ))
    (f g : SchwartzMap ℝ ℂ)
    (phi psi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    fieldOneFiniteStageBruhatSelfDualPair S (f ⊗ₜ[ℂ] phi) (g ⊗ₜ[ℂ] psi) =
      (∫ x, star (f x) * g x) *
        fieldOneFiniteStageFiniteBruhatPair S phi psi := by
  unfold fieldOneFiniteStageBruhatSelfDualPair fieldOneFiniteStageFiniteBruhatPair
  change
    (∫ a : ℝ × FieldOneFiniteStageFinitePart S,
      star (f a.1 * phi.1 a.2) * (g a.1 * psi.1 a.2)
      ∂((volume : Measure ℝ).prod
        (Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1))) = _
  rw [show (fun a : ℝ × FieldOneFiniteStageFinitePart S =>
      star (f a.1 * phi.1 a.2) * (g a.1 * psi.1 a.2)) =
      fun a => (star (f a.1) * g a.1) *
        (star (phi.1 a.2) * psi.1 a.2) by
    funext a
    simp only [star_mul]
    ring]
  exact integral_prod_mul
    (μ := (volume : Measure ℝ))
    (ν := Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)
    (fun x => star (f x) * g x)
    (fun y => star (phi.1 y) * psi.1 y)

theorem fieldOneFiniteStageBruhatFourierSelfDualPair_tmul
    (S : Finset (HeightOneSpectrum ℤ))
    (f g : SchwartzMap ℝ ℂ)
    (phi psi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    fieldOneFiniteStageBruhatFourierSelfDualPair S (f ⊗ₜ[ℂ] phi) (g ⊗ₜ[ℂ] psi) =
      (∫ x, star ((𝓕 f) (-x)) * (𝓕 g) (-x)) *
        fieldOneFiniteStageFiniteBruhatPair S
          (fieldOneFiniteStageFiniteBruhatFourierBruhat S phi)
          (fieldOneFiniteStageFiniteBruhatFourierBruhat S psi) := by
  unfold fieldOneFiniteStageBruhatFourierSelfDualPair fieldOneFiniteStageFiniteBruhatPair
  simp_rw [fieldOneFiniteStageBruhatFourierEval_tmul,
    fieldOneFiniteStageFiniteBruhatFourierBruhat_apply]
  change
    (∫ w : ℝ × FieldOneFiniteStageFinitePart S,
      star ((𝓕 f) (-w.1) *
          fieldOneFiniteStageFiniteBruhatFourier S phi w.2) *
        ((𝓕 g) (-w.1) *
          fieldOneFiniteStageFiniteBruhatFourier S psi w.2)
      ∂((volume : Measure ℝ).prod
        (Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1))) = _
  calc
    (∫ w : ℝ × FieldOneFiniteStageFinitePart S,
      star ((𝓕 f) (-w.1) *
          fieldOneFiniteStageFiniteBruhatFourier S phi w.2) *
        ((𝓕 g) (-w.1) *
          fieldOneFiniteStageFiniteBruhatFourier S psi w.2)
      ∂((volume : Measure ℝ).prod
        (Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1))) =
      ∫ w : ℝ × FieldOneFiniteStageFinitePart S,
        (star ((𝓕 f) (-w.1)) * (𝓕 g) (-w.1)) *
          (star (fieldOneFiniteStageFiniteBruhatFourier S phi w.2) *
            fieldOneFiniteStageFiniteBruhatFourier S psi w.2)
      ∂((volume : Measure ℝ).prod
        (Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)) := by
        apply integral_congr_ae
        filter_upwards [] with w
        simp only [star_mul]
        ring
    _ = _ := integral_prod_mul
      (μ := (volume : Measure ℝ))
      (ν := Measure.pi fun v : ↑S => fieldOneLocalSelfDualAddHaar v.1)
      (fun x => star ((𝓕 f) (-x)) * (𝓕 g) (-x))
      (fun y => star (fieldOneFiniteStageFiniteBruhatFourier S phi y) *
        fieldOneFiniteStageFiniteBruhatFourier S psi y)

theorem fieldOneFiniteStageBruhatFourierSelfDualPair_tmul_parseval
    (S : Finset (HeightOneSpectrum ℤ))
    (f g : SchwartzMap ℝ ℂ)
    (phi psi : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    fieldOneFiniteStageBruhatFourierSelfDualPair S (f ⊗ₜ[ℂ] phi) (g ⊗ₜ[ℂ] psi) =
      fieldOneFiniteStageBruhatSelfDualPair S (f ⊗ₜ[ℂ] phi) (g ⊗ₜ[ℂ] psi) := by
  rw [fieldOneFiniteStageBruhatFourierSelfDualPair_tmul, fieldOneFiniteStageBruhatRealFourierReflectedPair_parseval,
    fieldOneFiniteStageFiniteBruhatFourier_parseval, fieldOneFiniteStageBruhatSelfDualPair_tmul]

theorem fieldOneFiniteStageBruhatFourier_parseval
    (S : Finset (HeightOneSpectrum ℤ))
    (x y : FieldOneFiniteStageBruhatSchwartz S) :
    fieldOneFiniteStageBruhatFourierSelfDualPair S x y = fieldOneFiniteStageBruhatSelfDualPair S x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp [fieldOneFiniteStageBruhatFourierSelfDualPair, fieldOneFiniteStageBruhatSelfDualPair]
  | tmul f phi =>
      induction y using TensorProduct.induction_on with
      | zero => simp [fieldOneFiniteStageBruhatFourierSelfDualPair, fieldOneFiniteStageBruhatSelfDualPair]
      | tmul g psi => exact fieldOneFiniteStageBruhatFourierSelfDualPair_tmul_parseval S f g phi psi
      | add y z hy hz =>
          rw [fieldOneFiniteStageBruhatFourierSelfDualPair_add_right, fieldOneFiniteStageBruhatSelfDualPair_add_right, hy, hz]
  | add x z hx hz =>
      rw [fieldOneFiniteStageBruhatFourierSelfDualPair_add_left, fieldOneFiniteStageBruhatSelfDualPair_add_left, hx, hz]


end
end GaloisForLFunctions.RHTower

