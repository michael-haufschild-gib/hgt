import GaloisForLFunctions.RHTower.CCMRationalAdelicEndpointReal
import GaloisForLFunctions.RHTower.CCMRationalFiniteAdeleHaarCharacter
import GaloisForLFunctions.RHTower.CCMRationalClassSpaceSection
import GaloisForLFunctions.RHTower.CyclicModuleDoubleKernelEndomorphism

/-!
# Exact class-space action on the rational adelic cyclic source

For `c = (u,r) in Zhat^times x R_+^times`, pullback by multiplication
with `c` acts on the actual Bruhat--Schwartz tensor core.  It commutes
with diagonal rational scaling, hence extends coefficientwise to the crossed
product and then to its minimal unitization.  Zero evaluation is fixed.  Haar
integration is multiplied by `r^-1`; the finite profinite-unit factor has Haar
character one.  Consequently the action preserves the genuine nonunital
cyclic module and its two endpoint kernels in every degree.
-/

noncomputable section

open CategoryTheory MeasureTheory
open scoped TensorProduct

namespace GaloisForLFunctions.RHTower

private abbrev Arch := CCMRationalArchimedeanSchwartz
private abbrev FinBruhat := CCMRationalFiniteBruhatSchwartz
private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra
private abbrev Section := CCMRationalClassSpaceSection

local instance cCMRationalAdelicClassSpaceSourceActionLocalInst1 : DecidableEq Scale := Classical.decEq _

/-! ## Bruhat--Schwartz coefficient action -/

/-- Positive coordinate of a class-space section as a real unit. -/
def ccmRationalPositiveUnitReal (r : Units NNReal) : ℝˣ where
  val := (r.val : ℝ)
  inv := (r.inv : ℝ)
  val_inv := by exact_mod_cast r.val_inv
  inv_val := by exact_mod_cast r.inv_val

@[simp]
theorem ccmRationalPositiveUnitReal_val (r : Units NNReal) :
    (ccmRationalPositiveUnitReal r : ℝ) = (r.val : ℝ) :=
  rfl

/-- Pullback of a real Schwartz function by the positive class-space
coordinate. -/
def ccmRationalClassSpaceArchimedeanRightAction (c : Section) :
    Arch →ₗ[ℂ] Arch :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft
      (ccmRationalPositiveUnitReal c.2))).toLinearMap

@[simp]
theorem ccmRationalClassSpaceArchimedeanRightAction_apply
    (c : Section) (f : Arch) (x : ℝ) :
    ccmRationalClassSpaceArchimedeanRightAction c f x =
      f ((c.2.val : ℝ) * x) :=
  rfl

/-- Pullback of a finite Bruhat function by the profinite-unit coordinate. -/
def ccmRationalClassSpaceFiniteRightAction
    (c : Section) (f : FinBruhat) : FinBruhat :=
  let h := ccmRationalFiniteAdeleUnitMulHomeomorph c.1.val
  ⟨LocallyConstant.comap ⟨h, h.continuous⟩ f.1,
    f.2.comp_homeomorph h⟩

@[simp]
theorem ccmRationalClassSpaceFiniteRightAction_apply
    (c : Section) (f : FinBruhat) (x : CCMRationalFiniteAdele) :
    (ccmRationalClassSpaceFiniteRightAction c f).1 x =
      f.1 ((c.1.val : CCMRationalFiniteAdeleˣ) * x) :=
  rfl

theorem ccmRationalClassSpaceFiniteRightAction_zero (c : Section) :
    ccmRationalClassSpaceFiniteRightAction c 0 = 0 := by
  apply Subtype.ext
  ext x
  simp

theorem ccmRationalClassSpaceFiniteRightAction_add
    (c : Section) (f g : FinBruhat) :
    ccmRationalClassSpaceFiniteRightAction c (f + g) =
      ccmRationalClassSpaceFiniteRightAction c f +
        ccmRationalClassSpaceFiniteRightAction c g := by
  apply Subtype.ext
  ext x
  simp

theorem ccmRationalClassSpaceFiniteRightAction_smul
    (c : Section) (z : ℂ) (f : FinBruhat) :
    ccmRationalClassSpaceFiniteRightAction c (z • f) =
      z • ccmRationalClassSpaceFiniteRightAction c f := by
  apply Subtype.ext
  ext x
  simp

/-- Finite coordinate pullback, bundled linearly. -/
def ccmRationalClassSpaceFiniteRightActionLinear (c : Section) :
    FinBruhat →ₗ[ℂ] FinBruhat where
  toFun := ccmRationalClassSpaceFiniteRightAction c
  map_add' := ccmRationalClassSpaceFiniteRightAction_add c
  map_smul' := ccmRationalClassSpaceFiniteRightAction_smul c

/-- Diagonal class-space pullback on the actual adelic tensor core. -/
def ccmRationalAdelicBruhatClassSpaceRightAction (c : Section) :
    Core →ₗ[ℂ] Core :=
  TensorProduct.map
    (ccmRationalClassSpaceArchimedeanRightAction c)
    (ccmRationalClassSpaceFiniteRightActionLinear c)

@[simp]
theorem ccmRationalAdelicBruhatClassSpaceRightAction_tmul
    (c : Section) (f : Arch) (g : FinBruhat) :
    ccmRationalAdelicBruhatClassSpaceRightAction c (f ⊗ₜ[ℂ] g) =
      ccmRationalClassSpaceArchimedeanRightAction c f ⊗ₜ[ℂ]
        ccmRationalClassSpaceFiniteRightAction c g :=
  rfl

theorem ccmRationalClassSpaceArchimedeanRightAction_map_mul
    (c : Section) (f g : Arch) :
    ccmRationalClassSpaceArchimedeanRightAction c (f * g) =
      ccmRationalClassSpaceArchimedeanRightAction c f *
        ccmRationalClassSpaceArchimedeanRightAction c g := by
  ext x
  simp

theorem ccmRationalClassSpaceFiniteRightAction_map_mul
    (c : Section) (f g : FinBruhat) :
    ccmRationalClassSpaceFiniteRightAction c (f * g) =
      ccmRationalClassSpaceFiniteRightAction c f *
        ccmRationalClassSpaceFiniteRightAction c g := by
  apply Subtype.ext
  ext x
  simp

/-- Class-space pullback is a nonunital algebra endomorphism of the exact
Bruhat tensor core. -/
theorem ccmRationalAdelicBruhatClassSpaceRightAction_map_mul
    (c : Section) (x y : Core) :
    ccmRationalAdelicBruhatClassSpaceRightAction c (x * y) =
      ccmRationalAdelicBruhatClassSpaceRightAction c x *
        ccmRationalAdelicBruhatClassSpaceRightAction c y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f' g' =>
          rw [ccmRationalAdelicBruhat_tmul_mul_tmul,
            ccmRationalAdelicBruhatClassSpaceRightAction_tmul,
            ccmRationalAdelicBruhatClassSpaceRightAction_tmul,
            ccmRationalAdelicBruhatClassSpaceRightAction_tmul,
            ccmRationalAdelicBruhat_tmul_mul_tmul,
            ccmRationalClassSpaceArchimedeanRightAction_map_mul,
            ccmRationalClassSpaceFiniteRightAction_map_mul]
      | add y z hy hz =>
          rw [ccmRationalAdelicBruhat_mul_add, map_add, map_add,
            ccmRationalAdelicBruhat_mul_add, hy, hz]
  | add x y hx hy =>
      rw [ccmRationalAdelicBruhat_add_mul, map_add, map_add,
        ccmRationalAdelicBruhat_add_mul, hx, hy]

/-- Class-space pullback commutes with the diagonal rational action. -/
theorem ccmRationalAdelicBruhatClassSpaceRightAction_smul
    (c : Section) (k : Scale) (x : Core) :
    ccmRationalAdelicBruhatClassSpaceRightAction c (k • x) =
      k • ccmRationalAdelicBruhatClassSpaceRightAction c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simp only [ccmRationalAdelicScaling_smul_tmul,
        ccmRationalAdelicBruhatClassSpaceRightAction_tmul]
      congr 1
      · ext x
        simp only [ccmRationalClassSpaceArchimedeanRightAction_apply,
          ccmRationalArchimedeanScaling_apply]
        congr 1
        push_cast
        ring
      · apply Subtype.ext
        ext x
        simp only [ccmRationalClassSpaceFiniteRightAction_apply,
          ccmRationalFiniteBruhatScaling_apply]
        congr 1
        ring
  | add x y hx hy => simp [hx, hy]

/-! ## Crossed product and unitization -/

/-- Coefficientwise class-space pullback on the algebraic crossed product. -/
def ccmRationalAdelicCrossedClassSpaceRightAction
    (c : Section) (F : Crossed) : Crossed :=
  F.sum fun k a => Finsupp.single k
    (ccmRationalAdelicBruhatClassSpaceRightAction c a)

@[simp]
theorem ccmRationalAdelicCrossedClassSpaceRightAction_single
    (c : Section) (k : Scale) (a : Core) :
    ccmRationalAdelicCrossedClassSpaceRightAction c (Finsupp.single k a) =
      Finsupp.single k (ccmRationalAdelicBruhatClassSpaceRightAction c a) := by
  unfold ccmRationalAdelicCrossedClassSpaceRightAction
  apply Finsupp.sum_single_index
  simp

@[simp]
theorem ccmRationalAdelicCrossedClassSpaceRightAction_apply
    (c : Section) (F : Crossed) (k : Scale) :
    ccmRationalAdelicCrossedClassSpaceRightAction c F k =
      ccmRationalAdelicBruhatClassSpaceRightAction c (F k) := by
  classical
  change (F.sum fun i a => Finsupp.single i
      (ccmRationalAdelicBruhatClassSpaceRightAction c a)) k = _
  rw [Finsupp.sum_apply]
  induction F using Finsupp.induction with
  | zero => simp
  | @single_add i a F hi ha hF =>
      rw [Finsupp.sum_add_index]
      · by_cases hik : i = k
        · subst i
          simp [hF]
        · simp [hik, hF]
      · intro j
        simp
      · intro j hj a b
        simp

theorem ccmRationalAdelicCrossedClassSpaceRightAction_add
    (c : Section) (F G : Crossed) :
    ccmRationalAdelicCrossedClassSpaceRightAction c (F + G) =
      ccmRationalAdelicCrossedClassSpaceRightAction c F +
        ccmRationalAdelicCrossedClassSpaceRightAction c G := by
  classical
  ext k
  simp

theorem ccmRationalAdelicCrossedClassSpaceRightAction_smul
    (c : Section) (z : ℂ) (F : Crossed) :
    ccmRationalAdelicCrossedClassSpaceRightAction c (z • F) =
      z • ccmRationalAdelicCrossedClassSpaceRightAction c F := by
  classical
  ext k
  simp

@[simp]
theorem ccmRationalAdelicCrossedClassSpaceRightAction_zero
    (c : Section) :
    ccmRationalAdelicCrossedClassSpaceRightAction c (0 : Crossed) = 0 := by
  ext k
  simp

theorem ccmRationalAdelicCrossedClassSpaceRightAction_mul
    (c : Section) (F G : Crossed) :
    ccmRationalAdelicCrossedClassSpaceRightAction c (F * G) =
      ccmRationalAdelicCrossedClassSpaceRightAction c F *
        ccmRationalAdelicCrossedClassSpaceRightAction c G := by
  classical
  have hpure (k l : Scale) (a b : Core) :
      ccmRationalAdelicCrossedClassSpaceRightAction c
          (Finsupp.single k a * Finsupp.single l b) =
        ccmRationalAdelicCrossedClassSpaceRightAction c (Finsupp.single k a) *
          ccmRationalAdelicCrossedClassSpaceRightAction c
            (Finsupp.single l b) := by
    simp only [ccmRationalAdelicCrossedProduct_single_mul_single,
      ccmRationalAdelicCrossedClassSpaceRightAction_single]
    congr 1
    rw [ccmRationalAdelicBruhatClassSpaceRightAction_map_mul,
      ccmRationalAdelicBruhatClassSpaceRightAction_smul]
  have hpureLeft (k : Scale) (a : Core) (H : Crossed) :
      ccmRationalAdelicCrossedClassSpaceRightAction c
          (Finsupp.single k a * H) =
        ccmRationalAdelicCrossedClassSpaceRightAction c (Finsupp.single k a) *
          ccmRationalAdelicCrossedClassSpaceRightAction c H := by
    induction H using Finsupp.induction with
    | zero => simp
    | @single_add l b H hl hb hH =>
        rw [ccmRationalAdelicCrossedProduct_mul_add,
          ccmRationalAdelicCrossedClassSpaceRightAction_add,
          ccmRationalAdelicCrossedClassSpaceRightAction_add,
          ccmRationalAdelicCrossedProduct_mul_add, hpure, hH]
  induction F using Finsupp.induction with
  | zero => simp
  | @single_add k a F hk ha hF =>
      rw [ccmRationalAdelicCrossedProduct_add_mul,
        ccmRationalAdelicCrossedClassSpaceRightAction_add,
        ccmRationalAdelicCrossedClassSpaceRightAction_add,
        ccmRationalAdelicCrossedProduct_add_mul, hpureLeft, hF]

/-- Crossed-product class-space action as a nonunital algebra homomorphism. -/
def ccmRationalAdelicCrossedClassSpaceRightActionHom (c : Section) :
    Crossed →ₙₐ[ℂ] Crossed where
  toFun := ccmRationalAdelicCrossedClassSpaceRightAction c
  map_zero' := by ext k; simp
  map_add' := ccmRationalAdelicCrossedClassSpaceRightAction_add c
  map_smul' := ccmRationalAdelicCrossedClassSpaceRightAction_smul c
  map_mul' := ccmRationalAdelicCrossedClassSpaceRightAction_mul c

/-- Unital extension to the exact cyclic source algebra. -/
def ccmRationalAdelicSourceClassSpaceRightActionHom (c : Section) :
    Source →ₐ[ℂ] Source :=
  Unitization.lift <|
    (Unitization.inrNonUnitalAlgHom ℂ Crossed).comp
      (ccmRationalAdelicCrossedClassSpaceRightActionHom c)

@[simp]
theorem ccmRationalAdelicSourceClassSpaceRightActionHom_fst
    (c : Section) (x : Source) :
    (ccmRationalAdelicSourceClassSpaceRightActionHom c x).fst = x.fst := by
  rw [ccmRationalAdelicSourceClassSpaceRightActionHom,
    Unitization.lift_apply]
  change (algebraMap ℂ Source x.fst +
    ((Unitization.inrNonUnitalAlgHom ℂ Crossed).comp
      (ccmRationalAdelicCrossedClassSpaceRightActionHom c)) x.snd).fst = x.fst
  simp [Unitization.algebraMap_eq_inl]

@[simp]
theorem ccmRationalAdelicSourceClassSpaceRightActionHom_snd
    (c : Section) (x : Source) :
    (ccmRationalAdelicSourceClassSpaceRightActionHom c x).snd =
      ccmRationalAdelicCrossedClassSpaceRightAction c x.snd := by
  rw [ccmRationalAdelicSourceClassSpaceRightActionHom,
    Unitization.lift_apply]
  change (algebraMap ℂ Source x.fst +
    ((Unitization.inrNonUnitalAlgHom ℂ Crossed).comp
      (ccmRationalAdelicCrossedClassSpaceRightActionHom c)) x.snd).snd = _
  simp [Unitization.algebraMap_eq_inl]
  rfl

/-! ## Exact endpoint covariance -/

theorem ccmRationalAdelicBruhatZeroEval_classSpaceRightAction
    (c : Section) (x : Core) :
    ccmRationalAdelicBruhatZeroEval
        (ccmRationalAdelicBruhatClassSpaceRightAction c x) =
      ccmRationalAdelicBruhatZeroEval x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g => simp
  | add x y hx hy => simp [hx, hy]

/-- Multiplication by a profinite unit on the additive finite adele group. -/
def ccmRationalProfiniteUnitFiniteAdeleAddEquiv
    (u : CCMRationalProfiniteUnit) :
    CCMRationalFiniteAdele ≃ₜ+ CCMRationalFiniteAdele :=
  ContinuousAddEquiv.mulLeft u.val

theorem ccmRationalProfiniteUnitFiniteAdeleAddEquiv_preimage_integral
    (u : CCMRationalProfiniteUnit) :
    ccmRationalProfiniteUnitFiniteAdeleAddEquiv u ⁻¹'
        ccmRationalIntegralFiniteAdeles =
      ccmRationalIntegralFiniteAdeles := by
  ext x
  constructor
  · intro hx v
    have huinv := u.2.2 v
    have hux := hx v
    have hprod := mul_mem huinv hux
    change (((u.val⁻¹ : CCMRationalFiniteAdeleˣ) :
        CCMRationalFiniteAdele) v) *
      ((((u.val : CCMRationalFiniteAdeleˣ) :
        CCMRationalFiniteAdele) v) * x v) ∈
      CCMRationalLocalIntegers v at hprod
    have huv : (((u.val⁻¹ : CCMRationalFiniteAdeleˣ) :
          CCMRationalFiniteAdele) v) *
        (((u.val : CCMRationalFiniteAdeleˣ) :
          CCMRationalFiniteAdele) v) = 1 := by
      have h := congrArg (fun y : CCMRationalFiniteAdele => y v)
        (Units.inv_mul u.val)
      exact h
    rw [← mul_assoc, huv, one_mul] at hprod
    exact hprod
  · intro hx v
    exact mul_mem (u.2.1 v) (hx v)

/-- Every profinite unit has additive Haar character one. -/
theorem ccmRationalProfiniteUnitFiniteAdeleHaarCharacter
    (u : CCMRationalProfiniteUnit) :
    addEquivAddHaarChar
        (ccmRationalProfiniteUnitFiniteAdeleAddEquiv u) = 1 := by
  have h := addEquivAddHaarChar_smul_preimage
    ccmRationalFiniteAdeleHaar
    (X := ccmRationalIntegralFiniteAdeles)
    (ccmRationalProfiniteUnitFiniteAdeleAddEquiv u)
  rw [ccmRationalProfiniteUnitFiniteAdeleAddEquiv_preimage_integral,
    ccmRationalFiniteAdeleHaar_integral_subring] at h
  simpa using h

theorem ccmRationalFiniteBruhatIntegral_classSpaceRightAction
    (c : Section) (f : FinBruhat) :
    ccmRationalFiniteBruhatIntegral
        (ccmRationalClassSpaceFiniteRightAction c f) =
      ccmRationalFiniteBruhatIntegral f := by
  rw [ccmRationalFiniteBruhatIntegral_apply,
    ccmRationalFiniteBruhatIntegral_apply]
  change (∫ x, f.1 (ccmRationalProfiniteUnitFiniteAdeleAddEquiv c.1 x)
      ∂ccmRationalFiniteAdeleHaar) = _
  have hmap :
      (∫ x, f.1 (ccmRationalProfiniteUnitFiniteAdeleAddEquiv c.1 x)
          ∂ccmRationalFiniteAdeleHaar) =
        ∫ y, f.1 y ∂(ccmRationalFiniteAdeleHaar.map
          (ccmRationalProfiniteUnitFiniteAdeleAddEquiv c.1)) :=
    (integral_map_equiv
      (ccmRationalProfiniteUnitFiniteAdeleAddEquiv c.1).toHomeomorph.toMeasurableEquiv
      f.1).symm
  rw [hmap]
  have hmeasure := addEquivAddHaarChar_smul_map
    ccmRationalFiniteAdeleHaar
    (ccmRationalProfiniteUnitFiniteAdeleAddEquiv c.1)
  rw [ccmRationalProfiniteUnitFiniteAdeleHaarCharacter] at hmeasure
  simpa using congrArg
    (fun μ : Measure CCMRationalFiniteAdele => ∫ x, f.1 x ∂μ) hmeasure

theorem ccmRationalArchimedeanSchwartzIntegral_classSpaceRightAction
    (c : Section) (f : Arch) :
    ccmRationalArchimedeanSchwartzIntegral
        (ccmRationalClassSpaceArchimedeanRightAction c f) =
      ((c.2.val : ℝ)⁻¹) • ccmRationalArchimedeanSchwartzIntegral f := by
  simp only [ccmRationalArchimedeanSchwartzIntegral_apply]
  change (∫ x : ℝ, f ((c.2.val : ℝ) * x)) = _
  have hcpos : 0 < (c.2.val : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr c.2.ne_zero : 0 < c.2.val)
  rw [Measure.integral_comp_mul_left, abs_inv, abs_of_pos hcpos]

theorem ccmRationalAdelicBruhatIntegral_classSpaceRightAction
    (c : Section) (x : Core) :
    ccmRationalAdelicBruhatIntegral
        (ccmRationalAdelicBruhatClassSpaceRightAction c x) =
      ((c.2.val : ℝ)⁻¹) • ccmRationalAdelicBruhatIntegral x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simp only [ccmRationalAdelicBruhatClassSpaceRightAction_tmul,
        ccmRationalAdelicBruhatIntegral_tmul,
        ccmRationalArchimedeanSchwartzIntegral_classSpaceRightAction,
        ccmRationalFiniteBruhatIntegral_classSpaceRightAction,
        Complex.real_smul]
      ring
  | add x y hx hy => simp [hx, hy, smul_add]

theorem ccmRationalAdelicEpsilonZeroNonunital_classSpaceRightAction
    (c : Section) (F : Crossed) :
    ccmRationalAdelicEpsilonZeroNonunital
        (ccmRationalAdelicCrossedClassSpaceRightAction c F) =
      ccmRationalAdelicEpsilonZeroNonunital F := by
  change ccmRationalAdelicBruhatZeroEval
      (ccmRationalAdelicCrossedClassSpaceRightAction c F 1) =
    ccmRationalAdelicBruhatZeroEval (F 1)
  rw [ccmRationalAdelicCrossedClassSpaceRightAction_apply,
    ccmRationalAdelicBruhatZeroEval_classSpaceRightAction]

theorem ccmRationalAdelicEpsilonOneNonunital_classSpaceRightAction
    (c : Section) (F : Crossed) :
    ccmRationalAdelicEpsilonOneNonunital
        (ccmRationalAdelicCrossedClassSpaceRightAction c F) =
      ((c.2.val : ℝ)⁻¹) • ccmRationalAdelicEpsilonOneNonunital F := by
  rw [ccmRationalAdelicEpsilonOneNonunital_apply,
    ccmRationalAdelicEpsilonOneNonunital_apply,
    ccmRationalAdelicCrossedClassSpaceRightAction_apply,
    ccmRationalAdelicBruhatIntegral_classSpaceRightAction]

end GaloisForLFunctions.RHTower
