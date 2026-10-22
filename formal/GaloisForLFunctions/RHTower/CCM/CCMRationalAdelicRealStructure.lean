import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicEpsilonZero
import GaloisForLFunctions.RHTower.KRealCyclicWord

/-!
# Real structure on the rational adelic CCM source

The rational CCM source is the minimal unitization of the finite-support crossed product of the
actual algebraic Bruhat--Schwartz adelic core by `ℚˣ`.  On a monomial its Real structure is

`α(fₖ Uₖ) = sign(k) · conj(fₖ ∘ (-1)) Uₖ`.

This file extends that formula to the whole crossed product and its minimal unitization.  The
resulting map is a conjugate-linear, unital, multiplicative involution and therefore induces an
even Real structure on the genuine cyclic bar module.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra

local instance cCMRationalAdelicRealStructureLocalInst1 : DecidableEq Scale := Classical.decEq _

/-! ## Monomial Real twist -/

/-- Sign-reflection on a coefficient of scaling degree `k`. -/
def ccmRationalAdelicMonomialRealTwist (k : Scale) (a : Core) : Core :=
  ccmRationalUnitSign k.val •
    ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma a

@[simp]
theorem ccmRationalAdelicMonomialRealTwist_zero (k : Scale) :
    ccmRationalAdelicMonomialRealTwist k 0 = 0 := by
  simp [ccmRationalAdelicMonomialRealTwist]

theorem ccmRationalAdelicMonomialRealTwist_add
    (k : Scale) (a b : Core) :
    ccmRationalAdelicMonomialRealTwist k (a + b) =
      ccmRationalAdelicMonomialRealTwist k a +
        ccmRationalAdelicMonomialRealTwist k b := by
  simp [ccmRationalAdelicMonomialRealTwist]

theorem ccmRationalAdelicMonomialRealTwist_smul
    (k : Scale) (z : ℂ) (a : Core) :
    ccmRationalAdelicMonomialRealTwist k (z • a) =
      star z • ccmRationalAdelicMonomialRealTwist k a := by
  rw [ccmRationalAdelicMonomialRealTwist,
    ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma.map_smulₛₗ]
  rw [ccmRationalAdelicMonomialRealTwist]
  simp only [smul_smul]
  change (ccmRationalUnitSign k.val * star z) •
      ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma a =
    (star z * ccmRationalUnitSign k.val) •
      ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma a
  rw [mul_comm (ccmRationalUnitSign k.val) (star z)]

theorem ccmRationalAdelicMonomialRealTwist_sq
    (k : Scale) (a : Core) :
    ccmRationalAdelicMonomialRealTwist k
        (ccmRationalAdelicMonomialRealTwist k a) = a := by
  rw [ccmRationalAdelicMonomialRealTwist,
    ccmRationalAdelicMonomialRealTwist,
    ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma.map_smulₛₗ]
  change ccmRationalUnitSign k.val • star (ccmRationalUnitSign k.val) •
      ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma
        (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma a) = a
  rw [ccmRationalUnitSign_star, smul_smul,
    ccmRationalUnitSign_sq, one_smul]
  exact ccmRationalAdelicBruhatSimpleTensorKRealEven.sq a

/-- The sign twist is compatible with the twisted-convolution coefficient law. -/
theorem ccmRationalAdelicMonomialRealTwist_product
    (k l : Scale) (a b : Core) :
    ccmRationalAdelicMonomialRealTwist (k * l) (a * (k • b)) =
      ccmRationalAdelicMonomialRealTwist k a *
        (k • ccmRationalAdelicMonomialRealTwist l b) := by
  rw [ccmRationalAdelicMonomialRealTwist,
    ccmRationalAdelicBruhatSimpleTensor_sigma_mul,
    ccmRationalAdelicBruhatScaling_sigma]
  simp only [ccmRationalAdelicScaling_mul_val,
    ccmRationalUnitSign_mul]
  rw [ccmRationalAdelicMonomialRealTwist,
    ccmRationalAdelicMonomialRealTwist]
  have hscale :
      k • (ccmRationalUnitSign l.val •
          ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma b) =
        ccmRationalUnitSign l.val •
          (k • ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma b) :=
    (ccmRationalAdelicBruhatScaling k).map_smul _ _
  symm
  rw [hscale]
  calc
    (ccmRationalUnitSign k.val •
          ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma a) *
        (ccmRationalUnitSign l.val •
          (k • ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma b)) =
      ccmRationalUnitSign k.val •
        (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma a *
          (ccmRationalUnitSign l.val •
            (k • ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma b))) :=
        smul_mul_assoc _ _ _
    _ = ccmRationalUnitSign k.val •
        (ccmRationalUnitSign l.val •
          (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma a *
            (k • ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma b))) := by
      rw [mul_smul_comm]
    _ = (ccmRationalUnitSign k.val * ccmRationalUnitSign l.val) •
        (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma a *
          (k • ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma b)) := by
      rw [smul_smul]

/-! ## Finite-support crossed product -/

/-- Coefficientwise Real structure on the actual rational adelic crossed product. -/
def ccmRationalAdelicCrossedProductRealStructure (F : Crossed) : Crossed :=
  F.sum fun k a ↦
    Finsupp.single k (ccmRationalAdelicMonomialRealTwist k a)

@[simp]
theorem ccmRationalAdelicCrossedProductRealStructure_single
    (k : Scale) (a : Core) :
    ccmRationalAdelicCrossedProductRealStructure (Finsupp.single k a) =
      Finsupp.single k (ccmRationalAdelicMonomialRealTwist k a) := by
  unfold ccmRationalAdelicCrossedProductRealStructure
  apply Finsupp.sum_single_index
  simp

@[simp]
theorem ccmRationalAdelicCrossedProductRealStructure_apply
    (F : Crossed) (k : Scale) :
    ccmRationalAdelicCrossedProductRealStructure F k =
      ccmRationalAdelicMonomialRealTwist k (F k) := by
  classical
  change (F.sum fun i a ↦
      Finsupp.single i (ccmRationalAdelicMonomialRealTwist i a)) k = _
  rw [Finsupp.sum_apply]
  induction F using Finsupp.induction with
  | zero => simp
  | @single_add i a F hi ha hF =>
      rw [Finsupp.sum_add_index]
      · by_cases hik : i = k
        · subst i
          simp [hF, ccmRationalAdelicMonomialRealTwist_add]
        · simp [hik, hF]
      · intro j
        simp
      · intro j hj b₁ b₂
        simp [ccmRationalAdelicMonomialRealTwist_add]

@[simp]
theorem ccmRationalAdelicCrossedProductRealStructure_zero :
    ccmRationalAdelicCrossedProductRealStructure (0 : Crossed) = 0 := by
  ext k
  simp

theorem ccmRationalAdelicCrossedProductRealStructure_add
    (F G : Crossed) :
    ccmRationalAdelicCrossedProductRealStructure (F + G) =
      ccmRationalAdelicCrossedProductRealStructure F +
        ccmRationalAdelicCrossedProductRealStructure G := by
  classical
  ext k
  simp [ccmRationalAdelicMonomialRealTwist_add]

theorem ccmRationalAdelicCrossedProductRealStructure_smul
    (z : ℂ) (F : Crossed) :
    ccmRationalAdelicCrossedProductRealStructure (z • F) =
      star z • ccmRationalAdelicCrossedProductRealStructure F := by
  classical
  ext k
  simp [ccmRationalAdelicMonomialRealTwist_smul]

/-- Crossed-product Real structure bundled conjugate-linearly. -/
def ccmRationalAdelicCrossedProductRealStructureₛₗ :
    Crossed →ₗ⋆[ℂ] Crossed where
  toFun := ccmRationalAdelicCrossedProductRealStructure
  map_add' := ccmRationalAdelicCrossedProductRealStructure_add
  map_smul' := ccmRationalAdelicCrossedProductRealStructure_smul

theorem ccmRationalAdelicCrossedProductRealStructure_sq (F : Crossed) :
    ccmRationalAdelicCrossedProductRealStructure
        (ccmRationalAdelicCrossedProductRealStructure F) = F := by
  classical
  ext k
  simp [ccmRationalAdelicMonomialRealTwist_sq]

theorem ccmRationalAdelicCrossedProductRealStructure_mul
    (F G : Crossed) :
    ccmRationalAdelicCrossedProductRealStructure (F * G) =
      ccmRationalAdelicCrossedProductRealStructure F *
        ccmRationalAdelicCrossedProductRealStructure G := by
  classical
  have hpure (k l : Scale) (a b : Core) :
      ccmRationalAdelicCrossedProductRealStructure
          (Finsupp.single k a * Finsupp.single l b) =
        ccmRationalAdelicCrossedProductRealStructure (Finsupp.single k a) *
          ccmRationalAdelicCrossedProductRealStructure (Finsupp.single l b) := by
    simp [ccmRationalAdelicCrossedProduct_single_mul_single,
      ccmRationalAdelicMonomialRealTwist_product]
  have hpureLeft (k : Scale) (a : Core) (H : Crossed) :
      ccmRationalAdelicCrossedProductRealStructure (Finsupp.single k a * H) =
        ccmRationalAdelicCrossedProductRealStructure (Finsupp.single k a) *
          ccmRationalAdelicCrossedProductRealStructure H := by
    induction H using Finsupp.induction with
    | zero => simp
    | @single_add l b H hl hb hH =>
        rw [ccmRationalAdelicCrossedProduct_mul_add,
          ccmRationalAdelicCrossedProductRealStructure_add,
          ccmRationalAdelicCrossedProductRealStructure_add,
          ccmRationalAdelicCrossedProduct_mul_add, hpure, hH]
  induction F using Finsupp.induction with
  | zero => simp
  | @single_add k a F hk ha hF =>
      rw [ccmRationalAdelicCrossedProduct_add_mul,
        ccmRationalAdelicCrossedProductRealStructure_add,
        ccmRationalAdelicCrossedProductRealStructure_add,
        ccmRationalAdelicCrossedProduct_add_mul, hpureLeft, hF]

/-! ## Minimal unitization -/

/-- Real involution on the unital CCM source. -/
def ccmRationalAdelicSourceRealStructure (x : Source) : Source :=
  Unitization.equiv.symm
    (star x.fst, ccmRationalAdelicCrossedProductRealStructure x.snd)

@[simp]
theorem ccmRationalAdelicSourceRealStructure_fst (x : Source) :
    (ccmRationalAdelicSourceRealStructure x).fst = star x.fst :=
  rfl

@[simp]
theorem ccmRationalAdelicSourceRealStructure_snd (x : Source) :
    (ccmRationalAdelicSourceRealStructure x).snd =
      ccmRationalAdelicCrossedProductRealStructure x.snd :=
  rfl

theorem ccmRationalAdelicSourceRealStructure_add (x y : Source) :
    ccmRationalAdelicSourceRealStructure (x + y) =
      ccmRationalAdelicSourceRealStructure x +
        ccmRationalAdelicSourceRealStructure y := by
  apply Unitization.ext <;>
    simp [ccmRationalAdelicCrossedProductRealStructure_add]

theorem ccmRationalAdelicSourceRealStructure_smul (z : ℂ) (x : Source) :
    ccmRationalAdelicSourceRealStructure (z • x) =
      star z • ccmRationalAdelicSourceRealStructure x := by
  apply Unitization.ext <;>
    simp [ccmRationalAdelicCrossedProductRealStructure_smul]

theorem ccmRationalAdelicSourceRealStructure_sq (x : Source) :
    ccmRationalAdelicSourceRealStructure
        (ccmRationalAdelicSourceRealStructure x) = x := by
  apply Unitization.ext
  · simp
  · simp [ccmRationalAdelicCrossedProductRealStructure_sq]

theorem ccmRationalAdelicSourceRealStructure_one :
    ccmRationalAdelicSourceRealStructure (1 : Source) = 1 := by
  apply Unitization.ext <;> simp

theorem ccmRationalAdelicSourceRealStructure_mul (x y : Source) :
    ccmRationalAdelicSourceRealStructure (x * y) =
      ccmRationalAdelicSourceRealStructure x *
        ccmRationalAdelicSourceRealStructure y := by
  apply Unitization.ext
  · simp
  · simp only [Unitization.snd_mul,
      ccmRationalAdelicSourceRealStructure_snd,
      ccmRationalAdelicSourceRealStructure_fst,
      ccmRationalAdelicCrossedProductRealStructure_add,
      ccmRationalAdelicCrossedProductRealStructure_smul,
      ccmRationalAdelicCrossedProductRealStructure_mul]

/-- Source involution bundled as a conjugate-linear map. -/
def ccmRationalAdelicSourceRealStructureₛₗ :
    Source →ₗ⋆[ℂ] Source where
  toFun := ccmRationalAdelicSourceRealStructure
  map_add' := ccmRationalAdelicSourceRealStructure_add
  map_smul' := ccmRationalAdelicSourceRealStructure_smul

/-- Exact even Real algebra structure on the unital rational CCM adelic source. -/
def ccmRationalAdelicSourceKRealAlgebra :
    KRealAlgebraStructure Source where
  sigma := ccmRationalAdelicSourceRealStructureₛₗ
  sq x := by
    change ccmRationalAdelicSourceRealStructure
        (ccmRationalAdelicSourceRealStructure x) = kRealParityAction false x
    rw [ccmRationalAdelicSourceRealStructure_sq]
    rfl
  map_one := ccmRationalAdelicSourceRealStructure_one
  map_mul := ccmRationalAdelicSourceRealStructure_mul

end RHTower
end GaloisForLFunctions
