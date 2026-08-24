import GaloisForLFunctions.HTGeometry.ScaledGammaNaturalOrbitCompleteness
import GaloisForLFunctions.HTGeometry.AnalyticSubringFractionEvaluation
import GaloisForLFunctions.HTGeometry.AnalyticFiniteProductDomain
import GaloisForLFunctions.HTGeometry.IncommensuratePeriodMeromorphicModel
import GaloisForLFunctions.RHTower.SelbergClass.GammaPoleOrder

/-!
# Exact exponential--rational classification of positive-scale Gamma products

This module upgrades scaled-residue character completeness from its finite Fourier statement to
the genuine meromorphic product.  The zero-charge direction is constructive: Gauss multiplication,
integer recurrence, and coordinate dilation produce one nonzero rational function times one
exponential.  The converse is proved by the affine Gamma divisor: a surviving canonical orbit has
infinitely many simple poles, while every other incommensurable orbit meets that progression at
most once and a rational function has only finitely many exceptional points.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex
open Bottcher
open _root_.HTGeometry
open Filter Set Topology Function
open scoped BigOperators

noncomputable section

local instance scaledGammaExpRatDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance scaledGammaExpRatComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance scaledGammaExpRatComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance scaledGammaExpRatRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

/-- Genuine finite positive-scale Gamma product in the global meromorphic field. -/
def positiveGammaFamilyMero {d : ℕ} (f : Fin d → PositiveAffineGammaFactor) :
    meroField Set.univ :=
  ∏ i, gammaScaleShiftMero (f i).scale
    (by exact_mod_cast (f i).scale_pos.ne') (f i).offset ^ (f i).multiplicity

/-- Exact exponential--rational subgroup of the global meromorphic field.  The nonzero complex
constant is absorbed into the nonzero rational factor. -/
def IsExponentialRationalMero (x : meroField Set.univ) : Prop :=
  ∃ r : RatFunc ℂ, r ≠ 0 ∧ ∃ beta : ℂ,
    x = algebraMap (RatFunc ℂ) (meroField Set.univ) r *
      physicalExponentialMero beta

theorem physicalExponentialMero_neg (beta : ℂ) :
    (physicalExponentialMero beta)⁻¹ = physicalExponentialMero (-beta) := by
  have hprod : physicalExponentialMero beta * physicalExponentialMero (-beta) = 1 := by
    rw [← physicalExponentialMero_add]
    simp
  calc
    (physicalExponentialMero beta)⁻¹ =
        (physicalExponentialMero beta)⁻¹ *
          (physicalExponentialMero beta * physicalExponentialMero (-beta)) := by
            rw [hprod, mul_one]
    _ = physicalExponentialMero (-beta) := by
      rw [← mul_assoc, inv_mul_cancel₀ (physicalExponentialMero_ne_zero beta), one_mul]

theorem physicalExponentialMero_zpow (beta : ℂ) (m : ℤ) :
    physicalExponentialMero beta ^ m =
      physicalExponentialMero ((m : ℂ) * beta) := by
  cases m with
  | ofNat n => exact physicalExponentialMero_pow beta n
  | negSucc n =>
      rw [zpow_negSucc, physicalExponentialMero_pow, physicalExponentialMero_neg]
      congr 1
      push_cast
      ring

theorem isExponentialRationalMero_one :
    IsExponentialRationalMero (1 : meroField Set.univ) := by
  refine ⟨1, one_ne_zero, 0, ?_⟩
  rw [map_one, one_mul, physicalExponentialMero_zero]

theorem isExponentialRationalMero_ratfunc (r : RatFunc ℂ) (hr : r ≠ 0) :
    IsExponentialRationalMero
      (algebraMap (RatFunc ℂ) (meroField Set.univ) r) := by
  refine ⟨r, hr, 0, ?_⟩
  simp

theorem isExponentialRationalMero_physicalExponential (beta : ℂ) :
    IsExponentialRationalMero (physicalExponentialMero beta) := by
  refine ⟨1, one_ne_zero, beta, ?_⟩
  rw [map_one, one_mul]

theorem IsExponentialRationalMero.mul {x y : meroField Set.univ}
    (hx : IsExponentialRationalMero x) (hy : IsExponentialRationalMero y) :
    IsExponentialRationalMero (x * y) := by
  obtain ⟨r, hr, beta, rfl⟩ := hx
  obtain ⟨q, hq, gamma, rfl⟩ := hy
  refine ⟨r * q, mul_ne_zero hr hq, beta + gamma, ?_⟩
  rw [map_mul, physicalExponentialMero_add]
  ring

theorem IsExponentialRationalMero.inv {x : meroField Set.univ}
    (hx : IsExponentialRationalMero x) :
    IsExponentialRationalMero x⁻¹ := by
  obtain ⟨r, hr, beta, rfl⟩ := hx
  refine ⟨r⁻¹, inv_ne_zero hr, -beta, ?_⟩
  rw [mul_inv_rev, map_inv₀, physicalExponentialMero_neg]
  ring

theorem IsExponentialRationalMero.zpow {x : meroField Set.univ}
    (hx : IsExponentialRationalMero x) (m : ℤ) :
    IsExponentialRationalMero (x ^ m) := by
  obtain ⟨r, hr, beta, rfl⟩ := hx
  refine ⟨r ^ m, zpow_ne_zero m hr, (m : ℂ) * beta, ?_⟩
  rw [mul_zpow, map_zpow₀, physicalExponentialMero_zpow]

theorem isExponentialRationalMero_finset_prod
    {ι : Type*} (s : Finset ι) (x : ι → meroField Set.univ)
    (hx : ∀ i ∈ s, IsExponentialRationalMero (x i)) :
    IsExponentialRationalMero (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isExponentialRationalMero_one
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hx i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => hx j (Finset.mem_insert_of_mem hj))

/-- Coordinate dilation sends an exponential mode to the mode with scaled frequency. -/
theorem complexScaleMeroEquiv_physicalExponentialMero
    (delta : ℂ) (hdelta : delta ≠ 0) (beta : ℂ) :
    complexScaleMeroEquiv delta hdelta (physicalExponentialMero beta) =
      physicalExponentialMero (beta * delta) := by
  rw [physicalExponentialMero, physicalExponentialMero,
    complexScaleMeroEquiv_algebraMap]
  congr 1
  apply Subtype.ext
  apply univGerm_ext
  intro z
  rw [univGermEval_complexScaleAnalyticEquiv,
    univGermEval_physicalExponentialAnalytic,
    univGermEval_physicalExponentialAnalytic]
  congr 1
  ring

theorem gammaShiftMero_eq_gammaScaleShiftMero_one (a : ℂ) :
    gammaShiftMero a = gammaScaleShiftMero (1 : ℂ) one_ne_zero a := by
  rw [gammaShiftMero, gammaScaleShiftMero_eq]
  congr 2
  apply Subtype.ext
  apply univGerm_ext
  intro z
  rw [univGermEval_reciprocalGammaShiftAnalytic,
    univGermEval_reciprocalGammaScaleShiftAnalytic]
  simp

/-- The exponential--rational subgroup is invariant under every nonzero coordinate dilation. -/
theorem IsExponentialRationalMero.complexScale
    {x : meroField Set.univ} (hx : IsExponentialRationalMero x)
    (delta : ℂ) (hdelta : delta ≠ 0) :
    IsExponentialRationalMero (complexScaleMeroEquiv delta hdelta x) := by
  obtain ⟨r, hr, beta, rfl⟩ := hx
  refine ⟨ratScaleBy delta hdelta r,
    (map_ne_zero_iff _ (ratScaleBy delta hdelta).injective).mpr hr,
    beta * delta, ?_⟩
  rw [map_mul, complexScaleMeroEquiv_physicalExponentialMero]
  congr 1
  exact complexScaleMeroEquiv_ratfuncToMero delta hdelta r

theorem isExponentialRationalMero_gammaNatScaleGaussGaugeMero
    {n : ℕ} (hn : 0 < n) (a : ℂ) :
    IsExponentialRationalMero (gammaNatScaleGaussGaugeMero n a) := by
  refine ⟨RatFunc.C (gammaNatScaleGaussConstant n a),
    ratFuncC_ne_zero (gammaNatScaleGaussConstant_ne_zero hn a),
    (n : ℂ) * Complex.log (n : ℂ), ?_⟩
  rw [gammaNatScaleGaussGaugeMero,
    ratFuncC_toMero_eq_complex_natScale]

theorem isExponentialRationalMero_gammaNatScaleFamilyGaugeMero
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    IsExponentialRationalMero (gammaNatScaleFamilyGaugeMero n a m) := by
  rw [gammaNatScaleFamilyGaugeMero]
  apply isExponentialRationalMero_finset_prod
  intro i hi
  exact (isExponentialRationalMero_gammaNatScaleGaussGaugeMero (hn i) (a i)).zpow (m i)

/-- Vanishing canonical refined charges gives a literal rational function for the refined product. -/
theorem isExponentialRationalMero_gammaNatScaleFamilyRefinedMero_of_orbitCharge
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hcharge : ∀ c : NaturalScaleGammaOrbit n a,
      naturalScaleGammaOrbitCharge n a m c = 0) :
    IsExponentialRationalMero (gammaNatScaleFamilyRefinedMero n a m) := by
  rw [gammaNatScaleFamilyRefinedMero_eq_slotProduct,
    gammaFintypeOrbitProductMero_automatic_normalForm]
  have hreduced : gammaShiftOrbitReducedProductMero
      (gammaNatScaleRefinedSlotShift n a) (gammaNatScaleRefinedSlotCharge m) = 1 := by
    rw [gammaShiftOrbitReducedProductMero]
    apply Finset.prod_eq_one
    intro c hc
    rw [show gammaShiftOrbitCharge (gammaNatScaleRefinedSlotShift n a)
        (gammaNatScaleRefinedSlotCharge m) c = 0 by
      exact hcharge c,
      zpow_zero]
  rw [hreduced, mul_one]
  exact isExponentialRationalMero_ratfunc
    (gammaShiftOrbitGaugeRat (naturalScaleGammaSlotShift n a) (fun x => m x.1))
    (gammaShiftOrbitGaugeRat_ne_zero _ _)

/-- Constructive common-natural-scale half of the exact classification. -/
theorem isExponentialRationalMero_gammaNatScaleFamilyMero_of_orbitCharge
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i)
    (hcharge : ∀ c : NaturalScaleGammaOrbit n a,
      naturalScaleGammaOrbitCharge n a m c = 0) :
    IsExponentialRationalMero (gammaNatScaleFamilyMero n a m) := by
  rw [gammaNatScaleFamilyMero_normalForm n a m hn]
  exact (isExponentialRationalMero_gammaNatScaleFamilyGaugeMero n a m hn).mul
    (isExponentialRationalMero_gammaNatScaleFamilyRefinedMero_of_orbitCharge
      n a m hcharge)

/-- Constructive commensurable-block half of the exact classification. -/
theorem isExponentialRationalMero_commonUnitScaleGammaFamilyMero_of_orbitCharge
    {d : ℕ} (delta : ℝ) (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hdelta : 0 < delta) (hn : ∀ i, 0 < n i)
    (hcharge : ∀ c : NaturalScaleGammaOrbit n a,
      naturalScaleGammaOrbitCharge n a m c = 0) :
    IsExponentialRationalMero
      (commonUnitScaleGammaFamilyMero delta n a m hdelta hn) := by
  rw [commonUnitScaleGammaFamilyMero_eq_complexScale]
  exact (isExponentialRationalMero_gammaNatScaleFamilyMero_of_orbitCharge
    n a m hn hcharge).complexScale (delta : ℂ) (by exact_mod_cast hdelta.ne')

/-- Restricting the genuine arbitrary-scale product to one canonical class gives its common-unit
product literally. -/
theorem positiveGammaFamilyMero_commonUnitScaleGammaFactor
    {d : ℕ} (delta : ℝ) (n : Fin d → ℕ) (a : Fin d → ℂ) (m : Fin d → ℤ)
    (hdelta : 0 < delta) (hn : ∀ i, 0 < n i) :
    positiveGammaFamilyMero (commonUnitScaleGammaFactor delta n a m hdelta hn) =
      commonUnitScaleGammaFamilyMero delta n a m hdelta hn := by
  rw [positiveGammaFamilyMero, commonUnitScaleGammaFamilyMero]
  apply Finset.prod_congr rfl
  intro i hi
  congr 2
  norm_cast

theorem positiveGammaFamilyMero_classFactor_eq_commonUnitScale
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor)
    (c : PositiveGammaScaleClass f) :
    positiveGammaFamilyMero (positiveGammaScaleClassFactor f c) =
      commonUnitScaleGammaFamilyMero
        (canonicalPositiveGammaCommonUnit f c)
        (positiveGammaScaleClassNaturalScale f c)
        (positiveGammaScaleClassOffset f c)
        (positiveGammaScaleClassMultiplicity f c)
        (canonicalPositiveGammaCommonUnit_pos f c)
        (positiveGammaScaleClassNaturalScale_pos f c) := by
  calc
    positiveGammaFamilyMero (positiveGammaScaleClassFactor f c) =
        positiveGammaFamilyMero
          (commonUnitScaleGammaFactor
            (canonicalPositiveGammaCommonUnit f c)
            (positiveGammaScaleClassNaturalScale f c)
            (positiveGammaScaleClassOffset f c)
            (positiveGammaScaleClassMultiplicity f c)
            (canonicalPositiveGammaCommonUnit_pos f c)
            (positiveGammaScaleClassNaturalScale_pos f c)) :=
      congrArg positiveGammaFamilyMero
        (positiveGammaScaleClassFactor_eq_commonUnitScale f c)
    _ = _ := positiveGammaFamilyMero_commonUnitScaleGammaFactor _ _ _ _ _ _

/-- The original product is exactly the product of its canonical rational-commensurability
blocks. -/
theorem prod_positiveGammaFamilyMero_classFactor_eq
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor) :
    ∏ c : PositiveGammaScaleClass f,
        positiveGammaFamilyMero (positiveGammaScaleClassFactor f c) =
      positiveGammaFamilyMero f := by
  classical
  rw [positiveGammaFamilyMero]
  calc
    ∏ c : PositiveGammaScaleClass f,
        positiveGammaFamilyMero (positiveGammaScaleClassFactor f c) =
      ∏ c : PositiveGammaScaleClass f,
        ∏ i : PositiveGammaScaleClassFiber f c,
          gammaScaleShiftMero (f i).scale
            (by exact_mod_cast (f i).scale_pos.ne') (f i).offset ^
              (f i).multiplicity := by
        apply Finset.prod_congr rfl
        intro c hc
        rw [positiveGammaFamilyMero]
        simpa [positiveGammaScaleClassFactor] using
          (Equiv.prod_comp (positiveGammaScaleClassFiberEquivFin f c).symm
            (fun i : PositiveGammaScaleClassFiber f c =>
              gammaScaleShiftMero (f i).scale
                (by exact_mod_cast (f i).scale_pos.ne') (f i).offset ^
                  (f i).multiplicity))
    _ = ∏ c : PositiveGammaScaleClass f,
          ∏ i : Fin d, if Quotient.mk'' i = c then
            gammaScaleShiftMero (f i).scale
              (by exact_mod_cast (f i).scale_pos.ne') (f i).offset ^
                (f i).multiplicity else 1 := by
        apply Finset.prod_congr rfl
        intro c hc
        rw [← Finset.prod_filter]
        symm
        exact Finset.prod_subtype
          (Finset.univ.filter fun i : Fin d => Quotient.mk'' i = c)
          (fun i => by simp)
          (fun i => gammaScaleShiftMero (f i).scale
            (by exact_mod_cast (f i).scale_pos.ne') (f i).offset ^
              (f i).multiplicity)
    _ = ∏ i : Fin d, gammaScaleShiftMero (f i).scale
          (by exact_mod_cast (f i).scale_pos.ne') (f i).offset ^
            (f i).multiplicity := by
        rw [Finset.prod_comm]
        apply Finset.prod_congr rfl
        intro i hi
        rw [Finset.prod_eq_single (Quotient.mk'' i)]
        · simp
        · intro c hc hci
          simp [hci.symm]
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim

/-- Vanishing of the actual scaled residue character constructively forces the genuine arbitrary
positive-scale Gamma product into the exponential--rational subgroup. -/
theorem isExponentialRationalMero_positiveGammaFamilyMero_of_alienChargeZero
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor)
    (hzero : ScaledGammaAlienChargeZero f) :
    IsExponentialRationalMero (positiveGammaFamilyMero f) := by
  have hcharges := (scaledGammaAlienChargeZero_iff_canonicalOrbitCharges f).mp hzero
  rw [← prod_positiveGammaFamilyMero_classFactor_eq f]
  apply isExponentialRationalMero_finset_prod
  intro c hc
  rw [positiveGammaFamilyMero_classFactor_eq_commonUnitScale]
  exact isExponentialRationalMero_commonUnitScaleGammaFamilyMero_of_orbitCharge
    (canonicalPositiveGammaCommonUnit f c)
    (positiveGammaScaleClassNaturalScale f c)
    (positiveGammaScaleClassOffset f c)
    (positiveGammaScaleClassMultiplicity f c)
    (canonicalPositiveGammaCommonUnit_pos f c)
    (positiveGammaScaleClassNaturalScale_pos f c)
    (hcharges c)

/-! ## Divisor rigidity for a finite separated affine family -/

variable {ι : Type*} [Fintype ι]

/-- Reciprocal-Gamma entire germ attached to an arbitrary positive affine clock. -/
def affineGammaReciprocalAnalytic (scale : ι → ℝ) (offset : ι → ℂ) (i : ι) :
    analyticSubring Set.univ :=
  reciprocalGammaScaleShiftAnalytic (scale i : ℂ) (offset i)

/-- Pointwise entire representative of `affineGammaReciprocalAnalytic`. -/
def affineGammaReciprocalFunction (scale : ι → ℝ) (offset : ι → ℂ)
    (i : ι) (z : ℂ) : ℂ :=
  reciprocalGammaEntire ((scale i : ℂ) * z + offset i)

omit [Fintype ι] in
@[simp] theorem univGermEval_affineGammaReciprocalAnalytic
    (scale : ι → ℝ) (offset : ι → ℂ) (i : ι) (z : ℂ) :
    univGermEval z
        (affineGammaReciprocalAnalytic scale offset i :
          Germ (Filter.principal Set.univ) ℂ) =
      affineGammaReciprocalFunction scale offset i z := by
  rfl

omit [Fintype ι] in theorem affineGammaReciprocalAnalytic_ne_zero
    (scale : ι → ℝ) (offset : ι → ℂ) (hscale : ∀ i, 0 < scale i) (i : ι) :
    affineGammaReciprocalAnalytic scale offset i ≠ 0 := by
  intro hzero
  have hmap := congrArg
    (algebraMap (analyticSubring Set.univ) (meroField Set.univ)) hzero
  have hmap' : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (reciprocalGammaScaleShiftAnalytic (scale i : ℂ) (offset i)) = 0 := by
    simpa [affineGammaReciprocalAnalytic] using hmap
  have hgamma := gammaScaleShiftMero_ne_zero (scale i : ℂ)
    (by exact_mod_cast (hscale i).ne') (offset i)
  rw [gammaScaleShiftMero_eq, hmap', inv_zero] at hgamma
  exact hgamma rfl

/-- Entire numerator obtained by moving negative Gamma exponents upstairs. -/
def affineGammaProductNumeratorAnalytic
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ) :
    analyticSubring Set.univ :=
  ∏ i, affineGammaReciprocalAnalytic scale offset i ^ (-m i).toNat

/-- Entire denominator obtained from positive Gamma exponents. -/
def affineGammaProductDenominatorAnalytic
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ) :
    analyticSubring Set.univ :=
  ∏ i, affineGammaReciprocalAnalytic scale offset i ^ (m i).toNat

theorem affineGammaProductNumeratorAnalytic_ne_zero
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ)
    (hscale : ∀ i, 0 < scale i) :
    affineGammaProductNumeratorAnalytic scale offset m ≠ 0 := by
  classical
  rw [affineGammaProductNumeratorAnalytic, Finset.prod_ne_zero_iff]
  intro i hi
  exact pow_ne_zero _ (affineGammaReciprocalAnalytic_ne_zero scale offset hscale i)

theorem affineGammaProductDenominatorAnalytic_ne_zero
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ)
    (hscale : ∀ i, 0 < scale i) :
    affineGammaProductDenominatorAnalytic scale offset m ≠ 0 := by
  classical
  rw [affineGammaProductDenominatorAnalytic, Finset.prod_ne_zero_iff]
  intro i hi
  exact pow_ne_zero _ (affineGammaReciprocalAnalytic_ne_zero scale offset hscale i)

/-- Pointwise numerator used in the divisor calculation. -/
def affineGammaProductNumeratorFunction
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ) (z : ℂ) : ℂ :=
  ∏ i, affineGammaReciprocalFunction scale offset i z ^ (-m i).toNat

/-- Pointwise denominator used in the divisor calculation. -/
def affineGammaProductDenominatorFunction
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ) (z : ℂ) : ℂ :=
  ∏ i, affineGammaReciprocalFunction scale offset i z ^ (m i).toNat

@[simp] theorem univGermEval_affineGammaProductNumeratorAnalytic
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ) (z : ℂ) :
    univGermEval z
        (affineGammaProductNumeratorAnalytic scale offset m :
          Germ (Filter.principal Set.univ) ℂ) =
      affineGammaProductNumeratorFunction scale offset m z := by
  classical
  rw [affineGammaProductNumeratorAnalytic,
    affineGammaProductNumeratorFunction]
  change univGermEval z
      ((∏ i ∈ Finset.univ,
        affineGammaReciprocalAnalytic scale offset i ^ (-m i).toNat :
          analyticSubring Set.univ) : Germ (Filter.principal Set.univ) ℂ) = _
  rw [univGermEval_analyticSubring_finset_prod]
  apply Finset.prod_congr rfl
  intro i hi
  change univGermEval z
      ((affineGammaReciprocalAnalytic scale offset i :
        Germ (Filter.principal Set.univ) ℂ) ^ (-m i).toNat) = _
  rw [map_pow, univGermEval_affineGammaReciprocalAnalytic]

@[simp] theorem univGermEval_affineGammaProductDenominatorAnalytic
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ) (z : ℂ) :
    univGermEval z
        (affineGammaProductDenominatorAnalytic scale offset m :
          Germ (Filter.principal Set.univ) ℂ) =
      affineGammaProductDenominatorFunction scale offset m z := by
  classical
  rw [affineGammaProductDenominatorAnalytic,
    affineGammaProductDenominatorFunction]
  change univGermEval z
      ((∏ i ∈ Finset.univ,
        affineGammaReciprocalAnalytic scale offset i ^ (m i).toNat :
          analyticSubring Set.univ) : Germ (Filter.principal Set.univ) ℂ) = _
  rw [univGermEval_analyticSubring_finset_prod]
  apply Finset.prod_congr rfl
  intro i hi
  change univGermEval z
      ((affineGammaReciprocalAnalytic scale offset i :
        Germ (Filter.principal Set.univ) ℂ) ^ (m i).toNat) = _
  rw [map_pow, univGermEval_affineGammaReciprocalAnalytic]

/-- Genuine meromorphic product for an arbitrary finite positive affine family. -/
def affineGammaFintypeProductMero
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ)
    (hscale : ∀ i, 0 < scale i) : meroField Set.univ :=
  ∏ i, gammaScaleShiftMero (scale i : ℂ)
    (by exact_mod_cast (hscale i).ne') (offset i) ^ m i

theorem inv_zpow_eq_toNat_div {K : Type*} [Field K] (x : K) (m : ℤ) :
    (x⁻¹) ^ m = x ^ (-m).toNat / x ^ m.toNat := by
  rw [inv_zpow']
  cases m with
  | ofNat n => simp
  | negSucc n =>
      simp
      exact zpow_natCast x (n + 1)

/-- Every finite affine Gamma product has an explicit quotient of two entire reciprocal-Gamma
products. -/
theorem affineGammaFintypeProductMero_eq_fraction
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ)
    (hscale : ∀ i, 0 < scale i) :
    affineGammaFintypeProductMero scale offset m hscale =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (affineGammaProductNumeratorAnalytic scale offset m) /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (affineGammaProductDenominatorAnalytic scale offset m) := by
  classical
  rw [affineGammaFintypeProductMero,
    affineGammaProductNumeratorAnalytic,
    affineGammaProductDenominatorAnalytic, map_prod, map_prod,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [gammaScaleShiftMero_eq, inv_zpow_eq_toNat_div, map_pow, map_pow]
  rfl

/-- Polynomial/exponential normal form as a quotient of two global entire germs. -/
theorem exponentialRationalMero_eq_analytic_fraction
    (r : RatFunc ℂ) (beta : ℂ) :
    algebraMap (RatFunc ℂ) (meroField Set.univ) r *
        physicalExponentialMero beta =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ r.num * physicalExponentialAnalytic beta) /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ r.denom) := by
  have hr := congrArg
    (algebraMap (RatFunc ℂ) (meroField Set.univ)) (RatFunc.num_div_denom r)
  rw [map_div₀] at hr
  change ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) r.num) /
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) r.denom) =
    ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ r at hr
  rw [ratfuncToMero_algebraMap_polynomial,
    ratfuncToMero_algebraMap_polynomial] at hr
  change ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ r * physicalExponentialMero beta = _
  rw [← hr, physicalExponentialMero, map_mul]
  simp only [polyToMero, RingHom.comp_apply]
  simp only [div_eq_mul_inv]
  ring

/-- Equality of the two meromorphic fractions forces equality after clearing their nonzero entire
denominators. -/
theorem analytic_crossProduct_eq_of_affineGammaProduct_eq_exponentialRational
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ)
    (hscale : ∀ i, 0 < scale i) (r : RatFunc ℂ) (beta : ℂ)
    (heq : affineGammaFintypeProductMero scale offset m hscale =
      algebraMap (RatFunc ℂ) (meroField Set.univ) r * physicalExponentialMero beta) :
    affineGammaProductNumeratorAnalytic scale offset m *
        polyToAnalytic Set.univ r.denom =
      (polyToAnalytic Set.univ r.num * physicalExponentialAnalytic beta) *
        affineGammaProductDenominatorAnalytic scale offset m := by
  have hfrac :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (affineGammaProductNumeratorAnalytic scale offset m) /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (affineGammaProductDenominatorAnalytic scale offset m) =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ r.num * physicalExponentialAnalytic beta) /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ r.denom) := by
    rw [← affineGammaFintypeProductMero_eq_fraction scale offset m hscale,
      ← exponentialRationalMero_eq_analytic_fraction]
    exact heq
  have hdenGamma : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (affineGammaProductDenominatorAnalytic scale offset m) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective
      (analyticSubring Set.univ) (meroField Set.univ))).mpr
      (affineGammaProductDenominatorAnalytic_ne_zero scale offset m hscale)
  have hdenRatA : polyToAnalytic Set.univ r.denom ≠ 0 :=
    (map_ne_zero_iff (polyToAnalytic Set.univ)
      (polyToAnalytic_injective (U := Set.univ) Set.infinite_univ)).mpr
        (RatFunc.denom_ne_zero r)
  have hdenRat : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (polyToAnalytic Set.univ r.denom) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective
      (analyticSubring Set.univ) (meroField Set.univ))).mpr hdenRatA
  have hcross := (div_eq_div_iff hdenGamma hdenRat).mp hfrac
  apply IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ)
  simpa only [map_mul] using hcross

/-- `n`-th pole of one positive affine Gamma clock. -/
def affineGammaPolePoint (scale : ι → ℝ) (offset : ι → ℂ)
    (i : ι) (n : ℕ) : ℂ :=
  -((offset i + n) / (scale i : ℂ))

omit [Fintype ι] in theorem affineGammaPolePoint_injective
    (scale : ι → ℝ) (offset : ι → ℂ) (hscale : ∀ i, 0 < scale i) (i : ι) :
    Function.Injective (affineGammaPolePoint scale offset i) := by
  intro n k h
  have hs : (scale i : ℂ) ≠ 0 := by exact_mod_cast (hscale i).ne'
  have hcast : (n : ℂ) = (k : ℂ) := by
    have h' := congrArg (fun z : ℂ => -z * (scale i : ℂ)) h
    simp only [affineGammaPolePoint] at h'
    field_simp [hs] at h'
    linear_combination h'
  exact_mod_cast hcast

omit [Fintype ι] in theorem analyticOnNhd_affineGammaReciprocalFunction
    (scale : ι → ℝ) (offset : ι → ℂ) (i : ι) :
    AnalyticOnNhd ℂ (affineGammaReciprocalFunction scale offset i) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact contDiff_reciprocalGammaEntire.differentiable (by simp) |>.comp (by fun_prop)

omit [Fintype ι] in
/-- The reciprocal Gamma clock has a simple zero at every affine Gamma pole. -/
theorem meromorphicOrderAt_affineGammaReciprocalFunction_pole
    (scale : ι → ℝ) (offset : ι → ℂ) (hscale : ∀ i, 0 < scale i)
    (i : ι) (n : ℕ) :
    meromorphicOrderAt (affineGammaReciprocalFunction scale offset i)
      (affineGammaPolePoint scale offset i n) = (1 : ℤ) := by
  have hs : scale i ≠ 0 := (hscale i).ne'
  change meromorphicOrderAt
      ((fun z : ℂ => Complex.Gamma ((scale i : ℂ) * z + offset i))⁻¹)
      (-((offset i + n) / (scale i : ℂ))) = (1 : ℤ)
  rw [meromorphicOrderAt_inv,
    Complex.meromorphicOrderAt_Gamma_affine_neg_nat (scale i) hs (offset i) n]
  norm_num

omit [Fintype ι] in
/-- Away from its affine pole progression, a reciprocal Gamma clock has order zero. -/
theorem meromorphicOrderAt_affineGammaReciprocalFunction_off_poles
    (scale : ι → ℝ) (offset : ι → ℂ) (hscale : ∀ i, 0 < scale i)
    (i : ι) (z : ℂ)
    (hoff : ∀ n : ℕ, z ≠ affineGammaPolePoint scale offset i n) :
    meromorphicOrderAt (affineGammaReciprocalFunction scale offset i) z = 0 := by
  have harg : ∀ n : ℕ, (scale i : ℂ) * z + offset i ≠ -(n : ℂ) := by
    intro n h
    apply hoff n
    have hs : (scale i : ℂ) ≠ 0 := by exact_mod_cast (hscale i).ne'
    simp only [affineGammaPolePoint]
    field_simp [hs]
    linear_combination h
  have han : AnalyticAt ℂ (affineGammaReciprocalFunction scale offset i) z :=
    analyticOnNhd_affineGammaReciprocalFunction scale offset i z (Set.mem_univ z)
  have hne : affineGammaReciprocalFunction scale offset i z ≠ 0 := by
    exact inv_ne_zero (Complex.Gamma_ne_zero harg)
  rw [han.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (.inr hne)]
  rfl

theorem meromorphicAt_affineGammaProductNumeratorFunction
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ) (z : ℂ) :
    MeromorphicAt (affineGammaProductNumeratorFunction scale offset m) z := by
  classical
  rw [show affineGammaProductNumeratorFunction scale offset m =
      ∏ i, (affineGammaReciprocalFunction scale offset i) ^ (-m i).toNat by
    funext w
    simp [affineGammaProductNumeratorFunction]]
  exact MeromorphicAt.prod fun i _ =>
    ((analyticOnNhd_affineGammaReciprocalFunction scale offset i z
      (Set.mem_univ z)).pow _).meromorphicAt

theorem meromorphicAt_affineGammaProductDenominatorFunction
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ) (z : ℂ) :
    MeromorphicAt (affineGammaProductDenominatorFunction scale offset m) z := by
  classical
  rw [show affineGammaProductDenominatorFunction scale offset m =
      ∏ i, (affineGammaReciprocalFunction scale offset i) ^ (m i).toNat by
    funext w
    simp [affineGammaProductDenominatorFunction]]
  exact MeromorphicAt.prod fun i _ =>
    ((analyticOnNhd_affineGammaReciprocalFunction scale offset i z
      (Set.mem_univ z)).pow _).meromorphicAt

/-- Numerator order at a pole belonging to exactly one affine progression. -/
theorem meromorphicOrderAt_affineGammaProductNumeratorFunction_isolated
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ)
    (hscale : ∀ i, 0 < scale i) (i0 : ι) (n : ℕ)
    (hisolated : ∀ i, i ≠ i0 → ∀ k : ℕ,
      affineGammaPolePoint scale offset i0 n ≠ affineGammaPolePoint scale offset i k) :
    meromorphicOrderAt (affineGammaProductNumeratorFunction scale offset m)
        (affineGammaPolePoint scale offset i0 n) =
      (((-m i0).toNat : ℕ) : ℤ) := by
  classical
  rw [show affineGammaProductNumeratorFunction scale offset m =
      ∏ i, (affineGammaReciprocalFunction scale offset i) ^ (-m i).toNat by
    funext w
    simp [affineGammaProductNumeratorFunction]]
  rw [meromorphicOrderAt_prod]
  · rw [Finset.sum_eq_single i0]
    · rw [meromorphicOrderAt_pow
          ((analyticOnNhd_affineGammaReciprocalFunction scale offset i0 _
            (Set.mem_univ _)).meromorphicAt),
        meromorphicOrderAt_affineGammaReciprocalFunction_pole scale offset hscale]
      cases m i0 <;> simp
    · intro i hi hii
      rw [meromorphicOrderAt_pow
          ((analyticOnNhd_affineGammaReciprocalFunction scale offset i _
            (Set.mem_univ _)).meromorphicAt),
        meromorphicOrderAt_affineGammaReciprocalFunction_off_poles scale offset hscale]
      · simp
      · exact hisolated i hii
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · intro i hi
    exact ((analyticOnNhd_affineGammaReciprocalFunction scale offset i _
      (Set.mem_univ _)).pow _).meromorphicAt

/-- Denominator order at a pole belonging to exactly one affine progression. -/
theorem meromorphicOrderAt_affineGammaProductDenominatorFunction_isolated
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ)
    (hscale : ∀ i, 0 < scale i) (i0 : ι) (n : ℕ)
    (hisolated : ∀ i, i ≠ i0 → ∀ k : ℕ,
      affineGammaPolePoint scale offset i0 n ≠ affineGammaPolePoint scale offset i k) :
    meromorphicOrderAt (affineGammaProductDenominatorFunction scale offset m)
        (affineGammaPolePoint scale offset i0 n) =
      (((m i0).toNat : ℕ) : ℤ) := by
  classical
  rw [show affineGammaProductDenominatorFunction scale offset m =
      ∏ i, (affineGammaReciprocalFunction scale offset i) ^ (m i).toNat by
    funext w
    simp [affineGammaProductDenominatorFunction]]
  rw [meromorphicOrderAt_prod]
  · rw [Finset.sum_eq_single i0]
    · rw [meromorphicOrderAt_pow
          ((analyticOnNhd_affineGammaReciprocalFunction scale offset i0 _
            (Set.mem_univ _)).meromorphicAt),
        meromorphicOrderAt_affineGammaReciprocalFunction_pole scale offset hscale]
      cases m i0 <;> simp
    · intro i hi hii
      rw [meromorphicOrderAt_pow
          ((analyticOnNhd_affineGammaReciprocalFunction scale offset i _
            (Set.mem_univ _)).meromorphicAt),
        meromorphicOrderAt_affineGammaReciprocalFunction_off_poles scale offset hscale]
      · simp
      · exact hisolated i hii
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · intro i hi
    exact ((analyticOnNhd_affineGammaReciprocalFunction scale offset i _
      (Set.mem_univ _)).pow _).meromorphicAt

theorem meromorphicOrderAt_polynomial_eval_eq_zero_of_not_root
    (P : Polynomial ℂ) (z : ℂ) (hz : ¬ P.IsRoot z) :
    meromorphicOrderAt (fun w : ℂ => P.eval w) z = 0 := by
  have han : AnalyticAt ℂ (fun w : ℂ => P.eval w) z :=
    analyticOnNhd_polyEval Set.univ P z (Set.mem_univ z)
  have hne : P.eval z ≠ 0 := by simpa [Polynomial.IsRoot] using hz
  have hzero : analyticOrderAt (fun w : ℂ => P.eval w) z = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr hne)
  rw [han.meromorphicOrderAt_eq, hzero]
  rfl

theorem meromorphicOrderAt_polynomial_mul_exp_eq_zero_of_not_root
    (P : Polynomial ℂ) (beta z : ℂ) (hz : ¬ P.IsRoot z) :
    meromorphicOrderAt (fun w : ℂ => P.eval w * Complex.exp (beta * w)) z = 0 := by
  have hpoly : AnalyticAt ℂ (fun w : ℂ => P.eval w) z :=
    analyticOnNhd_polyEval Set.univ P z (Set.mem_univ z)
  have hexp : AnalyticAt ℂ (fun w : ℂ => Complex.exp (beta * w)) z := by fun_prop
  have han : AnalyticAt ℂ (fun w : ℂ => P.eval w * Complex.exp (beta * w)) z :=
    hpoly.mul hexp
  have hne : P.eval z * Complex.exp (beta * z) ≠ 0 :=
    mul_ne_zero (by simpa [Polynomial.IsRoot] using hz) (Complex.exp_ne_zero _)
  have hzero : analyticOrderAt
      (fun w : ℂ => P.eval w * Complex.exp (beta * w)) z = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr hne)
  rw [han.meromorphicOrderAt_eq, hzero]
  rfl

/-- Branch indices where two affine Gamma pole progressions meet. -/
def affineGammaPoleCollisionSet (scale : ι → ℝ) (offset : ι → ℂ)
    (i j : ι) : Set ℕ :=
  {n | ∃ k : ℕ,
    affineGammaPolePoint scale offset i n = affineGammaPolePoint scale offset j k}

omit [Fintype ι] in theorem finite_affineGammaPolePoint_polynomialRoots
    (scale : ι → ℝ) (offset : ι → ℂ) (hscale : ∀ i, 0 < scale i)
    (i : ι) (P : Polynomial ℂ) (hP : P ≠ 0) :
    {n : ℕ | P.IsRoot (affineGammaPolePoint scale offset i n)}.Finite := by
  apply Set.Finite.preimage
    (f := affineGammaPolePoint scale offset i)
    (s := {z : ℂ | P.IsRoot z})
  · intro n hn k hk hnk
    exact affineGammaPolePoint_injective scale offset hscale i hnk
  · exact Polynomial.finite_setOf_isRoot hP

theorem exists_nat_outside_finite_set (s : Set ℕ) (hs : s.Finite) :
    ∃ n : ℕ, n ∉ s := by
  by_contra h
  push Not at h
  have hsu : s = Set.univ := Set.eq_univ_of_forall h
  exact (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) (by
    rwa [← hsu])

/-- **Separated affine-Gamma divisor rigidity.**  If distinct pole progressions have finite
intersection, a finite signed Gamma product is exponential--rational only when every exponent is
zero.  This is a native meromorphic-divisor theorem, independent of differential algebraicity. -/
theorem isExponentialRationalMero_affineGammaFintypeProductMero_iff
    (scale : ι → ℝ) (offset : ι → ℂ) (m : ι → ℤ)
    (hscale : ∀ i, 0 < scale i)
    (hsep : ∀ i j, i ≠ j →
      (affineGammaPoleCollisionSet scale offset i j).Finite) :
    IsExponentialRationalMero
        (affineGammaFintypeProductMero scale offset m hscale) ↔
      ∀ i, m i = 0 := by
  classical
  constructor
  · rintro ⟨r, hr, beta, heq⟩ i0
    let crossBad : Set ℕ :=
      {n | ∃ j : ι, j ≠ i0 ∧ n ∈ affineGammaPoleCollisionSet scale offset i0 j}
    have hcrossBad : crossBad.Finite := by
      let indices : Set ι := {j | j ≠ i0}
      have hindices : indices.Finite := Set.toFinite _
      have hu : (⋃ j ∈ indices,
          affineGammaPoleCollisionSet scale offset i0 j).Finite :=
        hindices.biUnion fun j hj => hsep i0 j hj.symm
      apply hu.subset
      intro n hn
      obtain ⟨j, hj, hn⟩ := hn
      exact Set.mem_iUnion_of_mem j (Set.mem_iUnion_of_mem hj hn)
    let numBad : Set ℕ :=
      {n | r.num.IsRoot (affineGammaPolePoint scale offset i0 n)}
    let denBad : Set ℕ :=
      {n | r.denom.IsRoot (affineGammaPolePoint scale offset i0 n)}
    have hnumBad : numBad.Finite :=
      finite_affineGammaPolePoint_polynomialRoots scale offset hscale i0 r.num
        (RatFunc.num_ne_zero hr)
    have hdenBad : denBad.Finite :=
      finite_affineGammaPolePoint_polynomialRoots scale offset hscale i0 r.denom
        (RatFunc.denom_ne_zero r)
    let bad : Set ℕ := crossBad ∪ numBad ∪ denBad
    have hbad : bad.Finite := (hcrossBad.union hnumBad).union hdenBad
    obtain ⟨n, hn⟩ := exists_nat_outside_finite_set bad hbad
    have hncross : n ∉ crossBad := by
      intro h
      exact hn (Or.inl (Or.inl h))
    have hnnum : ¬ r.num.IsRoot (affineGammaPolePoint scale offset i0 n) := by
      intro h
      exact hn (Or.inl (Or.inr h))
    have hnden : ¬ r.denom.IsRoot (affineGammaPolePoint scale offset i0 n) := by
      intro h
      exact hn (Or.inr h)
    have hisolated : ∀ i, i ≠ i0 → ∀ k : ℕ,
        affineGammaPolePoint scale offset i0 n ≠
          affineGammaPolePoint scale offset i k := by
      intro i hi k hik
      apply hncross
      exact ⟨i, hi, k, hik⟩
    have hcross :=
      analytic_crossProduct_eq_of_affineGammaProduct_eq_exponentialRational
        scale offset m hscale r beta heq
    have hfun :
        (fun z => affineGammaProductNumeratorFunction scale offset m z *
          r.denom.eval z) =
        (fun z => (r.num.eval z * Complex.exp (beta * z)) *
          affineGammaProductDenominatorFunction scale offset m z) := by
      funext z
      have hz := congrArg
        (fun a : analyticSubring Set.univ =>
          univGermEval z (a : Germ (Filter.principal Set.univ) ℂ)) hcross
      rw [univGermEval_analyticSubring_mul,
        univGermEval_affineGammaProductNumeratorAnalytic,
        univGermEval_analyticSubring_mul,
        univGermEval_analyticSubring_mul,
        univGermEval_physicalExponentialAnalytic,
        univGermEval_affineGammaProductDenominatorAnalytic] at hz
      exact hz
    let p := affineGammaPolePoint scale offset i0 n
    have hleft : meromorphicOrderAt
        (fun z => affineGammaProductNumeratorFunction scale offset m z *
          r.denom.eval z) p = (((-m i0).toNat : ℕ) : ℤ) := by
      change meromorphicOrderAt
        (affineGammaProductNumeratorFunction scale offset m *
          fun z => r.denom.eval z) p = _
      rw [meromorphicOrderAt_mul
        (meromorphicAt_affineGammaProductNumeratorFunction scale offset m p)
        ((analyticOnNhd_polyEval Set.univ r.denom p (Set.mem_univ p)).meromorphicAt),
        meromorphicOrderAt_affineGammaProductNumeratorFunction_isolated
          scale offset m hscale i0 n hisolated,
        meromorphicOrderAt_polynomial_eval_eq_zero_of_not_root r.denom p hnden,
        add_zero]
    have hright : meromorphicOrderAt
        (fun z => (r.num.eval z * Complex.exp (beta * z)) *
          affineGammaProductDenominatorFunction scale offset m z) p =
        (((m i0).toNat : ℕ) : ℤ) := by
      change meromorphicOrderAt
        ((fun z : ℂ => r.num.eval z * Complex.exp (beta * z)) *
          affineGammaProductDenominatorFunction scale offset m) p = _
      rw [meromorphicOrderAt_mul
        ((by
          have hpoly := analyticOnNhd_polyEval Set.univ r.num p (Set.mem_univ p)
          have hexp : AnalyticAt ℂ (fun z : ℂ => Complex.exp (beta * z)) p := by
            fun_prop
          exact (hpoly.mul hexp).meromorphicAt) :
          MeromorphicAt (fun z : ℂ => r.num.eval z * Complex.exp (beta * z)) p)
        (meromorphicAt_affineGammaProductDenominatorFunction scale offset m p),
        meromorphicOrderAt_polynomial_mul_exp_eq_zero_of_not_root r.num beta p hnnum,
        meromorphicOrderAt_affineGammaProductDenominatorFunction_isolated
          scale offset m hscale i0 n hisolated,
        zero_add]
    have hordTop :
        (↑(((-m i0).toNat : ℕ) : ℤ) : WithTop ℤ) =
          (↑(((m i0).toNat : ℕ) : ℤ) : WithTop ℤ) := by
      rw [← hleft, hfun, hright]
    have hord : (((-m i0).toNat : ℕ) : ℤ) = (((m i0).toNat : ℕ) : ℤ) :=
      WithTop.coe_eq_coe.mp hordTop
    have hnat : (-m i0).toNat = (m i0).toNat := by
      exact_mod_cast hord
    cases hmi : m i0 with
    | ofNat k =>
        simp [hmi] at hnat
        omega
    | negSucc k =>
        simp [hmi] at hnat
  · intro hm
    have hone : affineGammaFintypeProductMero scale offset m hscale = 1 := by
      rw [affineGammaFintypeProductMero]
      simp [hm]
    rw [hone]
    exact isExponentialRationalMero_one

/-! ## Canonical residual product and global normal form -/

/-- Canonical residual Gamma sectors: one representative for every refined shift orbit in every
rational-commensurability class. -/
abbrev CanonicalPositiveGammaResidualIndex {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) :=
  Σ c : PositiveGammaScaleClass f,
    GammaShiftOrbit
      (gammaNatScaleRefinedSlotShift
        (positiveGammaScaleClassNaturalScale f c)
        (positiveGammaScaleClassOffset f c))

/-- Positive scale of one canonical residual sector. -/
def canonicalPositiveGammaResidualScale {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor)
    (u : CanonicalPositiveGammaResidualIndex f) : ℝ :=
  canonicalPositiveGammaCommonUnit f u.1

/-- Shift representative of one canonical residual sector. -/
def canonicalPositiveGammaResidualOffset {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor)
    (u : CanonicalPositiveGammaResidualIndex f) : ℂ :=
  gammaNatScaleRefinedSlotShift
    (positiveGammaScaleClassNaturalScale f u.1)
    (positiveGammaScaleClassOffset f u.1) u.2.out

/-- Signed charge of one canonical residual sector. -/
def canonicalPositiveGammaResidualMultiplicity {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor)
    (u : CanonicalPositiveGammaResidualIndex f) : ℤ :=
  gammaShiftOrbitCharge
    (gammaNatScaleRefinedSlotShift
      (positiveGammaScaleClassNaturalScale f u.1)
      (positiveGammaScaleClassOffset f u.1))
    (gammaNatScaleRefinedSlotCharge
      (positiveGammaScaleClassMultiplicity f u.1)) u.2

theorem canonicalPositiveGammaResidualScale_pos {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) :
    ∀ u : CanonicalPositiveGammaResidualIndex f,
      0 < canonicalPositiveGammaResidualScale f u :=
  fun u => canonicalPositiveGammaCommonUnit_pos f u.1

/-- Residual block in one commensurability class after Gauss multiplication and recurrence. -/
def canonicalPositiveGammaClassResidualMero {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor)
    (c : PositiveGammaScaleClass f) : meroField Set.univ :=
  complexScaleMeroEquiv (canonicalPositiveGammaCommonUnit f c : ℂ)
    (by exact_mod_cast (canonicalPositiveGammaCommonUnit_pos f c).ne')
    (gammaShiftOrbitReducedProductMero
      (gammaNatScaleRefinedSlotShift
        (positiveGammaScaleClassNaturalScale f c)
        (positiveGammaScaleClassOffset f c))
      (gammaNatScaleRefinedSlotCharge
        (positiveGammaScaleClassMultiplicity f c)))

/-- Exponential--rational gauge removed from one commensurability class. -/
def canonicalPositiveGammaClassGaugeMero {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor)
    (c : PositiveGammaScaleClass f) : meroField Set.univ :=
  complexScaleMeroEquiv (canonicalPositiveGammaCommonUnit f c : ℂ)
    (by exact_mod_cast (canonicalPositiveGammaCommonUnit_pos f c).ne')
    (gammaNatScaleFamilyGaugeMero
        (positiveGammaScaleClassNaturalScale f c)
        (positiveGammaScaleClassOffset f c)
        (positiveGammaScaleClassMultiplicity f c) *
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ
        (gammaShiftOrbitGaugeRat
          (gammaNatScaleRefinedSlotShift
            (positiveGammaScaleClassNaturalScale f c)
            (positiveGammaScaleClassOffset f c))
          (gammaNatScaleRefinedSlotCharge
            (positiveGammaScaleClassMultiplicity f c))))

theorem isExponentialRationalMero_canonicalPositiveGammaClassGaugeMero
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor)
    (c : PositiveGammaScaleClass f) :
    IsExponentialRationalMero (canonicalPositiveGammaClassGaugeMero f c) := by
  apply IsExponentialRationalMero.complexScale
  · exact (isExponentialRationalMero_gammaNatScaleFamilyGaugeMero
      (positiveGammaScaleClassNaturalScale f c)
      (positiveGammaScaleClassOffset f c)
      (positiveGammaScaleClassMultiplicity f c)
      (positiveGammaScaleClassNaturalScale_pos f c)).mul
        (isExponentialRationalMero_ratfunc _
          (gammaShiftOrbitGaugeRat_ne_zero _ _))

/-- Exact classwise Gauss/recurrence normal form. -/
theorem positiveGammaFamilyMero_classFactor_normalForm
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor)
    (c : PositiveGammaScaleClass f) :
    positiveGammaFamilyMero (positiveGammaScaleClassFactor f c) =
      canonicalPositiveGammaClassGaugeMero f c *
        canonicalPositiveGammaClassResidualMero f c := by
  rw [positiveGammaFamilyMero_classFactor_eq_commonUnitScale,
    commonUnitScaleGammaFamilyMero_eq_complexScale,
    gammaNatScaleFamilyMero_normalForm
      (positiveGammaScaleClassNaturalScale f c)
      (positiveGammaScaleClassOffset f c)
      (positiveGammaScaleClassMultiplicity f c)
      (positiveGammaScaleClassNaturalScale_pos f c),
    gammaNatScaleFamilyRefinedMero_eq_slotProduct,
    gammaFintypeOrbitProductMero_automatic_normalForm,
    map_mul, map_mul]
  rw [canonicalPositiveGammaClassGaugeMero,
    canonicalPositiveGammaClassResidualMero, map_mul]
  ring

/-- Product of all canonical exponential--rational class gauges. -/
def canonicalPositiveGammaGaugeMero {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) : meroField Set.univ :=
  ∏ c, canonicalPositiveGammaClassGaugeMero f c

/-- Product of all canonical residual Gamma sectors, grouped by scale class. -/
def canonicalPositiveGammaResidualMero {d : ℕ}
    (f : Fin d → PositiveAffineGammaFactor) : meroField Set.univ :=
  ∏ c, canonicalPositiveGammaClassResidualMero f c

theorem isExponentialRationalMero_canonicalPositiveGammaGaugeMero
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor) :
    IsExponentialRationalMero (canonicalPositiveGammaGaugeMero f) := by
  rw [canonicalPositiveGammaGaugeMero]
  exact isExponentialRationalMero_finset_prod Finset.univ _
    (fun c hc => isExponentialRationalMero_canonicalPositiveGammaClassGaugeMero f c)

theorem IsExponentialRationalMero.ne_zero {x : meroField Set.univ}
    (hx : IsExponentialRationalMero x) : x ≠ 0 := by
  obtain ⟨r, hr, beta, rfl⟩ := hx
  exact mul_ne_zero
    ((map_ne_zero_iff _ (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ).injective).mpr hr)
    (physicalExponentialMero_ne_zero beta)

/-- Exact global decomposition into one exponential--rational gauge and the canonical residual
Gamma product. -/
theorem positiveGammaFamilyMero_global_normalForm
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor) :
    positiveGammaFamilyMero f = canonicalPositiveGammaGaugeMero f *
      canonicalPositiveGammaResidualMero f := by
  rw [← prod_positiveGammaFamilyMero_classFactor_eq f]
  simp_rw [positiveGammaFamilyMero_classFactor_normalForm]
  exact Finset.prod_mul_distrib

/-- Ungrouping the classwise residual product gives the single finite affine family indexed by
canonical residual sectors. -/
theorem canonicalPositiveGammaResidualMero_eq_affineGammaFintypeProductMero
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor) :
    canonicalPositiveGammaResidualMero f =
      affineGammaFintypeProductMero
        (canonicalPositiveGammaResidualScale f)
        (canonicalPositiveGammaResidualOffset f)
        (canonicalPositiveGammaResidualMultiplicity f)
        (canonicalPositiveGammaResidualScale_pos f) := by
  classical
  rw [canonicalPositiveGammaResidualMero,
    affineGammaFintypeProductMero, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro c hc
  rw [canonicalPositiveGammaClassResidualMero,
    gammaShiftOrbitReducedProductMero, map_prod]
  apply Finset.prod_congr rfl
  intro q hq
  rw [map_zpow₀, gammaShiftMero_eq_gammaScaleShiftMero_one,
    complexScaleMeroEquiv_gammaScaleShiftMero]
  change gammaScaleShiftMero
      ((1 : ℂ) * (canonicalPositiveGammaCommonUnit f c : ℂ)) _
        (gammaNatScaleRefinedSlotShift
          (positiveGammaScaleClassNaturalScale f c)
          (positiveGammaScaleClassOffset f c) q.out) ^
          gammaShiftOrbitCharge
            (gammaNatScaleRefinedSlotShift
              (positiveGammaScaleClassNaturalScale f c)
              (positiveGammaScaleClassOffset f c))
            (gammaNatScaleRefinedSlotCharge
              (positiveGammaScaleClassMultiplicity f c)) q =
    gammaScaleShiftMero (canonicalPositiveGammaCommonUnit f c : ℂ) _
        (gammaNatScaleRefinedSlotShift
          (positiveGammaScaleClassNaturalScale f c)
          (positiveGammaScaleClassOffset f c) q.out) ^
          gammaShiftOrbitCharge
            (gammaNatScaleRefinedSlotShift
              (positiveGammaScaleClassNaturalScale f c)
              (positiveGammaScaleClassOffset f c))
            (gammaNatScaleRefinedSlotCharge
              (positiveGammaScaleClassMultiplicity f c)) q
  congr 2
  ring

/-- Commensurability of two canonical class units would identify the original quotient classes. -/
theorem eq_of_canonicalPositiveGammaCommonUnit_commensurate
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor)
    {c e : PositiveGammaScaleClass f}
    (hunit : PositiveGammaScaleCommensurate
      (canonicalPositiveGammaCommonUnit f c)
      (canonicalPositiveGammaCommonUnit f e)) :
    c = e := by
  obtain ⟨q, hq, hqeq⟩ := hunit
  let nc := canonicalPositiveGammaNaturalScale f c.out
  let ne := canonicalPositiveGammaNaturalScale f e.out
  have hnc : 0 < nc := canonicalPositiveGammaNaturalScale_pos f c.out
  have hne : 0 < ne := canonicalPositiveGammaNaturalScale_pos f e.out
  have hc := positiveGammaScale_eq_canonicalCommonUnit_mul_naturalScale f c.out
  have he := positiveGammaScale_eq_canonicalCommonUnit_mul_naturalScale f e.out
  have hc' : (f c.out).scale =
      canonicalPositiveGammaCommonUnit f c * nc := by
    simpa only [Quotient.out_eq] using hc
  have he' : (f e.out).scale =
      canonicalPositiveGammaCommonUnit f e * ne := by
    simpa only [Quotient.out_eq] using he
  let r : ℚ := q * (nc : ℚ) / (ne : ℚ)
  have hr : 0 < r := div_pos (mul_pos hq (by exact_mod_cast hnc))
    (by exact_mod_cast hne)
  have hscale : PositiveGammaScaleCommensurate
      (f c.out).scale (f e.out).scale := by
    refine ⟨r, hr, ?_⟩
    rw [hc', he', hqeq]
    have hneR : (ne : ℝ) ≠ 0 := by exact_mod_cast hne.ne'
    dsimp only [r]
    push_cast
    field_simp [hneR]
  have hquot : (Quotient.mk'' c.out : PositiveGammaScaleClass f) =
      Quotient.mk'' e.out := Quotient.sound hscale
  simpa only [Quotient.out_eq] using hquot

/-- Two distinct common affine-pole collisions force positive rational commensurability of the
two real scales. -/
theorem positiveGammaScaleCommensurate_of_two_affinePoleEqualities
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (b c : ℂ)
    {n₁ n₂ k₁ k₂ : ℕ} (hn : n₁ ≠ n₂)
    (h₁ : -((b + n₁) / (x : ℂ)) = -((c + k₁) / (y : ℂ)))
    (h₂ : -((b + n₂) / (x : ℂ)) = -((c + k₂) / (y : ℂ))) :
    PositiveGammaScaleCommensurate x y := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  field_simp [hxC, hyC] at h₁ h₂
  have hdiffC : (y : ℂ) * ((n₁ : ℂ) - (n₂ : ℂ)) =
      (x : ℂ) * ((k₁ : ℂ) - (k₂ : ℂ)) := by
    linear_combination -h₁ + h₂
  have hdiffR : y * ((n₁ : ℝ) - (n₂ : ℝ)) =
      x * ((k₁ : ℝ) - (k₂ : ℝ)) := by
    exact_mod_cast hdiffC
  have hk : (k₁ : ℤ) - (k₂ : ℤ) ≠ 0 := by
    intro hk0
    have hkEq : k₁ = k₂ := by omega
    rw [hkEq, sub_self, mul_zero] at hdiffR
    have hnEqR : (n₁ : ℝ) = (n₂ : ℝ) := by nlinarith
    exact hn (by exact_mod_cast hnEqR)
  let q : ℚ := (((n₁ : ℤ) - (n₂ : ℤ) : ℤ) : ℚ) /
    (((k₁ : ℤ) - (k₂ : ℤ) : ℤ) : ℚ)
  have hkR : (k₁ : ℝ) - (k₂ : ℝ) ≠ 0 := by
    exact_mod_cast hk
  have hqcast : (q : ℝ) = x / y := by
    dsimp [q]
    push_cast
    field_simp [hkR, hy.ne']
    nlinarith [hdiffR]
  have hqpos : 0 < q := by
    exact_mod_cast (show (0 : ℝ) < (q : ℝ) by rw [hqcast]; exact div_pos hx hy)
  refine ⟨q, hqpos, ?_⟩
  rw [hqcast]
  field_simp [hy.ne']

/-- Distinct sectors of the canonical residual family have only finitely many common poles. -/
theorem finite_canonicalPositiveGammaResidualCollisionSet
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor)
    (u v : CanonicalPositiveGammaResidualIndex f) (huv : u ≠ v) :
    (affineGammaPoleCollisionSet
      (canonicalPositiveGammaResidualScale f)
      (canonicalPositiveGammaResidualOffset f) u v).Finite := by
  classical
  rcases u with ⟨c, q⟩
  rcases v with ⟨e, r⟩
  by_cases hce : c = e
  · subst e
    have hqr : q ≠ r := by
      intro h
      apply huv
      cases h
      rfl
    apply Set.finite_empty.subset
    intro n hn
    obtain ⟨k, hcol⟩ := hn
    exfalso
    apply hqr
    have hrel : gammaShiftOrbitRel
        (gammaNatScaleRefinedSlotShift
          (positiveGammaScaleClassNaturalScale f c)
          (positiveGammaScaleClassOffset f c)) q.out r.out := by
      refine ⟨(k : ℤ) - (n : ℤ), ?_⟩
      have hscaleC : (canonicalPositiveGammaCommonUnit f c : ℂ) ≠ 0 := by
        exact_mod_cast (canonicalPositiveGammaCommonUnit_pos f c).ne'
      have hcol' := congrArg
        (fun z : ℂ => -z * (canonicalPositiveGammaCommonUnit f c : ℂ)) hcol
      simp only [affineGammaPolePoint,
        canonicalPositiveGammaResidualScale,
        canonicalPositiveGammaResidualOffset] at hcol'
      field_simp [hscaleC] at hcol'
      push_cast
      linear_combination hcol'
    have hout : (Quotient.mk'' q.out : GammaShiftOrbit
        (gammaNatScaleRefinedSlotShift
          (positiveGammaScaleClassNaturalScale f c)
          (positiveGammaScaleClassOffset f c))) = Quotient.mk'' r.out :=
      Quotient.sound hrel
    exact (Quotient.out_eq q).symm.trans (hout.trans (Quotient.out_eq r))
  · apply Set.Subsingleton.finite
    intro n₁ hn₁ n₂ hn₂
    by_contra hn
    obtain ⟨k₁, h₁⟩ := hn₁
    obtain ⟨k₂, h₂⟩ := hn₂
    have hcomm := positiveGammaScaleCommensurate_of_two_affinePoleEqualities
      (canonicalPositiveGammaCommonUnit_pos f c)
      (canonicalPositiveGammaCommonUnit_pos f e)
      (canonicalPositiveGammaResidualOffset f ⟨c, q⟩)
      (canonicalPositiveGammaResidualOffset f ⟨e, r⟩)
      hn h₁ h₂
    exact hce (eq_of_canonicalPositiveGammaCommonUnit_commensurate f hcomm)

/-- The canonical residual product is exponential--rational exactly when every residual divisor
multiplicity vanishes. -/
theorem isExponentialRationalMero_canonicalPositiveGammaResidualMero_iff
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor) :
    IsExponentialRationalMero (canonicalPositiveGammaResidualMero f) ↔
      ∀ u : CanonicalPositiveGammaResidualIndex f,
        canonicalPositiveGammaResidualMultiplicity f u = 0 := by
  rw [canonicalPositiveGammaResidualMero_eq_affineGammaFintypeProductMero]
  exact isExponentialRationalMero_affineGammaFintypeProductMero_iff
    (canonicalPositiveGammaResidualScale f)
    (canonicalPositiveGammaResidualOffset f)
    (canonicalPositiveGammaResidualMultiplicity f)
    (canonicalPositiveGammaResidualScale_pos f)
    (finite_canonicalPositiveGammaResidualCollisionSet f)

/-- Residual multiplicities are definitionally the canonical natural-scale orbit charges. -/
theorem canonicalPositiveGammaResidualMultiplicity_zero_iff_canonicalOrbitCharges
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor) :
    (∀ u : CanonicalPositiveGammaResidualIndex f,
        canonicalPositiveGammaResidualMultiplicity f u = 0) ↔
      ∀ c : PositiveGammaScaleClass f,
        ∀ q : NaturalScaleGammaOrbit
          (positiveGammaScaleClassNaturalScale f c)
          (positiveGammaScaleClassOffset f c),
        naturalScaleGammaOrbitCharge
          (positiveGammaScaleClassNaturalScale f c)
          (positiveGammaScaleClassOffset f c)
          (positiveGammaScaleClassMultiplicity f c) q = 0 := by
  constructor
  · intro h c q
    exact h ⟨c, q⟩
  · intro h u
    exact h u.1 u.2

/-- Literal exponential--rationality forces vanishing of the actual scaled alien character. -/
theorem scaledGammaAlienChargeZero_of_isExponentialRationalMero_positiveGammaFamilyMero
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor)
    (h : IsExponentialRationalMero (positiveGammaFamilyMero f)) :
    ScaledGammaAlienChargeZero f := by
  have hgauge := isExponentialRationalMero_canonicalPositiveGammaGaugeMero f
  have hgauge0 := hgauge.ne_zero
  have hnormal := positiveGammaFamilyMero_global_normalForm f
  have hresEq : canonicalPositiveGammaResidualMero f =
      (canonicalPositiveGammaGaugeMero f)⁻¹ * positiveGammaFamilyMero f := by
    rw [hnormal]
    field_simp [hgauge0]
  have hres : IsExponentialRationalMero
      (canonicalPositiveGammaResidualMero f) := by
    rw [hresEq]
    exact hgauge.inv.mul h
  have hm :=
    (isExponentialRationalMero_canonicalPositiveGammaResidualMero_iff f).mp hres
  have hcharges :=
    (canonicalPositiveGammaResidualMultiplicity_zero_iff_canonicalOrbitCharges f).mp hm
  exact (scaledGammaAlienChargeZero_iff_canonicalOrbitCharges f).mpr hcharges

/-- **Exact scaled-Gamma classification.**  For every finite signed product of positive-scale
affine Gamma factors, the full scaled Borel-residue character vanishes exactly when the genuine
meromorphic product is a nonzero rational function times one exponential. -/
theorem scaledGammaAlienChargeZero_iff_exponentialRationalMero
    {d : ℕ} (f : Fin d → PositiveAffineGammaFactor) :
    ScaledGammaAlienChargeZero f ↔
      IsExponentialRationalMero (positiveGammaFamilyMero f) := by
  exact ⟨isExponentialRationalMero_positiveGammaFamilyMero_of_alienChargeZero f,
    scaledGammaAlienChargeZero_of_isExponentialRationalMero_positiveGammaFamilyMero f⟩

/-- Closed Borel-residue, canonical-charge, and literal exponential--rational capstone for
arbitrary finite positive-scale Gamma packets. -/
theorem scaledGammaBorelResidueCharacter_exponentialRational_capstone :
    ∀ {d : ℕ} (f : Fin d → PositiveAffineGammaFactor),
      (∀ t : ℝ, t ≠ 0 →
        Tendsto
          (fun ξ : ℂ =>
            (ξ - 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) *
              scaledGammaBorelPolarPart f ξ)
          (nhdsWithin (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
            ({2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)}ᶜ))
          (nhds ((2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) *
            scaledGammaAlienChargeAt f t))) ∧
      (ScaledGammaAlienChargeZero f ↔
        IsExponentialRationalMero (positiveGammaFamilyMero f)) ∧
      (IsExponentialRationalMero (positiveGammaFamilyMero f) ↔
        ∀ c : PositiveGammaScaleClass f,
          ∀ q : NaturalScaleGammaOrbit
            (positiveGammaScaleClassNaturalScale f c)
            (positiveGammaScaleClassOffset f c),
          naturalScaleGammaOrbitCharge
            (positiveGammaScaleClassNaturalScale f c)
            (positiveGammaScaleClassOffset f c)
            (positiveGammaScaleClassMultiplicity f c) q = 0) := by
  intro d f
  refine ⟨fun t ht => scaledGammaBorelPolarPart_residue f t ht,
    scaledGammaAlienChargeZero_iff_exponentialRationalMero f, ?_⟩
  rw [← scaledGammaAlienChargeZero_iff_exponentialRationalMero f]
  exact scaledGammaAlienChargeZero_iff_canonicalOrbitCharges f

end
end GaloisForLFunctions.HTGeometry
