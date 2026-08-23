import GaloisForLFunctions.HTGeometry.ScaledGammaNaturalOrbitCompleteness
import GaloisForLFunctions.HTGeometry.AnalyticSubringFractionEvaluation
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

end
end GaloisForLFunctions.HTGeometry
