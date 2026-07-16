import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit
import GaloisForLFunctions.HTGeometry.OrbitChargeSuperselection

/-!
# Analytic Gamma superselection

The cellular orbit quotient is already computed by `OrbitChargeSuperselection`.  This file closes
its analytic Gamma interface.  Every finite common-scale presentation is reduced, inside the
global meromorphic differential field, to a rational gauge times one Gamma power on each occupied
translation orbit.  Consequently the product is differentially algebraic over `ℂ(X)` exactly
when every orbit charge vanishes, and every nonneutral sector is hypertranscendental.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance meromorphicGammaSuperselectionDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meromorphicGammaSuperselectionIntAlgebraAnalytic :
    Algebra ℤ (analyticSubring Set.univ) := Ring.toIntAlgebra _

local instance meromorphicGammaSuperselectionIntAlgebraMero :
    Algebra ℤ (meroField Set.univ) := Ring.toIntAlgebra _

local instance meromorphicGammaSuperselectionIntAlgebraRatFunc :
    Algebra ℤ (RatFunc ℂ) := Ring.toIntAlgebra _

local instance meromorphicGammaSuperselectionDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- Translation by one carries the analytic reciprocal-Gamma germ at `b` to the germ at
`b + 1`. -/
theorem addTranslationAnalyticEquiv_reciprocalGammaShift_eq_add_one (b : ℂ) :
    addTranslationAnalyticEquiv 1 (reciprocalGammaShiftAnalytic b) =
      reciprocalGammaShiftAnalytic (b + 1) := by
  apply Subtype.ext
  change (reciprocalGammaShiftAnalytic b).1.compTendsto (addTranslation 1)
      (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)) =
    (reciprocalGammaShiftAnalytic (b + 1)).1
  rw [show (reciprocalGammaShiftAnalytic b).1 =
      Germ.ofFun (l := 𝓟 Set.univ) (fun z => reciprocalGammaEntire (z + b)) from rfl,
    Germ.coe_compTendsto]
  rw [show (reciprocalGammaShiftAnalytic (b + 1)).1 =
      Germ.ofFun (l := 𝓟 Set.univ)
        (fun z => reciprocalGammaEntire (z + (b + 1))) from rfl]
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by
    simp only [Function.comp_apply, addTranslation]
    congr 1
    ring

/-- Translation of the genuine meromorphic Gamma element is the next parameter translate. -/
theorem addTranslationMeroEquiv_gammaShiftMero_eq_add_one (b : ℂ) :
    addTranslationMeroEquiv 1 (gammaShiftMero b) = gammaShiftMero (b + 1) := by
  rw [gammaShiftMero, gammaShiftMero, map_inv₀,
    addTranslationMeroEquiv_algebraMap,
    addTranslationAnalyticEquiv_reciprocalGammaShift_eq_add_one]

/-- The rational Pochhammer factor relating `Γ(z+b+n)` and `Γ(z+b)`. -/
def gammaOrbitNatFactor (b : ℂ) (n : ℕ) : RatFunc ℂ :=
  ∏ i ∈ Finset.range n, (RatFunc.X + RatFunc.C (b + (i : ℂ)))

theorem gammaOrbitNatFactor_ne_zero (b : ℂ) (n : ℕ) :
    gammaOrbitNatFactor b n ≠ 0 := by
  rw [gammaOrbitNatFactor, Finset.prod_ne_zero_iff]
  intro i _
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_add]
  exact RatFunc.algebraMap_ne_zero
    (Polynomial.X_add_C_ne_zero (b + (i : ℂ)))

/-- Exact meromorphic Pochhammer reduction for every natural translate. -/
theorem gammaShiftMero_add_nat (b : ℂ) (n : ℕ) :
    gammaShiftMero (b + (n : ℂ)) =
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ (gammaOrbitNatFactor b n) *
        gammaShiftMero b := by
  induction n with
  | zero => simp [gammaOrbitNatFactor]
  | succ n ih =>
      rw [show b + ((n + 1 : ℕ) : ℂ) = (b + (n : ℂ)) + 1 by
        push_cast
        ring]
      rw [← addTranslationMeroEquiv_gammaShiftMero_eq_add_one
        (b + (n : ℂ)), addTranslationMeroEquiv_gammaShiftMero]
      rw [ih]
      simp only [gammaOrbitNatFactor, Finset.prod_range_succ, map_mul]
      ring

/-- Total integer charge on a chosen common-scale translation orbit. -/
def gammaCommonScaleOrbitCharge {d e : ℕ}
    (m : Fin d → Fin e → ℤ) (c : Fin d) : ℤ :=
  ∑ j, m c j

/-- The rational gauge left after every factor is reduced to its chosen orbit representative. -/
def gammaCommonScaleGaugeRat {d e : ℕ} (b : Fin d → ℂ)
    (nn : Fin d → Fin e → ℕ) (m : Fin d → Fin e → ℤ) : RatFunc ℂ :=
  ∏ c, ∏ j, gammaOrbitNatFactor (b c) (nn c j) ^ m c j

/-- The genuine meromorphic product represented by a finite common-scale Gamma datum. -/
def gammaCommonScaleProductMero {d e : ℕ} (b : Fin d → ℂ)
    (nn : Fin d → Fin e → ℕ) (m : Fin d → Fin e → ℤ) :
    meroField Set.univ :=
  ∏ c, ∏ j, gammaShiftMero (b c + (nn c j : ℂ)) ^ m c j

theorem gammaCommonScaleGaugeRat_ne_zero {d e : ℕ} (b : Fin d → ℂ)
    (nn : Fin d → Fin e → ℕ) (m : Fin d → Fin e → ℤ) :
    gammaCommonScaleGaugeRat b nn m ≠ 0 := by
  rw [gammaCommonScaleGaugeRat, Finset.prod_ne_zero_iff]
  intro c _
  rw [Finset.prod_ne_zero_iff]
  intro j _
  exact zpow_ne_zero _ (gammaOrbitNatFactor_ne_zero (b c) (nn c j))

/-- **Analytic charge normal form.**  A finite common-scale Gamma product is a nonzero rational
gauge times one genuine Gamma power per chosen translation-orbit representative. -/
theorem gammaCommonScaleProductMero_normalForm {d e : ℕ} (b : Fin d → ℂ)
    (nn : Fin d → Fin e → ℕ) (m : Fin d → Fin e → ℤ) :
    gammaCommonScaleProductMero b nn m =
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ (gammaCommonScaleGaugeRat b nn m) *
        gammaOrbitProductMero b (gammaCommonScaleOrbitCharge m) := by
  rw [gammaCommonScaleProductMero, gammaCommonScaleGaugeRat,
    gammaOrbitProductMero]
  simp_rw [gammaShiftMero_add_nat, mul_zpow]
  simp_rw [Finset.prod_mul_distrib, map_prod, map_zpow₀]
  apply congrArg₂ (· * ·)
  · rfl
  · apply Finset.prod_congr rfl
    intro c _
    have hcollapse : ∀ s : Finset (Fin e),
        (∏ j ∈ s, gammaShiftMero (b c) ^ m c j) =
          gammaShiftMero (b c) ^ (∑ j ∈ s, m c j) := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | @insert j s hj ih =>
          rw [Finset.prod_insert hj, Finset.sum_insert hj]
          rw [ih, zpow_add₀ (gammaShiftMero_ne_zero (b c))]
    simpa [gammaCommonScaleOrbitCharge] using hcollapse Finset.univ

local instance meromorphicGammaSuperselectionRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance meromorphicGammaSuperselectionRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance meromorphicGammaSuperselectionDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance meromorphicGammaSuperselectionCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- Vanishing orbit charges give an explicit rational, hence differentially algebraic, product. -/
theorem differentialAlgebraicOver_gammaCommonScaleProductMero_of_charge_eq_zero
    {d e : ℕ} (b : Fin d → ℂ) (nn : Fin d → Fin e → ℕ)
    (m : Fin d → Fin e → ℤ)
    (hcharge : ∀ c, gammaCommonScaleOrbitCharge m c = 0) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaCommonScaleProductMero b nn m) := by
  rw [gammaCommonScaleProductMero_normalForm]
  have hnormal : gammaOrbitProductMero b (gammaCommonScaleOrbitCharge m) = 1 := by
    rw [gammaOrbitProductMero]
    apply Finset.prod_eq_one
    intro c _
    rw [hcharge c, zpow_zero]
  rw [hnormal, mul_one]
  exact HTGeometry.differentialAlgebraicOver_algebraMap
    (gammaCommonScaleGaugeRat b nn m)

/-- A nonzero charge on a translation orbit separated from all other chosen representatives forces
the whole finite product to be hypertranscendental over `ℂ(X)`. -/
theorem hypertranscendentalOver_gammaCommonScaleProductMero_of_charge_ne_zero
    {d e : ℕ} (b : Fin d → ℂ) (nn : Fin d → Fin e → ℕ)
    (m : Fin d → Fin e → ℤ) (c0 : Fin d)
    (hcharge : gammaCommonScaleOrbitCharge m c0 ≠ 0)
    (hsep : ∀ c, c ≠ c0 → ∀ n : ℤ, b c - b c0 ≠ (n : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaCommonScaleProductMero b nn m) := by
  have hnormal : HypertranscendentalOver (RatFunc ℂ)
      (gammaOrbitProductMero b (gammaCommonScaleOrbitCharge m)) :=
    hypertranscendentalOver_gammaOrbitProductMero b
      (gammaCommonScaleOrbitCharge m) c0 hcharge hsep
  unfold HypertranscendentalOver
  intro hproduct
  have hgaugeDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (algebraMap (RatFunc ℂ) (meroField Set.univ)
        (gammaCommonScaleGaugeRat b nn m)) :=
    HTGeometry.differentialAlgebraicOver_algebraMap
      (gammaCommonScaleGaugeRat b nn m)
  have hdiv := HTGeometry.differentialAlgebraicOver_div hproduct hgaugeDA
  have hgauge : algebraMap (RatFunc ℂ) (meroField Set.univ)
      (gammaCommonScaleGaugeRat b nn m) ≠ 0 :=
    (map_ne_zero_iff _
      (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective).mpr
        (gammaCommonScaleGaugeRat_ne_zero b nn m)
  have heq : gammaCommonScaleProductMero b nn m /
        algebraMap (RatFunc ℂ) (meroField Set.univ)
          (gammaCommonScaleGaugeRat b nn m) =
      gammaOrbitProductMero b (gammaCommonScaleOrbitCharge m) := by
    rw [gammaCommonScaleProductMero_normalForm]
    field_simp [hgauge]
    rw [mul_comm]
    congr 1
  rw [heq] at hdiv
  exact hnormal hdiv

/-- **Analytic Gamma superselection kernel.**  For pairwise separated translation-orbit
representatives, the differentially algebraic subgroup is exactly the zero-charge sector. -/
theorem differentialAlgebraicOver_gammaCommonScaleProductMero_iff_charge_eq_zero
    {d e : ℕ} (b : Fin d → ℂ) (nn : Fin d → Fin e → ℕ)
    (m : Fin d → Fin e → ℤ)
    (hsep : ∀ c c', c ≠ c' → ∀ n : ℤ, b c - b c' ≠ (n : ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (gammaCommonScaleProductMero b nn m) ↔
      ∀ c, gammaCommonScaleOrbitCharge m c = 0 := by
  constructor
  · intro hDA c
    by_contra hc
    exact (hypertranscendentalOver_gammaCommonScaleProductMero_of_charge_ne_zero
      b nn m c hc (fun c' hc' => hsep c' c hc')) hDA
  · exact differentialAlgebraicOver_gammaCommonScaleProductMero_of_charge_eq_zero
      b nn m

/-- The kernel theorem is invariant under every nonzero differentially algebraic meromorphic
gauge.  In particular this includes the constant, exponential, and rational gauges in the
common-scale Gamma superselection group. -/
theorem differentialAlgebraicOver_mul_gammaCommonScaleProductMero_iff_charge_eq_zero
    {d e : ℕ} (b : Fin d → ℂ) (nn : Fin d → Fin e → ℕ)
    (m : Fin d → Fin e → ℤ) (a : meroField Set.univ) (ha : a ≠ 0)
    (haDA : DifferentialAlgebraicOver (RatFunc ℂ) a)
    (hsep : ∀ c c', c ≠ c' → ∀ n : ℤ, b c - b c' ≠ (n : ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (a * gammaCommonScaleProductMero b nn m) ↔
      ∀ c, gammaCommonScaleOrbitCharge m c = 0 := by
  rw [← differentialAlgebraicOver_gammaCommonScaleProductMero_iff_charge_eq_zero
    b nn m hsep]
  constructor
  · intro hproduct
    have hdiv := HTGeometry.differentialAlgebraicOver_div hproduct haDA
    have heq : (a * gammaCommonScaleProductMero b nn m) / a =
        gammaCommonScaleProductMero b nn m := by
      field_simp [ha]
    rwa [heq] at hdiv
  · exact fun hproduct =>
      HTGeometry.differentialAlgebraicOver_mul haDA hproduct

/-- Every finite integer charge sector has a canonical one-factor-per-orbit presentation. -/
theorem gammaCommonScaleOrbitCharge_surjective {d : ℕ} :
    Function.Surjective
      (fun m : Fin d → Fin 1 → ℤ => gammaCommonScaleOrbitCharge m) := by
  intro q
  refine ⟨fun c _ => q c, ?_⟩
  funext c
  simp [gammaCommonScaleOrbitCharge]

/-- The analytic dichotomy in sector form: a finite separated-orbit product is
hypertranscendental exactly when some orbit charge is nonzero. -/
theorem hypertranscendentalOver_gammaCommonScaleProductMero_iff_exists_charge_ne_zero
    {d e : ℕ} (b : Fin d → ℂ) (nn : Fin d → Fin e → ℕ)
    (m : Fin d → Fin e → ℤ)
    (hsep : ∀ c c', c ≠ c' → ∀ n : ℤ, b c - b c' ≠ (n : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
        (gammaCommonScaleProductMero b nn m) ↔
      ∃ c, gammaCommonScaleOrbitCharge m c ≠ 0 := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_gammaCommonScaleProductMero_iff_charge_eq_zero
      b nn m hsep]
  simp only [not_forall]

/-- Every nonzero differentially algebraic gauge leaves the nonneutral sectors
hypertranscendental. -/
theorem hypertranscendentalOver_mul_gammaCommonScaleProductMero_iff_exists_charge_ne_zero
    {d e : ℕ} (b : Fin d → ℂ) (nn : Fin d → Fin e → ℕ)
    (m : Fin d → Fin e → ℤ) (a : meroField Set.univ) (ha : a ≠ 0)
    (haDA : DifferentialAlgebraicOver (RatFunc ℂ) a)
    (hsep : ∀ c c', c ≠ c' → ∀ n : ℤ, b c - b c' ≠ (n : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
        (a * gammaCommonScaleProductMero b nn m) ↔
      ∃ c, gammaCommonScaleOrbitCharge m c ≠ 0 := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_mul_gammaCommonScaleProductMero_iff_charge_eq_zero
      b nn m a ha haDA hsep]
  simp only [not_forall]

end

end GaloisForLFunctions
