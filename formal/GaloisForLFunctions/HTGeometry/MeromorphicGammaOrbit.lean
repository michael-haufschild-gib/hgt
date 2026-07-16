import GaloisForLFunctions.HTGeometry.MeromorphicRatFuncTranslation
import GaloisForLFunctions.HTGeometry.MeromorphicFractionJets
import GaloisForLFunctions.HTGeometry.ReciprocalGammaPoleBranchTaylor
import GaloisForLFunctions.HTGeometry.GammaOrbitRationalIncrement
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary

/-!
# Shifted Gamma functions in the global meromorphic differential field

The entire reciprocal Gamma function gives a literal nonzero fraction-field element for every
translate of Gamma.  Its recurrence yields the Gamma shift law in the global meromorphic field,
and logarithmic differentiation yields the digamma rational increment.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance meromorphicGammaOrbitDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meromorphicGammaOrbitIntAlgebraAnalytic :
    Algebra ℤ (analyticSubring Set.univ) := Ring.toIntAlgebra _

local instance meromorphicGammaOrbitIntAlgebraMero :
    Algebra ℤ (meroField Set.univ) := Ring.toIntAlgebra _

local instance meromorphicGammaOrbitIntAlgebraRatFunc :
    Algebra ℤ (RatFunc ℂ) := Ring.toIntAlgebra _

local instance meromorphicGammaOrbitDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- The reciprocal of `Γ(z+b)` as an entire analytic germ. -/
def reciprocalGammaShiftAnalytic (b : ℂ) : analyticSubring Set.univ :=
  univAnalytic (fun z => reciprocalGammaEntire (z + b)) (by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact (contDiff_reciprocalGammaEntire.differentiable (by simp)).comp
      (differentiable_id.add (differentiable_const b)))

/-- The translated reciprocal-Gamma germ is nonzero. -/
theorem reciprocalGammaShiftAnalytic_ne_zero (b : ℂ) :
    reciprocalGammaShiftAnalytic b ≠ 0 := by
  intro hzero
  have hv := congrArg Subtype.val hzero
  simp only [reciprocalGammaShiftAnalytic, univAnalytic,
    ZeroMemClass.coe_zero] at hv
  change Germ.ofFun (l := 𝓟 Set.univ)
      (fun z => reciprocalGammaEntire (z + b)) =
    Germ.ofFun (l := 𝓟 Set.univ) (fun _ : ℂ => 0) at hv
  rw [Germ.coe_eq] at hv
  have hvalue := eventually_principal.mp hv (1 - b) (Set.mem_univ _)
  simp [reciprocalGammaEntire] at hvalue

/-- The entire reciprocal-Gamma recurrence as an identity of analytic germs. -/
theorem addTranslationAnalyticEquiv_reciprocalGammaShift_mul_coordinate (b : ℂ) :
    addTranslationAnalyticEquiv 1 (reciprocalGammaShiftAnalytic b) *
        polyToAnalytic Set.univ (Polynomial.X + Polynomial.C b) =
      reciprocalGammaShiftAnalytic b := by
  apply Subtype.ext
  change
    (addTranslationAnalyticEquiv 1 (reciprocalGammaShiftAnalytic b)).1 *
      (polyToAnalytic Set.univ (Polynomial.X + Polynomial.C b)).1 =
    (reciprocalGammaShiftAnalytic b).1
  rw [show (addTranslationAnalyticEquiv 1
      (reciprocalGammaShiftAnalytic b)).1 =
        (reciprocalGammaShiftAnalytic b).1.compTendsto (addTranslation 1)
            (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)) from rfl]
  rw [show (reciprocalGammaShiftAnalytic b).1 =
      Germ.ofFun (l := 𝓟 Set.univ) (fun z => reciprocalGammaEntire (z + b)) from rfl,
    show (polyToAnalytic Set.univ (Polynomial.X + Polynomial.C b)).1 =
      Germ.ofFun (l := 𝓟 Set.univ)
        (fun z => (Polynomial.X + Polynomial.C b).eval z) from rfl,
    Germ.coe_compTendsto]
  rw [← Germ.coe_mul]
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by
    have h := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + b)
    change reciprocalGammaEntire (z + b) =
      (z + b) * reciprocalGammaEntire (z + b + 1) at h
    simp only [Pi.mul_apply, Function.comp_apply, addTranslation,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rw [show z + 1 + b = z + b + 1 by ring, h, mul_comm]

/-- The genuine meromorphic element represented by `Γ(z+b)`. -/
def gammaShiftMero (b : ℂ) : meroField Set.univ :=
  (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    (reciprocalGammaShiftAnalytic b))⁻¹

theorem gammaShiftMero_ne_zero (b : ℂ) : gammaShiftMero b ≠ 0 := by
  apply inv_ne_zero
  intro hzero
  exact reciprocalGammaShiftAnalytic_ne_zero b
    ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
      (by simpa using hzero))

/-- The meromorphic Gamma recurrence `T Γ_b = (X+b) Γ_b`. -/
theorem addTranslationMeroEquiv_gammaShiftMero (b : ℂ) :
    addTranslationMeroEquiv 1 (gammaShiftMero b) =
      ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ (RatFunc.X + RatFunc.C b) *
        gammaShiftMero b := by
  let a := algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    (reciprocalGammaShiftAnalytic b)
  let ta := algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    (addTranslationAnalyticEquiv 1 (reciprocalGammaShiftAnalytic b))
  let u := ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ (RatFunc.X + RatFunc.C b)
  have hu : u ≠ 0 := by
    change ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ (RatFunc.X + RatFunc.C b) ≠ 0
    apply (map_ne_zero_iff _ (ratfuncToMero Set.univ isOpen_univ
      isPreconnected_univ Set.univ_nonempty Set.infinite_univ).injective).mpr
    rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_add]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero b)
  have hrec : ta * u = a := by
    have h := congrArg
      (algebraMap (analyticSubring Set.univ) (meroField Set.univ))
      (addTranslationAnalyticEquiv_reciprocalGammaShift_mul_coordinate b)
    simp only [map_mul] at h
    have huPoly : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (polyToAnalytic Set.univ (Polynomial.X + Polynomial.C b)) = u := by
      change polyToMero Set.univ (Polynomial.X + Polynomial.C b) =
        ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ (RatFunc.X + RatFunc.C b)
      rw [show RatFunc.X + RatFunc.C b =
          algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.X + Polynomial.C b) by
        simp [RatFunc.algebraMap_X, RatFunc.algebraMap_C]]
      exact (ratfuncToMero_algebraMap_polynomial Set.univ isOpen_univ
        isPreconnected_univ Set.univ_nonempty Set.infinite_univ _).symm
    change ta * algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (polyToAnalytic Set.univ (Polynomial.X + Polynomial.C b)) = a at h
    rw [huPoly] at h
    exact h
  rw [gammaShiftMero, map_inv₀, addTranslationMeroEquiv_algebraMap]
  change ta⁻¹ = u * a⁻¹
  rw [← hrec, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]

/-- The meromorphic logarithmic derivative of `Γ(z+b)`. -/
def digammaShiftMero (b : ℂ) : meroField Set.univ :=
  Differential.logDeriv (gammaShiftMero b)

/-- The logarithmic derivative satisfies the exact digamma shift law in the field. -/
theorem addTranslationMeroEquiv_digammaShiftMero (b : ℂ) :
    addTranslationMeroEquiv 1 (digammaShiftMero b) =
      digammaShiftMero b +
        ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ
          (1 / (RatFunc.X + RatFunc.C b)) := by
  let g := gammaShiftMero b
  let u := ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ (RatFunc.X + RatFunc.C b)
  have hg : g ≠ 0 := gammaShiftMero_ne_zero b
  have huRat : RatFunc.X + RatFunc.C b ≠ 0 := by
    rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_add]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero b)
  have hu : u ≠ 0 :=
    by
      change ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ (RatFunc.X + RatFunc.C b) ≠ 0
      exact (map_ne_zero_iff _ (ratfuncToMero Set.univ isOpen_univ
        isPreconnected_univ Set.univ_nonempty Set.infinite_univ).injective).mpr huRat
  have hdu : u′ = 1 := by
    change (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ (RatFunc.X + RatFunc.C b))′ = 1
    rw [meroField_deriv_ratfuncToMero]
    rw [show RatFunc.X + RatFunc.C b =
        algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.X + Polynomial.C b) by
      simp [RatFunc.algebraMap_X, RatFunc.algebraMap_C]]
    rw [HTGeometry.ratFuncCoordinateDerivation_algebraMap]
    simp
  rw [digammaShiftMero, Differential.logDeriv, map_div₀,
    addTranslationMeroEquiv_deriv, addTranslationMeroEquiv_gammaShiftMero]
  change (u * g)′ / (u * g) = g′ / g +
    ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ
      (1 / (RatFunc.X + RatFunc.C b))
  rw [Derivation.leibniz, hdu]
  simp only [smul_eq_mul, mul_one, map_div₀, map_one]
  change (u * g′ + g) / (u * g) = g′ / g + 1 / u
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  rw [add_mul]
  congr 1
  · calc
      u * g′ * (g⁻¹ * u⁻¹) = g′ * g⁻¹ * (u * u⁻¹) := by ring
      _ = g′ * g⁻¹ := by rw [mul_inv_cancel₀ hu, mul_one]
  · calc
      g * (g⁻¹ * u⁻¹) = (g * g⁻¹) * u⁻¹ := by ring
      _ = u⁻¹ := by rw [mul_inv_cancel₀ hg, one_mul]

/-- The rational coordinate derivative of `X+b` is one. -/
theorem ratFuncCoordinateDerivation_X_add_C (b : ℂ) :
    HTGeometry.ratFuncCoordinateDerivation ℂ (RatFunc.X + RatFunc.C b) = 1 := by
  rw [show RatFunc.X + RatFunc.C b =
      algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.X + Polynomial.C b) by
    simp [RatFunc.algebraMap_X, RatFunc.algebraMap_C]]
  rw [HTGeometry.ratFuncCoordinateDerivation_algebraMap]
  simp

/-- Successive rational Gamma-orbit increments are successive coordinate derivatives. -/
theorem ratFuncCoordinateDerivation_gammaOrbitIncrement
    {d : ℕ} (b M : Fin d → ℂ) (j : ℕ) :
    HTGeometry.ratFuncCoordinateDerivation ℂ (gammaOrbitIncrement b M j) =
      gammaOrbitIncrement b M (j + 1) := by
  classical
  rw [gammaOrbitIncrement, map_sum, gammaOrbitIncrement]
  refine Finset.sum_congr rfl fun c _ => ?_
  let u : RatFunc ℂ := RatFunc.X + RatFunc.C (b c)
  let A : ℂ := M c * ((-1 : ℂ) ^ j * (j.factorial : ℂ))
  have hu : u ≠ 0 := by
    dsimp [u]
    rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_add]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero (b c))
  have hDu : HTGeometry.ratFuncCoordinateDerivation ℂ u = 1 := by
    exact ratFuncCoordinateDerivation_X_add_C (b c)
  have hDA : HTGeometry.ratFuncCoordinateDerivation ℂ (RatFunc.C A) = 0 := by
    rw [← RatFunc.algebraMap_eq_C]
    exact (HTGeometry.ratFuncCoordinateDerivation ℂ).map_algebraMap A
  change HTGeometry.ratFuncCoordinateDerivation ℂ (RatFunc.C A / u ^ (j + 1)) =
    RatFunc.C
        (M c * ((-1 : ℂ) ^ (j + 1) * ((j + 1).factorial : ℂ))) /
      u ^ (j + 2)
  rw [Derivation.leibniz_div, hDA, Derivation.leibniz_pow, hDu]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_one]
  field_simp [hu]
  rw [Nat.factorial_succ, pow_succ]
  dsimp [A]
  rw [← RatFunc.algebraMap_eq_C]
  push_cast
  ring

/-- A finite linear combination of shifted digamma elements in the genuine meromorphic field. -/
def gammaOrbitDigammaMero {d : ℕ} (b M : Fin d → ℂ) : meroField Set.univ :=
  ∑ c : Fin d,
    ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ (RatFunc.C (M c)) *
      digammaShiftMero (b c)

/-- The complete finite-orbit digamma carrier has the expected rational unit-shift increment. -/
theorem addTranslationMeroEquiv_gammaOrbitDigammaMero
    {d : ℕ} (b M : Fin d → ℂ) :
    addTranslationMeroEquiv 1 (gammaOrbitDigammaMero b M) =
      gammaOrbitDigammaMero b M +
        ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ (gammaOrbitIncrement b M 0) := by
  classical
  rw [gammaOrbitDigammaMero, map_sum]
  simp_rw [map_mul, addTranslationMeroEquiv_ratfuncToMero]
  simp_rw [show ∀ c : Fin d, ratShift (RatFunc.C (M c)) = RatFunc.C (M c) by
    intro c
    rw [← RatFunc.algebraMap_eq_C]
    exact ratShift_const (M c)]
  simp_rw [addTranslationMeroEquiv_digammaShiftMero, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [gammaOrbitIncrement, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, zero_add, pow_one,
    map_div₀, map_one]
  rw [← RatFunc.algebraMap_eq_C]
  ring

/-- Every differential jet of the orbit carrier translates by the corresponding rational
increment. -/
theorem addTranslationMeroEquiv_gammaOrbitDigammaMero_jet
    {d : ℕ} (b M : Fin d → ℂ) (j : ℕ) :
    addTranslationMeroEquiv 1 (differentialJet j (gammaOrbitDigammaMero b M)) =
      differentialJet j (gammaOrbitDigammaMero b M) +
        ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
          Set.univ_nonempty Set.infinite_univ (gammaOrbitIncrement b M j) := by
  induction j with
  | zero =>
      simpa [differentialJet_zero] using
        addTranslationMeroEquiv_gammaOrbitDigammaMero b M
  | succ j ih =>
      rw [differentialJet_succ, addTranslationMeroEquiv_deriv, ih,
        (Differential.deriv : Derivation ℤ (meroField Set.univ)
          (meroField Set.univ)).map_add,
        meroField_deriv_ratfuncToMero,
        ratFuncCoordinateDerivation_gammaOrbitIncrement]

/-- **Analytic separated-orbit Gamma law.**  A finite shifted-digamma combination with one
nonzero charge on an orbit separated from all the others is hypertranscendental over `ℂ(X)` in
the genuine global meromorphic differential field. -/
theorem hypertranscendentalOver_gammaOrbitDigammaMero
    {d : ℕ} (b M : Fin d → ℂ) (c0 : Fin d) (hM : M c0 ≠ 0)
    (hsep : ∀ c, c ≠ c0 → ∀ n : ℤ, b c - b c0 ≠ (n : ℂ)) :
    letI : Algebra (RatFunc ℂ) (meroField Set.univ) :=
      (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ).toAlgebra
    HypertranscendentalOver (RatFunc ℂ) (gammaOrbitDigammaMero b M) := by
  letI : Algebra (RatFunc ℂ) (meroField Set.univ) :=
    (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ).toAlgebra
  apply hypertranscendentalOver_of_rationalShiftJets
    (addTranslationMeroEquiv 1) (fun r => addTranslationMeroEquiv_ratfuncToMero r)
    (gammaOrbitDigammaMero b M) (gammaOrbitIncrement b M)
  · intro j
    exact addTranslationMeroEquiv_gammaOrbitDigammaMero_jet b M j
  · intro m w delta h
    exact ratShift_sub_gammaOrbitIncrement_combination b M c0 hM hsep h

/-- Algebraic logarithmic differentiation of an integer power. -/
theorem differential_logDeriv_zpow
    {R : Type*} [Field R] [Differential R] (x : R) (hx : x ≠ 0) (n : ℤ) :
    Differential.logDeriv (x ^ n) = (n : R) * Differential.logDeriv x := by
  unfold Differential.logDeriv
  rw [Derivation.leibniz_zpow, zpow_sub_one₀ hx]
  simp only [zsmul_eq_mul, smul_eq_mul]
  have hxn : x ^ n ≠ 0 := zpow_ne_zero n hx
  field_simp [hx, hxn]

/-- The rational coordinate derivation, regarded as the integer-linear derivation carried by a
differential field. -/
@[reducible] def ratFuncCoordinateDifferential : Differential (RatFunc ℂ) where
  deriv := Derivation.restrictScalars ℤ
    (HTGeometry.ratFuncCoordinateDerivation ℂ)

@[simp]
theorem ratFuncCoordinateDifferential_apply (r : RatFunc ℂ) :
    letI := ratFuncCoordinateDifferential
    r′ = HTGeometry.ratFuncCoordinateDerivation ℂ r := rfl

/-- A genuine finite signed product of shifted Gamma elements. -/
def gammaOrbitProductMero {d : ℕ} (b : Fin d → ℂ) (m : Fin d → ℤ) :
    meroField Set.univ :=
  ∏ c : Fin d, gammaShiftMero (b c) ^ m c

theorem gammaOrbitProductMero_ne_zero
    {d : ℕ} (b : Fin d → ℂ) (m : Fin d → ℤ) :
    gammaOrbitProductMero b m ≠ 0 := by
  classical
  rw [gammaOrbitProductMero, Finset.prod_ne_zero_iff]
  intro c _
  exact zpow_ne_zero _ (gammaShiftMero_ne_zero (b c))

/-- The logarithmic derivative of the signed Gamma product is exactly its orbit-digamma
carrier, with the integer exponents embedded as complex charges. -/
theorem logDeriv_gammaOrbitProductMero
    {d : ℕ} (b : Fin d → ℂ) (m : Fin d → ℤ) :
    Differential.logDeriv (gammaOrbitProductMero b m) =
      gammaOrbitDigammaMero b (fun c => ((m c : ℤ) : ℂ)) := by
  classical
  rw [gammaOrbitProductMero, Differential.logDeriv_prod]
  · rw [gammaOrbitDigammaMero]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [differential_logDeriv_zpow _ (gammaShiftMero_ne_zero (b c))]
    have hm : ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ (RatFunc.C ((m c : ℤ) : ℂ)) =
        ((m c : ℤ) : meroField Set.univ) := by
      rw [show RatFunc.C ((m c : ℤ) : ℂ) =
          ((m c : ℤ) : RatFunc ℂ) by
        exact map_intCast RatFunc.C (m c)]
      exact map_intCast _ (m c)
    rw [hm]
    rfl
  · intro c _
    exact zpow_ne_zero _ (gammaShiftMero_ne_zero (b c))

/-- **Finite signed Gamma-product hypertranscendence.**  If one exponent is nonzero and its
translation orbit is separated from all other chosen representatives, then the genuine
meromorphic Gamma product is hypertranscendental over `ℂ(X)`. -/
theorem hypertranscendentalOver_gammaOrbitProductMero
    {d : ℕ} (b : Fin d → ℂ) (m : Fin d → ℤ) (c0 : Fin d) (hm : m c0 ≠ 0)
    (hsep : ∀ c, c ≠ c0 → ∀ n : ℤ, b c - b c0 ≠ (n : ℂ)) :
    letI : Algebra (RatFunc ℂ) (meroField Set.univ) :=
      (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
        Set.univ_nonempty Set.infinite_univ).toAlgebra
    HypertranscendentalOver (RatFunc ℂ) (gammaOrbitProductMero b m) := by
  letI : Algebra (RatFunc ℂ) (meroField Set.univ) :=
    (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ).toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
    { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }
  letI : CharZero (meroField Set.univ) :=
    charZero_of_injective_algebraMap
      (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective
  have hmC : ((m c0 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hm
  have hlog : HypertranscendentalOver (RatFunc ℂ)
      (Differential.logDeriv (gammaOrbitProductMero b m)) := by
    rw [logDeriv_gammaOrbitProductMero]
    exact hypertranscendentalOver_gammaOrbitDigammaMero
      b (fun c => ((m c : ℤ) : ℂ)) c0 hmC hsep
  exact (hypertranscendentalOver_deriv_div_self_iff
    (gammaOrbitProductMero b m)).mp hlog

end

end GaloisForLFunctions
