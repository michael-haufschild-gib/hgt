import GaloisForLFunctions.HTGeometry.MeromorphicGammaSuperselection

/-!
# Euler reflection and oriented Gamma superselection

This file realizes negative-slope Gamma factors in the global meromorphic differential field.
Euler reflection turns each such factor into a nonzero differentially algebraic sine gauge times
the inverse positive-slope factor on the reflected translation orbit.  Finite oriented products
therefore have one surviving charge vector, exactly as computed abstractly in
`ReflectedOrbitCharge`.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance meromorphicGammaReflectionDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meromorphicGammaReflectionIntAlgebraAnalytic :
    Algebra ℤ (analyticSubring Set.univ) := Ring.toIntAlgebra _

local instance meromorphicGammaReflectionIntAlgebraMero :
    Algebra ℤ (meroField Set.univ) := Ring.toIntAlgebra _

local instance meromorphicGammaReflectionIntAlgebraRatFunc :
    Algebra ℤ (RatFunc ℂ) := Ring.toIntAlgebra _

local instance meromorphicGammaReflectionDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- The entire reciprocal of the negative-slope factor `Γ(-z+b)`. -/
def reciprocalGammaNegativeShiftAnalytic (b : ℂ) : analyticSubring Set.univ :=
  univAnalytic (fun z => reciprocalGammaEntire (-z + b)) (by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact contDiff_reciprocalGammaEntire.differentiable (by simp) |>.comp
      (by fun_prop))

/-- The entire sine quotient occurring in Euler reflection. -/
def gammaReflectionSineAnalytic (b : ℂ) : analyticSubring Set.univ :=
  univAnalytic
    (fun z => Complex.sin ((Real.pi : ℂ) * (-z + b)) / (Real.pi : ℂ))
    (by
      rw [Complex.analyticOnNhd_univ_iff_differentiable]
      fun_prop)

/-- Euler reflection in the entire reciprocal-Gamma form, valid also at integral arguments. -/
theorem reciprocalGammaEntire_mul_one_sub (u : ℂ) :
    reciprocalGammaEntire u * reciprocalGammaEntire (1 - u) =
      Complex.sin ((Real.pi : ℂ) * u) / (Real.pi : ℂ) := by
  have h := congrArg Inv.inv (Complex.Gamma_mul_Gamma_one_sub u)
  simpa [reciprocalGammaEntire, div_eq_mul_inv, mul_comm] using h

/-- Euler reflection as an identity of entire analytic germs. -/
theorem reciprocalGammaNegativeShift_mul_positive (b : ℂ) :
    reciprocalGammaNegativeShiftAnalytic b *
        reciprocalGammaShiftAnalytic (1 - b) =
      gammaReflectionSineAnalytic b := by
  apply Subtype.ext
  change (reciprocalGammaNegativeShiftAnalytic b).1 *
      (reciprocalGammaShiftAnalytic (1 - b)).1 =
    (gammaReflectionSineAnalytic b).1
  rw [show (reciprocalGammaNegativeShiftAnalytic b).1 =
      Germ.ofFun (l := 𝓟 Set.univ)
        (fun z => reciprocalGammaEntire (-z + b)) from rfl,
    show (reciprocalGammaShiftAnalytic (1 - b)).1 =
      Germ.ofFun (l := 𝓟 Set.univ)
        (fun z => reciprocalGammaEntire (z + (1 - b))) from rfl,
    show (gammaReflectionSineAnalytic b).1 =
      Germ.ofFun (l := 𝓟 Set.univ)
        (fun z => Complex.sin ((Real.pi : ℂ) * (-z + b)) /
          (Real.pi : ℂ)) from rfl,
    ← Germ.coe_mul, Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by
    change reciprocalGammaEntire (-z + b) *
      reciprocalGammaEntire (z + (1 - b)) =
        Complex.sin ((Real.pi : ℂ) * (-z + b)) / (Real.pi : ℂ)
    rw [show z + (1 - b) = 1 - (-z + b) by ring]
    exact reciprocalGammaEntire_mul_one_sub (-z + b)

/-- The genuine negative-slope meromorphic Gamma element `Γ(-z+b)`. -/
def gammaNegativeShiftMero (b : ℂ) : meroField Set.univ :=
  (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    (reciprocalGammaNegativeShiftAnalytic b))⁻¹

/-- The meromorphic sine quotient `sin(π(-z+b))/π`. -/
def gammaReflectionSineMero (b : ℂ) : meroField Set.univ :=
  algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    (gammaReflectionSineAnalytic b)

/-- The nonzero Euler-reflection gauge `π/sin(π(-z+b))`. -/
def gammaReflectionGaugeMero (b : ℂ) : meroField Set.univ :=
  (gammaReflectionSineMero b)⁻¹

/-- **Genuine meromorphic Euler reflection.**  A negative-slope Gamma factor is its sine gauge
times the inverse positive-slope factor on the reflected orbit. -/
theorem gammaNegativeShiftMero_reflection (b : ℂ) :
    gammaNegativeShiftMero b =
      gammaReflectionGaugeMero b * (gammaShiftMero (1 - b))⁻¹ := by
  have h := congrArg
    (algebraMap (analyticSubring Set.univ) (meroField Set.univ))
    (reciprocalGammaNegativeShift_mul_positive b)
  simp only [map_mul] at h
  rw [gammaNegativeShiftMero, gammaReflectionGaugeMero,
    gammaReflectionSineMero, gammaShiftMero, inv_inv]
  rw [← h, mul_inv_rev]
  have hp : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (reciprocalGammaShiftAnalytic (1 - b)) ≠ 0 := by
    intro hz
    exact reciprocalGammaShiftAnalytic_ne_zero (1 - b)
      ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
        (by simpa using hz))
  field_simp [hp]

/-- The cosine companion used to certify the sine gauge's differential equation. -/
def gammaReflectionCosineAnalytic (b : ℂ) : analyticSubring Set.univ :=
  univAnalytic (fun z => Complex.cos ((Real.pi : ℂ) * (-z + b))) (by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    fun_prop)

/-- The analytic constant `π²`. -/
def gammaReflectionPiSqAnalytic : analyticSubring Set.univ :=
  polyToAnalytic Set.univ (Polynomial.C ((Real.pi : ℂ) ^ 2))

theorem analyticSubringDeriv_gammaReflectionSineAnalytic (b : ℂ) :
    analyticSubringDeriv isOpen_univ (gammaReflectionSineAnalytic b) =
      -gammaReflectionCosineAnalytic b := by
  apply Subtype.ext
  change analyticGermDeriv isOpen_univ (gammaReflectionSineAnalytic b).1 =
    (-gammaReflectionCosineAnalytic b).1
  rw [show (gammaReflectionSineAnalytic b).1 =
      Germ.ofFun (l := 𝓟 Set.univ)
        (fun z => Complex.sin ((Real.pi : ℂ) * (-z + b)) /
          (Real.pi : ℂ)) from rfl,
    analyticGermDeriv_coe]
  change (deriv (fun z => Complex.sin ((Real.pi : ℂ) * (-z + b)) /
      (Real.pi : ℂ)) : Germ (𝓟 Set.univ) ℂ) =
    -(Germ.ofFun (l := 𝓟 Set.univ)
      (fun z => Complex.cos ((Real.pi : ℂ) * (-z + b))))
  rw [← Germ.coe_neg, Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by
    change deriv (fun z => Complex.sin ((Real.pi : ℂ) * (-z + b)) /
      (Real.pi : ℂ)) z =
        -Complex.cos ((Real.pi : ℂ) * (-z + b))
    have hu : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * (-z + b))
        (-(Real.pi : ℂ)) z := by
      convert ((hasDerivAt_id z).neg.add_const b).const_mul (Real.pi : ℂ) using 1
      all_goals ring
    rw [(hu.csin.div_const (Real.pi : ℂ)).deriv]
    field_simp [show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero]

theorem analyticSubringDeriv_gammaReflectionCosineAnalytic (b : ℂ) :
    analyticSubringDeriv isOpen_univ (gammaReflectionCosineAnalytic b) =
      gammaReflectionPiSqAnalytic * gammaReflectionSineAnalytic b := by
  apply Subtype.ext
  change analyticGermDeriv isOpen_univ (gammaReflectionCosineAnalytic b).1 =
    (gammaReflectionPiSqAnalytic * gammaReflectionSineAnalytic b).1
  rw [show (gammaReflectionCosineAnalytic b).1 =
      Germ.ofFun (l := 𝓟 Set.univ)
        (fun z => Complex.cos ((Real.pi : ℂ) * (-z + b))) from rfl,
    analyticGermDeriv_coe]
  change (deriv (fun z => Complex.cos ((Real.pi : ℂ) * (-z + b))) :
      Germ (𝓟 Set.univ) ℂ) =
    (gammaReflectionPiSqAnalytic).1 * (gammaReflectionSineAnalytic b).1
  rw [show (gammaReflectionSineAnalytic b).1 =
      Germ.ofFun (l := 𝓟 Set.univ)
        (fun z => Complex.sin ((Real.pi : ℂ) * (-z + b)) /
          (Real.pi : ℂ)) from rfl]
  rw [show (gammaReflectionPiSqAnalytic).1 =
      Germ.ofFun (l := 𝓟 Set.univ)
        (fun z => (Polynomial.C ((Real.pi : ℂ) ^ 2)).eval z) from rfl]
  rw [← Germ.coe_mul, Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by
    simp only [Polynomial.eval_C]
    change deriv (fun z => Complex.cos ((Real.pi : ℂ) * (-z + b))) z =
      (Real.pi : ℂ) ^ 2 *
        (Complex.sin ((Real.pi : ℂ) * (-z + b)) / (Real.pi : ℂ))
    have hu : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * (-z + b))
        (-(Real.pi : ℂ)) z := by
      convert ((hasDerivAt_id z).neg.add_const b).const_mul (Real.pi : ℂ) using 1
      all_goals ring
    convert hu.ccos.deriv using 1
    field_simp [show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero]

/-- The meromorphic cosine companion. -/
def gammaReflectionCosineMero (b : ℂ) : meroField Set.univ :=
  algebraMap (analyticSubring Set.univ) (meroField Set.univ)
    (gammaReflectionCosineAnalytic b)

theorem gammaReflectionSineMero_deriv (b : ℂ) :
    (gammaReflectionSineMero b)′ = -gammaReflectionCosineMero b := by
  rw [gammaReflectionSineMero,
    meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ
      Set.univ_nonempty,
    analyticSubringDeriv_gammaReflectionSineAnalytic, map_neg]
  rfl

theorem gammaReflectionCosineMero_deriv (b : ℂ) :
    (gammaReflectionCosineMero b)′ =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          gammaReflectionPiSqAnalytic *
        gammaReflectionSineMero b := by
  rw [gammaReflectionCosineMero,
    meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ
      Set.univ_nonempty,
    analyticSubringDeriv_gammaReflectionCosineAnalytic, map_mul]
  rfl

theorem gammaReflectionSineMero_secondDeriv (b : ℂ) :
    (gammaReflectionSineMero b)′′ =
      -algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          gammaReflectionPiSqAnalytic *
        gammaReflectionSineMero b := by
  rw [gammaReflectionSineMero_deriv, map_neg,
    gammaReflectionCosineMero_deriv]
  ring

local instance meromorphicGammaReflectionRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance meromorphicGammaReflectionRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance meromorphicGammaReflectionDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance meromorphicGammaReflectionCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

theorem gammaReflectionPiSqAnalytic_map :
    algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        gammaReflectionPiSqAnalytic =
      algebraMap (RatFunc ℂ) (meroField Set.univ)
        (RatFunc.C ((Real.pi : ℂ) ^ 2)) := by
  change polyToMero Set.univ (Polynomial.C ((Real.pi : ℂ) ^ 2)) =
    ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ
        (RatFunc.C ((Real.pi : ℂ) ^ 2))
  rw [show RatFunc.C ((Real.pi : ℂ) ^ 2) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C ((Real.pi : ℂ) ^ 2)) by
    simp [RatFunc.algebraMap_C]]
  exact (ratfuncToMero_algebraMap_polynomial Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty Set.infinite_univ _).symm

/-- The sine quotient is differentially algebraic over `ℂ(X)` by its explicit second-order
linear differential equation. -/
theorem differentialAlgebraicOver_gammaReflectionSineMero (b : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (gammaReflectionSineMero b) := by
  let c : (Unit × ℕ) →₀ RatFunc ℂ :=
    Finsupp.single ((), 2) 1 +
      Finsupp.single ((), 0) (RatFunc.C ((Real.pi : ℂ) ^ 2))
  have hc : c ≠ 0 := by
    intro h
    have hv := DFunLike.congr_fun h ((), 2)
    simp [c] at hv
  apply differentialAlgebraicOver_of_finsupp_jet_linear_eq
    (C := RatFunc ℂ) (K := RatFunc ℂ)
      (x := gammaReflectionSineMero b) c hc 0
  rw [Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index (fun _ => by simp)]
  rw [Finsupp.sum_add_index (by simp) (by simp [add_mul])]
  simp [differentialJet_zero, differentialJet_succ,
    gammaReflectionSineMero_secondDeriv,
    gammaReflectionPiSqAnalytic_map]

/-- The Euler-reflection gauge is differentially algebraic over `ℂ(X)`. -/
theorem differentialAlgebraicOver_gammaReflectionGaugeMero (b : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (gammaReflectionGaugeMero b) := by
  exact HTGeometry.differentialAlgebraicOver_inv
    (differentialAlgebraicOver_gammaReflectionSineMero b)

theorem reciprocalGammaNegativeShiftAnalytic_ne_zero (b : ℂ) :
    reciprocalGammaNegativeShiftAnalytic b ≠ 0 := by
  intro hzero
  have hv := congrArg Subtype.val hzero
  simp only [reciprocalGammaNegativeShiftAnalytic, univAnalytic,
    ZeroMemClass.coe_zero] at hv
  change Germ.ofFun (l := 𝓟 Set.univ)
      (fun z => reciprocalGammaEntire (-z + b)) =
    Germ.ofFun (l := 𝓟 Set.univ) (fun _ : ℂ => 0) at hv
  rw [Germ.coe_eq] at hv
  have hvalue := eventually_principal.mp hv (b - 1) (Set.mem_univ _)
  simp [reciprocalGammaEntire] at hvalue

theorem gammaReflectionSineAnalytic_ne_zero (b : ℂ) :
    gammaReflectionSineAnalytic b ≠ 0 := by
  rw [← reciprocalGammaNegativeShift_mul_positive]
  exact mul_ne_zero (reciprocalGammaNegativeShiftAnalytic_ne_zero b)
    (reciprocalGammaShiftAnalytic_ne_zero (1 - b))

theorem gammaReflectionSineMero_ne_zero (b : ℂ) :
    gammaReflectionSineMero b ≠ 0 := by
  intro hzero
  exact gammaReflectionSineAnalytic_ne_zero b
    ((IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ))
      (by simpa [gammaReflectionSineMero] using hzero))

theorem gammaReflectionGaugeMero_ne_zero (b : ℂ) :
    gammaReflectionGaugeMero b ≠ 0 :=
  inv_ne_zero (gammaReflectionSineMero_ne_zero b)

/-- Differential algebraicity is closed under integer powers. -/
theorem HTGeometry.differentialAlgebraicOver_zpow
    {x : meroField Set.univ}
    (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) (n : ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (x ^ n) := by
  cases n with
  | ofNat n =>
      simpa using HTGeometry.differentialAlgebraicOver_pow hx n
  | negSucc n =>
      rw [zpow_negSucc]
      exact HTGeometry.differentialAlgebraicOver_inv
        (HTGeometry.differentialAlgebraicOver_pow hx (n + 1))

/-- A finite product of differentially algebraic meromorphic elements remains differentially
algebraic. -/
theorem HTGeometry.differentialAlgebraicOver_finset_prod
    {ι : Type*} {s : Finset ι} {f : ι → meroField Set.univ}
    (hf : ∀ i ∈ s, DifferentialAlgebraicOver (RatFunc ℂ) (f i)) :
    DifferentialAlgebraicOver (RatFunc ℂ) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using
        (HTGeometry.differentialAlgebraicOver_algebraMap
          (E := meroField Set.univ) (1 : RatFunc ℂ))
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact HTGeometry.differentialAlgebraicOver_mul (hf i (by simp))
        (ih fun j hj => hf j (by simp [hj]))

private theorem reflectedGammaPower_normalForm
    (a x : meroField Set.univ) (hx : x ≠ 0) (p n : ℤ) :
    x ^ p * (a * x⁻¹) ^ n = a ^ n * x ^ (p - n) := by
  rw [mul_zpow, inv_zpow, ← zpow_neg]
  calc
    x ^ p * (a ^ n * x ^ (-n)) = a ^ n * (x ^ p * x ^ (-n)) := by
      ac_rfl
    _ = a ^ n * x ^ (p + -n) := by rw [zpow_add₀ hx]
    _ = a ^ n * x ^ (p - n) := by rw [sub_eq_add_neg]

/-- A finite product with positive and negative orientations, already normalized to one common
scale. -/
def gammaOrientedProductMero {d e : ℕ} (b : Fin d → ℂ)
    (nn : Fin d → Fin e → ℕ) (p n : Fin d → Fin e → ℤ) :
    meroField Set.univ :=
  ∏ c, ∏ j,
    gammaShiftMero (b c + (nn c j : ℂ)) ^ p c j *
      gammaNegativeShiftMero (1 - (b c + (nn c j : ℂ))) ^ n c j

/-- The total sine gauge produced by all negative-orientation factors. -/
def gammaOrientedGaugeMero {d e : ℕ} (b : Fin d → ℂ)
    (nn : Fin d → Fin e → ℕ) (n : Fin d → Fin e → ℤ) :
    meroField Set.univ :=
  ∏ c, ∏ j,
    gammaReflectionGaugeMero (1 - (b c + (nn c j : ℂ))) ^ n c j

/-- The surviving oriented charge: positive charge minus reflected negative charge. -/
def gammaOrientedOrbitCharge {d e : ℕ}
    (p n : Fin d → Fin e → ℤ) (c : Fin d) : ℤ :=
  ∑ j, p c j - ∑ j, n c j

/-- **Analytic oriented normal form.**  Euler reflection removes every negative orientation into
a DA sine gauge and subtracts its exponent from the corresponding positive orbit. -/
theorem gammaOrientedProductMero_normalForm {d e : ℕ} (b : Fin d → ℂ)
    (nn : Fin d → Fin e → ℕ) (p n : Fin d → Fin e → ℤ) :
    gammaOrientedProductMero b nn p n =
      gammaOrientedGaugeMero b nn n *
        gammaCommonScaleProductMero b nn (fun c j => p c j - n c j) := by
  rw [gammaOrientedProductMero, gammaOrientedGaugeMero,
    gammaCommonScaleProductMero]
  simp_rw [gammaNegativeShiftMero_reflection]
  simp_rw [show 1 - (1 - (b _ + (nn _ _ : ℂ))) =
      b _ + (nn _ _ : ℂ) by ring]
  simp_rw [reflectedGammaPower_normalForm _ _ (gammaShiftMero_ne_zero _)]
  simp_rw [Finset.prod_mul_distrib]

theorem gammaOrientedGaugeMero_ne_zero {d e : ℕ} (b : Fin d → ℂ)
    (nn : Fin d → Fin e → ℕ) (n : Fin d → Fin e → ℤ) :
    gammaOrientedGaugeMero b nn n ≠ 0 := by
  rw [gammaOrientedGaugeMero, Finset.prod_ne_zero_iff]
  intro c _
  rw [Finset.prod_ne_zero_iff]
  intro j _
  exact zpow_ne_zero _ (gammaReflectionGaugeMero_ne_zero _)

theorem differentialAlgebraicOver_gammaOrientedGaugeMero
    {d e : ℕ} (b : Fin d → ℂ) (nn : Fin d → Fin e → ℕ)
    (n : Fin d → Fin e → ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (gammaOrientedGaugeMero b nn n) := by
  rw [gammaOrientedGaugeMero]
  apply HTGeometry.differentialAlgebraicOver_finset_prod
  intro c _
  apply HTGeometry.differentialAlgebraicOver_finset_prod
  intro j _
  exact HTGeometry.differentialAlgebraicOver_zpow
    (differentialAlgebraicOver_gammaReflectionGaugeMero _) (n c j)

theorem gammaCommonScaleOrbitCharge_sub_eq_gammaOrientedOrbitCharge
    {d e : ℕ} (p n : Fin d → Fin e → ℤ) (c : Fin d) :
    gammaCommonScaleOrbitCharge (fun c j => p c j - n c j) c =
      gammaOrientedOrbitCharge p n c := by
  simp [gammaCommonScaleOrbitCharge, gammaOrientedOrbitCharge,
    Finset.sum_sub_distrib]

/-- **Analytic oriented Gamma kernel.**  After any nonzero DA gauge, an arbitrary-orientation
common-scale product is DA exactly when every oriented charge vanishes. -/
theorem differentialAlgebraicOver_mul_gammaOrientedProductMero_iff_charge_eq_zero
    {d e : ℕ} (b : Fin d → ℂ) (nn : Fin d → Fin e → ℕ)
    (p n : Fin d → Fin e → ℤ) (a : meroField Set.univ) (ha : a ≠ 0)
    (haDA : DifferentialAlgebraicOver (RatFunc ℂ) a)
    (hsep : ∀ c c', c ≠ c' → ∀ k : ℤ, b c - b c' ≠ (k : ℂ)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (a * gammaOrientedProductMero b nn p n) ↔
      ∀ c, gammaOrientedOrbitCharge p n c = 0 := by
  rw [gammaOrientedProductMero_normalForm]
  rw [show a * (gammaOrientedGaugeMero b nn n *
      gammaCommonScaleProductMero b nn (fun c j => p c j - n c j)) =
    (a * gammaOrientedGaugeMero b nn n) *
      gammaCommonScaleProductMero b nn (fun c j => p c j - n c j) by ring]
  rw [differentialAlgebraicOver_mul_gammaCommonScaleProductMero_iff_charge_eq_zero
    b nn (fun c j => p c j - n c j) (a * gammaOrientedGaugeMero b nn n)
    (mul_ne_zero ha (gammaOrientedGaugeMero_ne_zero b nn n))
    (HTGeometry.differentialAlgebraicOver_mul haDA
      (differentialAlgebraicOver_gammaOrientedGaugeMero b nn n)) hsep]
  exact forall_congr' fun c => by
    rw [gammaCommonScaleOrbitCharge_sub_eq_gammaOrientedOrbitCharge]

/-- Every nonneutral oriented sector is hypertranscendental, and only those sectors are. -/
theorem hypertranscendentalOver_mul_gammaOrientedProductMero_iff_exists_charge_ne_zero
    {d e : ℕ} (b : Fin d → ℂ) (nn : Fin d → Fin e → ℕ)
    (p n : Fin d → Fin e → ℤ) (a : meroField Set.univ) (ha : a ≠ 0)
    (haDA : DifferentialAlgebraicOver (RatFunc ℂ) a)
    (hsep : ∀ c c', c ≠ c' → ∀ k : ℤ, b c - b c' ≠ (k : ℂ)) :
    HypertranscendentalOver (RatFunc ℂ)
        (a * gammaOrientedProductMero b nn p n) ↔
      ∃ c, gammaOrientedOrbitCharge p n c ≠ 0 := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_mul_gammaOrientedProductMero_iff_charge_eq_zero
      b nn p n a ha haDA hsep]
  simp only [not_forall]

/-- Every finite integer oriented charge vector has a one-factor-per-orbit realization. -/
theorem gammaOrientedOrbitCharge_surjective {d : ℕ} :
    Function.Surjective
      (fun q : (Fin d → Fin 1 → ℤ) × (Fin d → Fin 1 → ℤ) =>
        gammaOrientedOrbitCharge q.1 q.2) := by
  intro q
  refine ⟨(fun c _ => q c, fun _ _ => 0), ?_⟩
  funext c
  simp [gammaOrientedOrbitCharge]

end

end GaloisForLFunctions
