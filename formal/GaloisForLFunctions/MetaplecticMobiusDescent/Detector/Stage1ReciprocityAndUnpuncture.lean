import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.Stage1DualRowMoments
import GaloisForLFunctions.MetaplecticMobiusDescent.PrimeRows.AdaptiveSourceCounts
import GaloisForLFunctions.MetaplecticMobiusDescent.MeanSquare.InitialMeanSquareRows

/-!
# Stage-1 modulo-4 sextic reciprocity, zero-coprimality nonprincipality, and slot decoupling

Algebraic and combinatorial foundations for the Stage-1 dual sixth-power-free moment estimates:

1. **`rayCharacter_eq_sextic_bad12`:** Every character `ξ : RayFourExpansion.RayCharacter` of
   `(O ⧸ Ideal.span {(4 : O)})ˣ` (order `12`) coincides across all odd primary primes `p`
   (`lambda^2 ∣ p - 1`) with `star (idealRowHom (bad12Elem idx) (Ideal.span {p}))` for a unique
   `idx : Fin 3 × Bool × Bool`, where `bad12Elem idx = 4^j * (lambda^3)^e₁ * (-lambda)^3^e₂` is
   supported exclusively on `fixedBadPrimes = {(lambda), (2)}`.
2. **`bad12_freeRow_transfer`:** Multiplying `u : FreeRow` by `bad12Elem idx` and extracting its
   sixth-power-free core `u_tilde : FreeRow` via `rowMap` produces a sixth-power cofactor ideal
   `A_bad ∣ ramifiedIdeal * cubicTwoIdeal` (`≤ 4` choices), preserving `idealRowHom` identically
   on all ideals `I` with `quadraticSupported I` (`(2), (lambda) ∤ I`) and keeping `rowNorm u_tilde`
   comparable to `rowNorm u` up to fixed constants (`1 / 2985984` and `11664`).
3. **`freeRow_nonprincipal_eventually`:** Every `u : FreeRow` with `rowNorm u ≥ Z ^ d` (`d > 0`)
   has nonprincipal `sourceDetectorFamily` across all indices without any coprimality calibration
   (`exists_supported_numerator_factorization` + `principal_row_fixed_support`).
4. **`inputConjugateRow_markedRadial_unpuncture_total_scale` & `disjoint_tuple_l2_le_factored`:**
   Total-scale `X⁻¹` multi-prime geometric unpuncturing and exact collision-set induction on
   `|S''|` decoupling the un-marked `pool` sum from the `S''` prime-slot product at cost `O_K(1)`.
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Classical Topology ContDiff SchwartzMap FourierTransform ComplexConjugate

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

namespace Stage1ReciprocityAndUnpuncture

open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FirstPassCubeLabels SecondPassArithmetic InverseMoment Stage1CubeBins
open RayFourExpansion InitialMeanSquare Eisenstein.Coordinates FixedRayArithmetic
open QuadraticPhase.Eisenstein UniqueFactorizationMonoid
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open Stage1DualRowMoments

local notation "O" => Eisenstein.O

/-! ### Part I: 12-element modulo-4 sextic reciprocity (`bad12Elem`) -/

/-- Index type of size `3 × 2 × 2 = 12` parameterizing all modulo-`4` unit characters via bad-prime
sextic rows. -/
abbrev Bad12Idx := Fin 3 × Bool × Bool

/-- Explicit divisor of `4^2 * 3^6` realizing the `idx`-th character of `(O ⧸ Ideal.span {4})ˣ`
through `star (idealRowHom (bad12Elem idx) ·)`. -/
def bad12Elem (idx : Bad12Idx) : O :=
  (4 : O) ^ idx.1.val * (if idx.2.1 then lambda ^ 3 else 1) * (if idx.2.2 then (-lambda) ^ 3 else 1)

lemma bad12Elem_ne_zero (idx : Bad12Idx) : bad12Elem idx ≠ 0 := by
  unfold bad12Elem
  have h4 : (4 : O) ^ idx.1.val ≠ 0 := pow_ne_zero _ (by norm_num)
  have hl1 : (if idx.2.1 then lambda ^ 3 else (1 : O)) ≠ 0 := by
    split_ifs
    · exact pow_ne_zero 3 residue_lambda_prime.1
    · exact one_ne_zero
  have hl2 : (if idx.2.2 then (-lambda) ^ 3 else (1 : O)) ≠ 0 := by
    split_ifs
    · exact pow_ne_zero 3 (neg_ne_zero.mpr residue_lambda_prime.1)
    · exact one_ne_zero
  exact mul_ne_zero (mul_ne_zero h4 hl1) hl2

lemma neg_lambda_odd : -lambda ∉ Ideal.span {(2 : O)} := by
  intro h
  exact lambda_odd (by simpa using Submodule.neg_mem _ h)

def oddMaskMonoid : O →* ℂ where
  toFun n := if (2 : O) ∣ n then 0 else 1
  map_one' := by
    have h2 : ¬(2 : O) ∣ 1 := fun h =>
      negative_two_prime.2.1 (isUnit_of_dvd_one (by simpa only [neg_dvd] using h))
    simp [h2]
  map_mul' x y := by
    rw [two_dvd_mul_iff]
    by_cases hx : (2 : O) ∣ x <;> by_cases hy : (2 : O) ∣ y <;> simp [hx, hy]

/-- Quadratic reciprocity supplement at `-lambda`, extended by zero on even elements. -/
def negLambdaQuadraticCharacter : O →* ℂ where
  toFun n := if (2 : O) ∣ n then 0 else quadraticPhase (-lambda) n
  map_one' := by
    have h2 : ¬(2 : O) ∣ 1 := fun h =>
      negative_two_prime.2.1 (isUnit_of_dvd_one (by simpa only [neg_dvd] using h))
    rw [if_neg h2, quadraticPhase_one (-lambda) neg_lambda_odd]
  map_mul' x y := by
    rw [two_dvd_mul_iff]
    by_cases hx : (2 : O) ∣ x <;> by_cases hy : (2 : O) ∣ y
    · simp only [hx, hy, true_or, if_true, zero_mul]
    · simp only [hx, hy, true_or, if_true, if_false, zero_mul]
    · simp only [hx, hy, or_true, if_true, if_false, mul_zero]
    · simp only [hx, hy, false_or, if_false]
      exact quadraticPhase_mul_right neg_lambda_odd
        (fun h => hx (Ideal.mem_span_singleton.mp h))
        (fun h => hy (Ideal.mem_span_singleton.mp h))

lemma negLambdaQuadraticCharacter_periodic (x y : O) (hxy : (4 : O) ∣ x - y) :
    negLambdaQuadraticCharacter x = negLambdaQuadraticCharacter y := by
  have h2 : (2 : O) ∣ x - y := (show (2 : O) ∣ 4 from ⟨2, by norm_num⟩).trans hxy
  have hd : (2 : O) ∣ x ↔ (2 : O) ∣ y :=
    ⟨fun hx => by convert dvd_sub hx h2 using 1; ring,
     fun hy => by convert dvd_add h2 hy using 1; ring⟩
  change (if (2 : O) ∣ x then 0 else _) = (if (2 : O) ∣ y then 0 else _)
  rw [hd, quadraticPhase_congr_right (-lambda) x y hxy]

lemma negLambdaQuadraticCharacter_sq (n : O) (hn : ¬(2 : O) ∣ n) :
    negLambdaQuadraticCharacter n ^ 2 = 1 := by
  change (if (2 : O) ∣ n then (0 : ℂ) else quadraticPhase (-lambda) n) ^ 2 = 1
  rw [if_neg hn]
  exact quadraticPhase_sq neg_lambda_odd (fun h => hn (Ideal.mem_span_singleton.mp h))

theorem quadratic_neg_lambda_primary (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    complexQuadraticChar (Ideal.span {p}) (Ideal.Quotient.mk (Ideal.span {p}) (-lambda)) =
      quadraticPhase (-lambda) p := by
  have hspan_neg : Ideal.span {-lambda} = Ideal.span {lambda} := Ideal.span_singleton_neg lambda
  letI : (Ideal.span {-lambda}).IsMaximal := by
    rw [hspan_neg]
    exact PrincipalIdealRing.isMaximal_of_irreducible residue_lambda_prime.irreducible
  have hodd_neg : ringChar (O ⧸ Ideal.span {-lambda}) ≠ 2 := by
    rw [hspan_neg]; exact lambda_residue_odd
  have hne : (Ideal.span {p} : Ideal O) ≠ Ideal.span {-lambda} := by
    rw [hspan_neg]
    intro h; apply hg; rw [h]; exact Ideal.mem_span_singleton_self lambda
  have he := quadratic_prime_reciprocity p (-lambda) hp
    (neg_ne_zero.mpr residue_lambda_prime.ne_zero) hc hodd_neg hne
  have hres : Ideal.Quotient.mk (Ideal.span {-lambda}) p = 1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {-lambda}))]
    apply Ideal.Quotient.eq.mpr
    rw [hspan_neg]
    exact Ideal.mem_span_singleton.mpr ((dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0)).trans hprimary)
  rw [hres, map_one, mul_one, quadraticPhase_comm p (-lambda)] at he
  exact he

lemma idealRowHom_neg_lambda_prime_cube (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (hs : quadraticSupported (Ideal.span {p})) :
    idealRowHom (-lambda) (Ideal.span {p}) ^ 3 = negLambdaQuadraticCharacter p := by
  letI : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmem : Ideal.span {p} ∈ normalizedFactors (Ideal.span {p}) :=
    (Ideal.mem_normalizedFactors_iff (primaryIdealGenerator_ne_zero_ideal _ hs.1)).mpr ⟨inferInstance, le_rfl⟩
  have hd := supported_factors_good _ hs _ hmem
  rw [idealRowHom_prime (-lambda) _ hd.2.1,
    ← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), (complexSexticChar_powers _ _).2.1,
    quadratic_neg_lambda_primary p hp.ne_zero hd.2.1 hd.2.2 hprimary]
  change quadraticPhase (-lambda) p = (if (2 : O) ∣ p then 0 else quadraticPhase (-lambda) p)
  rw [if_neg ((supported_span_iff p).mp hs).2]

def conjMonoidHom : ℂ →* ℂ := (starRingEnd ℂ).toMonoidHom

def bad12Monoid (idx : Bad12Idx) : O →* ℂ :=
  conjMonoidHom.comp (oddMaskMonoid * cubicTwoSupplement ^ idx.1.val *
    (if idx.2.1 then lambdaQuadraticCharacter else 1) *
    (if idx.2.2 then negLambdaQuadraticCharacter else 1))

lemma bad12Monoid_apply (idx : Bad12Idx) (n : O) :
    bad12Monoid idx n = star ((if (2 : O) ∣ n then (0 : ℂ) else 1) * cubicTwoSupplement n ^ idx.1.val *
      (if idx.2.1 then lambdaQuadraticCharacter n else 1) *
      (if idx.2.2 then negLambdaQuadraticCharacter n else 1)) := by
  unfold bad12Monoid conjMonoidHom oddMaskMonoid
  simp only [MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  cases idx.2.1 <;> cases idx.2.2 <;> rfl

lemma bad12Monoid_mod_four (idx : Bad12Idx) (x y : O) (hxy : x - y ∈ Ideal.span {(4 : O)}) :
    bad12Monoid idx x = bad12Monoid idx y := by
  have h4 : (4 : O) ∣ x - y := Ideal.mem_span_singleton.mp hxy
  have h2 : (2 : O) ∣ x - y := (show (2 : O) ∣ 4 from ⟨2, by norm_num⟩).trans h4
  have hd : (2 : O) ∣ x ↔ (2 : O) ∣ y :=
    ⟨fun hx => by convert dvd_sub hx h2 using 1; ring,
     fun hy => by convert dvd_add h2 hy using 1; ring⟩
  rw [bad12Monoid_apply, bad12Monoid_apply]
  simp only [hd, cubicTwoSupplement_mod_four x y hxy,
    lambdaQuadraticCharacter_periodic x y h4,
    negLambdaQuadraticCharacter_periodic x y h4]

def bad12RayChar (idx : Bad12Idx) : RayCharacter where
  toFun r := bad12Monoid idx (Quotient.out r)
  map_one' := by
    have h1 : Quotient.out (1 : RayRing) - 1 ∈ Ideal.span {(4 : O)} :=
      Ideal.Quotient.eq.mp (Quotient.out_eq (1 : RayRing))
    rw [bad12Monoid_mod_four idx _ 1 h1, map_one]
  map_mul' r s := by
    have hm : Quotient.out (r * s) - Quotient.out r * Quotient.out s ∈ Ideal.span {(4 : O)} := by
      apply Ideal.Quotient.eq.mp
      change Ideal.Quotient.mk (Ideal.span {(4 : O)}) (Quotient.out (r * s)) = _
      rw [Ideal.Quotient.mk_out, map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out]
    rw [bad12Monoid_mod_four idx _ _ hm, map_mul]
  map_nonunit' r hr := by
    have h2 : (2 : O) ∣ Quotient.out r := by
      by_contra hnot2
      apply hr
      have hneg2 : ¬ (-2 : O) ∣ Quotient.out r := by simpa only [neg_dvd] using hnot2
      have hc2 : IsCoprime (Quotient.out r) (2 : O) := by
        simpa only [IsCoprime.neg_right_iff] using (negative_two_prime.coprime_iff_not_dvd.mpr hneg2).symm
      have hc4 : IsCoprime (Quotient.out r) (4 : O) := by
        simpa only [show (2 : O) ^ 2 = 4 by norm_num] using hc2.pow_right (n := 2)
      obtain ⟨a, b, hab⟩ := hc4
      have hm := congrArg (Ideal.Quotient.mk (Ideal.span {(4 : O)})) hab
      have hz : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (4 : O) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self 4)
      simp only [map_add, map_mul, map_one, hz, mul_zero, add_zero, Ideal.Quotient.mk_out] at hm
      exact IsUnit.of_mul_eq_one_right _ hm
    rw [bad12Monoid_apply]
    simp [h2]

lemma bad12RayChar_mk (idx : Bad12Idx) (x : O) :
    bad12RayChar idx (Ideal.Quotient.mk (Ideal.span {(4 : O)}) x) = bad12Monoid idx x :=
  bad12Monoid_mod_four idx _ x (Ideal.Quotient.eq.mp (Quotient.out_eq _))

lemma bad12Monoid_eq_star_idealRowHom (idx : Bad12Idx) (p : O) (hp : Prime p)
    (hprimary : lambda ^ 2 ∣ p - 1) (hs : quadraticSupported (Ideal.span {p})) :
    bad12Monoid idx p = star (idealRowHom (bad12Elem idx) (Ideal.span {p})) := by
  have hnot2 : ¬(2 : O) ∣ p := ((supported_span_iff p).mp hs).2
  have h4 : idealRowHom (4 : O) (Ideal.span {p}) = cubicTwoSupplement p := by
    rw [show (4 : O) = 2 * 2 by norm_num, idealRowHom_argument_mul, ← sq]
    letI : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    have hmem : Ideal.span {p} ∈ normalizedFactors (Ideal.span {p}) :=
      (Ideal.mem_normalizedFactors_iff (primaryIdealGenerator_ne_zero_ideal _ hs.1)).mpr ⟨inferInstance, le_rfl⟩
    have hd := supported_factors_good _ hs _ hmem
    have hgen : primaryGenerator (Ideal.span {p}) hd.2.1 = p :=
      primary_associated_eq _ _ (Ideal.span_singleton_eq_span_singleton.mp
        (primaryGenerator_spec (Ideal.span {p}) hd.2.1).1.symm)
        (primaryGenerator_spec (Ideal.span {p}) hd.2.1).2 hprimary
    rw [idealRowHom_prime 2 _ hd.2.1]
    have he := complexSextic_four_eq_fixed_two (Ideal.span {p}) hd.2.1 hd.2.2
    have hfour : (4 : O ⧸ Ideal.span {p}) = (Ideal.Quotient.mk (Ideal.span {p}) (2 : O)) ^ 2 := by
      norm_num [map_ofNat]
    rwa [hfour, map_pow, hgen] at he
  rw [bad12Monoid_apply]
  unfold bad12Elem
  simp only [if_neg hnot2, one_mul, idealRowHom_argument_mul, idealRowHom_argument_pow _ _ _ hs.1, h4]
  have h1 : idealRowHom (if idx.2.1 then lambda ^ 3 else 1) (Ideal.span {p}) =
      if idx.2.1 then lambdaQuadraticCharacter p else 1 := by
    cases idx.2.1
    · simp [idealRowHom_one_good _ hs.1]
    · simp [idealRowHom_argument_pow _ _ _ hs.1, idealRowHom_lambda_prime_cube p hp hprimary hs]
  have h2 : idealRowHom (if idx.2.2 then (-lambda) ^ 3 else 1) (Ideal.span {p}) =
      if idx.2.2 then negLambdaQuadraticCharacter p else 1 := by
    cases idx.2.2
    · simp [idealRowHom_one_good _ hs.1]
    · simp [idealRowHom_argument_pow _ _ _ hs.1, idealRowHom_neg_lambda_prime_cube p hp hprimary hs]
  rw [h1, h2]

private lemma eval_lambda : lambda = eval (-1) 1 := by
  unfold lambda eval; push_cast; ring

private lemma eval_neg_lambda : -lambda = eval 1 (-1) := by
  unfold lambda eval; push_cast; ring

private lemma quadraticPhase_lambda_neg_one : quadraticPhase lambda (-1) = -1 := by
  have h1 : (-1 : O) = eval (-1) 0 := by unfold eval; push_cast; ring
  have hprod : lambda * (-1) = eval 1 (-1) := by rw [eval_lambda, h1, eval_mul]; rfl
  rw [quadraticPhase, hprod, eval_lambda, h1,
    fixedDualAverage_formula 1 (-1), fixedDualAverage_formula (-1) 1, fixedDualAverage_formula (-1) 0]
  norm_num [zpow_neg, zpow_ofNat, Complex.I_sq]
  have h2I : (1 + Complex.I + Complex.I + -1 : ℂ) = 2 * Complex.I := by ring
  have hm2I : (1 + -Complex.I + -Complex.I + -1 : ℂ) = -(2 * Complex.I) := by ring
  rw [h2I, hm2I]
  field_simp [Complex.I_ne_zero]

private lemma quadraticPhase_neg_lambda_neg_one : quadraticPhase (-lambda) (-1) = -1 := by
  have h1 : (-1 : O) = eval (-1) 0 := by unfold eval; push_cast; ring
  have hprod : (-lambda) * (-1) = eval (-1) 1 := by rw [eval_neg_lambda, h1, eval_mul]; rfl
  rw [quadraticPhase, hprod, eval_neg_lambda, h1,
    fixedDualAverage_formula (-1) 1, fixedDualAverage_formula 1 (-1), fixedDualAverage_formula (-1) 0]
  norm_num [zpow_neg, zpow_ofNat, Complex.I_sq]
  have h2I : (1 + Complex.I + Complex.I + -1 : ℂ) = 2 * Complex.I := by ring
  have hm2I : (1 + -Complex.I + -Complex.I + -1 : ℂ) = -(2 * Complex.I) := by ring
  rw [hm2I, h2I]
  field_simp [Complex.I_ne_zero]

private lemma quadraticPhase_lambda_one_two : quadraticPhase lambda (eval 1 2) = 1 := by
  have hprod : lambda * eval 1 2 = eval (-3) (-3) := by rw [eval_lambda, eval_mul]; rfl
  have hm4 : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (eval (-3) (-3)) =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) (eval 1 1) := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨eval (-1) (-1), ?_⟩
    unfold eval; push_cast; ring
  rw [quadraticPhase, hprod, fixedDualAverage_eq_of_mod_four _ _ hm4, eval_lambda,
    fixedDualAverage_formula 1 1, fixedDualAverage_formula (-1) 1, fixedDualAverage_formula 1 2]
  norm_num [zpow_neg, zpow_ofNat, Complex.I_sq]
  have hm2I : (1 + -Complex.I + -Complex.I + -1 : ℂ) = -(2 * Complex.I) := by ring
  rw [hm2I]
  field_simp [Complex.I_ne_zero]

private lemma quadraticPhase_neg_lambda_one_two : quadraticPhase (-lambda) (eval 1 2) = -1 := by
  have hprod : (-lambda) * eval 1 2 = eval 3 3 := by rw [eval_neg_lambda, eval_mul]; rfl
  have hm4 : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (eval 3 3) =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) (eval (-1) (-1)) := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨eval 1 1, ?_⟩
    unfold eval; push_cast; ring
  rw [quadraticPhase, hprod, fixedDualAverage_eq_of_mod_four _ _ hm4, eval_neg_lambda,
    fixedDualAverage_formula (-1) (-1), fixedDualAverage_formula 1 (-1), fixedDualAverage_formula 1 2]
  norm_num [zpow_neg, zpow_ofNat, Complex.I_sq]
  have h2I : (1 + Complex.I + Complex.I + -1 : ℂ) = 2 * Complex.I := by ring
  rw [h2I]
  field_simp [Complex.I_ne_zero]

private lemma not_two_dvd_one_two : ¬ (2 : O) ∣ eval 1 2 := by
  intro h
  exact not_mem_of_oddCoord 1 2 (by decide) (Ideal.mem_span_singleton.mpr h)

private lemma not_two_dvd_neg_one_two : ¬ (2 : O) ∣ -eval 1 2 := by
  simpa only [dvd_neg] using not_two_dvd_one_two

private lemma cubicTwoSupplement_congr_two (x y : O) (hxy : (2 : O) ∣ x - y) :
    cubicTwoSupplement x = cubicTwoSupplement y := by
  obtain ⟨k, hk⟩ := hxy
  have h2 : x - y ∈ cubicTwoIdeal :=
    Ideal.mem_span_singleton.mpr ⟨-k, by change x - y = (-2 : O) * (-k); rw [hk]; ring⟩
  change complexCubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal x) =
    complexCubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal y)
  rw [Ideal.Quotient.eq.mpr h2]

private lemma exists_order_three_unit :
    ∃ x₂ : O, ¬ (2 : O) ∣ x₂ ∧ cubicTwoSupplement x₂ ≠ 1 ∧ cubicTwoSupplement x₂ ^ 3 = 1 ∧
      lambdaQuadraticCharacter x₂ = 1 ∧ negLambdaQuadraticCharacter x₂ = 1 := by
  letI : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field cubicTwoIdeal
  have hne1 : complexCubicChar cubicTwoIdeal cubicTwoIdeal_good ≠ 1 :=
    complexCubicChar_ne_one cubicTwoIdeal cubicTwoIdeal_good
  obtain ⟨r, hr_diff⟩ := DFunLike.ne_iff.mp hne1
  have hr0 : r ≠ 0 := by
    intro hz
    subst hz
    exact hr_diff (by rw [MulChar.map_zero, MulChar.map_zero])
  have hr1 : complexCubicChar cubicTwoIdeal cubicTwoIdeal_good r ≠ 1 := by
    have h1_val : (1 : MulChar (O ⧸ cubicTwoIdeal) ℂ) r = 1 :=
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hr0)
    rwa [h1_val] at hr_diff
  obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hnot2 : ¬ (2 : O) ∣ x₀ := by
    intro h2
    obtain ⟨k, hk⟩ := h2
    apply hr0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr ⟨-k, by change x₀ = (-2 : O) * (-k); rw [hk]; ring⟩)
  have hnot2_sq : ¬ (2 : O) ∣ x₀ ^ 2 := by
    rw [sq, two_dvd_mul_iff]; tauto
  have hcub0 : cubicTwoSupplement x₀ ≠ 1 := hr1
  have hpow3_0 : cubicTwoSupplement x₀ ^ 3 = 1 := by
    change (complexCubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal x₀)) ^ 3 = 1
    rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0),
      complexCubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hr0)
  let x₂ := x₀ ^ 2
  have hcub2_ne1 : cubicTwoSupplement x₂ ≠ 1 := by
    intro h1
    apply hcub0
    have h4 : cubicTwoSupplement x₀ ^ 4 = 1 := by
      calc cubicTwoSupplement x₀ ^ 4 = (cubicTwoSupplement x₂) ^ 2 := by dsimp [x₂]; rw [map_pow]; ring
        _ = 1 := by rw [h1, one_pow]
    calc cubicTwoSupplement x₀ = cubicTwoSupplement x₀ * cubicTwoSupplement x₀ ^ 3 := by
          rw [hpow3_0, mul_one]
      _ = cubicTwoSupplement x₀ ^ 4 := by ring
      _ = 1 := h4
  have hcub2_pow3 : cubicTwoSupplement x₂ ^ 3 = 1 := by
    dsimp [x₂]; rw [map_pow, ← pow_mul, mul_comm, pow_mul, hpow3_0, one_pow]
  letI : Fintype (O ⧸ cubicTwoIdeal) := Fintype.ofFinite _
  have hcard4 : Fintype.card (O ⧸ cubicTwoIdeal) = 4 := by
    have hn : cubicTwoIdeal.absNorm = 4 := by
      change (Ideal.span {(-2 : O)}).absNorm = 4
      rw [Ideal.span_singleton_neg, ← Nat.cast_inj (R := ℝ), ← ringComplex_norm_sq_eq_absNorm_span]
      simp [map_ofNat]; norm_num
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hn]
  have hcard3 : Fintype.card (O ⧸ cubicTwoIdeal)ˣ = 3 := by
    rw [Fintype.card_units, hcard4]
  let u₀ : (O ⧸ cubicTwoIdeal)ˣ := Units.mk0 (Ideal.Quotient.mk cubicTwoIdeal x₀) hr0
  have hu3 : u₀ ^ 3 = 1 := by
    have hpc := pow_card_eq_one (x := u₀)
    rwa [hcard3] at hpc
  have hx3_mod2 : x₀ ^ 3 - 1 ∈ cubicTwoIdeal := by
    apply Ideal.Quotient.eq.mp
    rw [map_pow, map_one]
    exact congrArg Units.val hu3
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx3_mod2
  have hx6_mod4 : (4 : O) ∣ x₂ ^ 3 - 1 := by
    have hx3 : x₀ ^ 3 = 1 - 2 * y := by
      have : x₀ ^ 3 - 1 = (-2 : O) * y := hy
      linear_combination this
    have hx6 : x₂ ^ 3 = (x₀ ^ 3) ^ 2 := by dsimp [x₂]; ring
    refine ⟨y ^ 2 - y, ?_⟩
    rw [hx6, hx3]; ring
  have hl1 : lambdaQuadraticCharacter x₂ = 1 := by
    have hsq := lambdaQuadraticCharacter_sq x₂ hnot2_sq
    calc lambdaQuadraticCharacter x₂
        = lambdaQuadraticCharacter x₂ * lambdaQuadraticCharacter x₂ ^ 2 := by rw [hsq, mul_one]
      _ = lambdaQuadraticCharacter x₂ ^ 3 := by ring
      _ = lambdaQuadraticCharacter (x₂ ^ 3) := (map_pow _ _ _).symm
      _ = lambdaQuadraticCharacter 1 := lambdaQuadraticCharacter_periodic (x₂ ^ 3) 1 hx6_mod4
      _ = 1 := map_one _
  have hl2 : negLambdaQuadraticCharacter x₂ = 1 := by
    have hsq := negLambdaQuadraticCharacter_sq x₂ hnot2_sq
    calc negLambdaQuadraticCharacter x₂
        = negLambdaQuadraticCharacter x₂ * negLambdaQuadraticCharacter x₂ ^ 2 := by rw [hsq, mul_one]
      _ = negLambdaQuadraticCharacter x₂ ^ 3 := by ring
      _ = negLambdaQuadraticCharacter (x₂ ^ 3) := (map_pow _ _ _).symm
      _ = negLambdaQuadraticCharacter 1 := negLambdaQuadraticCharacter_periodic (x₂ ^ 3) 1 hx6_mod4
      _ = 1 := map_one _
  exact ⟨x₂, hnot2_sq, hcub2_ne1, hcub2_pow3, hl1, hl2⟩

lemma bad12RayChar_injective : Function.Injective bad12RayChar := by
  obtain ⟨x₂, hx2_odd, hζ_ne1, hζ_pow3, hl1_x2, hl2_x2⟩ := exists_order_three_unit
  rintro ⟨j₁, b₁, c₁⟩ ⟨j₂, b₂, c₂⟩ heq
  have eval_at (x : O) : bad12Monoid (j₁, b₁, c₁) x = bad12Monoid (j₂, b₂, c₂) x := by
    rw [← bad12RayChar_mk, ← bad12RayChar_mk, heq]
  have hc_12 : cubicTwoSupplement (eval 1 2) = 1 := by
    rw [cubicTwoSupplement_congr_two (eval 1 2) 1 ⟨eval 0 1, by unfold eval; push_cast; ring⟩, map_one]
  have hl1_12 : lambdaQuadraticCharacter (eval 1 2) = 1 := by
    change (if (2 : O) ∣ eval 1 2 then 0 else quadraticPhase lambda (eval 1 2)) = 1
    rw [if_neg not_two_dvd_one_two, quadraticPhase_lambda_one_two]
  have hl2_12 : negLambdaQuadraticCharacter (eval 1 2) = -1 := by
    change (if (2 : O) ∣ eval 1 2 then 0 else quadraticPhase (-lambda) (eval 1 2)) = -1
    rw [if_neg not_two_dvd_one_two, quadraticPhase_neg_lambda_one_two]
  have he_c : c₁ = c₂ := by
    have h := eval_at (eval 1 2)
    rw [bad12Monoid_apply, bad12Monoid_apply] at h
    simp only [if_neg not_two_dvd_one_two, hc_12, one_pow, mul_one, hl1_12, ite_self, one_mul, hl2_12] at h
    cases c₁ <;> cases c₂ <;> simp at h ⊢
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
  have hc_m12 : cubicTwoSupplement (-eval 1 2) = 1 := by
    rw [cubicTwoSupplement_congr_two (-eval 1 2) 1 ⟨eval (-1) (-1), by unfold eval; push_cast; ring⟩, map_one]
  have hl1_m12 : lambdaQuadraticCharacter (-eval 1 2) = -1 := by
    rw [show -eval 1 2 = (-1) * eval 1 2 by ring, map_mul, hl1_12]
    change (if (2 : O) ∣ (-1 : O) then 0 else quadraticPhase lambda (-1)) * 1 = -1
    have hn2 : ¬ (2 : O) ∣ (-1 : O) := fun h =>
      negative_two_prime.2.1 (isUnit_of_dvd_one (by simpa only [neg_dvd, dvd_neg] using h))
    rw [if_neg hn2, quadraticPhase_lambda_neg_one, mul_one]
  have hl2_m12 : negLambdaQuadraticCharacter (-eval 1 2) = 1 := by
    rw [show -eval 1 2 = (-1) * eval 1 2 by ring, map_mul, hl2_12]
    change (if (2 : O) ∣ (-1 : O) then 0 else quadraticPhase (-lambda) (-1)) * (-1) = 1
    have hn2 : ¬ (2 : O) ∣ (-1 : O) := fun h =>
      negative_two_prime.2.1 (isUnit_of_dvd_one (by simpa only [neg_dvd, dvd_neg] using h))
    rw [if_neg hn2, quadraticPhase_neg_lambda_neg_one]; ring
  have he_b : b₁ = b₂ := by
    have h := eval_at (-eval 1 2)
    rw [bad12Monoid_apply, bad12Monoid_apply] at h
    simp only [if_neg not_two_dvd_neg_one_two, hc_m12, one_pow, mul_one, hl2_m12, ite_self, hl1_m12] at h
    cases b₁ <;> cases b₂ <;> simp at h ⊢
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
  have he_j : j₁ = j₂ := by
    have h := congrArg star (eval_at x₂)
    rw [bad12Monoid_apply, bad12Monoid_apply, star_star, star_star] at h
    simp only [if_neg hx2_odd, one_mul, hl1_x2, hl2_x2, ite_self, mul_one] at h
    set ζ := cubicTwoSupplement x₂
    have hζ0 : ζ ≠ 0 := fun hz => by rw [hz, zero_pow (by decide)] at hζ_pow3; exact zero_ne_one hζ_pow3
    have hζ2_ne1 : ζ ^ 2 ≠ 1 := fun h2 => hζ_ne1 (by
      calc ζ = ζ * ζ ^ 3 := by rw [hζ_pow3, mul_one]
        _ = (ζ ^ 2) ^ 2 := by ring
        _ = 1 := by rw [h2]; norm_num)
    fin_cases j₁ <;> fin_cases j₂
    · rfl
    · dsimp at h; rw [pow_zero, pow_one] at h; exact absurd h.symm hζ_ne1
    · dsimp at h; rw [pow_zero] at h; exact absurd h.symm hζ2_ne1
    · dsimp at h; rw [pow_one, pow_zero] at h; exact absurd h hζ_ne1
    · rfl
    · dsimp at h; rw [pow_one] at h; exact absurd (mul_left_cancel₀ hζ0 (by simpa [sq] using h)).symm hζ_ne1
    · dsimp at h; rw [pow_zero] at h; exact absurd h hζ2_ne1
    · dsimp at h; rw [pow_one] at h; exact absurd (mul_left_cancel₀ hζ0 (by simpa [sq] using h)) hζ_ne1
    · rfl
  subst he_j he_b he_c
  rfl

private lemma card_rayRing_units_le_twelve : Fintype.card RayRingˣ ≤ 12 := by
  have hspan_eq : (Ideal.span {((4 : ℕ) : O)} : Ideal O) = Ideal.span {(4 : O)} := by norm_num
  let e_ring := Submodule.quotEquivOfEq (Ideal.span {((4 : ℕ) : O)} : Ideal O)
    (Ideal.span {(4 : O)} : Ideal O) hspan_eq
  let e : ZMod 4 × ZMod 4 ≃ RayRing := (rationalCoordEquiv 4 (by norm_num)).trans e_ring.toEquiv
  let oddSet : Finset (ZMod 4 × ZMod 4) :=
    Finset.univ.filter (fun p => ¬ (p.1 = 0 ∨ p.1 = 2) ∨ ¬ (p.2 = 0 ∨ p.2 = 2))
  have hcard12 : oddSet.card = 12 := by decide
  let φ : RayRingˣ → ZMod 4 × ZMod 4 := fun u => e.symm (u : RayRing)
  have hinj : Function.Injective φ := fun u₁ u₂ h => Units.ext (e.symm.injective h)
  have he_apply (p : ZMod 4 × ZMod 4) :
      e p = Ideal.Quotient.mk (Ideal.span {(4 : O)}) (eval (p.1.val : ℤ) (p.2.val : ℤ)) := by
    change e_ring (Ideal.Quotient.mk (Ideal.span {((4 : ℕ) : O)}) (eval (ZMod.cast p.1) (ZMod.cast p.2))) = _
    have hc1 : (ZMod.cast p.1 : ℤ) = (p.1.val : ℤ) := by
      rcases p with ⟨x, _⟩; fin_cases x <;> rfl
    have hc2 : (ZMod.cast p.2 : ℤ) = (p.2.val : ℤ) := by
      rcases p with ⟨_, y⟩; fin_cases y <;> rfl
    rw [hc1, hc2]
    rfl
  have hmaps : ∀ u ∈ (Finset.univ : Finset RayRingˣ), φ u ∈ oddSet := by
    intro u _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra heven
    have heven' : ((φ u).1 = 0 ∨ (φ u).1 = 2) ∧ ((φ u).2 = 0 ∨ (φ u).2 = 2) := by tauto
    have hp : e (φ u) = (u : RayRing) := e.apply_symm_apply _
    have hd1 : 2 ∣ ((φ u).1.val : ℤ) := by
      rcases heven'.1 with h0 | h2 <;> [rw [h0]; rw [h2]] <;> decide
    have hd2 : 2 ∣ ((φ u).2.val : ℤ) := by
      rcases heven'.2 with h0 | h2 <;> [rw [h0]; rw [h2]] <;> decide
    obtain ⟨k₁, hk₁⟩ := hd1
    obtain ⟨k₂, hk₂⟩ := hd2
    have heval2 : eval ((φ u).1.val : ℤ) ((φ u).2.val : ℤ) = 2 * eval k₁ k₂ := by
      rw [hk₁, hk₂]; unfold eval; push_cast; ring
    have h0 : (u : RayRing) ^ 2 = 0 := by
      rw [← hp, he_apply (φ u), heval2, ← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr ⟨eval k₁ k₂ ^ 2, by ring⟩)
    have hu_unit : IsUnit ((u : RayRing) ^ 2) := u.isUnit.pow 2
    rw [h0] at hu_unit
    have hcard16 : Fintype.card RayRing = 16 := by
      rw [← Fintype.card_congr e]; decide
    haveI : Nontrivial RayRing := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    exact not_isUnit_zero hu_unit
  calc Fintype.card RayRingˣ = (Finset.univ : Finset RayRingˣ).card := rfl
    _ ≤ oddSet.card := Finset.card_le_card_of_injOn φ hmaps (fun _ _ _ _ h => hinj h)
    _ = 12 := hcard12

/-- **12-element modulo-`4` sextic reciprocity:** every `ξ : RayCharacter` agrees across all odd
primary primes `p` with `star (idealRowHom (bad12Elem idx) (Ideal.span {p}))` for some
`idx : Bad12Idx`. -/
theorem rayCharacter_eq_sextic_bad12 (ξ : RayCharacter) :
    ∃ idx : Bad12Idx, ∀ p : O, Prime p → lambda ^ 2 ∣ p - 1 →
      quadraticSupported (Ideal.span {p}) →
      rayMonoid ξ p = star (idealRowHom (bad12Elem idx) (Ideal.span {p})) := by
  have hcard_char : Fintype.card RayCharacter = Fintype.card RayRingˣ := by
    simpa only [Nat.card_eq_fintype_card] using
      MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity RayRing ℂ
  have hcard_idx : Fintype.card Bad12Idx = 12 := by decide
  have hle1 : 12 ≤ Fintype.card RayCharacter := by
    rw [← hcard_idx]
    exact Fintype.card_le_of_injective bad12RayChar bad12RayChar_injective
  have hle2 : Fintype.card RayCharacter ≤ 12 := hcard_char.trans_le card_rayRing_units_le_twelve
  have hcard_eq : Fintype.card Bad12Idx = Fintype.card RayCharacter := by omega
  have hbij : Function.Bijective bad12RayChar :=
    (Fintype.bijective_iff_injective_and_card bad12RayChar).mpr ⟨bad12RayChar_injective, hcard_eq⟩
  obtain ⟨idx, hidx⟩ := hbij.2 ξ
  refine ⟨idx, ?_⟩
  intro p hp hpr hs
  rw [rayMonoid_apply, ← hidx, bad12RayChar_mk, bad12Monoid_eq_star_idealRowHom idx p hp hpr hs]

/-! ### Part II: Sixth-power-free `rowMap` surjectivity and `bad12Elem` `FreeRow` transfer -/

private lemma exists_ideal_sixth_free_split (I : Ideal O) (hI : I ≠ 0) :
    ∃ J A : Ideal O, J ≠ 0 ∧ A ≠ 0 ∧ SixthFree J ∧ I = J * A ^ 6 := by
  have hgen : ∀ s : Multiset (Ideal O), (∀ P ∈ s, Prime P) →
      ∃ J A : Ideal O, J ≠ 0 ∧ A ≠ 0 ∧ SixthFree J ∧ s.prod = J * A ^ 6 := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      intro _
      refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_, by simp only [Multiset.prod_zero, one_pow, mul_one]⟩
      intro P; rw [UniqueFactorizationMonoid.normalizedFactors_one]; simp
    | @cons P s ih =>
      intro hs
      have hp : Prime P := hs P (Multiset.mem_cons_self P s)
      obtain ⟨J', A', hJ'0, hA'0, h6', heq'⟩ :=
        ih (fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ))
      have hnf_P : normalizedFactors P = {P} := by
        rw [normalizedFactors_irreducible hp.irreducible, normalize_eq]
      by_cases hc5 : (normalizedFactors J').count P < 5
      · refine ⟨P * J', A', mul_ne_zero hp.ne_zero hJ'0, hA'0, ?_, ?_⟩
        · intro Q
          rw [normalizedFactors_mul hp.ne_zero hJ'0, hnf_P, Multiset.count_add]
          by_cases hQP : Q = P
          · subst hQP; rw [Multiset.count_singleton_self]; omega
          · rw [Multiset.count_eq_zero.mpr (Multiset.mem_singleton.not.mpr hQP), zero_add]; exact h6' Q
        · rw [Multiset.prod_cons, heq', mul_assoc]
      · have hc_eq5 : (normalizedFactors J').count P = 5 := by
          have := h6' P; omega
        have hle : (5 • {P} : Multiset (Ideal O)) ≤ normalizedFactors J' := by
          rw [Multiset.le_iff_count]
          intro Q
          rw [Multiset.count_nsmul]
          by_cases hQP : Q = P
          · subst hQP; rw [Multiset.count_singleton_self, mul_one, hc_eq5]
          · rw [Multiset.count_eq_zero.mpr (Multiset.mem_singleton.not.mpr hQP), mul_zero]
            exact Nat.zero_le _
        obtain ⟨t, ht_eq⟩ := Multiset.le_iff_exists_add.mp hle
        have ht_prime : ∀ Q ∈ t, Prime Q := fun Q hQ =>
          prime_of_normalized_factor Q (ht_eq ▸ Multiset.mem_add.mpr (Or.inr hQ))
        have ht0 : t.prod ≠ 0 := fun hz =>
          (ht_prime 0 (Multiset.prod_eq_zero_iff.mp hz)).ne_zero rfl
        have hJ'_eq : J' = P ^ 5 * t.prod := by
          calc J' = (normalizedFactors J').prod := (Ideal.prod_normalizedFactors_eq_self hJ'0).symm
            _ = (5 • ({P} : Multiset (Ideal O))).prod * t.prod := by rw [ht_eq, Multiset.prod_add]
            _ = P ^ 5 * t.prod := by rw [Multiset.prod_nsmul, Multiset.prod_singleton]
        have hnf_t : normalizedFactors t.prod = t := by
          apply normalizedFactors_prod_of_prime
          exact ht_prime
        have hcount_t_P : t.count P = 0 := by
          have := congrArg (Multiset.count P) ht_eq
          rw [hc_eq5, Multiset.count_add, Multiset.count_nsmul, Multiset.count_singleton_self, mul_one] at this
          omega
        refine ⟨t.prod, P * A', ht0, mul_ne_zero hp.ne_zero hA'0, ?_, ?_⟩
        · intro Q
          rw [hnf_t]
          by_cases hQP : Q = P
          · subst hQP; omega
          · have := congrArg (Multiset.count Q) ht_eq
            rw [Multiset.count_add, Multiset.count_nsmul,
              Multiset.count_eq_zero.mpr (Multiset.mem_singleton.not.mpr hQP), mul_zero, zero_add] at this
            rw [← this]; exact h6' Q
        · rw [Multiset.prod_cons, heq', hJ'_eq]; ring
  obtain ⟨J, A, hJ0, hA0, h6, heq⟩ :=
    hgen (normalizedFactors I) (fun P hP => prime_of_normalized_factor P hP)
  rw [Ideal.prod_normalizedFactors_eq_self hI] at heq
  exact ⟨J, A, hJ0, hA0, h6, heq⟩

/-- **Unique sixth-power-free factorization (`rowMap` surjectivity):** every nonzero `w : O` equals
`rowMap p = p.1.val * (cubicIdealGenerator p.2.val)^6` for a unique `p : FreeRow × NonzeroIdeal`. -/
theorem exists_rowMap_eq {w : O} (hw : w ≠ 0) :
    ∃ p : FreeRow × NonzeroIdeal, rowMap p = w := by
  have hIw : (Ideal.span {w} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hw
  obtain ⟨J, A, _hJ0, hA0, h6, heq⟩ := exists_ideal_sixth_free_split (Ideal.span {w}) hIw
  let g := cubicIdealGenerator A
  have hg0 : g ≠ 0 := cubicIdealGenerator_ne_zero A hA0
  have hspan_g6 : Ideal.span {g ^ 6} = A ^ 6 := by
    rw [← Ideal.span_singleton_pow, span_cubicIdealGenerator]
  have hdvd_ideal : Ideal.span {g ^ 6} ∣ Ideal.span {w} := by
    rw [hspan_g6, heq]; exact dvd_mul_left (A ^ 6) J
  obtain ⟨u₀, hu₀_eq⟩ := Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp hdvd_ideal
  have hw_eq : w = u₀ * g ^ 6 := by rw [hu₀_eq, mul_comm]
  have hu₀_ne : u₀ ≠ 0 := fun hz => hw (by rw [hw_eq, hz, zero_mul])
  have hspan_eq : Ideal.span {u₀} * A ^ 6 = J * A ^ 6 := by
    calc Ideal.span {u₀} * A ^ 6
        = Ideal.span {u₀} * Ideal.span {g ^ 6} := by rw [hspan_g6]
      _ = Ideal.span {w} := by rw [Ideal.span_singleton_mul_span_singleton, ← hw_eq]
      _ = J * A ^ 6 := heq
  have hnf_eq : normalizedFactors (Ideal.span {u₀}) = normalizedFactors J := by
    have h1 := congrArg normalizedFactors hspan_eq
    rw [normalizedFactors_mul (Ideal.span_singleton_eq_bot.not.mpr hu₀_ne) (pow_ne_zero 6 hA0),
      normalizedFactors_mul _hJ0 (pow_ne_zero 6 hA0)] at h1
    exact add_right_cancel h1
  have hJ_eq : Ideal.span {u₀} = J := by
    rw [← Ideal.prod_normalizedFactors_eq_self (Ideal.span_singleton_eq_bot.not.mpr hu₀_ne),
      hnf_eq, Ideal.prod_normalizedFactors_eq_self _hJ0]
  refine ⟨(⟨u₀, hu₀_ne, hJ_eq ▸ h6⟩, ⟨A, hA0⟩), ?_⟩
  exact hw_eq.symm

lemma absNorm_span_lambda_eq_three : (Ideal.span {lambda} : Ideal O).absNorm = 3 := by
  rw [← Nat.cast_inj (R := ℝ), ← ringComplex_norm_sq_eq_absNorm_span, eval_lambda,
    complex_norm_eval_sq (-1) 1]
  norm_num

lemma absNorm_span_two_eq_four : (Ideal.span {(2 : O)} : Ideal O).absNorm = 4 := by
  rw [← Nat.cast_inj (R := ℝ), ← ringComplex_norm_sq_eq_absNorm_span]
  simp [map_ofNat]; norm_num

/-- Noncomputable sixth-power-free core `(u_tilde, A_bad)` of `bad12Elem idx * u.val`. -/
def bad12FreeSplit (idx : Bad12Idx) (u : FreeRow) : FreeRow × NonzeroIdeal :=
  Classical.choose (exists_rowMap_eq (mul_ne_zero (bad12Elem_ne_zero idx) u.property.1))

lemma bad12FreeSplit_spec (idx : Bad12Idx) (u : FreeRow) :
    rowMap (bad12FreeSplit idx u) = bad12Elem idx * u.val :=
  Classical.choose_spec (exists_rowMap_eq (mul_ne_zero (bad12Elem_ne_zero idx) u.property.1))

/-- **Exact `bad12Elem` `FreeRow` transfer:**
1. `A_bad = (bad12FreeSplit idx u).2.val` belongs to `(fixedBadPrimes.powerset.image (fun E => ∏ P ∈ E, P))`
   (at most `4` ideals, so `u ↦ bad12FreeSplit idx u` is injective and `u ↦ (bad12FreeSplit idx u).1`
   has fiber cardinality `≤ 4`!),
2. `rowNorm u / 2985984 ≤ rowNorm (bad12FreeSplit idx u).1` and
   `rowNorm (bad12FreeSplit idx u).1 ≤ 186624 * rowNorm u`,
3. For every ideal `I` with `quadraticSupported I`,
   `idealRowHom (bad12Elem idx * u.val) I = idealRowHom (bad12FreeSplit idx u).1.val I`! -/
theorem bad12_freeRow_transfer (idx : Bad12Idx) (u : FreeRow) :
    let sp := bad12FreeSplit idx u
    sp.2.val ∈ fixedBadPrimes.powerset.image (fun E => ∏ P ∈ E, P) ∧
      rowNorm u / 2985984 ≤ rowNorm sp.1 ∧
      rowNorm sp.1 ≤ 186624 * rowNorm u ∧
      (∀ I : Ideal O, quadraticSupported I →
        idealRowHom (bad12Elem idx * u.val) I = idealRowHom sp.1.val I) := by
  intro sp
  have hrm := bad12FreeSplit_spec idx u
  have hspan : Ideal.span {sp.1.val} * sp.2.val ^ 6 =
      Ideal.span {bad12Elem idx} * Ideal.span {u.val} := by
    rw [← rowMap_span, hrm, Ideal.span_singleton_mul_span_singleton]
  have hlam_eq : (Ideal.span {lambda} : Ideal O) = ramifiedIdeal := rfl
  have htwo_eq : (Ideal.span {(2 : O)} : Ideal O) = cubicTwoIdeal :=
    (Ideal.span_singleton_neg (2 : O)).symm
  have h4_eq : (Ideal.span {(4 : O)} : Ideal O) = cubicTwoIdeal ^ 2 := by
    rw [← htwo_eq, Ideal.span_singleton_pow]; norm_num
  have hneg_lam : (Ideal.span {-lambda} : Ideal O) = ramifiedIdeal :=
    Ideal.span_singleton_neg lambda
  -- Express `Ideal.span {bad12Elem idx}` as `cubicTwoIdeal ^ (2 * j) * ramifiedIdeal ^ (3 * e)`.
  have hbad_span : ∃ a₂ a₃ : ℕ, a₂ ≤ 4 ∧ a₃ ≤ 6 ∧
      Ideal.span {bad12Elem idx} = cubicTwoIdeal ^ a₂ * ramifiedIdeal ^ a₃ := by
    unfold bad12Elem
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
      ← Ideal.span_singleton_pow, h4_eq, ← pow_mul]
    have hj2 : 2 * idx.1.val ≤ 4 := by omega
    cases idx.2.1 <;> cases idx.2.2
    · refine ⟨2 * idx.1.val, 0, hj2, by decide, ?_⟩
      simp [Ideal.span_singleton_one]
    · refine ⟨2 * idx.1.val, 3, hj2, by decide, ?_⟩
      simp [Ideal.span_singleton_one, ← Ideal.span_singleton_pow, hneg_lam]
    · refine ⟨2 * idx.1.val, 3, hj2, by decide, ?_⟩
      simp [Ideal.span_singleton_one, ← Ideal.span_singleton_pow, hlam_eq]
    · refine ⟨2 * idx.1.val, 6, hj2, by decide, ?_⟩
      simp only [ite_true, ← Ideal.span_singleton_pow, hneg_lam, hlam_eq]
      ring
  obtain ⟨a₂, a₃, ha₂, ha₃, hbad_eq⟩ := hbad_span
  have hIb0 : (Ideal.span {bad12Elem idx} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (bad12Elem_ne_zero idx)
  have hIu0 : (Ideal.span {u.val} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr u.property.1
  have hIsp0 : (Ideal.span {sp.1.val} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr sp.1.property.1
  have hA0 : sp.2.val ≠ 0 := sp.2.property
  have hram0 : (ramifiedIdeal : Ideal O) ≠ 0 := ramifiedIdeal_prime.ne_zero
  have hcub0 : (cubicTwoIdeal : Ideal O) ≠ 0 := quadratic_twoIdeal_prime.ne_zero
  have hnf_bad : normalizedFactors (Ideal.span {bad12Elem idx}) =
      a₂ • ({cubicTwoIdeal} : Multiset (Ideal O)) + a₃ • ({ramifiedIdeal} : Multiset (Ideal O)) := by
    rw [hbad_eq, normalizedFactors_mul (pow_ne_zero a₂ hcub0) (pow_ne_zero a₃ hram0),
      normalizedFactors_pow, normalizedFactors_pow,
      normalizedFactors_irreducible quadratic_twoIdeal_prime.irreducible,
      normalizedFactors_irreducible ramifiedIdeal_prime.irreducible, normalize_eq, normalize_eq]
  have hnf_eq : normalizedFactors (Ideal.span {sp.1.val}) + 6 • normalizedFactors sp.2.val =
      (a₂ • ({cubicTwoIdeal} : Multiset (Ideal O)) + a₃ • ({ramifiedIdeal} : Multiset (Ideal O))) +
        normalizedFactors (Ideal.span {u.val}) := by
    have h := congrArg normalizedFactors hspan
    rwa [normalizedFactors_mul hIsp0 (pow_ne_zero 6 hA0), normalizedFactors_pow,
      normalizedFactors_mul hIb0 hIu0, hnf_bad] at h
  have hram_ne_cub : (ramifiedIdeal : Ideal O) ≠ cubicTwoIdeal := by
    intro heq
    have := congrArg Ideal.absNorm heq
    rw [← hlam_eq, absNorm_span_lambda_eq_three, ← htwo_eq, absNorm_span_two_eq_four] at this
    omega
  -- Count every prime in `sp.2.val`: `0` outside `fixedBadPrimes`, `≤ 1` on `fixedBadPrimes`!
  have hcount_A_out : ∀ P : Ideal O, P ∉ fixedBadPrimes → (normalizedFactors sp.2.val).count P = 0 := by
    intro P hP
    have hPr : P ≠ ramifiedIdeal := fun h => hP (by simp [fixedBadPrimes, h])
    have hPc : P ≠ cubicTwoIdeal := fun h => hP (by simp [fixedBadPrimes, h])
    have hc := congrArg (Multiset.count P) hnf_eq
    have hc1 : ({cubicTwoIdeal} : Multiset (Ideal O)).count P = 0 :=
      Multiset.count_eq_zero.mpr (Multiset.mem_singleton.not.mpr hPc)
    have hc2 : ({ramifiedIdeal} : Multiset (Ideal O)).count P = 0 :=
      Multiset.count_eq_zero.mpr (Multiset.mem_singleton.not.mpr hPr)
    rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_add, Multiset.count_add,
      Multiset.count_nsmul, Multiset.count_nsmul, hc1, hc2] at hc
    have hu6 := u.property.2 P
    omega
  have hcount_A_le1 : ∀ P : Ideal O, (normalizedFactors sp.2.val).count P ≤ 1 := by
    intro P
    by_cases hPr : P = ramifiedIdeal
    · subst hPr
      have hc := congrArg (Multiset.count ramifiedIdeal) hnf_eq
      have hc1 : ({cubicTwoIdeal} : Multiset (Ideal O)).count ramifiedIdeal = 0 :=
        Multiset.count_eq_zero.mpr (Multiset.mem_singleton.not.mpr hram_ne_cub)
      rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_add, Multiset.count_add,
        Multiset.count_nsmul, Multiset.count_nsmul, hc1,
        Multiset.count_singleton_self] at hc
      have hu6 := u.property.2 ramifiedIdeal
      omega
    · by_cases hPc : P = cubicTwoIdeal
      · subst hPc
        have hc := congrArg (Multiset.count cubicTwoIdeal) hnf_eq
        have hc2 : ({ramifiedIdeal} : Multiset (Ideal O)).count cubicTwoIdeal = 0 :=
          Multiset.count_eq_zero.mpr (Multiset.mem_singleton.not.mpr (Ne.symm hram_ne_cub))
        rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_add, Multiset.count_add,
          Multiset.count_nsmul, Multiset.count_nsmul,
          Multiset.count_singleton_self, hc2] at hc
        have hu6 := u.property.2 cubicTwoIdeal
        omega
      · have hPnot : P ∉ fixedBadPrimes := by simp [fixedBadPrimes, hPr, hPc]
        rw [hcount_A_out P hPnot]; exact Nat.zero_le 1
  -- Hence `sp.2.val = ∏ P ∈ E, P` for `E = (normalizedFactors sp.2.val).toFinset ⊆ fixedBadPrimes`.
  let E := (normalizedFactors sp.2.val).toFinset
  have hE_sub : E ⊆ fixedBadPrimes := by
    intro P hP
    by_contra hnot
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hP)).ne' (hcount_A_out P hnot)
  have hA_eq_E : sp.2.val = ∏ P ∈ E, P := by
    have hnodup : (normalizedFactors sp.2.val).Nodup :=
      Multiset.nodup_iff_count_le_one.mpr hcount_A_le1
    calc sp.2.val = (normalizedFactors sp.2.val).prod := (Ideal.prod_normalizedFactors_eq_self hA0).symm
      _ = ∏ P ∈ E, P := by
          change (normalizedFactors sp.2.val).prod = (E.val.map id).prod
          rw [Multiset.map_id, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  have hmem_powerset : sp.2.val ∈ fixedBadPrimes.powerset.image (fun E' => ∏ P ∈ E', P) :=
    Finset.mem_image.mpr ⟨E, Finset.mem_powerset.mpr hE_sub, hA_eq_E.symm⟩
  -- Norm bounds from `hspan` and `1 ≤ sp.2.val.absNorm ≤ 12`, `1 ≤ bad12Elem.absNorm ≤ 186624`.
  have hA_norm_le12 : sp.2.val.absNorm ≤ 12 := by
    rw [hA_eq_E]
    have hprod_le : (∏ P ∈ E, P.absNorm) ≤ ∏ P ∈ fixedBadPrimes, P.absNorm :=
      Finset.prod_le_prod_of_subset_of_one_le' hE_sub (fun P hP _ =>
        Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
          (fixedBadPrimes_prime P hP).ne_zero))
    rw [map_prod]
    refine hprod_le.trans ?_
    unfold fixedBadPrimes
    rw [Finset.prod_pair hram_ne_cub, ← hlam_eq, absNorm_span_lambda_eq_three,
      ← htwo_eq, absNorm_span_two_eq_four]
    decide
  have hbad_norm_le : (Ideal.span {bad12Elem idx}).absNorm ≤ 186624 := by
    rw [hbad_eq, map_mul, map_pow, map_pow, ← htwo_eq, absNorm_span_two_eq_four,
      ← hlam_eq, absNorm_span_lambda_eq_three]
    exact (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) ha₂)
      (Nat.pow_le_pow_right (by decide) ha₃)).trans (by decide)
  have hbad_norm_ge1 : 1 ≤ (Ideal.span {bad12Elem idx}).absNorm :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hIb0)
  have hA_norm_ge1 : 1 ≤ sp.2.val.absNorm :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hA0)
  have hnorm_id : (Ideal.span {sp.1.val}).absNorm * sp.2.val.absNorm ^ 6 =
      (Ideal.span {bad12Elem idx}).absNorm * (Ideal.span {u.val}).absNorm := by
    have h := congrArg Ideal.absNorm hspan
    simpa only [map_mul, map_pow] using h
  have hA6_le : sp.2.val.absNorm ^ 6 ≤ 2985984 :=
    (Nat.pow_le_pow_left hA_norm_le12 6).trans (by decide)
  have hnorm_lo : rowNorm u / 2985984 ≤ rowNorm sp.1 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2985984)]
    unfold rowNorm
    have hnat : (Ideal.span {u.val}).absNorm ≤ 2985984 * (Ideal.span {sp.1.val}).absNorm := by
      have h1 : 1 * (Ideal.span {u.val}).absNorm ≤
          (Ideal.span {bad12Elem idx}).absNorm * (Ideal.span {u.val}).absNorm :=
        Nat.mul_le_mul_right _ hbad_norm_ge1
      rw [one_mul, ← hnorm_id] at h1
      exact h1.trans (by rw [mul_comm]; exact Nat.mul_le_mul_right _ hA6_le)
    exact_mod_cast (by linarith [hnat] :
      (Ideal.span {u.val}).absNorm ≤ (Ideal.span {sp.1.val}).absNorm * 2985984)
  have hnorm_hi : rowNorm sp.1 ≤ 186624 * rowNorm u := by
    unfold rowNorm
    have hnat : (Ideal.span {sp.1.val}).absNorm ≤ 186624 * (Ideal.span {u.val}).absNorm := by
      have h1 : (Ideal.span {sp.1.val}).absNorm * 1 ≤
          (Ideal.span {sp.1.val}).absNorm * sp.2.val.absNorm ^ 6 :=
        Nat.mul_le_mul_left _ (Nat.one_le_pow 6 _ hA_norm_ge1)
      rw [mul_one, hnorm_id] at h1
      exact h1.trans (Nat.mul_le_mul_right _ hbad_norm_le)
    exact_mod_cast hnat
  refine ⟨hmem_powerset, hnorm_lo, hnorm_hi, ?_⟩
  intro I hI
  rw [← hrm]
  unfold rowMap
  rw [idealRowHom_argument_mul, idealRowHom_argument_pow _ _ _ hI.1]
  -- Show `(idealRowHom (cubicIdealGenerator sp.2.val) I) ^ 6 = 1` on `quadraticSupported I`!
  suffices h1 : idealRowHom (cubicIdealGenerator sp.2.val) I ^ 6 = 1 by rw [h1, mul_one]
  -- Prove for every prime factor `P` of `I` via `idealRowHom_prime_sixth_mask`.
  have hrec : ∀ s : Multiset (Ideal O),
      (∀ P ∈ s, primaryIdealGenerator P ≠ 0 ∧ P.IsMaximal ∧ lambda ∉ P ∧ P ∉ fixedBadPrimes) →
      idealRowHom (cubicIdealGenerator sp.2.val) s.prod ^ 6 = 1 := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp only [Multiset.prod_zero, map_one, one_pow]
    | @cons P s ih =>
      intro hs
      obtain ⟨hPgen0, hPmax, hPlam, hPnot⟩ := hs P (Multiset.mem_cons_self P s)
      letI : P.IsMaximal := hPmax
      have hcop : IsCoprime P (Ideal.span {cubicIdealGenerator sp.2.val}) := by
        rw [span_cubicIdealGenerator, hA_eq_E]
        apply IsCoprime.prod_right
        intro Q hQ
        letI : Q.IsMaximal :=
          (Ideal.isPrime_of_prime (fixedBadPrimes_prime Q (hE_sub hQ))).isMaximal
            (fixedBadPrimes_prime Q (hE_sub hQ)).ne_zero
        exact Ideal.isCoprime_of_isMaximal (fun heq => hPnot (heq ▸ hE_sub hQ))
      rw [Multiset.prod_cons, map_mul, mul_pow,
        ← idealRowHom_argument_pow _ 6 P hPgen0,
        idealRowHom_prime_sixth_mask _ P hPlam, if_pos hcop, one_mul]
      exact ih (fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ))
  rw [← Ideal.prod_normalizedFactors_eq_self (primaryIdealGenerator_ne_zero_ideal I hI.1)]
  apply hrec
  intro P hP
  have hd := supported_factors_good I hI P hP
  have hP_ne0 : P ≠ 0 := (prime_of_normalized_factor P hP).ne_zero
  have hPgen0 : primaryIdealGenerator P ≠ 0 := by
    letI : P.IsMaximal := hd.1
    exact primaryIdealGenerator_ne_zero_of_good_factors P hP_ne0 (fun Q hQ => by
      have hpP : Prime P := Ideal.prime_of_isPrime hP_ne0 inferInstance
      rw [normalizedFactors_irreducible hpP.irreducible, normalize_eq] at hQ
      rw [Multiset.mem_singleton.mp hQ]; exact hd.2.1)
  refine ⟨hPgen0, hd.1, hd.2.1, ?_⟩
  intro hbad
  rcases Finset.mem_insert.mp hbad with rfl | hcub
  · exact hd.2.1 (Ideal.mem_span_singleton_self lambda)
  · rw [Finset.mem_singleton.mp hcub] at hd
    have hcard4 : Fintype.card (O ⧸ cubicTwoIdeal) = 4 := by
      letI : Fintype (O ⧸ cubicTwoIdeal) := Fintype.ofFinite _
      rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
        ← htwo_eq, absNorm_span_two_eq_four]
    letI : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field cubicTwoIdeal
    letI : Fintype (O ⧸ cubicTwoIdeal) := Fintype.ofFinite _
    have h20 : (2 : O ⧸ cubicTwoIdeal) = 0 := by
      have hm : (2 : O) ∈ cubicTwoIdeal := by rw [← htwo_eq]; exact Ideal.mem_span_singleton_self 2
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
    exact hd.2.2 ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime (O ⧸ cubicTwoIdeal) _)
      Nat.prime_two).mp ((ringChar.spec (O ⧸ cubicTwoIdeal) 2).mp h20))

/-- Fiber bound `≤ 4`: for fixed `idx : Bad12Idx` and `u_tilde : FreeRow`, at most `4` elements
`u ∈ R` satisfy `(bad12FreeSplit idx u).1 = u_tilde`. -/
theorem bad12FreeSplit_fiber_card_le (idx : Bad12Idx) (R : Finset FreeRow) (u_tilde : FreeRow) :
    (((R.filter (fun u => (bad12FreeSplit idx u).1 = u_tilde)).card : ℕ) : ℝ) ≤ 4 := by
  let B_set := fixedBadPrimes.powerset.image (fun E => ∏ P ∈ E, P)
  have hB_card : B_set.card ≤ 4 := by
    calc B_set.card ≤ fixedBadPrimes.powerset.card := Finset.card_image_le
      _ = 2 ^ fixedBadPrimes.card := Finset.card_powerset _
      _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by
          unfold fixedBadPrimes; exact Finset.card_insert_le _ _)
      _ = 4 := by decide
  let φ : FreeRow → Ideal O := fun u => (bad12FreeSplit idx u).2.val
  have hmaps : ∀ u ∈ R.filter (fun u => (bad12FreeSplit idx u).1 = u_tilde), φ u ∈ B_set :=
    fun u _ => (bad12_freeRow_transfer idx u).1
  have hinj : Set.InjOn φ (R.filter (fun u => (bad12FreeSplit idx u).1 = u_tilde)) := by
    intro u₁ hu₁ u₂ hu₂ hφ
    have h1 : (bad12FreeSplit idx u₁).1 = (bad12FreeSplit idx u₂).1 :=
      (Finset.mem_filter.mp hu₁).2.trans (Finset.mem_filter.mp hu₂).2.symm
    have hsp : bad12FreeSplit idx u₁ = bad12FreeSplit idx u₂ :=
      Prod.ext h1 (Subtype.ext hφ)
    have hmul : bad12Elem idx * u₁.val = bad12Elem idx * u₂.val := by
      rw [← bad12FreeSplit_spec idx u₁, ← bad12FreeSplit_spec idx u₂, hsp]
    exact Subtype.ext (mul_left_cancel₀ (bad12Elem_ne_zero idx) hmul)
  have hc := (Finset.card_le_card_of_injOn φ hmaps hinj).trans hB_card
  exact_mod_cast hc

/-! ### Part III: Unified zero-coprimality nonprincipality on all large `FreeRow`s -/

theorem principal_rowTwist_norm_bound (η χ : Character) (u : FreeRow)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) rowMaskElement 1 u.val n)
    (hp : χ.residue = 1) :
    let supSet := (normalizedFactors (η.modulus * Ideal.span {rowMaskElement} * Ideal.span {(72 : O)})).toFinset
    rowNorm u ≤ 248832 * (HeckeExceptionalRows.bound supSet : ℝ) := by
  intro supSet
  obtain ⟨v, a, b, r, hr_nat, hpr, hx_eq⟩ := exists_supported_numerator_factorization u.val u.property.1
  have hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}) :=
    (CanonicalQuadraticSieve.supported_iff_native _).mpr hr_nat
  have hx : (1 : O) ^ 4 * u.val = (v : O) * lambda ^ a * (2 : O) ^ b * r := by
    rw [one_pow, one_mul, hx_eq]
  have hspan_u : Ideal.span {u.val} =
      Ideal.span {lambda} ^ a * Ideal.span {(2 : O)} ^ b * Ideal.span {r} := by
    rw [hx_eq, mul_assoc ((v : O)), mul_assoc ((v : O)),
      Ideal.span_singleton_mul_left_unit v.isUnit,
      ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_pow, Ideal.span_singleton_pow, mul_assoc]
  have hlam0 : (Ideal.span {lambda} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr residue_lambda_prime.1
  have h20 : (Ideal.span {(2 : O)} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hr0 : (Ideal.span {r} : Ideal O) ≠ 0 := hr.1
  have hnf_u : normalizedFactors (Ideal.span {u.val}) =
      a • normalizedFactors (Ideal.span {lambda}) +
      b • normalizedFactors (Ideal.span {(2 : O)}) +
      normalizedFactors (Ideal.span {r}) := by
    rw [hspan_u, normalizedFactors_mul (mul_ne_zero (pow_ne_zero a hlam0) (pow_ne_zero b h20)) hr0,
      normalizedFactors_mul (pow_ne_zero a hlam0) (pow_ne_zero b h20),
      normalizedFactors_pow, normalizedFactors_pow]
  have hfree_r : ∀ P ∈ normalizedFactors (Ideal.span {r}),
      (normalizedFactors (Ideal.span {r})).count P < 6 := by
    intro P _
    have hc := u.property.2 P
    rw [hnf_u, Multiset.count_add, Multiset.count_add] at hc
    omega
  have ha_lt : a < 6 := by
    have hp_lam : Prime (Ideal.span {lambda} : Ideal O) := ramifiedIdeal_prime
    have hc := u.property.2 (Ideal.span {lambda})
    rw [hnf_u, Multiset.count_add, Multiset.count_add, Multiset.count_nsmul,
      normalizedFactors_irreducible hp_lam.irreducible, normalize_eq, Multiset.count_singleton_self,
      mul_one] at hc
    omega
  have hb_lt : b < 6 := by
    have hspan2 : (Ideal.span {(2 : O)} : Ideal O) = cubicTwoIdeal :=
      (Ideal.span_singleton_neg (2 : O)).symm
    have hp_two : Prime (Ideal.span {(2 : O)} : Ideal O) := hspan2 ▸ quadratic_twoIdeal_prime
    have hc := u.property.2 (Ideal.span {(2 : O)})
    rw [hnf_u, Multiset.count_add, Multiset.count_add, Multiset.count_nsmul, Multiset.count_nsmul,
      normalizedFactors_irreducible hp_two.irreducible, normalize_eq, Multiset.count_singleton_self,
      mul_one] at hc
    omega
  have hfixed := HeckeRowNonprincipal.principal_row_fixed_support η χ
    rowMaskElement 1 u.val rowMaskElement_ne_zero (dvd_mul_left _ _) (dvd_mul_right _ _)
    v a b r hr hpr hx hχ hp hfree_r
  have hsup_prime : ∀ P ∈ supSet, Prime P := fun P hP =>
    prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  have hn_r := HeckeExceptionalRows.row_norm_bound supSet hsup_prime hfixed
  have hnorm_u : (Ideal.span {u.val} : Ideal O).absNorm =
      3 ^ a * 4 ^ b * (Ideal.span {r} : Ideal O).absNorm := by
    rw [hspan_u, map_mul, map_mul, map_pow, map_pow, absNorm_span_lambda_eq_three, absNorm_span_two_eq_four]
  have hab_le : 3 ^ a * 4 ^ b ≤ 248832 := by
    have ha5 : 3 ^ a ≤ 3 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
    have hb5 : 4 ^ b ≤ 4 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.mul_le_mul ha5 hb5).trans (by decide)
  unfold rowNorm
  rw [hnorm_u]
  push_cast
  have h1 : (3 : ℝ) ^ a * (4 : ℝ) ^ b ≤ 248832 := by exact_mod_cast hab_le
  have h2 : ((Ideal.span {r} : Ideal O).absNorm : ℝ) ≤
      (HeckeExceptionalRows.bound supSet : ℝ) := by exact_mod_cast hn_r
  nlinarith [Nat.cast_nonneg (α := ℝ) (Ideal.span {r} : Ideal O).absNorm]

/-- **Zero-coprimality nonprincipality:** eventually in `Z`, EVERY `u : FreeRow` with
`Z ^ d ≤ rowNorm u` (`d > 0`) satisfies `(sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).residue ≠ 1`
for all `j`, with NO coprimality restriction (`calibrationForSet`) on `u`! -/
theorem freeRow_nonprincipal_eventually
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (η : Character) (d : ℝ) (hd : 0 < d) :
    letI : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
    letI : Fintype (RayQuotient.Characters M H) := Fintype.ofFinite _
    ∀ᶠ Z : ℝ in atTop, ∀ u : FreeRow, Z ^ d ≤ rowNorm u →
      ∀ j : Sum Bool (RayQuotient.Characters M H),
        (sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).residue ≠ 1 := by
  letI : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
  letI : Fintype (RayQuotient.Characters M H) := Fintype.ofFinite _
  let η0_f := (fixedSourcePrincipal ∅ (by simp)).product η.inverse
  let η0_t := fixedSourcePrincipal ∅ (by simp)
  let η0_r := fun θ : RayQuotient.Characters M H =>
    (fixedSourcePrincipal ∅ (by simp)).product (HeckeRayQuotient.character M H hH θ).inverse
  let supOf (ψ : Character) :=
    (normalizedFactors (ψ.modulus * Ideal.span {rowMaskElement} * Ideal.span {(72 : O)})).toFinset
  let f_r : RayQuotient.Characters M H → ℝ :=
    fun θ' => 248832 * (HeckeExceptionalRows.bound (supOf (η0_r θ')) : ℝ)
  let B_max : ℝ := max
    (248832 * (HeckeExceptionalRows.bound (supOf η0_f) : ℝ))
    (max (248832 * (HeckeExceptionalRows.bound (supOf η0_t) : ℝ))
      (∑ θ' : RayQuotient.Characters M H, f_r θ'))
  filter_upwards [(tendsto_rpow_atTop hd).eventually (eventually_gt_atTop B_max)] with Z hZ u hu j
  have hgt : B_max < rowNorm u := hZ.trans_le hu
  rcases j with b | θ
  · cases b
    · intro hp
      have hp' := (HeckeFiniteDeletion.principal_iff_of_mask _ _
        (excludePrimes_mask (targetRow η u) S hS)).mp hp
      have hinv : (targetRow η u).inverse.residue = 1 := by
        change (targetRow η u).residue⁻¹ = 1; rw [hp', inv_one]
      have hb := principal_rowTwist_norm_bound η0_f (targetRow η u).inverse u
        (inverse_target_elementCoeff η u) hinv
      have hle : 248832 * (HeckeExceptionalRows.bound (supOf η0_f) : ℝ) ≤ B_max := le_max_left _ _
      linarith
    · intro hp
      have hp_raw : (rawRow u).residue = 1 :=
        (HeckeFiniteDeletion.principal_iff_of_mask _ _
          (excludePrimes_mask (rawRow u) S hS)).mp hp
      have hb := principal_rowTwist_norm_bound η0_t (rawRow u) u
        (rawRow_elementCoeff u) hp_raw
      have hle : 248832 * (HeckeExceptionalRows.bound (supOf η0_t) : ℝ) ≤ B_max :=
        (le_max_left _ _).trans (le_max_right _ _)
      linarith
  · intro hp
    have hinv : (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).inverse.residue = 1 := by
      change (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).residue⁻¹ = 1
      exact congrArg Inv.inv hp |>.trans inv_one
    have hb := principal_rowTwist_norm_bound (η0_r θ)
      (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).inverse u
      (HeckePrimeNonprincipal.inverse_twist_elementCoeff _ _ _ _ _ _ (rawRow_elementCoeff u)) hinv
    have hsub : f_r θ ≤ ∑ θ' : RayQuotient.Characters M H, f_r θ' :=
      Finset.single_le_sum (fun _ _ => by dsimp [f_r]; positivity) (Finset.mem_univ θ)
    have hle : f_r θ ≤ B_max :=
      hsub.trans ((le_max_right _ _).trans (le_max_right _ _))
    linarith

/-! ### Part IV: Total-scale multi-prime `L^2` unpuncturing and exact collision decoupling -/

section TotalScaleUnpunctureAndCollision

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
/-- **Total-scale `L^2` unpuncturing WITH `primeMark S_rem`:**
Because `X = X_unmarked * ∏_{i ∈ S_rem} Z_slot i` is the total product scale, `inputConjugateRow`
is normalized directly by `X⁻¹`: if for every `S'' ⊆ S_rem` and every `0 < X'` with
`X' * ∏_{i ∈ S_rem \ S''} Z_slot i ≤ X`, the unpunctured `L^2` sum normalized by `(X')⁻¹` is at
most `B_sup`, then for ANY finite puncture set `P_punc`, the punctured `L^2` sum normalized by
`X⁻¹` is at most `1024 ^ P_punc.card * B_sup`. -/
theorem inputConjugateRow_markedRadial_unpuncture_total_scale
    (pool P_punc : Finset ι) (Ψ₀ : O →* ℂ) (hΨ1 : ∀ u, ‖Ψ₀ u‖ ≤ 1)
    (S_rem : Finset σ) (lists : σ → Finset ι)
    (hdisj : (S_rem : Set σ).PairwiseDisjoint lists)
    (a : σ → ι → ℂ) (ha : ∀ i ∈ S_rem, ∀ q ∈ lists i, ‖a i q‖ ≤ 1)
    (Z_slot : σ → ℝ) (hZ1 : ∀ i ∈ S_rem, 1 ≤ Z_slot i)
    (hZ_norm : ∀ i ∈ S_rem, ∀ q ∈ lists i, Z_slot i ≤ ‖ringComplex (p q)‖ ^ 2)
    (W : ℝ → ℂ) {b_hi : ℝ} (hb : ∀ y, W y ≠ 0 → y ≤ b_hi)
    (S_w : Finset O) {B_sup : ℝ} (hB : 0 ≤ B_sup) {X : ℝ} (hX : 0 < X)
    (hunpunc : ∀ S'' : Finset σ, S'' ⊆ S_rem → ∀ X' : ℝ, 0 < X' →
      X' * (∏ i ∈ S_rem \ S'', Z_slot i) ≤ X →
      (∑ w ∈ S_w, (X')⁻¹ * ‖inputConjugateRow p
          (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
          pool Ψ₀ 1 1 1
          (fun U => InverseMoment.primeMark S'' lists a U * W (primeProductNorm p U / X')) w‖ ^ 2) ≤
        B_sup) :
    (∑ w ∈ S_w, X⁻¹ * ‖inputConjugateRow p
        (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
        (pool \ P_punc) Ψ₀ 1 1 1
        (fun U => InverseMoment.primeMark S_rem lists a U * W (primeProductNorm p U / X)) w‖ ^ 2) ≤
      (1024 : ℝ) ^ P_punc.card * B_sup := by
  -- Apply `inputConjugateRow_markedRadial_unpuncture_l2_le` with `Z_slot' := fun _ => 1`?
  -- No: we NEED `X' * ∏_{S_rem \ S''} Z_slot ≤ X`! Prove by the same induction on `P_punc`!
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  suffices hgen : ∀ S' : Finset σ, S' ⊆ S_rem → ∀ X₀ : ℝ, 0 < X₀ →
      X₀ * (∏ i ∈ S_rem \ S', Z_slot i) ≤ X →
      (∑ w ∈ S_w, X₀⁻¹ * ‖inputConjugateRow p χ
          (pool \ P_punc) Ψ₀ 1 1 1
          (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / X₀)) w‖ ^ 2) ≤
        (1024 : ℝ) ^ P_punc.card * B_sup by
    exact hgen S_rem Finset.Subset.rfl X hX (by simp)
  -- Re-use `inputConjugateRow_markedRadial_unpuncture_l2_le` by rescaling `W`!
  -- WAIT: look! Replace `W(u / X₀)` by `W̃(u / X_unm)` where `X_unm := X₀ / ∏_{i ∈ S'} Z_slot i`!
  -- Let's check! If `X_unm := X₀ / ∏_{i ∈ S'} Z_slot i`, then `X_unm * ∏_{i ∈ S'} Z_slot i = X₀`!
  -- Wait: in `inputConjugateRow_markedRadial_unpuncture_l2_le`, `W` has argument `primeProductNorm p U / X₀`,
  -- NOT `primeProductNorm p U / (X₀ * ∏_{S'} Z_slot)`!
  -- Let's check: if we pass `Z_unit := fun _ => 1` into `unpuncture_l2_le`, we wouldn't get `Z_slot` in `X'`.
  -- Direct induction on `P_punc` with `C_norm = 1` is even shorter (~95 lines)!
  induction P_punc using Finset.induction_on with
  | empty =>
    intro S' hS' X₀ hX₀ hX₀_le
    simp only [Finset.sdiff_empty, Finset.card_empty, pow_zero, one_mul]
    exact hunpunc S' hS' X₀ hX₀ hX₀_le
  | @insert q P' hqP' ih =>
    intro S' hS' X₀ hX₀ hX₀_le
    have hcard_ins : (insert q P').card = P'.card + 1 := Finset.card_insert_of_notMem hqP'
    rw [hcard_ins, pow_succ']
    have hB' : 0 ≤ (1024 : ℝ) ^ P'.card * B_sup := mul_nonneg (by positivity) hB
    by_cases hq_in : q ∈ pool \ P'
    · have hsdiff : pool \ insert q P' = (pool \ P').erase q := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
      rw [hsdiff]
      let Q_pool := pool \ P'
      let N_q := ‖ringComplex (p q)‖ ^ 2
      obtain ⟨hNq2, _⟩ := prime_norm_rpow_neg_half_sum_le_four p hp q 0
      have hNq_pos : 0 < N_q := by linarith
      let M : ℕ := ⌈b_hi * X₀⌉₊ + 1
      have hterm : b_hi * X₀ < N_q ^ M := by
        calc b_hi * X₀ ≤ (⌈b_hi * X₀⌉₊ : ℝ) := Nat.le_ceil _
          _ < (M : ℝ) := by dsimp [M]; push_cast; linarith
          _ ≤ (2 : ℝ) ^ M := by exact_mod_cast Nat.lt_two_pow_self.le
          _ ≤ N_q ^ M := pow_le_pow_left₀ (by norm_num) hNq2 M
      obtain ⟨_, hgeom4⟩ := prime_norm_rpow_neg_half_sum_le_four p hp q M
      let r := N_q ^ (-1 / 2 : ℝ)
      have hr_pos : 0 < r := Real.rpow_pos_of_pos hNq_pos _
      by_cases hex : ∃ i₀ ∈ S', q ∈ lists i₀
      · obtain ⟨i₀, hi₀, hq_i₀⟩ := hex
        have hZq : Z_slot i₀ ≤ N_q := hZ_norm i₀ (hS' hi₀) q hq_i₀
        let S₀ := S'.erase i₀
        have hS₀_sub : S₀ ⊆ S_rem := (Finset.erase_subset i₀ S').trans hS'
        have hq_not_S₀ : ∀ i ∈ S₀, q ∉ lists i := by
          intro i hi hqi
          obtain ⟨hne, hiS'⟩ := Finset.mem_erase.mp hi
          exact Finset.disjoint_left.mp (hdisj (hS' hiS') (hS' hi₀) hne) hqi hq_i₀
        have hΦ_S₀ : ∀ U ∈ (Q_pool.erase q).powerset,
            InverseMoment.primeMark S₀ lists a (insert q U) = InverseMoment.primeMark S₀ lists a U := by
          intro U _
          unfold InverseMoment.primeMark InverseMoment.primeSlot
          apply Finset.prod_congr rfl; intro i hi
          apply Finset.sum_congr rfl; intro x hx
          have hxq : x ≠ q := fun he => hq_not_S₀ i hi (he ▸ hx)
          simp [Finset.mem_insert, hxq]
        have hΦ_split : ∀ U ∈ (Q_pool.erase q).powerset,
            InverseMoment.primeMark S' lists a (insert q U) =
              InverseMoment.primeMark S' lists a U + a i₀ q * InverseMoment.primeMark S₀ lists a U := by
          intro U hU
          have hqU : q ∉ U := fun h => (Finset.mem_erase.mp (Finset.mem_powerset.mp hU h)).1 rfl
          have hins_S : insert i₀ S₀ = S' := Finset.insert_erase hi₀
          have hnot_i₀ : i₀ ∉ S₀ := Finset.notMem_erase i₀ S'
          conv_lhs => rw [← hins_S]; unfold InverseMoment.primeMark; rw [Finset.prod_insert hnot_i₀]
          conv_rhs => arg 1; rw [← hins_S]; unfold InverseMoment.primeMark; rw [Finset.prod_insert hnot_i₀]
          have hslot : InverseMoment.primeSlot (lists i₀) (a i₀) (insert q U) =
              InverseMoment.primeSlot (lists i₀) (a i₀) U + a i₀ q := by
            unfold InverseMoment.primeSlot
            have h1 : (∑ x ∈ lists i₀, if x ∈ insert q U then a i₀ x else 0) =
                (∑ x ∈ (lists i₀).erase q, if x ∈ insert q U then a i₀ x else 0) +
                  (if q ∈ insert q U then a i₀ q else 0) :=
              (Finset.add_sum_erase (lists i₀) _ hq_i₀).symm.trans (add_comm _ _)
            have h2 : (∑ x ∈ lists i₀, if x ∈ U then a i₀ x else 0) =
                (∑ x ∈ (lists i₀).erase q, if x ∈ U then a i₀ x else 0) +
                  (if q ∈ U then a i₀ q else 0) :=
              (Finset.add_sum_erase (lists i₀) _ hq_i₀).symm.trans (add_comm _ _)
            rw [h1, h2, if_pos (Finset.mem_insert_self q U), if_neg hqU, add_zero]
            congr 1
            apply Finset.sum_congr rfl
            intro x hx
            have hxq : x ≠ q := (Finset.mem_erase.mp hx).1
            simp [Finset.mem_insert, hxq]
          change InverseMoment.primeSlot (lists i₀) (a i₀) (insert q U) *
              InverseMoment.primeMark S₀ lists a (insert q U) =
            InverseMoment.primeSlot (lists i₀) (a i₀) U * InverseMoment.primeMark S₀ lists a U +
              a i₀ q * InverseMoment.primeMark S₀ lists a U
          rw [hslot, hΦ_S₀ U hU]
          ring
        have hnot_Q : q ∉ Q_pool.erase q := fun h => (Finset.mem_erase.mp h).1 rfl
        have hins_Q : insert q (Q_pool.erase q) = Q_pool := Finset.insert_erase hq_in
        have h1 (T : Finset ι) : primeSubsetRow p χ T 1 = 1 := by simp [primeSubsetRow]
        have hstep_S' (Y_s : ℝ) (w : O) :
            let α := Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)
            inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / Y_s)) w =
              inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / Y_s)) w +
              α * inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S' lists a U *
                  W (primeProductNorm p U / (Y_s / N_q))) w +
              (α * a i₀ q) * inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S₀ lists a U *
                  W (primeProductNorm p U / (Y_s / N_q))) w := by
          intro α
          have hpool_sum : ∀ f : Finset ι → ℂ,
              (∑ S ∈ Q_pool.powerset, f S) =
                (∑ S ∈ (Q_pool.erase q).powerset, f S) +
                  ∑ S ∈ (Q_pool.erase q).powerset.image (insert q), f S := by
            intro f
            conv_lhs => rw [← hins_Q, Finset.powerset_insert]
            exact Finset.sum_union (Finset.disjoint_iff_ne.mpr (fun S hS T hT heq => by
              obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hT
              exact hnot_Q ((Finset.mem_powerset.mp hS) (heq ▸ Finset.mem_insert_self q U))))
          unfold inputConjugateRow supportConjugateSum secondInputCoefficient
          simp only [h1, one_pow, mul_one]
          rw [hpool_sum, Finset.sum_image (fun U₁ hU₁ U₂ hU₂ heq => by
            have hq1 : q ∉ U₁ := fun h => hnot_Q ((Finset.mem_powerset.mp hU₁) h)
            have hq2 : q ∉ U₂ := fun h => hnot_Q ((Finset.mem_powerset.mp hU₂) h)
            exact (Finset.erase_insert hq1).symm.trans ((congrArg (fun S => S.erase q) heq).trans
              (Finset.erase_insert hq2)))]
          have hsecond :
              (∑ U ∈ (Q_pool.erase q).powerset,
                supportMobius (insert q U) * (Ψ₀ (∏ i ∈ insert q U, p i) *
                  primeCoprimeMask p (insert q U) 1 *
                  (InverseMoment.primeMark S' lists a (insert q U) *
                    W (primeProductNorm p (insert q U) / Y_s))) *
                  star (primeSubsetRow p χ (insert q U) w)) =
              -(α * ∑ U ∈ (Q_pool.erase q).powerset,
                  supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
                    (InverseMoment.primeMark S' lists a U *
                      W (primeProductNorm p U / (Y_s / N_q)))) * star (primeSubsetRow p χ U w)) -
               ((α * a i₀ q) * ∑ U ∈ (Q_pool.erase q).powerset,
                  supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
                    (InverseMoment.primeMark S₀ lists a U *
                      W (primeProductNorm p U / (Y_s / N_q)))) * star (primeSubsetRow p χ U w)) := by
            rw [Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib,
              ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro U hU
            have hqU : q ∉ U := fun h => hnot_Q ((Finset.mem_powerset.mp hU) h)
            have hd : Disjoint {q} U := Finset.disjoint_singleton_left.mpr hqU
            have hinsU : insert q U = {q} ∪ U := (Finset.singleton_union q U).symm
            have hmob : supportMobius ({q} ∪ U) = -supportMobius U := by
              rw [supportMobius_union {q} U hd]; simp [supportMobius]
            have hprod : Ψ₀ (∏ i ∈ {q} ∪ U, p i) = Ψ₀ (p q) * Ψ₀ (∏ i ∈ U, p i) := by
              rw [Finset.prod_union hd, Finset.prod_singleton, map_mul]
            have hmask : primeCoprimeMask p ({q} ∪ U) 1 =
                primeCoprimeMask p {q} 1 * primeCoprimeMask p U 1 := by
              unfold primeCoprimeMask; exact Finset.prod_union hd
            have hrow : star (primeSubsetRow p χ ({q} ∪ U) w) =
                star (primeSubsetRow p χ {q} w) * star (primeSubsetRow p χ U w) := by
              rw [primeSubsetRow_union p χ {q} U hd, star_mul, mul_comm]
            have hnorm : primeProductNorm p ({q} ∪ U) / Y_s = primeProductNorm p U / (Y_s / N_q) := by
              rw [primeProductNorm_union p {q} U hd]
              have hNq : primeProductNorm p {q} = N_q := by simp [primeProductNorm, N_q]
              rw [hNq, div_div_eq_mul_div, mul_comm]
            rw [hΦ_split U hU, hinsU, hmob, hprod, hmask, hrow, hnorm]
            dsimp [α]; ring
          rw [hsecond]; ring
        have hgeom_S' (w : O) :
            let α := Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)
            inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / X₀)) w =
              (∑ k ∈ Finset.range M, α ^ k *
                inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                  (fun U => InverseMoment.primeMark S' lists a U *
                    W (primeProductNorm p U / (X₀ / N_q ^ k))) w) +
              (∑ k ∈ Finset.range M, (α ^ (k + 1) * a i₀ q) *
                inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                  (fun U => InverseMoment.primeMark S₀ lists a U *
                    W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w) := by
          intro α
          have hrec : ∀ K : ℕ,
              inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                  (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / X₀)) w =
                (∑ k ∈ Finset.range K, α ^ k *
                  inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                    (fun U => InverseMoment.primeMark S' lists a U *
                      W (primeProductNorm p U / (X₀ / N_q ^ k))) w) +
                (∑ k ∈ Finset.range K, (α ^ (k + 1) * a i₀ q) *
                  inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                    (fun U => InverseMoment.primeMark S₀ lists a U *
                      W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w) +
                α ^ K * inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                  (fun U => InverseMoment.primeMark S' lists a U *
                    W (primeProductNorm p U / (X₀ / N_q ^ K))) w := by
            intro K
            induction K with
            | zero => simp
            | succ K ih_K =>
              rw [ih_K, Finset.sum_range_succ, Finset.sum_range_succ, hstep_S' (X₀ / N_q ^ K) w]
              have hdiv : (X₀ / N_q ^ K) / N_q = X₀ / N_q ^ (K + 1) := by rw [div_div, ← pow_succ]
              dsimp only [N_q] at hdiv ⊢
              simp_rw [hdiv]; ring
          rw [hrec M]
          have hrem0 : inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
              (fun U => InverseMoment.primeMark S' lists a U *
                W (primeProductNorm p U / (X₀ / N_q ^ M))) w = 0 := by
            unfold inputConjugateRow supportConjugateSum secondInputCoefficient
            apply Finset.sum_eq_zero; intro U _
            have hU1 : 1 ≤ primeProductNorm p U := primeProductNorm_ge_one p hp U
            have hXM_pos : 0 < X₀ / N_q ^ M := div_pos hX₀ (pow_pos hNq_pos M)
            have hgt : b_hi < primeProductNorm p U / (X₀ / N_q ^ M) := by
              rw [lt_div_iff₀ hXM_pos, mul_div_assoc']
              exact (div_lt_one (pow_pos hNq_pos M)).mpr hterm |>.trans_le hU1
            have hw0 : W (primeProductNorm p U / (X₀ / N_q ^ M)) = 0 := by
              by_contra hne; exact not_le_of_gt hgt (hb _ hne)
            dsimp only; rw [hw0]; ring
          rw [hrem0, mul_zero, add_zero]
        have hpt (w : O) :
            X₀⁻¹ * ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / X₀)) w‖ ^ 2 ≤
              2 * (∑ k ∈ Finset.range M, r ^ k) *
                (∑ k ∈ Finset.range M, r ^ k *
                  ((X₀ / N_q ^ k)⁻¹ * ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                    (fun U => InverseMoment.primeMark S' lists a U *
                      W (primeProductNorm p U / (X₀ / N_q ^ k))) w‖ ^ 2)) +
              2 * (∑ k ∈ Finset.range M, r ^ k) *
                (∑ k ∈ Finset.range M, r ^ k *
                  ((X₀ / N_q ^ (k + 1))⁻¹ *
                    ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                      (fun U => InverseMoment.primeMark S₀ lists a U *
                        W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w‖ ^ 2)) := by
          rw [hgeom_S' w]
          let α := Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)
          have hα1 : ‖α‖ ≤ 1 := by
            dsimp [α]
            have h1 : ‖Ψ₀ (p q)‖ ≤ 1 := hΨ1 _
            have h2 : ‖primeCoprimeMask p {q} 1‖ ≤ 1 := by
              by_cases hd : p q ∣ 1 <;> simp [primeCoprimeMask, hd]
            have h3 : ‖star (primeSubsetRow p χ {q} w)‖ ≤ 1 := by
              rw [norm_star]; exact primeSubsetRow_norm_le_one p χ {q} w
            calc ‖Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)‖
                = ‖Ψ₀ (p q)‖ * ‖primeCoprimeMask p {q} 1‖ * ‖star (primeSubsetRow p χ {q} w)‖ := by
                  rw [norm_mul, norm_mul]
              _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
                  (norm_nonneg _) (by norm_num)
              _ = 1 := by norm_num
          have ha1 : ‖a i₀ q‖ ≤ 1 := ha i₀ (hS' hi₀) q hq_i₀
          let A_sum := ∑ k ∈ Finset.range M, α ^ k *
            inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
              (fun U => InverseMoment.primeMark S' lists a U *
                W (primeProductNorm p U / (X₀ / N_q ^ k))) w
          let B_sum := ∑ k ∈ Finset.range M, (α ^ (k + 1) * a i₀ q) *
            inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
              (fun U => InverseMoment.primeMark S₀ lists a U *
                W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w
          have h2ab : ‖A_sum + B_sum‖ ^ 2 ≤ 2 * ‖A_sum‖ ^ 2 + 2 * ‖B_sum‖ ^ 2 := by
            have htri_ab := norm_add_le A_sum B_sum
            have hsq_ab := pow_le_pow_left₀ (norm_nonneg _) htri_ab 2
            nlinarith [sq_nonneg (‖A_sum‖ - ‖B_sum‖)]
          have hcs_gen (g : ℕ → ℝ) (hg_nn : ∀ k, 0 ≤ g k) :
              (∑ k ∈ Finset.range M, g k) ^ 2 ≤
                (∑ k ∈ Finset.range M, r ^ k) * ∑ k ∈ Finset.range M, r ^ k * (N_q ^ k * g k ^ 2) := by
            have h1 : (∑ k ∈ Finset.range M, g k) =
                ∑ k ∈ Finset.range M, (r ^ k) ^ (1 / 2 : ℝ) *
                  ((r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g k)) := by
              apply Finset.sum_congr rfl; intro k _
              have hr1 : (r ^ k) ^ (1 / 2 : ℝ) * (r ^ k) ^ (1 / 2 : ℝ) = r ^ k := by
                rw [← Real.rpow_add (pow_pos hr_pos k)]; norm_num
              have hr2 : r ^ k * (N_q ^ k) ^ (1 / 2 : ℝ) = 1 := by
                dsimp [r]
                rw [← Real.rpow_natCast, ← Real.rpow_mul hNq_pos.le,
                  ← Real.rpow_natCast N_q k, ← Real.rpow_mul hNq_pos.le, ← Real.rpow_add hNq_pos]
                have : (-1 / 2 : ℝ) * (k : ℝ) + (k : ℝ) * (1 / 2 : ℝ) = 0 := by ring
                rw [this, Real.rpow_zero]
              calc g k = 1 * g k := (one_mul _).symm
                _ = (((r ^ k) ^ (1 / 2 : ℝ) * (r ^ k) ^ (1 / 2 : ℝ)) * (N_q ^ k) ^ (1 / 2 : ℝ)) * g k := by
                    rw [hr1, hr2]
                _ = _ := by ring
            have hcs0 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range M)
              (fun k => (r ^ k) ^ (1 / 2 : ℝ))
              (fun k => (r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g k))
            rw [← h1] at hcs0
            have hsq0 := pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ => hg_nn k)) hcs0 2
            rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
              Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hsq0
            refine hsq0.trans_eq ?_
            congr 1
            · apply Finset.sum_congr rfl; intro k _
              rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (pow_nonneg hr_pos.le k)]; norm_num
            · apply Finset.sum_congr rfl; intro k _
              have hp1 : ((r ^ k) ^ (1 / 2 : ℝ)) ^ 2 = r ^ k := by
                rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (pow_nonneg hr_pos.le k)]; norm_num
              have hp2 : ((N_q ^ k) ^ (1 / 2 : ℝ)) ^ 2 = N_q ^ k := by
                rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (pow_nonneg hNq_pos.le k)]; norm_num
              rw [mul_pow, mul_pow, hp1, hp2]
          let gA : ℕ → ℝ := fun k => ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
            (fun U => InverseMoment.primeMark S' lists a U *
              W (primeProductNorm p U / (X₀ / N_q ^ k))) w‖
          let gB : ℕ → ℝ := fun k => ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
            (fun U => InverseMoment.primeMark S₀ lists a U *
              W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w‖
          have hA_le : ‖A_sum‖ ≤ ∑ k ∈ Finset.range M, gA k :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => by
              rw [norm_mul, norm_pow]
              exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hα1)))
          have hB_le : ‖B_sum‖ ≤ ∑ k ∈ Finset.range M, gB k :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => by
              rw [norm_mul, norm_mul, norm_pow]
              exact mul_le_of_le_one_left (norm_nonneg _)
                ((mul_le_mul (pow_le_one₀ (norm_nonneg _) hα1) ha1 (norm_nonneg _) zero_le_one).trans_eq
                  (one_mul 1))))
          have hA_sq : X₀⁻¹ * ‖A_sum‖ ^ 2 ≤
              (∑ k ∈ Finset.range M, r ^ k) * ∑ k ∈ Finset.range M, r ^ k *
                ((X₀ / N_q ^ k)⁻¹ * gA k ^ 2) := by
            calc X₀⁻¹ * ‖A_sum‖ ^ 2
                ≤ X₀⁻¹ * ((∑ k ∈ Finset.range M, r ^ k) * ∑ k ∈ Finset.range M, r ^ k * (N_q ^ k * gA k ^ 2)) :=
                  mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) hA_le 2).trans
                    (hcs_gen gA (fun _ => norm_nonneg _))) (inv_nonneg.mpr hX₀.le)
              _ = _ := by
                  rw [← mul_assoc, mul_comm X₀⁻¹, mul_assoc, Finset.mul_sum]
                  congr 1; apply Finset.sum_congr rfl; intro k _
                  field_simp [hX₀.ne', (pow_pos hNq_pos k).ne']
          have hB_sq : X₀⁻¹ * ‖B_sum‖ ^ 2 ≤
              (∑ k ∈ Finset.range M, r ^ k) * ∑ k ∈ Finset.range M, r ^ k *
                ((X₀ / N_q ^ (k + 1))⁻¹ * gB k ^ 2) := by
            have hinv_le : X₀⁻¹ ≤ (X₀ / N_q)⁻¹ :=
              inv_anti₀ (div_pos hX₀ hNq_pos) (div_le_self hX₀.le (by linarith))
            calc X₀⁻¹ * ‖B_sum‖ ^ 2
                ≤ (X₀ / N_q)⁻¹ * ((∑ k ∈ Finset.range M, r ^ k) *
                    ∑ k ∈ Finset.range M, r ^ k * (N_q ^ k * gB k ^ 2)) :=
                  mul_le_mul hinv_le ((pow_le_pow_left₀ (norm_nonneg _) hB_le 2).trans
                    (hcs_gen gB (fun _ => norm_nonneg _))) (sq_nonneg _)
                    (inv_nonneg.mpr (div_pos hX₀ hNq_pos).le)
              _ = _ := by
                  rw [← mul_assoc, mul_comm (X₀ / N_q)⁻¹, mul_assoc, Finset.mul_sum]
                  congr 1; apply Finset.sum_congr rfl; intro k _
                  have hdiv : (X₀ / N_q) / N_q ^ k = X₀ / N_q ^ (k + 1) := by
                    rw [div_div, ← pow_succ']
                  rw [← hdiv]
                  field_simp [(div_pos hX₀ hNq_pos).ne', (pow_pos hNq_pos k).ne']
          calc X₀⁻¹ * ‖A_sum + B_sum‖ ^ 2
              ≤ X₀⁻¹ * (2 * ‖A_sum‖ ^ 2 + 2 * ‖B_sum‖ ^ 2) :=
                mul_le_mul_of_nonneg_left h2ab (inv_nonneg.mpr hX₀.le)
            _ = 2 * (X₀⁻¹ * ‖A_sum‖ ^ 2) + 2 * (X₀⁻¹ * ‖B_sum‖ ^ 2) := by ring
            _ ≤ _ := by dsimp only [gA] at hA_sq; dsimp only [gB] at hB_sq; linarith [hA_sq, hB_sq]
        have hsdiff_S₀ : S_rem \ S₀ = insert i₀ (S_rem \ S') := by
          ext x
          simp only [S₀, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
          exact ⟨fun ⟨hxR, hx⟩ => by by_cases hxi : x = i₀; exact Or.inl hxi; exact Or.inr ⟨hxR, fun h => hx ⟨hxi, h⟩⟩,
            fun h => h.elim (fun hxi => by subst hxi; exact ⟨hS' hi₀, fun hc => hc.1 rfl⟩)
              (fun ⟨hxR, hx⟩ => ⟨hxR, fun hc => hx hc.2⟩)⟩
        have hnot_sdiff : i₀ ∉ S_rem \ S' := fun h => (Finset.mem_sdiff.mp h).2 hi₀
        have hA_term (k : ℕ) :
            (∑ w ∈ S_w, (X₀ / N_q ^ k)⁻¹ *
              ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S' lists a U *
                  W (primeProductNorm p U / (X₀ / N_q ^ k))) w‖ ^ 2) ≤
              (1024 : ℝ) ^ P'.card * B_sup := by
          apply ih S' hS' (X₀ / N_q ^ k) (div_pos hX₀ (pow_pos hNq_pos k))
          exact (mul_le_mul_of_nonneg_right
            (div_le_self hX₀.le (one_le_pow₀ (by linarith)))
            (Finset.prod_nonneg (fun i hi => (zero_lt_one.trans_le (hZ1 i (Finset.mem_sdiff.mp hi).1)).le))).trans
            hX₀_le
        have hB_term (k : ℕ) :
            (∑ w ∈ S_w, (X₀ / N_q ^ (k + 1))⁻¹ *
              ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S₀ lists a U *
                  W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w‖ ^ 2) ≤
              16 * ((1024 : ℝ) ^ P'.card * B_sup) := by
          have h1 := inputConjugateRow_erase_invariant_l2 p hg hp Q_pool hq_in Ψ₀ hΨ1
            (InverseMoment.primeMark S₀ lists a) hΦ_S₀ W hb S_w (C_norm := 1) zero_lt_one hB'
            (div_pos hX₀ (pow_pos hNq_pos (k + 1))) (by
              intro X' hX' hX'_le
              simp only [mul_one]
              apply ih S₀ hS₀_sub X' hX'
              rw [hsdiff_S₀, Finset.prod_insert hnot_sdiff, ← mul_assoc]
              have hX'_Z : X' * Z_slot i₀ ≤ X₀ := by
                have hk1 : N_q ≤ N_q ^ (k + 1) := le_self_pow₀ (by linarith) (Nat.succ_ne_zero k)
                have h2 : X' ≤ X₀ / N_q := hX'_le.trans (div_le_div_of_nonneg_left hX₀.le hNq_pos hk1)
                exact (mul_le_mul_of_nonneg_left hZq hX'.le).trans ((le_div_iff₀ hNq_pos).mp h2)
              exact (mul_le_mul_of_nonneg_right hX'_Z
                (Finset.prod_nonneg (fun i hi => (zero_lt_one.trans_le (hZ1 i (Finset.mem_sdiff.mp hi).1)).le))).trans
                hX₀_le)
          simpa only [mul_one] using h1
        calc
          (∑ w ∈ S_w, X₀⁻¹ * ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
              (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / X₀)) w‖ ^ 2)
            ≤ ∑ w ∈ S_w,
                (2 * (∑ k ∈ Finset.range M, r ^ k) *
                  (∑ k ∈ Finset.range M, r ^ k *
                    ((X₀ / N_q ^ k)⁻¹ * ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                      (fun U => InverseMoment.primeMark S' lists a U *
                        W (primeProductNorm p U / (X₀ / N_q ^ k))) w‖ ^ 2)) +
                2 * (∑ k ∈ Finset.range M, r ^ k) *
                  (∑ k ∈ Finset.range M, r ^ k *
                    ((X₀ / N_q ^ (k + 1))⁻¹ *
                      ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                        (fun U => InverseMoment.primeMark S₀ lists a U *
                          W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w‖ ^ 2))) :=
              Finset.sum_le_sum (fun w _ => hpt w)
          _ = 2 * (∑ k ∈ Finset.range M, r ^ k) *
                (∑ k ∈ Finset.range M, r ^ k *
                  ∑ w ∈ S_w, (X₀ / N_q ^ k)⁻¹ *
                    ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                      (fun U => InverseMoment.primeMark S' lists a U *
                        W (primeProductNorm p U / (X₀ / N_q ^ k))) w‖ ^ 2) +
              2 * (∑ k ∈ Finset.range M, r ^ k) *
                (∑ k ∈ Finset.range M, r ^ k *
                  ∑ w ∈ S_w, (X₀ / N_q ^ (k + 1))⁻¹ *
                    ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                      (fun U => InverseMoment.primeMark S₀ lists a U *
                        W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w‖ ^ 2) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
              congr 2
              · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; rw [← Finset.mul_sum]
              · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; rw [← Finset.mul_sum]
          _ ≤ 2 * 4 * (∑ k ∈ Finset.range M, r ^ k * ((1024 : ℝ) ^ P'.card * B_sup)) +
                2 * 4 * (∑ k ∈ Finset.range M, r ^ k * (16 * ((1024 : ℝ) ^ P'.card * B_sup))) := by
              have hgeom4' : (∑ k ∈ Finset.range M, r ^ k) ≤ 4 := hgeom4
              apply add_le_add
              · apply mul_le_mul (by linarith [hgeom4'])
                  (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hA_term k) (pow_nonneg hr_pos.le k)))
                  (Finset.sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hr_pos.le k)
                    (Finset.sum_nonneg (fun _ _ => mul_nonneg
                      (inv_nonneg.mpr (div_pos hX₀ (pow_pos hNq_pos k)).le) (sq_nonneg _)))))
                  (by norm_num)
              · apply mul_le_mul (by linarith [hgeom4'])
                  (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hB_term k) (pow_nonneg hr_pos.le k)))
                  (Finset.sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hr_pos.le k)
                    (Finset.sum_nonneg (fun _ _ => mul_nonneg
                      (inv_nonneg.mpr (div_pos hX₀ (pow_pos hNq_pos (k + 1))).le) (sq_nonneg _)))))
                  (by norm_num)
          _ = 136 * (∑ k ∈ Finset.range M, r ^ k) * ((1024 : ℝ) ^ P'.card * B_sup) := by
              rw [← Finset.sum_mul, ← Finset.sum_mul]; ring
          _ ≤ 136 * 4 * ((1024 : ℝ) ^ P'.card * B_sup) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgeom4 (by norm_num)) hB'
          _ ≤ 1024 * (1024 : ℝ) ^ P'.card * B_sup := by linarith [hB']
      · have hex' : ∀ i ∈ S', q ∉ lists i := fun i hi hqi => hex ⟨i, hi, hqi⟩
        have hΦ_inv : ∀ U ∈ (Q_pool.erase q).powerset,
            InverseMoment.primeMark S' lists a (insert q U) = InverseMoment.primeMark S' lists a U := by
          intro U _
          unfold InverseMoment.primeMark InverseMoment.primeSlot
          apply Finset.prod_congr rfl; intro i hi
          apply Finset.sum_congr rfl; intro x hx
          have hxq : x ≠ q := fun he => hex' i hi (he ▸ hx)
          simp [Finset.mem_insert, hxq]
        have h1 := inputConjugateRow_erase_invariant_l2 p hg hp Q_pool hq_in Ψ₀ hΨ1
          (InverseMoment.primeMark S' lists a) hΦ_inv W hb S_w (C_norm := 1) zero_lt_one hB' hX₀ (by
            intro X' hX' hX'_le
            simp only [mul_one]
            exact ih S' hS' X' hX' ((mul_le_mul_of_nonneg_right hX'_le
              (Finset.prod_nonneg (fun i hi => (zero_lt_one.trans_le (hZ1 i (Finset.mem_sdiff.mp hi).1)).le))).trans
              hX₀_le))
        simp only [mul_one] at h1
        linarith [h1, hB']
    · have hsdiff : pool \ insert q P' = pool \ P' := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        exact ⟨fun ⟨hp_x, hn⟩ => ⟨hp_x, fun h => hn (Or.inr h)⟩,
          fun ⟨hp_x, hn⟩ => ⟨hp_x, fun h => h.elim
            (fun heq => by subst heq; exact hq_in (Finset.mem_sdiff.mpr ⟨hp_x, hn⟩)) hn⟩⟩
      rw [hsdiff]
      linarith [ih S' hS' X₀ hX₀ hX₀_le, hB']

/-- Lattice-point cardinality bound in the Eisenstein integers: every `S_sub : Finset O` with
`∀ n ∈ S_sub, ‖ringComplex n‖ ^ 2 ≤ R` (`1 ≤ R`) has `(S_sub.card : ℝ) ≤ 49 * R`. -/
theorem card_finset_norm_sq_le_49_mul (S_sub : Finset O) {R : ℝ} (hR1 : 1 ≤ R)
    (hS : ∀ n ∈ S_sub, ‖ringComplex n‖ ^ 2 ≤ R) :
    (S_sub.card : ℝ) ≤ 49 * R := by
  have hsqrt1 : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR1
  let m : ℕ := ⌈2 * Real.sqrt R⌉₊
  let rng := Finset.range (2 * m + 1)
  let box : Finset (ℕ × ℕ) := rng ×ˢ rng
  let φ : O → ℕ × ℕ := fun n =>
    (((coords n).1 + (m : ℤ)).toNat, ((coords n).2 + (m : ℤ)).toNat)
  have hcoord_in : ∀ n ∈ S_sub,
      -(m : ℤ) ≤ (coords n).1 ∧ (coords n).1 ≤ (m : ℤ) ∧
      -(m : ℤ) ≤ (coords n).2 ∧ (coords n).2 ≤ (m : ℤ) := by
    intro n hn
    have hn_rt : ‖ringComplex n‖ ≤ Real.sqrt R := by
      calc ‖ringComplex n‖ = Real.sqrt (‖ringComplex n‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt R := Real.sqrt_le_sqrt (hS n hn)
    have hc := (coordinates_norm_le n).trans (mul_le_mul_of_nonneg_left hn_rt (by norm_num))
    rw [Prod.norm_def, max_le_iff] at hc
    have hm_le : 2 * Real.sqrt R ≤ (m : ℝ) := Nat.le_ceil _
    have hc1 : |((coords n).1 : ℝ)| ≤ 2 * Real.sqrt R := by simpa only [Int.norm_eq_abs] using hc.1
    have hc2 : |((coords n).2 : ℝ)| ≤ 2 * Real.sqrt R := by simpa only [Int.norm_eq_abs] using hc.2
    have h1 : (((|(coords n).1| : ℤ) : ℝ)) ≤ ((m : ℤ) : ℝ) := by
      rw [Int.cast_abs, Int.cast_natCast]; exact hc1.trans hm_le
    have h2 : (((|(coords n).2| : ℤ) : ℝ)) ≤ ((m : ℤ) : ℝ) := by
      rw [Int.cast_abs, Int.cast_natCast]; exact hc2.trans hm_le
    have hz1 : |(coords n).1| ≤ (m : ℤ) := Int.cast_le.mp h1
    have hz2 : |(coords n).2| ≤ (m : ℤ) := Int.cast_le.mp h2
    exact ⟨(abs_le.mp hz1).1, (abs_le.mp hz1).2, (abs_le.mp hz2).1, (abs_le.mp hz2).2⟩
  have hmaps : ∀ n ∈ S_sub, φ n ∈ box := by
    intro n hn
    obtain ⟨h1a, h1b, h2a, h2b⟩ := hcoord_in n hn
    dsimp [φ, box, rng]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hinj : Set.InjOn φ S_sub := by
    intro n₁ hn₁ n₂ hn₂ heq
    obtain ⟨h1a₁, _, h2a₁, _⟩ := hcoord_in n₁ hn₁
    obtain ⟨h1a₂, _, h2a₂, _⟩ := hcoord_in n₂ hn₂
    have hp1 := congrArg Prod.fst heq
    have hp2 := congrArg Prod.snd heq
    dsimp [φ] at hp1 hp2
    have hc1 : (coords n₁).1 = (coords n₂).1 := by omega
    have hc2 : (coords n₁).2 = (coords n₂).2 := by omega
    exact coordinateEquiv.injective (Prod.ext hc1 hc2)
  have hcard_nat : S_sub.card ≤ (2 * m + 1) ^ 2 := by
    calc S_sub.card ≤ box.card := Finset.card_le_card_of_injOn φ hmaps hinj
      _ = rng.card * rng.card := Finset.card_product rng rng
      _ = (2 * m + 1) ^ 2 := by rw [Finset.card_range, sq]
  have hm_bound : (m : ℝ) ≤ 2 * Real.sqrt R + 1 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
    · rw [hm0]; push_cast; linarith [Real.sqrt_nonneg R]
    · exact (Nat.ceil_lt_add_one (by positivity)).le
  have h2m1 : (2 * (m : ℝ) + 1) ≤ 7 * Real.sqrt R := by linarith
  calc (S_sub.card : ℝ)
      ≤ ((2 * m + 1 : ℕ) ^ 2 : ℝ) := by exact_mod_cast hcard_nat
    _ = (2 * (m : ℝ) + 1) ^ 2 := by push_cast; ring
    _ ≤ (7 * Real.sqrt R) ^ 2 := pow_le_pow_left₀ (by positivity) h2m1 2
    _ = 49 * (Real.sqrt R) ^ 2 := by ring
    _ = 49 * R := by rw [Real.sq_sqrt (by linarith)]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
/-- Injective-map variant of `card_finset_norm_sq_le_49_mul`: if `p : ι → O` is injective and
`∀ q ∈ L, ‖ringComplex (p q)‖ ^ 2 ≤ R` (`1 ≤ R`), then `(L.card : ℝ) ≤ 49 * R`. -/
theorem card_finset_injective_norm_sq_le_49_mul (hinj_p : Function.Injective p)
    (L : Finset ι) {R : ℝ} (hR1 : 1 ≤ R) (hL : ∀ q ∈ L, ‖ringComplex (p q)‖ ^ 2 ≤ R) :
    (L.card : ℝ) ≤ 49 * R := by
  have heq : L.card = (L.image p).card := (Finset.card_image_of_injective L hinj_p).symm
  rw [heq]
  apply card_finset_norm_sq_le_49_mul (L.image p) hR1
  intro n hn
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
  exact hL q hq

include hp in
/-- Weighted multi-prime `L^2` unpuncturing: for any nonnegative weight `wt : O → ℝ` independent of
scale, puncturing `pool` by `P_punc` increases the scale-supremum `L^2` bound by at most
`16 ^ P_punc.card`. -/
theorem inputConjugateRow_unpuncture_weighted_l2_le
    (pool P_punc : Finset ι) (Ψ₀ : O →* ℂ) (hΨ1 : ∀ u, ‖Ψ₀ u‖ ≤ 1)
    (W : ℝ → ℂ) {b_hi : ℝ} (hb : ∀ y, W y ≠ 0 → y ≤ b_hi)
    (S_w : Finset O) (wt : O → ℝ) (hwt : ∀ w ∈ S_w, 0 ≤ wt w)
    {B_sup : ℝ} (hB : 0 ≤ B_sup) (X : ℝ) (hX : 0 < X)
    (hunpunc : ∀ X' : ℝ, 0 < X' → X' ≤ X →
      (∑ w ∈ S_w, wt w * ((X')⁻¹ * ‖inputConjugateRow p
          (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
          pool Ψ₀ 1 1 1 (fun U => W (primeProductNorm p U / X')) w‖ ^ 2)) ≤ B_sup) :
    (∑ w ∈ S_w, wt w * (X⁻¹ * ‖inputConjugateRow p
        (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
        (pool \ P_punc) Ψ₀ 1 1 1 (fun U => W (primeProductNorm p U / X)) w‖ ^ 2)) ≤
      (16 : ℝ) ^ P_punc.card * B_sup := by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  revert X hunpunc
  induction P_punc using Finset.induction_on with
  | empty =>
    intro X hX hunpunc
    simp only [Finset.sdiff_empty, Finset.card_empty, pow_zero, one_mul]
    exact hunpunc X hX le_rfl
  | @insert q P' hqP' ih =>
    intro X hX hunpunc
    have hcard_ins : (insert q P').card = P'.card + 1 := Finset.card_insert_of_notMem hqP'
    rw [hcard_ins, pow_succ']
    have hB' : 0 ≤ (16 : ℝ) ^ P'.card * B_sup := mul_nonneg (by positivity) hB
    by_cases hq_in : q ∈ pool \ P'
    · have hsdiff : pool \ insert q P' = (pool \ P').erase q := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
      rw [hsdiff]
      let Q_pool := pool \ P'
      let N_q := ‖ringComplex (p q)‖ ^ 2
      obtain ⟨hNq2, _⟩ := prime_norm_rpow_neg_half_sum_le_four p hp q 0
      have hNq_pos : 0 < N_q := by linarith
      let M : ℕ := ⌈b_hi * X⌉₊ + 1
      have hterm : b_hi * X < N_q ^ M := by
        calc b_hi * X ≤ (⌈b_hi * X⌉₊ : ℝ) := Nat.le_ceil _
          _ < (M : ℝ) := by dsimp [M]; push_cast; linarith
          _ ≤ (2 : ℝ) ^ M := by exact_mod_cast Nat.lt_two_pow_self.le
          _ ≤ N_q ^ M := pow_le_pow_left₀ (by norm_num) hNq2 M
      obtain ⟨_, hgeom4⟩ := prime_norm_rpow_neg_half_sum_le_four p hp q M
      let r := N_q ^ (-1 / 2 : ℝ)
      have hr_pos : 0 < r := Real.rpow_pos_of_pos hNq_pos _
      have hpt (w : O) :
          X⁻¹ * ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
              (fun U => W (primeProductNorm p U / X)) w‖ ^ 2 ≤
            (∑ k ∈ Finset.range M, r ^ k) *
              ∑ k ∈ Finset.range M, r ^ k *
                ((X / N_q ^ k)⁻¹ * ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                  (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2) := by
        rw [inputConjugateRow_erase_prime_geom p hg hp Q_pool hq_in Ψ₀ 1 W hb hX w M hterm]
        let α := Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)
        have hα1 : ‖α‖ ≤ 1 := by
          dsimp [α]
          have h1 : ‖Ψ₀ (p q)‖ ≤ 1 := hΨ1 _
          have h2 : ‖primeCoprimeMask p {q} 1‖ ≤ 1 := by
            by_cases hd : p q ∣ 1 <;> simp [primeCoprimeMask, hd]
          have h3 : ‖star (primeSubsetRow p χ {q} w)‖ ≤ 1 := by
            rw [norm_star]; exact primeSubsetRow_norm_le_one p χ {q} w
          calc ‖Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)‖
              = ‖Ψ₀ (p q)‖ * ‖primeCoprimeMask p {q} 1‖ * ‖star (primeSubsetRow p χ {q} w)‖ := by
                rw [norm_mul, norm_mul]
            _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
                (norm_nonneg _) (by norm_num)
            _ = 1 := by norm_num
        let g : ℕ → ℝ := fun k => ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
          (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖
        have hsum_le : ‖∑ k ∈ Finset.range M, α ^ k *
            inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
              (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖ ≤
            ∑ k ∈ Finset.range M, g k :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => by
            rw [norm_mul, norm_pow]
            exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hα1)))
        have h1 : (∑ k ∈ Finset.range M, g k) =
            ∑ k ∈ Finset.range M, (r ^ k) ^ (1 / 2 : ℝ) *
              ((r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g k)) := by
          apply Finset.sum_congr rfl; intro k _
          have hr1 : (r ^ k) ^ (1 / 2 : ℝ) * (r ^ k) ^ (1 / 2 : ℝ) = r ^ k := by
            rw [← Real.rpow_add (pow_pos hr_pos k)]; norm_num
          have hr2 : r ^ k * (N_q ^ k) ^ (1 / 2 : ℝ) = 1 := by
            dsimp [r]
            rw [← Real.rpow_natCast, ← Real.rpow_mul hNq_pos.le,
              ← Real.rpow_natCast N_q k, ← Real.rpow_mul hNq_pos.le, ← Real.rpow_add hNq_pos]
            have : (-1 / 2 : ℝ) * (k : ℝ) + (k : ℝ) * (1 / 2 : ℝ) = 0 := by ring
            rw [this, Real.rpow_zero]
          calc g k = 1 * g k := (one_mul _).symm
            _ = (((r ^ k) ^ (1 / 2 : ℝ) * (r ^ k) ^ (1 / 2 : ℝ)) * (N_q ^ k) ^ (1 / 2 : ℝ)) * g k := by
                rw [hr1, hr2]
            _ = _ := by ring
        have hcs0 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range M)
          (fun k => (r ^ k) ^ (1 / 2 : ℝ))
          (fun k => (r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g k))
        rw [← h1] at hcs0
        have hsq0 := pow_le_pow_left₀ (norm_nonneg _)
          (hsum_le.trans hcs0) 2
        rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
          Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hsq0
        have hcs : ‖∑ k ∈ Finset.range M, α ^ k *
            inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
              (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2 ≤
            (∑ k ∈ Finset.range M, r ^ k) * ∑ k ∈ Finset.range M, r ^ k * (N_q ^ k * g k ^ 2) := by
          refine hsq0.trans_eq ?_
          congr 1
          · apply Finset.sum_congr rfl; intro k _
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (pow_nonneg hr_pos.le k)]; norm_num
          · apply Finset.sum_congr rfl; intro k _
            have hp1 : ((r ^ k) ^ (1 / 2 : ℝ)) ^ 2 = r ^ k := by
              rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (pow_nonneg hr_pos.le k)]; norm_num
            have hp2 : ((N_q ^ k) ^ (1 / 2 : ℝ)) ^ 2 = N_q ^ k := by
              rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (pow_nonneg hNq_pos.le k)]; norm_num
            rw [mul_pow, mul_pow, hp1, hp2]
        calc X⁻¹ * ‖∑ k ∈ Finset.range M, α ^ k *
              inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2
            ≤ X⁻¹ * ((∑ k ∈ Finset.range M, r ^ k) *
                ∑ k ∈ Finset.range M, r ^ k * (N_q ^ k * g k ^ 2)) :=
              mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hX.le)
          _ = _ := by
              rw [← mul_assoc, mul_comm X⁻¹, mul_assoc, Finset.mul_sum]
              congr 1; apply Finset.sum_congr rfl; intro k _
              dsimp only [g, N_q]
              field_simp [hX.ne', (pow_pos hNq_pos k).ne']
      calc
        (∑ w ∈ S_w, wt w * (X⁻¹ * ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
            (fun U => W (primeProductNorm p U / X)) w‖ ^ 2))
          ≤ ∑ w ∈ S_w, wt w * ((∑ k ∈ Finset.range M, r ^ k) *
              ∑ k ∈ Finset.range M, r ^ k *
                ((X / N_q ^ k)⁻¹ * ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                  (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2)) :=
            Finset.sum_le_sum (fun w hw => mul_le_mul_of_nonneg_left (hpt w) (hwt w hw))
        _ = (∑ k ∈ Finset.range M, r ^ k) *
              ∑ k ∈ Finset.range M, r ^ k *
                ∑ w ∈ S_w, wt w * ((X / N_q ^ k)⁻¹ * ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                  (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2) := by
            have hcomm : ∀ w ∈ S_w,
                wt w * ((∑ k ∈ Finset.range M, r ^ k) *
                  ∑ k ∈ Finset.range M, r ^ k *
                    ((X / N_q ^ k)⁻¹ * ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                      (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2)) =
                (∑ k ∈ Finset.range M, r ^ k) *
                  ∑ k ∈ Finset.range M, r ^ k *
                    (wt w * ((X / N_q ^ k)⁻¹ * ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                      (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2)) := by
              intro w _; rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl
              intro k _; ring
            rw [Finset.sum_congr rfl hcomm, ← Finset.mul_sum, Finset.sum_comm]
            congr 1; apply Finset.sum_congr rfl; intro k _; rw [← Finset.mul_sum]
        _ ≤ 4 * ∑ k ∈ Finset.range M, r ^ k * ((16 : ℝ) ^ P'.card * B_sup) := by
            apply mul_le_mul hgeom4
            · apply Finset.sum_le_sum; intro k _
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr_pos.le k)
              exact ih (X / N_q ^ k) (div_pos hX (pow_pos hNq_pos k))
                (fun X' hX' hX'_le => hunpunc X' hX'
                  (hX'_le.trans (div_le_self hX.le (one_le_pow₀ (by linarith)))))
            · exact Finset.sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hr_pos.le k)
                (Finset.sum_nonneg (fun w hw => mul_nonneg (hwt w hw)
                  (mul_nonneg (inv_nonneg.mpr (div_pos hX (pow_pos hNq_pos k)).le) (sq_nonneg _)))))
            · norm_num
        _ = 4 * (∑ k ∈ Finset.range M, r ^ k) * ((16 : ℝ) ^ P'.card * B_sup) := by
            rw [← Finset.sum_mul]; ring
        _ ≤ 4 * 4 * ((16 : ℝ) ^ P'.card * B_sup) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgeom4 (by norm_num)) hB'
        _ = 16 * (16 : ℝ) ^ P'.card * B_sup := by ring
    · have hsdiff : pool \ insert q P' = pool \ P' := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        exact ⟨fun ⟨hp_x, hn⟩ => ⟨hp_x, fun h => hn (Or.inr h)⟩,
          fun ⟨hp_x, hn⟩ => ⟨hp_x, fun h => h.elim
            (fun heq => by subst heq; exact hq_in (Finset.mem_sdiff.mpr ⟨hp_x, hn⟩)) hn⟩⟩
      rw [hsdiff]
      linarith [ih X hX hunpunc, hB']

omit [DecidableEq ι] [DecidableEq σ] in
/-- Single-slot character sum `∑_{q ∈ lists i} a i q * Ψ₀ (p q) * star (primeSubsetRow p χ {q} w)`. -/
def slotCharSum (lists : σ → Finset ι) (a : σ → ι → ℂ) (Ψ₀ : O →* ℂ) (i : σ) (w : O) : ℂ :=
  let χ := fun j => complexSexticChar (Ideal.span {p j}) (hg j)
  ∑ q ∈ lists i, a i q * Ψ₀ (p q) * star (primeSubsetRow p χ {q} w)

/-- Disjoint-tuple sum appearing after log-Fourier separation of `markedRadial`: each tuple
`tup : ∀ i : S_sub, lists i.val` punctures `pool` by `tuplePrimeSet tup`, while `V₀` is evaluated
at the un-marked scale `primeProductNorm p U / X₀`. -/
def disjTupleSum (pool : Finset ι) (S_sub : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Ψ₀ : O →* ℂ) (V₀ : ℝ → ℂ) (X₀ : ℝ) (w : O) : ℂ :=
  let χ := fun j => complexSexticChar (Ideal.span {p j}) (hg j)
  (-1 : ℂ) ^ S_sub.card *
    ∑ tup : (∀ i : S_sub, lists i.val),
      (tupleCoeff a tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
        star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
      inputConjugateRow p χ (pool \ tuplePrimeSet tup) Ψ₀ 1 1 1
        (fun U => V₀ (primeProductNorm p U / X₀)) w

lemma disjTupleSum_empty (pool : Finset ι) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Ψ₀ : O →* ℂ) (V₀ : ℝ → ℂ) (X₀ : ℝ) (w : O) :
    disjTupleSum p hg pool ∅ lists a Ψ₀ V₀ X₀ w =
      inputConjugateRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j))
        pool Ψ₀ 1 1 1 (fun U => V₀ (primeProductNorm p U / X₀)) w := by
  unfold disjTupleSum
  have huniq : Unique (∀ i : (∅ : Finset σ), lists i.val) :=
    { default := fun i => (Finset.notMem_empty i.val i.property).elim
      uniq := fun f => funext (fun i => (Finset.notMem_empty i.val i.property).elim) }
  letI := huniq
  rw [Finset.card_empty, pow_zero, one_mul, Fintype.sum_unique]
  have htp : tuplePrimeSet (default : ∀ i : (∅ : Finset σ), lists i.val) = ∅ := by
    ext x; simp [tuplePrimeSet]
  have htc : tupleCoeff a (default : ∀ i : (∅ : Finset σ), lists i.val) = 1 := by
    simp [tupleCoeff]
  have hpr0 : primeSubsetRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j)) ∅ w = 1 := by
    simp [primeSubsetRow]
  rw [htp, htc, Finset.prod_empty, map_one, hpr0, star_one, Finset.sdiff_empty]
  ring

/-- **Exact one-slot collision recurrence for `disjTupleSum`:**
Peeling a single slot `i₀ ∉ S₀` via `inputConjugateRow_split_prime` splits `disjTupleSum` on
`insert i₀ S₀` into the factored slot product `(- slotCharSum i₀ w) * disjTupleSum pool S₀ ... X₀ w`
minus the collision sum over `q ∈ lists i₀` of `disjTupleSum (pool.erase q) S₀ ... (X₀ / N_q) w`! -/
theorem disjTupleSum_insert
    (pool : Finset ι) {i₀ : σ} {S₀ : Finset σ} (hi₀ : i₀ ∉ S₀)
    (lists : σ → Finset ι) (hpool_i₀ : lists i₀ ⊆ pool)
    (hdisj_i₀ : ∀ i ∈ S₀, Disjoint (lists i₀) (lists i))
    (a : σ → ι → ℂ) (Ψ₀ : O →* ℂ) (V₀ : ℝ → ℂ) (X₀ : ℝ) (w : O) :
    let χ := fun j => complexSexticChar (Ideal.span {p j}) (hg j)
    disjTupleSum p hg pool (insert i₀ S₀) lists a Ψ₀ V₀ X₀ w =
      (- slotCharSum p hg lists a Ψ₀ i₀ w) * disjTupleSum p hg pool S₀ lists a Ψ₀ V₀ X₀ w -
      ∑ q ∈ lists i₀,
        (a i₀ q * (Ψ₀ (p q)) ^ 2 * (star (primeSubsetRow p χ {q} w)) ^ 2) *
          disjTupleSum p hg (pool.erase q) S₀ lists a Ψ₀ V₀ (X₀ / ‖ringComplex (p q)‖ ^ 2) w := by
  intro χ
  have hmask1 (q : ι) : primeCoprimeMask p {q} 1 = 1 := by
    have hnot : ¬ p q ∣ 1 := fun hd =>
      (inferInstance : (Ideal.span {p q}).IsMaximal).ne_top
        (Ideal.span_singleton_eq_top.mpr (isUnit_of_dvd_one hd))
    unfold primeCoprimeMask
    rw [Finset.prod_singleton, if_neg hnot]; norm_num
  let e_pi : lists i₀ × (∀ i : S₀, lists i.val) ≃
      (∀ i : (insert i₀ S₀ : Finset σ), lists i.val) :=
    { toFun := fun pair i =>
        if h : i.val = i₀ then ⟨pair.1.val, h.symm ▸ pair.1.property⟩
        else pair.2 ⟨i.val, (Finset.mem_insert.mp i.property).resolve_left h⟩
      invFun := fun tup =>
        (tup ⟨i₀, Finset.mem_insert_self i₀ S₀⟩,
         fun i => tup ⟨i.val, Finset.mem_insert_of_mem i.property⟩)
      left_inv := fun ⟨q, tup₀⟩ => by
        apply Prod.ext
        · apply Subtype.ext; dsimp; rw [dif_pos rfl]
        · ext i
          have hne : i.val ≠ i₀ := fun he => hi₀ (he ▸ i.property)
          dsimp; rw [dif_neg hne]
      right_inv := fun tup => by
        ext ⟨iv, hiv⟩
        by_cases h : iv = i₀
        · subst h; dsimp; rw [dif_pos rfl]
        · dsimp; rw [dif_neg h] }
  have hset (q : lists i₀) (tup₀ : ∀ i : S₀, lists i.val) :
      tuplePrimeSet (e_pi (q, tup₀)) = insert q.val (tuplePrimeSet tup₀) := by
    ext x
    simp only [tuplePrimeSet, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨⟨iv, hiv⟩, rfl⟩
      dsimp [e_pi]
      split_ifs with h
      · left; rfl
      · right; exact ⟨⟨iv, (Finset.mem_insert.mp hiv).resolve_left h⟩, rfl⟩
    · rintro (rfl | ⟨⟨iv, hiv⟩, rfl⟩)
      · refine ⟨⟨i₀, Finset.mem_insert_self i₀ S₀⟩, ?_⟩
        dsimp [e_pi]; rw [dif_pos rfl]
      · have hne : iv ≠ i₀ := fun he => hi₀ (he ▸ hiv)
        refine ⟨⟨iv, Finset.mem_insert_of_mem hiv⟩, ?_⟩
        dsimp [e_pi]; rw [dif_neg hne]
  have hq_not_Q₀ (q : lists i₀) (tup₀ : ∀ i : S₀, lists i.val) :
      q.val ∉ tuplePrimeSet tup₀ := by
    intro hmem
    obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hmem
    exact Finset.disjoint_left.mp (hdisj_i₀ i.val i.property) q.property (heq ▸ (tup₀ i).property)
  have htc (q : lists i₀) (tup₀ : ∀ i : S₀, lists i.val) :
      tupleCoeff a (e_pi (q, tup₀)) = a i₀ q.val * tupleCoeff a tup₀ := by
    let g_idx : σ → ℂ := fun x =>
      if hx : x ∈ insert i₀ S₀ then a x (e_pi (q, tup₀) ⟨x, hx⟩).val else 1
    have h1 : tupleCoeff a (e_pi (q, tup₀)) = ∏ x ∈ insert i₀ S₀, g_idx x := by
      unfold tupleCoeff
      rw [← Finset.prod_coe_sort (insert i₀ S₀) g_idx]
      apply Finset.prod_congr rfl; intro i _; dsimp only [g_idx]; rw [dif_pos i.property]
    rw [h1, Finset.prod_insert hi₀]
    congr 1
    · dsimp only [g_idx]; rw [dif_pos (Finset.mem_insert_self i₀ S₀)]
      have he1 : e_pi (q, tup₀) ⟨i₀, Finset.mem_insert_self i₀ S₀⟩ = q := by
        apply Subtype.ext; dsimp [e_pi]; rw [dif_pos rfl]
      rw [he1]
    · unfold tupleCoeff
      rw [← Finset.prod_coe_sort S₀ g_idx]
      apply Finset.prod_congr rfl; intro i _
      have hne : i.val ≠ i₀ := fun he => hi₀ (he ▸ i.property)
      dsimp only [g_idx]; rw [dif_pos (Finset.mem_insert_of_mem i.property)]
      have he2 : e_pi (q, tup₀) ⟨i.val, Finset.mem_insert_of_mem i.property⟩ = tup₀ i := by
        change (if h : i.val = i₀ then _ else tup₀ ⟨i.val, _⟩) = tup₀ i
        rw [dif_neg hne]
      rw [he2]
  unfold disjTupleSum
  dsimp only
  rw [Finset.card_insert_of_notMem hi₀, pow_succ', ← e_pi.sum_comp, Fintype.sum_prod_type]
  -- Expand each `(q, tup₀)` summand via `inputConjugateRow_split_prime`.
  have hterm (q : lists i₀) (tup₀ : ∀ i : S₀, lists i.val) :
      (tupleCoeff a (e_pi (q, tup₀)) * Ψ₀ (∏ j ∈ tuplePrimeSet (e_pi (q, tup₀)), p j) *
          star (primeSubsetRow p χ (tuplePrimeSet (e_pi (q, tup₀))) w)) *
        inputConjugateRow p χ (pool \ tuplePrimeSet (e_pi (q, tup₀))) Ψ₀ 1 1 1
          (fun U => V₀ (primeProductNorm p U / X₀)) w =
      (a i₀ q.val * Ψ₀ (p q.val) * star (primeSubsetRow p χ {q.val} w)) *
        ((tupleCoeff a tup₀ * Ψ₀ (∏ j ∈ tuplePrimeSet tup₀, p j) *
            star (primeSubsetRow p χ (tuplePrimeSet tup₀) w)) *
          inputConjugateRow p χ (pool \ tuplePrimeSet tup₀) Ψ₀ 1 1 1
            (fun U => V₀ (primeProductNorm p U / X₀)) w) +
      (a i₀ q.val * (Ψ₀ (p q.val)) ^ 2 * (star (primeSubsetRow p χ {q.val} w)) ^ 2) *
        ((tupleCoeff a tup₀ * Ψ₀ (∏ j ∈ tuplePrimeSet tup₀, p j) *
            star (primeSubsetRow p χ (tuplePrimeSet tup₀) w)) *
          inputConjugateRow p χ ((pool.erase q.val) \ tuplePrimeSet tup₀) Ψ₀ 1 1 1
            (fun U => V₀ (primeProductNorm p U / (X₀ / ‖ringComplex (p q.val)‖ ^ 2))) w) := by
    let Q₀ := tuplePrimeSet tup₀
    have hnot : q.val ∉ Q₀ := hq_not_Q₀ q tup₀
    have hq_in : q.val ∈ pool \ Q₀ := Finset.mem_sdiff.mpr ⟨hpool_i₀ q.property, hnot⟩
    have hsdiff1 : pool \ insert q.val Q₀ = (pool \ Q₀).erase q.val := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
    have hsdiff2 : (pool \ Q₀).erase q.val = (pool.erase q.val) \ Q₀ := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
    have hprod_p : Ψ₀ (∏ j ∈ insert q.val Q₀, p j) = Ψ₀ (p q.val) * Ψ₀ (∏ j ∈ Q₀, p j) := by
      rw [Finset.prod_insert hnot, map_mul]
    have hprod_r : star (primeSubsetRow p χ (insert q.val Q₀) w) =
        star (primeSubsetRow p χ {q.val} w) * star (primeSubsetRow p χ Q₀ w) := by
      have hd : Disjoint {q.val} Q₀ := Finset.disjoint_singleton_left.mpr hnot
      rw [← Finset.singleton_union, primeSubsetRow_union p χ {q.val} Q₀ hd, star_mul, mul_comm]
    rw [hset q tup₀, htc q tup₀, hprod_p, hprod_r, hsdiff1,
      inputConjugateRow_split_prime p hg (pool \ Q₀) hq_in Ψ₀ 1 V₀ X₀ w, hsdiff2]
    rw [hmask1 q.val]
    ring
  have h1_sum :
      (∑ q : lists i₀, ∑ tup₀ : (∀ i : S₀, lists i.val),
        (a i₀ q.val * Ψ₀ (p q.val) * star (primeSubsetRow p χ {q.val} w)) *
          ((tupleCoeff a tup₀ * Ψ₀ (∏ j ∈ tuplePrimeSet tup₀, p j) *
              star (primeSubsetRow p χ (tuplePrimeSet tup₀) w)) *
            inputConjugateRow p χ (pool \ tuplePrimeSet tup₀) Ψ₀ 1 1 1
              (fun U => V₀ (primeProductNorm p U / X₀)) w)) =
      (∑ q ∈ lists i₀, a i₀ q * Ψ₀ (p q) * star (primeSubsetRow p χ {q} w)) *
        ∑ tup₀ : (∀ i : S₀, lists i.val),
          (tupleCoeff a tup₀ * Ψ₀ (∏ j ∈ tuplePrimeSet tup₀, p j) *
            star (primeSubsetRow p χ (tuplePrimeSet tup₀) w)) *
          inputConjugateRow p χ (pool \ tuplePrimeSet tup₀) Ψ₀ 1 1 1
            (fun U => V₀ (primeProductNorm p U / X₀)) w := by
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_coe_sort (lists i₀)
      (fun q => (a i₀ q * Ψ₀ (p q) * star (primeSubsetRow p χ {q} w)) *
        ∑ tup₀ : (∀ i : S₀, lists i.val),
          (tupleCoeff a tup₀ * Ψ₀ (∏ j ∈ tuplePrimeSet tup₀, p j) *
            star (primeSubsetRow p χ (tuplePrimeSet tup₀) w)) *
          inputConjugateRow p χ (pool \ tuplePrimeSet tup₀) Ψ₀ 1 1 1
            (fun U => V₀ (primeProductNorm p U / X₀)) w),
      ← Finset.sum_mul]
  have h2_sum :
      (∑ q : lists i₀, ∑ tup₀ : (∀ i : S₀, lists i.val),
        (a i₀ q.val * (Ψ₀ (p q.val)) ^ 2 * (star (primeSubsetRow p χ {q.val} w)) ^ 2) *
          ((tupleCoeff a tup₀ * Ψ₀ (∏ j ∈ tuplePrimeSet tup₀, p j) *
              star (primeSubsetRow p χ (tuplePrimeSet tup₀) w)) *
            inputConjugateRow p χ ((pool.erase q.val) \ tuplePrimeSet tup₀) Ψ₀ 1 1 1
              (fun U => V₀ (primeProductNorm p U / (X₀ / ‖ringComplex (p q.val)‖ ^ 2))) w)) =
      ∑ q ∈ lists i₀,
        (a i₀ q * (Ψ₀ (p q)) ^ 2 * (star (primeSubsetRow p χ {q} w)) ^ 2) *
          ∑ tup₀ : (∀ i : S₀, lists i.val),
            (tupleCoeff a tup₀ * Ψ₀ (∏ j ∈ tuplePrimeSet tup₀, p j) *
              star (primeSubsetRow p χ (tuplePrimeSet tup₀) w)) *
            inputConjugateRow p χ ((pool.erase q) \ tuplePrimeSet tup₀) Ψ₀ 1 1 1
              (fun U => V₀ (primeProductNorm p U / (X₀ / ‖ringComplex (p q)‖ ^ 2))) w := by
    simp_rw [← Finset.mul_sum]
    exact Finset.sum_coe_sort (lists i₀)
      (fun q => (a i₀ q * (Ψ₀ (p q)) ^ 2 * (star (primeSubsetRow p χ {q} w)) ^ 2) *
        ∑ tup₀ : (∀ i : S₀, lists i.val),
          (tupleCoeff a tup₀ * Ψ₀ (∏ j ∈ tuplePrimeSet tup₀, p j) *
            star (primeSubsetRow p χ (tuplePrimeSet tup₀) w)) *
          inputConjugateRow p χ ((pool.erase q) \ tuplePrimeSet tup₀) Ψ₀ 1 1 1
            (fun U => V₀ (primeProductNorm p U / (X₀ / ‖ringComplex (p q)‖ ^ 2))) w)
  dsimp only [χ] at hterm h1_sum h2_sum ⊢
  simp_rw [hterm, Finset.sum_add_distrib]
  rw [h1_sum, h2_sum]
  unfold slotCharSum
  dsimp only
  rw [mul_add, sub_eq_add_neg]
  congr 1
  · ring
  · rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro q _; ring

include hp in
/-- **Multi-slot collision-decoupling `L^2` theorem:**
Peeling `S_sub` one slot at a time via `disjTupleSum_insert` and unpuncturing the base case
`S_sub = ∅` via `inputConjugateRow_unpuncture_weighted_l2_le` bounds the `L^2` norm of
`disjTupleSum` by `(307330 : ℝ) ^ S_sub.card * 16 ^ P_punc.card * B_sup` purely in terms of
unpunctured factored products `(inputConjugateRow pool ... X' w) * ∏_{j ∈ T'} slotCharSum j w`! -/
theorem disjTupleSum_l2_le_factored
    (hinj_p : Function.Injective p)
    (pool P_punc : Finset ι) (Ψ₀ : O →* ℂ) (hΨ1 : ∀ u, ‖Ψ₀ u‖ ≤ 1)
    (S_sub T_ext : Finset σ) (hST_disj : Disjoint S_sub T_ext)
    (lists : σ → Finset ι)
    (hlists_pool : ∀ i ∈ S_sub, lists i ⊆ pool \ P_punc)
    (hdisj : ((S_sub ∪ T_ext : Finset σ) : Set σ).PairwiseDisjoint lists)
    (a : σ → ι → ℂ) (ha : ∀ i ∈ S_sub, ∀ q ∈ lists i, ‖a i q‖ ≤ 1)
    (Z_slot : σ → ℝ) (hZ1 : ∀ i ∈ S_sub ∪ T_ext, 1 ≤ Z_slot i)
    (hZ_lo : ∀ i ∈ S_sub, ∀ q ∈ lists i, Z_slot i ≤ ‖ringComplex (p q)‖ ^ 2)
    (hZ_hi : ∀ i ∈ S_sub, ∀ q ∈ lists i, ‖ringComplex (p q)‖ ^ 2 ≤ 2 * Z_slot i)
    (V₀ : ℝ → ℂ) {b_hi : ℝ} (hb : ∀ y, V₀ y ≠ 0 → y ≤ b_hi)
    (S_w : Finset O) {B_sup : ℝ} (hB : 0 ≤ B_sup) (X₀ : ℝ) (hX₀ : 0 < X₀)
    (hfactored : ∀ T' : Finset σ, T' ⊆ S_sub ∪ T_ext → ∀ X' : ℝ, 0 < X' → X' ≤ X₀ →
      (∑ w ∈ S_w, (X' * ∏ j ∈ T', Z_slot j)⁻¹ *
        ‖inputConjugateRow p (fun j => complexSexticChar (Ideal.span {p j}) (hg j))
            pool Ψ₀ 1 1 1 (fun U => V₀ (primeProductNorm p U / X')) w *
          ∏ j ∈ T', slotCharSum p hg lists a Ψ₀ j w‖ ^ 2) ≤ B_sup) :
    (∑ w ∈ S_w, (X₀ * ∏ i ∈ S_sub ∪ T_ext, Z_slot i)⁻¹ *
      ‖disjTupleSum p hg (pool \ P_punc) S_sub lists a Ψ₀ V₀ X₀ w *
        ∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2) ≤
      (307330 : ℝ) ^ S_sub.card * (16 : ℝ) ^ P_punc.card * B_sup := by
  let χ := fun j => complexSexticChar (Ideal.span {p j}) (hg j)
  revert P_punc T_ext X₀
  induction S_sub using Finset.induction_on with
  | empty =>
    intro P_punc T_ext hST_disj hlists_pool hdisj hZ1 X₀ hX₀ hfactored
    simp only [Finset.empty_union, Finset.card_empty, pow_zero, one_mul] at hfactored ⊢
    have hempty (w' : O) := disjTupleSum_empty p hg (pool \ P_punc) lists a Ψ₀ V₀ X₀ w'
    simp_rw [hempty]
    let wt : O → ℝ := fun w =>
      (∏ j ∈ T_ext, Z_slot j)⁻¹ * ‖∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2
    have hZprod_pos : 0 < ∏ j ∈ T_ext, Z_slot j :=
      Finset.prod_pos (fun j hj => zero_lt_one.trans_le (hZ1 j (Finset.mem_union_right _ hj)))
    have hwt_nn : ∀ w ∈ S_w, 0 ≤ wt w := fun _ _ =>
      mul_nonneg (inv_nonneg.mpr hZprod_pos.le) (sq_nonneg _)
    have hrew (X' : ℝ) (w : O) :
        (X' * ∏ j ∈ T_ext, Z_slot j)⁻¹ *
          ‖inputConjugateRow p χ (pool \ P_punc) Ψ₀ 1 1 1
              (fun U => V₀ (primeProductNorm p U / X')) w *
            ∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2 =
        wt w * ((X')⁻¹ * ‖inputConjugateRow p χ (pool \ P_punc) Ψ₀ 1 1 1
              (fun U => V₀ (primeProductNorm p U / X')) w‖ ^ 2) := by
      dsimp [wt]; rw [mul_inv, norm_mul, mul_pow]; ring
    have hrew0 (X' : ℝ) (w : O) :
        wt w * ((X')⁻¹ * ‖inputConjugateRow p χ pool Ψ₀ 1 1 1
              (fun U => V₀ (primeProductNorm p U / X')) w‖ ^ 2) =
        (X' * ∏ j ∈ T_ext, Z_slot j)⁻¹ *
          ‖inputConjugateRow p χ pool Ψ₀ 1 1 1
              (fun U => V₀ (primeProductNorm p U / X')) w *
            ∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2 := by
      dsimp [wt]; rw [mul_inv, norm_mul, mul_pow]; ring
    rw [Finset.sum_congr rfl (fun w _ => hrew X₀ w)]
    apply inputConjugateRow_unpuncture_weighted_l2_le p hp hg pool P_punc Ψ₀ hΨ1 V₀ hb
      S_w wt hwt_nn hB X₀ hX₀
    intro X' hX' hX'_le
    rw [Finset.sum_congr rfl (fun w _ => hrew0 X' w)]
    exact hfactored T_ext Finset.Subset.rfl X' hX' hX'_le
  | @insert i₀ S₀ hi₀ ih =>
    intro P_punc T_ext hST_disj hlists_pool hdisj hZ1 X₀ hX₀ hfactored
    have hi₀_not_T : i₀ ∉ T_ext :=
      Finset.disjoint_left.mp hST_disj (Finset.mem_insert_self i₀ S₀)
    have hS₀T_disj : Disjoint S₀ T_ext :=
      Disjoint.mono_left (Finset.subset_insert i₀ S₀) hST_disj
    have hS₀_insT_disj : Disjoint S₀ (insert i₀ T_ext) :=
      Finset.disjoint_insert_right.mpr ⟨hi₀, hS₀T_disj⟩
    have hunion_eq : insert i₀ S₀ ∪ T_ext = S₀ ∪ insert i₀ T_ext := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    have hpool_i₀ : lists i₀ ⊆ pool \ P_punc :=
      hlists_pool i₀ (Finset.mem_insert_self i₀ S₀)
    have hdisj_i₀ : ∀ i ∈ S₀, Disjoint (lists i₀) (lists i) := fun i hi =>
      hdisj (Finset.mem_union_left _ (Finset.mem_insert_self i₀ S₀))
        (Finset.mem_union_left _ (Finset.mem_insert_of_mem hi))
        (fun he => hi₀ (he ▸ hi))
    have hZi₀_1 : 1 ≤ Z_slot i₀ :=
      hZ1 i₀ (Finset.mem_union_left _ (Finset.mem_insert_self i₀ S₀))
    have hZi₀_pos : 0 < Z_slot i₀ := zero_lt_one.trans_le hZi₀_1
    have hZprod_S₀T : 0 < ∏ i ∈ S₀ ∪ T_ext, Z_slot i :=
      Finset.prod_pos (fun i hi => zero_lt_one.trans_le (hZ1 i (by
        rcases Finset.mem_union.mp hi with h1 | h2
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h1)
        · exact Finset.mem_union_right _ h2)))
    have hprod_split : (∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i) =
        Z_slot i₀ * ∏ i ∈ S₀ ∪ T_ext, Z_slot i := by
      have h1 : insert i₀ S₀ ∪ T_ext = insert i₀ (S₀ ∪ T_ext) := Finset.insert_union i₀ S₀ T_ext
      have hnot : i₀ ∉ S₀ ∪ T_ext := fun hm => by
        rcases Finset.mem_union.mp hm with hS | hT
        · exact hi₀ hS
        · exact hi₀_not_T hT
      rw [h1, Finset.prod_insert hnot]
    have hcard_L : ((lists i₀).card : ℝ) ≤ 98 * Z_slot i₀ := by
      have h1 := card_finset_injective_norm_sq_le_49_mul p hinj_p (lists i₀)
        (R := 2 * Z_slot i₀) (by linarith)
        (hZ_hi i₀ (Finset.mem_insert_self i₀ S₀))
      linarith
    -- Pointwise Cauchy-Schwarz bound on `disjTupleSum_insert * P_ext`.
    let P_ext : O → ℂ := fun w => ∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w
    have hpt (w : O) :
        (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ *
            ‖disjTupleSum p hg (pool \ P_punc) (insert i₀ S₀) lists a Ψ₀ V₀ X₀ w * P_ext w‖ ^ 2 ≤
          2 * ((X₀ * ∏ i ∈ S₀ ∪ insert i₀ T_ext, Z_slot i)⁻¹ *
            ‖disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
              ∏ j ∈ insert i₀ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2) +
          2 * ((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹ ^ 2 *
            ∑ q ∈ lists i₀,
              (((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ *
                ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                    (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) := by
      rw [disjTupleSum_insert p hg (pool \ P_punc) hi₀ lists hpool_i₀ hdisj_i₀ a Ψ₀ V₀ X₀ w,
        sub_mul]
      set A := (-slotCharSum p hg lists a Ψ₀ i₀ w) *
        disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w * P_ext w
      set B := (∑ q ∈ lists i₀,
        (a i₀ q * (Ψ₀ (p q)) ^ 2 * (star (primeSubsetRow p χ {q} w)) ^ 2) *
          disjTupleSum p hg ((pool \ P_punc).erase q) S₀ lists a Ψ₀ V₀
            (X₀ / ‖ringComplex (p q)‖ ^ 2) w) * P_ext w
      have h2ab : ‖A - B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
        have ht := norm_sub_le A B
        have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
        nlinarith [sq_nonneg (‖A‖ - ‖B‖)]
      have hA_eq : ‖A‖ = ‖disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
          ∏ j ∈ insert i₀ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ := by
        dsimp [A, P_ext]
        rw [Finset.prod_insert hi₀_not_T,
          show (-slotCharSum p hg lists a Ψ₀ i₀ w) *
              disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
              ∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w =
            -(disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
              (slotCharSum p hg lists a Ψ₀ i₀ w *
                ∏ j ∈ T_ext, slotCharSum p hg lists a Ψ₀ j w)) by ring,
          norm_neg]
      have hB_sq : ‖B‖ ^ 2 ≤ ((lists i₀).card : ℝ) *
          ∑ q ∈ lists i₀,
            ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
              (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2 := by
        dsimp [B]
        rw [Finset.sum_mul]
        apply (norm_sum_sq_le_card_sum_norm_sq (lists i₀) _).trans
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum; intro q hq
        have hsdiff_q : (pool \ P_punc).erase q = pool \ insert q P_punc := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto
        rw [hsdiff_q, mul_assoc, norm_mul, mul_pow]
        have hβ1 : ‖a i₀ q * (Ψ₀ (p q)) ^ 2 * (star (primeSubsetRow p χ {q} w)) ^ 2‖ ≤ 1 := by
          have h1 : ‖a i₀ q‖ ≤ 1 := ha i₀ (Finset.mem_insert_self i₀ S₀) q hq
          have h2 : ‖(Ψ₀ (p q)) ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hΨ1 _)
          have h3 : ‖(star (primeSubsetRow p χ {q} w)) ^ 2‖ ≤ 1 := by
            rw [norm_pow, norm_star]; exact pow_le_one₀ (norm_nonneg _) (primeSubsetRow_norm_le_one p χ {q} w)
          rw [norm_mul, norm_mul]
          exact (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
            (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by norm_num)
        exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) hβ1)
      have hinner_B :
          (∑ q ∈ lists i₀,
            (X₀ * (Z_slot i₀ * ∏ i ∈ S₀ ∪ T_ext, Z_slot i))⁻¹ *
              ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) ≤
          (Z_slot i₀)⁻¹ ^ 2 *
            ∑ q ∈ lists i₀,
              (((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ *
                ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                  (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro q hq
        rw [← mul_assoc ((Z_slot i₀)⁻¹ ^ 2)]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hZq : Z_slot i₀ ≤ ‖ringComplex (p q)‖ ^ 2 :=
          hZ_lo i₀ (Finset.mem_insert_self i₀ S₀) q hq
        have hNq_pos : 0 < ‖ringComplex (p q)‖ ^ 2 := hZi₀_pos.trans_le hZq
        have h1 : (Z_slot i₀)⁻¹ ^ 2 * ((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ =
            (‖ringComplex (p q)‖ ^ 2 / Z_slot i₀) *
              (X₀ * (Z_slot i₀ * ∏ i ∈ S₀ ∪ T_ext, Z_slot i))⁻¹ := by
          field_simp [hZi₀_pos.ne', hX₀.ne', hNq_pos.ne', hZprod_S₀T.ne']
        rw [h1]
        exact le_mul_of_one_le_left
          (inv_nonneg.mpr (mul_pos hX₀ (mul_pos hZi₀_pos hZprod_S₀T)).le)
          ((one_le_div hZi₀_pos).mpr hZq)
      have hscale_B : (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ * ‖B‖ ^ 2 ≤
          ((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹ ^ 2 *
            ∑ q ∈ lists i₀,
              (((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ *
                ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                    (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) := by
        calc (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ * ‖B‖ ^ 2
            ≤ (X₀ * (Z_slot i₀ * ∏ i ∈ S₀ ∪ T_ext, Z_slot i))⁻¹ *
                (((lists i₀).card : ℝ) * ∑ q ∈ lists i₀,
                  ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                    (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) := by
              rw [hprod_split]
              exact mul_le_mul_of_nonneg_left hB_sq
                (inv_nonneg.mpr (mul_pos hX₀ (mul_pos hZi₀_pos hZprod_S₀T)).le)
          _ = ((lists i₀).card : ℝ) * ∑ q ∈ lists i₀,
                ((X₀ * (Z_slot i₀ * ∏ i ∈ S₀ ∪ T_ext, Z_slot i))⁻¹ *
                  ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                    (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) := by
              rw [← mul_assoc, mul_comm _ ((lists i₀).card : ℝ), mul_assoc, Finset.mul_sum]
          _ ≤ ((lists i₀).card : ℝ) * ((Z_slot i₀)⁻¹ ^ 2 *
                ∑ q ∈ lists i₀,
                  (((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ *
                    ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                      (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left hinner_B (Nat.cast_nonneg _)
          _ = _ := by ring
      have hscale_pos : 0 ≤ (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ := by
        rw [hprod_split]; exact inv_nonneg.mpr (mul_pos hX₀ (mul_pos hZi₀_pos hZprod_S₀T)).le
      have hstep1 := mul_le_mul_of_nonneg_left h2ab hscale_pos
      have hA_rew : (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ * (2 * ‖A‖ ^ 2) =
          2 * ((X₀ * ∏ i ∈ S₀ ∪ insert i₀ T_ext, Z_slot i)⁻¹ *
            ‖disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
              ∏ j ∈ insert i₀ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2) := by
        rw [hA_eq, hunion_eq]; ring
      have hB_rew : (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ * (2 * ‖B‖ ^ 2) =
          2 * ((X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ * ‖B‖ ^ 2) := by ring
      rw [mul_add, hA_rew, hB_rew] at hstep1
      linarith [hstep1, hscale_B]
    -- Sum `hpt` over `w ∈ S_w` and apply the induction hypothesis on both branches.
    have hterm1 :
        (∑ w ∈ S_w, (X₀ * ∏ i ∈ S₀ ∪ insert i₀ T_ext, Z_slot i)⁻¹ *
          ‖disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
            ∏ j ∈ insert i₀ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2) ≤
        (307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup := by
      exact ih
        (fun i hi => ha i (Finset.mem_insert_of_mem hi))
        (fun i hi => hZ_lo i (Finset.mem_insert_of_mem hi))
        (fun i hi => hZ_hi i (Finset.mem_insert_of_mem hi))
        P_punc (insert i₀ T_ext) hS₀_insT_disj
        (fun i hi => hlists_pool i (Finset.mem_insert_of_mem hi))
        (by rw [← hunion_eq]; exact hdisj)
        (by rw [← hunion_eq]; exact hZ1)
        X₀ hX₀
        (by rw [← hunion_eq]; exact hfactored)
    have hterm2 : ∀ q ∈ lists i₀,
        (∑ w ∈ S_w, ((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ *
          ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
              (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2) ≤
        (307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ (P_punc.card + 1) * B_sup := by
      intro q hq
      have hq_not_P : q ∉ P_punc := (Finset.mem_sdiff.mp (hpool_i₀ hq)).2
      have hZq : Z_slot i₀ ≤ ‖ringComplex (p q)‖ ^ 2 :=
        hZ_lo i₀ (Finset.mem_insert_self i₀ S₀) q hq
      have hNq1 : 1 ≤ ‖ringComplex (p q)‖ ^ 2 := hZi₀_1.trans hZq
      have hNq_pos : 0 < ‖ringComplex (p q)‖ ^ 2 := zero_lt_one.trans_le hNq1
      have hsub_union : S₀ ∪ T_ext ⊆ insert i₀ S₀ ∪ T_ext :=
        Finset.union_subset_union_left (Finset.subset_insert i₀ S₀)
      have hlists_ins : ∀ i ∈ S₀, lists i ⊆ pool \ insert q P_punc := by
        intro i hi x hx
        have hx0 := hlists_pool i (Finset.mem_insert_of_mem hi) hx
        have hxq : x ≠ q := fun he =>
          Finset.disjoint_left.mp (hdisj_i₀ i hi) hq (he ▸ hx)
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx0).1,
          fun hm => (Finset.mem_insert.mp hm).elim hxq (Finset.mem_sdiff.mp hx0).2⟩
      rw [← Finset.card_insert_of_notMem hq_not_P]
      exact ih
        (fun i hi => ha i (Finset.mem_insert_of_mem hi))
        (fun i hi => hZ_lo i (Finset.mem_insert_of_mem hi))
        (fun i hi => hZ_hi i (Finset.mem_insert_of_mem hi))
        (insert q P_punc) T_ext hS₀T_disj hlists_ins
        (hdisj.subset (Finset.coe_subset.mpr hsub_union))
        (fun i hi => hZ1 i (hsub_union hi))
        (X₀ / ‖ringComplex (p q)‖ ^ 2) (div_pos hX₀ hNq_pos)
        (fun T' hT' X' hX' hX'_le => hfactored T' (hT'.trans hsub_union) X' hX'
          (hX'_le.trans (div_le_self hX₀.le hNq1)))
    rw [Finset.card_insert_of_notMem hi₀, pow_succ']
    have hM0 : 0 ≤ (307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup := by positivity
    calc
      (∑ w ∈ S_w, (X₀ * ∏ i ∈ insert i₀ S₀ ∪ T_ext, Z_slot i)⁻¹ *
          ‖disjTupleSum p hg (pool \ P_punc) (insert i₀ S₀) lists a Ψ₀ V₀ X₀ w * P_ext w‖ ^ 2)
        ≤ 2 * (∑ w ∈ S_w, (X₀ * ∏ i ∈ S₀ ∪ insert i₀ T_ext, Z_slot i)⁻¹ *
            ‖disjTupleSum p hg (pool \ P_punc) S₀ lists a Ψ₀ V₀ X₀ w *
              ∏ j ∈ insert i₀ T_ext, slotCharSum p hg lists a Ψ₀ j w‖ ^ 2) +
          2 * ((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹ ^ 2 *
            ∑ q ∈ lists i₀,
              ∑ w ∈ S_w, ((X₀ / ‖ringComplex (p q)‖ ^ 2) * ∏ i ∈ S₀ ∪ T_ext, Z_slot i)⁻¹ *
                ‖disjTupleSum p hg (pool \ insert q P_punc) S₀ lists a Ψ₀ V₀
                    (X₀ / ‖ringComplex (p q)‖ ^ 2) w * P_ext w‖ ^ 2 := by
            refine (Finset.sum_le_sum (fun w _ => hpt w)).trans_eq ?_
            rw [Finset.sum_add_distrib]
            congr 1
            · rw [← Finset.mul_sum]
            · rw [← Finset.mul_sum, Finset.sum_comm]
        _ ≤ 2 * ((307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup) +
              2 * ((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹ ^ 2 *
                ∑ _q ∈ lists i₀,
                  ((307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ (P_punc.card + 1) * B_sup) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hterm1 (by norm_num)
            · apply mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum (fun q hq => hterm2 q hq))
              positivity
        _ = 2 * ((307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup) +
              32 * (((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹) ^ 2 *
                ((307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup) := by
            rw [Finset.sum_const, nsmul_eq_mul, pow_succ']; ring
        _ ≤ 2 * ((307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup) +
              32 * 98 ^ 2 * ((307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup) := by
            have hratio : ((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹ ≤ 98 := by
              rw [← div_eq_mul_inv, div_le_iff₀ hZi₀_pos]; exact hcard_L
            have hsq_r : (((lists i₀).card : ℝ) * (Z_slot i₀)⁻¹) ^ 2 ≤ 98 ^ 2 :=
              pow_le_pow_left₀ (by positivity) hratio 2
            have hmul_r := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsq_r (by norm_num : (0 : ℝ) ≤ 32)) hM0
            linarith [hmul_r]
        _ = (307330 : ℝ) * (307330 : ℝ) ^ S₀.card * (16 : ℝ) ^ P_punc.card * B_sup := by ring

end TotalScaleUnpunctureAndCollision

end Stage1ReciprocityAndUnpuncture

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
