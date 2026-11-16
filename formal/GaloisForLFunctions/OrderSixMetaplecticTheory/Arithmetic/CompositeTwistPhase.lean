import GaloisForLFunctions.OrderSixMetaplecticTheory.Arithmetic.ConductorNormalization

/-!
# Composite cubic-twist phases

For a finite set of primary primes, the actual composite Gauss phase differs from
the product of its prime phases by a cube root of unity. The same phase identifies
the coprime dilate correlation with the cubic twist of the theta square, coefficient
by coefficient and at the level of their Dirichlet series.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open Finset MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein
  SpectralTheoryOfTheCubicCover MetaplecticMobiusDescent.CubicEisenstein.RationalSource

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

/-- Distinct primary generators represent coprime prime ideals. -/
theorem PrimaryPrime.isCoprime_of_ne (P Q : PrimaryPrime) (h : P ≠ Q) :
    IsCoprime P.p Q.p := by
  apply P.prime.coprime_iff_not_dvd.mpr
  intro hd
  apply h
  exact PrimaryPrime.p_injective (primary_associated_eq _ _
    (P.prime.irreducible.associated_of_dvd Q.prime.irreducible hd) P.primary Q.primary)

/-- The squarefree primary conductor represented by a finite set of primary primes. -/
def primeConductor (S : Finset PrimaryPrime) : O := ∏ P ∈ S, P.p

theorem primeConductor_ne_zero (S : Finset PrimaryPrime) : primeConductor S ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun P _ => P.ne_zero

theorem primeConductor_primary (S : Finset PrimaryPrime) :
    lambda ^ 2 ∣ primeConductor S - 1 :=
  primary_finset_product S PrimaryPrime.p fun P _ => P.primary

theorem PrimaryPrime.isCoprime_primeConductor (P : PrimaryPrime) (S : Finset PrimaryPrime)
    (hP : P ∉ S) : IsCoprime P.p (primeConductor S) := by
  apply IsCoprime.prod_right
  intro Q hQ
  apply P.isCoprime_of_ne Q
  intro he
  apply hP
  simpa only [he] using hQ

/-- The actual phase multiplying the cubic twist in a coprime theta dilate. -/
def cubicConductorPhase (m : O) : ℂ :=
  ringComplex (symbol 9 m) * star (normalizedCubicUnitGauss m)

theorem cubicConductorPhase_one : cubicConductorPhase 1 = 1 := by
  simp only [cubicConductorPhase, symbol_one, map_one, normalizedCubicUnitGauss_one,
    star_one, mul_one]

/-- The cubic reciprocity symbol is the exact defect of multiplicativity. -/
theorem cubicConductorPhase_mul (a b : O) (ha : lambda ^ 2 ∣ a - 1)
    (hb : lambda ^ 2 ∣ b - 1) (hab : IsCoprime a b) :
    cubicConductorPhase (a * b) =
      ringComplex (symbol a b) * cubicConductorPhase a * cubicConductorPhase b := by
  unfold cubicConductorPhase
  rw [symbol_mul_denominator, map_mul,
    normalizedCubicUnitGauss_coprime_product a b (primary_ne_zero a ha)
      (primary_ne_zero b hb) ha hb hab]
  ring

/-- Squarefree composite phases have modulus one, with no coprimality premise left over. -/
theorem cubicConductorPhase_norm (S : Finset PrimaryPrime) :
    ‖cubicConductorPhase (primeConductor S)‖ = 1 := by
  have h9 : IsCoprime (9 : O) (primeConductor S) := by
    apply IsCoprime.prod_right
    intro P _
    have h := P.isCoprime_three.pow_left (m := 2)
    norm_num at h
    exact h
  have hG : ‖normalizedCubicUnitGauss (primeConductor S)‖ = 1 :=
    normalizedCubicUnitGauss_prime_product_norm S PrimaryPrime.p
      (fun P _ => P.prime) (fun P _ => P.primary)
      (fun P _ Q _ hPQ => P.isCoprime_of_ne Q hPQ)
  rw [cubicConductorPhase, norm_mul, norm_star,
    symbol_norm_one 9 _ (primeConductor_primary S) h9, hG, mul_one]

/-- Cubing removes all interactions between distinct prime factors. -/
theorem cubicConductorPhase_prod_cube (S : Finset PrimaryPrime) :
    cubicConductorPhase (primeConductor S) ^ 3 =
      (∏ P ∈ S, cubicConductorPhase P.p) ^ 3 := by
  induction S using Finset.induction_on with
  | empty => simp only [primeConductor, prod_empty, cubicConductorPhase_one]
  | @insert P S hP ih =>
    have hsym : ringComplex (symbol P.p (primeConductor S)) ^ 3 = 1 := by
      rw [← map_pow, symbol_cube_of_isCoprime _ _ (primeConductor_primary S)
        (P.isCoprime_primeConductor S hP), map_one]
    change cubicConductorPhase (∏ Q ∈ insert P S, Q.p) ^ 3 = _
    rw [prod_insert hP]
    change cubicConductorPhase (P.p * primeConductor S) ^ 3 = _
    rw [cubicConductorPhase_mul _ _ P.primary (primeConductor_primary S)
      (P.isCoprime_primeConductor S hP), mul_pow, mul_pow, hsym, one_mul,
      ih, prod_insert hP, mul_pow]

/-- The composite-to-prime phase ratio records all cross-prime cubic symbols. -/
def compositePhaseCorrection (S : Finset PrimaryPrime) : ℂ :=
  cubicConductorPhase (primeConductor S) / ∏ P ∈ S, cubicConductorPhase P.p

/-- Adding one prime contributes precisely its cubic symbol against the preceding conductor. -/
theorem compositePhaseCorrection_insert (S : Finset PrimaryPrime) (P : PrimaryPrime)
    (hP : P ∉ S) :
    compositePhaseCorrection (insert P S) =
      ringComplex (symbol P.p (primeConductor S)) * compositePhaseCorrection S := by
  have hnP : cubicConductorPhase P.p ≠ 0 := P.twistFactor_ne_zero
  have hnS : (∏ Q ∈ S, cubicConductorPhase Q.p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun Q _ => Q.twistFactor_ne_zero
  unfold compositePhaseCorrection
  rw [show primeConductor (insert P S) = P.p * primeConductor S from prod_insert hP,
    prod_insert hP, cubicConductorPhase_mul _ _ P.primary (primeConductor_primary S)
      (P.isCoprime_primeConductor S hP)]
  field_simp

/-- The interaction phase is always a cube root of unity. -/
theorem compositePhaseCorrection_cube (S : Finset PrimaryPrime) :
    compositePhaseCorrection S ^ 3 = 1 := by
  have hn : (∏ P ∈ S, cubicConductorPhase P.p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun P _ => P.twistFactor_ne_zero
  rw [compositePhaseCorrection, div_pow, cubicConductorPhase_prod_cube,
    div_self (pow_ne_zero 3 hn)]

theorem compositePhaseCorrection_norm (S : Finset PrimaryPrime) :
    ‖compositePhaseCorrection S‖ = 1 := by
  rw [compositePhaseCorrection, norm_div, cubicConductorPhase_norm, norm_prod]
  have hprod : (∏ P ∈ S, ‖cubicConductorPhase P.p‖) = 1 := by
    simp only [cubicConductorPhase, PrimaryPrime.twistFactor_norm, prod_const_one]
  rw [hprod, div_one]

theorem cubicConductorPhase_eq_correction_mul (S : Finset PrimaryPrime) :
    cubicConductorPhase (primeConductor S) =
      compositePhaseCorrection S * ∏ P ∈ S, cubicConductorPhase P.p := by
  have hn : (∏ P ∈ S, cubicConductorPhase P.p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun P _ => P.twistFactor_ne_zero
  rw [compositePhaseCorrection, div_mul_cancel₀ _ hn]

theorem conductorSymbol_eq_prod (S : Finset PrimaryPrime) (k : O) :
    ringComplex (symbol k (primeConductor S)) = ∏ P ∈ S, ringComplex (symbol k P.p) := by
  induction S using Finset.induction_on with
  | empty => simp only [primeConductor, prod_empty, symbol_one, map_one]
  | @insert P S hP ih =>
    change ringComplex (symbol k (∏ Q ∈ insert P S, Q.p)) = _
    rw [prod_insert hP, symbol_mul_denominator, map_mul, prod_insert hP]
    exact congrArg (ringComplex (symbol k P.p) * ·) ih

/-- A common prime kills the composite cubic symbol. -/
theorem conductorSymbol_eq_zero (S : Finset PrimaryPrime) (k : O)
    (h : ¬ ∀ P ∈ S, ¬ P.p ∣ k) : ringComplex (symbol k (primeConductor S)) = 0 := by
  push Not at h
  obtain ⟨P, hP, hPk⟩ := h
  rw [conductorSymbol_eq_prod]
  apply Finset.prod_eq_zero hP
  rw [← P.chi_res, (P.res_eq_zero_iff k).mpr hPk, MulChar.map_zero]

/-- The cubic twist at the squarefree composite conductor. -/
def compositeTwistCoeff (S : Finset PrimaryPrime) (k : O) : ℂ :=
  ringComplex (symbol k (primeConductor S)) * rationalSourceResidualFourierCoefficient k ^ 2

/-- The theta dilate restricted to frequencies coprime to its conductor. -/
def compositeDilateCoeff (S : Finset PrimaryPrime) (k : O) : ℂ :=
  if ∀ P ∈ S, ¬ P.p ∣ k then
    rationalSourceResidualFourierCoefficient k *
      rationalSourceResidualFourierCoefficient (k * primeConductor S)
  else 0

/-- The actual composite dilate and cubic twist agree up to the explicit unit Gauss phase. -/
theorem compositeDilateCoeff_eq_twist (S : Finset PrimaryPrime) (k : O) :
    compositeDilateCoeff S k =
      cubicConductorPhase (primeConductor S) * compositeTwistCoeff S k := by
  by_cases hk : ∀ P ∈ S, ¬ P.p ∣ k
  · have he : rationalSourceResidualFourierCoefficient (k * primeConductor S) =
        ringComplex (symbol (9 * k) (primeConductor S)) *
          star (normalizedCubicUnitGauss (primeConductor S)) *
          rationalSourceResidualFourierCoefficient k :=
      rationalSourceResidualFourierCoefficient_prime_product S PrimaryPrime.p
        (fun P _ => P.prime) (fun P _ => P.primary)
        (fun P _ Q _ hPQ => P.isCoprime_of_ne Q hPQ) k hk
    rw [compositeDilateCoeff, if_pos hk, he, compositeTwistCoeff,
      cubicConductorPhase, symbol_mul_numerator, map_mul]
    ring
  · rw [compositeDilateCoeff, if_neg hk, compositeTwistCoeff,
      conductorSymbol_eq_zero S k hk, zero_mul, mul_zero]

/-- Composite dilate and twist coefficients have identical absolute values. -/
theorem compositeDilateCoeff_norm (S : Finset PrimaryPrime) (k : O) :
    ‖compositeDilateCoeff S k‖ = ‖compositeTwistCoeff S k‖ := by
  rw [compositeDilateCoeff_eq_twist, norm_mul, cubicConductorPhase_norm, one_mul]

/-- The composite twist keeps exactly the magnitudes at frequencies coprime to its conductor. -/
theorem compositeTwistCoeff_norm (S : Finset PrimaryPrime) (k : O) :
    ‖compositeTwistCoeff S k‖ =
      if ∀ P ∈ S, ¬ P.p ∣ k then ‖rationalSourceResidualFourierCoefficient k ^ 2‖ else 0 := by
  by_cases hk : ∀ P ∈ S, ¬ P.p ∣ k
  · have hc : IsCoprime k (primeConductor S) :=
      IsCoprime.prod_right fun P hP => (P.prime.coprime_iff_not_dvd.mpr (hk P hP)).symm
    rw [if_pos hk, compositeTwistCoeff, norm_mul,
      symbol_norm_one k _ (primeConductor_primary S) hc, one_mul]
  · rw [if_neg hk, compositeTwistCoeff, conductorSymbol_eq_zero S k hk, zero_mul, norm_zero]

theorem compositeTwistCoeff_norm_le (S : Finset PrimaryPrime) (k : O) :
    ‖compositeTwistCoeff S k‖ ≤ ‖rationalSourceResidualFourierCoefficient k ^ 2‖ := by
  rw [compositeTwistCoeff_norm]
  split_ifs
  · exact le_rfl
  · exact norm_nonneg _

/-- The initial absolute convergence estimate is uniform in the finite prime set. -/
theorem summable_compositeTwistCoeff (S : Finset PrimaryPrime) {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun k : O => if k = 0 then 0 else
      ‖compositeTwistCoeff S k‖ * ‖cuspFrequency k‖ ^ (-σ)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_sq_coeff hσ)
  · split_ifs <;> positivity
  · split_ifs
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_right (compositeTwistCoeff_norm_le S k) (by positivity)

theorem summable_compositeDilateCoeff (S : Finset PrimaryPrime) {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun k : O => if k = 0 then 0 else
      ‖compositeDilateCoeff S k‖ * ‖cuspFrequency k‖ ^ (-σ)) := by
  simpa only [compositeDilateCoeff_norm] using summable_compositeTwistCoeff S hσ

/-- The coefficient identity passes to the actual Bessel Dirichlet series. -/
theorem compositeDilateDirichlet_eq (S : Finset PrimaryPrime) (s : ℂ) :
    besselDirichlet (compositeDilateCoeff S) s =
      cubicConductorPhase (primeConductor S) * besselDirichlet (compositeTwistCoeff S) s := by
  rw [besselDirichlet, besselDirichlet, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  split_ifs
  · ring
  · rw [compositeDilateCoeff_eq_twist]
    ring

#print axioms compositePhaseCorrection_cube
#print axioms compositePhaseCorrection_insert
#print axioms cubicConductorPhase_norm
#print axioms compositeDilateCoeff_eq_twist
#print axioms compositeDilateDirichlet_eq
#print axioms summable_compositeDilateCoeff

end GaloisForLFunctions.OrderSixMetaplecticTheory
