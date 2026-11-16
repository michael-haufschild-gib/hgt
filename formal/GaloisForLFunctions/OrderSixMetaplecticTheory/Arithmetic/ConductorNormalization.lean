import GaloisForLFunctions.OrderSixMetaplecticTheory.TheDilateCorrelationAtEveryPrimaryPrimeHasADoublePole
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicReciprocityAtACommonCharacteristic
import GaloisForLFunctions.HTGeometry.Analysis.ReciprocalPowerProducts
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Uniform normalization of the prime dilate factors

The actual dilate factor at `4/3` is `N(p)^(1/6)(N(p)+1)/(N(p)-1)`.
Removing the power of the norm and the first-order Euler factors leaves
`1-N(p)^(-2)`. Equal norms identify primary primes up to conjugation, so
each norm occurs at most twice. The reciprocal-square product estimate
then bounds the remaining correction uniformly over finite prime sets.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open Finset MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi

namespace PrimaryPrime

/-- Absolute norm of the primary prime's principal ideal. -/
def conductorNorm (P : PrimaryPrime) : ℕ := Ideal.absNorm (Ideal.span {P.p})

theorem conductorNorm_cast (P : PrimaryPrime) :
    (P.conductorNorm : ℝ) = ‖ringComplex P.p‖ ^ 2 :=
  (ringComplex_norm_sq_eq_absNorm_span P.p).symm

theorem conductorNorm_two_le (P : PrimaryPrime) : 2 ≤ P.conductorNorm := by
  have hp : (0 : ℝ) < P.conductorNorm := by
    rw [P.conductorNorm_cast]
    exact sq_pos_of_pos P.norm_pos
  have hn : P.conductorNorm ≠ 1 := by
    intro h
    apply P.rho_sq_ne_one
    have he : ‖ringComplex P.p‖ ^ 2 = (1 : ℝ) := by
      rw [← P.conductorNorm_cast, h, Nat.cast_one]
    exact_mod_cast he
  have hp' : 0 < P.conductorNorm := by exact_mod_cast hp
  omega

theorem p_injective : Function.Injective PrimaryPrime.p := by
  intro P Q h
  cases P
  cases Q
  cases h
  rfl

/-- Equal ideal norms give the same product with the conjugate. -/
theorem mul_conj_eq_of_conductorNorm_eq (P Q : PrimaryPrime)
    (h : P.conductorNorm = Q.conductorNorm) :
    P.p * conjO P.p = Q.p * conjO Q.p := by
  apply ringComplex_injective
  rw [map_mul, map_mul, ringComplex_conjO, ringComplex_conjO]
  change ringComplex P.p * (starRingEnd ℂ) (ringComplex P.p) =
    ringComplex Q.p * (starRingEnd ℂ) (ringComplex Q.p)
  rw [Complex.mul_conj', Complex.mul_conj']
  have he : ‖ringComplex P.p‖ ^ 2 = ‖ringComplex Q.p‖ ^ 2 := by
    rw [← P.conductorNorm_cast, ← Q.conductorNorm_cast, h]
  exact_mod_cast he

/-- A primary prime is determined by its norm up to conjugation. -/
theorem eq_or_conj_of_conductorNorm_eq (P Q : PrimaryPrime)
    (h : P.conductorNorm = Q.conductorNorm) :
    P.p = Q.p ∨ P.p = conjO Q.p := by
  have hd : P.p ∣ Q.p * conjO Q.p := by
    rw [← P.mul_conj_eq_of_conductorNorm_eq Q h]
    exact dvd_mul_right _ _
  rcases P.prime.dvd_mul.mp hd with hQ | hQ
  · exact Or.inl (primary_associated_eq _ _
      (P.prime.irreducible.associated_of_dvd Q.prime.irreducible hQ) P.primary Q.primary)
  · have hprime : Prime (conjO Q.p) := (MulEquiv.prime_iff conjO).mpr Q.prime
    exact Or.inr (primary_associated_eq _ _
      (P.prime.irreducible.associated_of_dvd hprime.irreducible hQ)
      P.primary (conjO_primary Q.primary))

theorem conductorSquare_pos (P : PrimaryPrime) :
    0 < 1 - 1 / (P.conductorNorm : ℝ) ^ 2 := by
  have hq : (1 : ℝ) < P.conductorNorm := by exact_mod_cast P.conductorNorm_two_le
  have hs : (1 : ℝ) < (P.conductorNorm : ℝ) ^ 2 := by
    nlinarith only [hq, sq_nonneg ((P.conductorNorm : ℝ) - 1)]
  exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hs)

/-- The real Euler ratio in the actual dilate factor. -/
def conductorRatio (P : PrimaryPrime) : ℝ :=
  ((P.conductorNorm : ℝ) + 1) / ((P.conductorNorm : ℝ) - 1)

/-- Removing the two first-order factors leaves one square-power factor. -/
theorem conductorRatio_normalization (P : PrimaryPrime) :
    P.conductorRatio * (1 - 1 / (P.conductorNorm : ℝ)) ^ 2 =
      1 - 1 / (P.conductorNorm : ℝ) ^ 2 := by
  have hq : (1 : ℝ) < P.conductorNorm := by exact_mod_cast P.conductorNorm_two_le
  have hq0 : (P.conductorNorm : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hq1 : (P.conductorNorm : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  unfold conductorRatio
  field_simp
  ring

theorem conductorFirst_pos (P : PrimaryPrime) :
    0 < 1 - 1 / (P.conductorNorm : ℝ) := by
  have hq : (1 : ℝ) < P.conductorNorm := by exact_mod_cast P.conductorNorm_two_le
  exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hq)

theorem conductorRatio_decomposition (P : PrimaryPrime) :
    P.conductorRatio = (1 / (1 - 1 / (P.conductorNorm : ℝ)) ^ 2) *
      (1 - 1 / (P.conductorNorm : ℝ) ^ 2) := by
  have he := (eq_div_iff (pow_ne_zero 2 (ne_of_gt P.conductorFirst_pos))).mpr
    P.conductorRatio_normalization
  rw [he]
  ring

/-- The normalized factor is the real conductor ratio, with no remaining phase. -/
theorem dilateFactor_div_norm_power (P : PrimaryPrime) :
    P.dilateFactor (4 / 3) / ((‖ringComplex P.p‖ : ℂ) ^ (1 / 3 : ℂ)) =
      (P.conductorRatio : ℂ) := by
  have ha : ((‖ringComplex P.p‖ : ℂ) ^ (1 / 3 : ℂ)) ≠ 0 := by
    simpa only [neg_neg] using P.rho_cpow_ne_zero (-(1 / 3 : ℂ))
  have hq : (‖ringComplex P.p‖ : ℂ) ^ 2 = (P.conductorNorm : ℂ) := by
    exact_mod_cast P.conductorNorm_cast.symm
  rw [P.dilateFactor_four_thirds, hq, mul_div_cancel_left₀ _ ha]
  unfold conductorRatio
  push_cast
  rfl

/-- The phase in the cubic-twist double-pole coefficient has modulus one. -/
theorem twistFactor_norm (P : PrimaryPrime) :
    ‖ringComplex (symbol 9 P.p) * star (normalizedCubicUnitGauss P.p)‖ = 1 := by
  have h9 : IsCoprime (9 : O) P.p := by
    have h := P.isCoprime_three.pow_left (m := 2)
    norm_num at h
    exact h
  rw [norm_mul, norm_star, normalizedCubicUnitGauss_prime_norm P.p P.prime P.primary,
    symbol_norm_one 9 P.p P.primary h9, mul_one]

end PrimaryPrime

/-- Norm repetitions in a finite primary-prime set have multiplicity at most two. -/
theorem conductorNorm_fiber_card_le_two (S : Finset PrimaryPrime) (q : ℕ) :
    (S.filter fun P => P.conductorNorm = q).card ≤ 2 := by
  by_cases h : (S.filter fun P => P.conductorNorm = q).Nonempty
  · obtain ⟨P, hP⟩ := h
    have hPq := (mem_filter.mp hP).2
    have hc : (S.filter fun Q => Q.conductorNorm = q).card ≤
        ({P.p, conjO P.p} : Finset O).card := by
      apply card_le_card_of_injOn PrimaryPrime.p
      · intro Q hQ
        have hQq := (mem_filter.mp hQ).2
        simpa only [mem_coe, mem_insert, mem_singleton] using
          Q.eq_or_conj_of_conductorNorm_eq P (hQq.trans hPq.symm)
      · intro P _ Q _ he
        exact PrimaryPrime.p_injective he
    exact hc.trans Finset.card_le_two
  · have he : (S.filter fun P => P.conductorNorm = q) = ∅ := by
      simpa using h
    rw [he, card_empty]
    omega

private theorem distinct_norm_product_lt_two (S : Finset PrimaryPrime) :
    (∏ q ∈ S.image PrimaryPrime.conductorNorm, (1 - 1 / (q : ℝ) ^ 2)⁻¹) < 2 := by
  have hq (q : ℕ) (hq : q ∈ S.image PrimaryPrime.conductorNorm) : 2 ≤ q := by
    obtain ⟨P, _, rfl⟩ := mem_image.mp hq
    exact P.conductorNorm_two_le
  have hi : Set.InjOn (fun q : ℕ => q - 2) (S.image PrimaryPrime.conductorNorm) := by
    intro q hq' r hr he
    have := hq q hq'
    have := hq r hr
    change q - 2 = r - 2 at he
    omega
  have h := HTGeometry.ReciprocalPowerProducts.subproduct_lt_uniform 0
    ((S.image PrimaryPrime.conductorNorm).image fun q => q - 2)
  rw [prod_image hi] at h
  have he : (∏ q ∈ S.image PrimaryPrime.conductorNorm,
      (1 - 1 / (((q - 2 : ℕ) : ℝ) + 2) ^ (0 + 2))⁻¹) =
      ∏ q ∈ S.image PrimaryPrime.conductorNorm, (1 - 1 / (q : ℝ) ^ 2)⁻¹ := by
    apply prod_congr rfl
    intro q hq'
    rw [Nat.cast_sub (hq q hq'), Nat.cast_ofNat, sub_add_cancel]
  have hs : (HTGeometry.ReciprocalPowerProducts.slope 0 + 1) /
      HTGeometry.ReciprocalPowerProducts.slope 0 = (2 : ℝ) := by
    norm_num [HTGeometry.ReciprocalPowerProducts.slope]
  rwa [he, hs] at h

private theorem inverse_square_product_lt_four (S : Finset PrimaryPrime) :
    (∏ P ∈ S, (1 - 1 / (P.conductorNorm : ℝ) ^ 2)⁻¹) < 4 := by
  let a : ℕ → ℝ := fun q => (1 - 1 / (q : ℝ) ^ 2)⁻¹
  have ha (q : ℕ) (hq : q ∈ S.image PrimaryPrime.conductorNorm) : 1 ≤ a q := by
    obtain ⟨P, _, rfl⟩ := mem_image.mp hq
    exact (one_le_inv₀ P.conductorSquare_pos).mpr (sub_le_self _ (by positivity))
  have hf : (∏ q ∈ S.image PrimaryPrime.conductorNorm,
      a q ^ (S.filter fun P => P.conductorNorm = q).card) =
      ∏ P ∈ S, a P.conductorNorm := by
    calc
      _ = ∏ q ∈ S.image PrimaryPrime.conductorNorm,
          ∏ P ∈ S.filter (fun P => P.conductorNorm = q), a P.conductorNorm := by
        apply prod_congr rfl
        intro q _
        calc
          _ = ∏ _P ∈ S.filter (fun P => P.conductorNorm = q), a q :=
            (Finset.prod_const _).symm
          _ = _ := prod_congr rfl fun P hP => by rw [(mem_filter.mp hP).2]
      _ = _ := prod_fiberwise_of_maps_to (s := S) (t := S.image PrimaryPrime.conductorNorm)
        (g := PrimaryPrime.conductorNorm)
        (fun P hP => mem_image_of_mem PrimaryPrime.conductorNorm hP)
        (fun P : PrimaryPrime => a P.conductorNorm)
  have hbound : (∏ P ∈ S, a P.conductorNorm) ≤
      (∏ q ∈ S.image PrimaryPrime.conductorNorm, a q) ^ 2 := by
    rw [← hf, ← prod_pow]
    apply Finset.prod_le_prod
    · intro q hq
      exact pow_nonneg (zero_le_one.trans (ha q hq)) _
    · intro q hq
      exact pow_le_pow_right₀ (ha q hq) (conductorNorm_fiber_card_le_two S q)
  have hlt := pow_lt_pow_left₀ (distinct_norm_product_lt_two S)
    (Finset.prod_nonneg fun q hq => zero_le_one.trans (ha q hq)) (by norm_num : 2 ≠ 0)
  exact hbound.trans_lt (by simpa only [a, show (2 : ℝ) ^ 2 = 4 by norm_num] using hlt)

/-- The square-power Euler correction over an actual finite set of primary primes. -/
def conductorSquareCorrection (S : Finset PrimaryPrime) : ℝ :=
  ∏ P ∈ S, (1 - 1 / (P.conductorNorm : ℝ) ^ 2)

theorem conductorSquareCorrection_pos (S : Finset PrimaryPrime) :
    0 < conductorSquareCorrection S :=
  Finset.prod_pos fun P _ => P.conductorSquare_pos

/-- The entire square-power correction stays between `1/4` and `1`, independently of the conductor. -/
theorem conductorSquareCorrection_bounds (S : Finset PrimaryPrime) :
    (1 / 4 : ℝ) < conductorSquareCorrection S ∧ conductorSquareCorrection S ≤ 1 := by
  constructor
  · have h := inverse_square_product_lt_four S
    rw [prod_inv_distrib] at h
    change (conductorSquareCorrection S)⁻¹ < 4 at h
    rw [← one_div, div_lt_iff₀ (conductorSquareCorrection_pos S)] at h
    linarith only [h]
  · exact Finset.prod_le_one (fun P _ => P.conductorSquare_pos.le)
      (fun P _ => sub_le_self _ (by positivity))

/-- The correction decreases as more primary primes are included. -/
theorem conductorSquareCorrection_antitone : Antitone conductorSquareCorrection := by
  intro S T hST
  exact Finset.prod_le_prod_of_subset_of_le_one hST
    (fun P _ => P.conductorSquare_pos.le)
    (fun P _ _ => sub_le_self _ (by positivity))

/-- The square-power correction converges over all primary primes, without choosing an ordering. -/
theorem conductorSquare_multipliable :
    Multipliable (fun P : PrimaryPrime => 1 - 1 / (P.conductorNorm : ℝ) ^ 2) := by
  have hb : BddBelow (Set.range conductorSquareCorrection) := by
    refine ⟨1 / 4, ?_⟩
    rintro _ ⟨S, rfl⟩
    exact (conductorSquareCorrection_bounds S).1.le
  exact ⟨⨅ S, conductorSquareCorrection S,
    tendsto_atTop_ciInf conductorSquareCorrection_antitone hb⟩

/-- The infinite square-power conductor correction. -/
def conductorSquareConstant : ℝ :=
  ∏' P : PrimaryPrime, (1 - 1 / (P.conductorNorm : ℝ) ^ 2)

/-- The infinite correction is positive and uniformly separated from zero. -/
theorem conductorSquareConstant_bounds :
    (1 / 4 : ℝ) ≤ conductorSquareConstant ∧ conductorSquareConstant ≤ 1 := by
  exact ⟨le_hasProd_of_le_prod conductorSquare_multipliable.hasProd
      (fun S => (conductorSquareCorrection_bounds S).1.le),
    hasProd_le_of_prod_le conductorSquare_multipliable.hasProd
      (fun S => (conductorSquareCorrection_bounds S).2)⟩

/-- The first-order Euler weight that remains after removing the bounded correction. -/
def conductorFirstOrderWeight (S : Finset PrimaryPrime) : ℝ :=
  ∏ P ∈ S, 1 / (1 - 1 / (P.conductorNorm : ℝ)) ^ 2

theorem conductorFirstOrderWeight_pos (S : Finset PrimaryPrime) :
    0 < conductorFirstOrderWeight S := by
  apply Finset.prod_pos
  intro P _
  exact div_pos zero_lt_one (pow_pos P.conductorFirst_pos 2)

/-- Exact separation of first-order conductor growth from its bounded square-power correction. -/
theorem conductorRatio_product_eq (S : Finset PrimaryPrime) :
    (∏ P ∈ S, P.conductorRatio) = conductorFirstOrderWeight S * conductorSquareCorrection S := by
  unfold conductorFirstOrderWeight conductorSquareCorrection
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun P _ => P.conductorRatio_decomposition

theorem conductorRatio_product_bounds (S : Finset PrimaryPrime) :
    conductorFirstOrderWeight S / 4 < (∏ P ∈ S, P.conductorRatio) ∧
      (∏ P ∈ S, P.conductorRatio) ≤ conductorFirstOrderWeight S := by
  rw [conductorRatio_product_eq]
  have h := conductorSquareCorrection_bounds S
  constructor
  · have hh := mul_lt_mul_of_pos_left h.1 (conductorFirstOrderWeight_pos S)
    simpa only [mul_one_div] using hh
  · simpa only [mul_one] using
      mul_le_mul_of_nonneg_left h.2 (conductorFirstOrderWeight_pos S).le

/-- The actual prime dilate factors with the norm power and first-order Euler factors removed. -/
def normalizedDilateProduct (S : Finset PrimaryPrime) : ℂ :=
  ∏ P ∈ S, (P.dilateFactor (4 / 3) / ((‖ringComplex P.p‖ : ℂ) ^ (1 / 3 : ℂ))) *
    (((1 - 1 / (P.conductorNorm : ℝ)) ^ 2 : ℝ) : ℂ)

/-- The normalized spectral factors are exactly the positive arithmetic correction. -/
theorem normalizedDilateProduct_eq (S : Finset PrimaryPrime) :
    normalizedDilateProduct S = (conductorSquareCorrection S : ℂ) := by
  unfold normalizedDilateProduct conductorSquareCorrection
  rw [Complex.ofReal_prod]
  apply prod_congr rfl
  intro P _
  rw [P.dilateFactor_div_norm_power, ← Complex.ofReal_mul, P.conductorRatio_normalization]

/-- Actual prime dilate factors have a uniformly nonvanishing normalized finite product. -/
theorem normalizedDilateProduct_bounds (S : Finset PrimaryPrime) :
    (1 / 4 : ℝ) < ‖normalizedDilateProduct S‖ ∧ ‖normalizedDilateProduct S‖ ≤ 1 := by
  rw [normalizedDilateProduct_eq, Complex.norm_real,
    Real.norm_of_nonneg (conductorSquareCorrection_pos S).le]
  exact conductorSquareCorrection_bounds S

/-- Product of the prime dilate residue weights after removing their norm and first-order factors.
The common spectral coefficient `216π³r³` is omitted at each prime. -/
def normalizedDilateResidueProduct (S : Finset PrimaryPrime) : ℂ :=
  ∏ P ∈ S, (((‖ringComplex P.p‖ : ℂ) ^ (1 / 3 : ℂ)) / P.dilateFactor (4 / 3)) /
    (((1 - 1 / (P.conductorNorm : ℝ)) ^ 2 : ℝ) : ℂ)

theorem normalizedDilateResidueProduct_eq (S : Finset PrimaryPrime) :
    normalizedDilateResidueProduct S = (normalizedDilateProduct S)⁻¹ := by
  unfold normalizedDilateResidueProduct normalizedDilateProduct
  rw [← prod_inv_distrib]
  apply prod_congr rfl
  intro P _
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- The normalized prime residue weights have uniformly bounded products. -/
theorem normalizedDilateResidueProduct_bounds (S : Finset PrimaryPrime) :
    1 ≤ ‖normalizedDilateResidueProduct S‖ ∧ ‖normalizedDilateResidueProduct S‖ < 4 := by
  rw [normalizedDilateResidueProduct_eq, normalizedDilateProduct_eq, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg (conductorSquareCorrection_pos S).le]
  have h := conductorSquareCorrection_bounds S
  constructor
  · exact (one_le_inv₀ (conductorSquareCorrection_pos S)).mpr h.2
  · rw [← one_div, div_lt_iff₀ (conductorSquareCorrection_pos S)]
    linarith only [h.1]

/-- The corresponding weights of the cubic-twist residues, including their actual Gauss phases. -/
def normalizedCubicTwistResidueProduct (S : Finset PrimaryPrime) : ℂ :=
  ∏ P ∈ S, (((‖ringComplex P.p‖ : ℂ) ^ (1 / 3 : ℂ)) /
    (P.dilateFactor (4 / 3) *
      (ringComplex (symbol 9 P.p) * star (normalizedCubicUnitGauss P.p)))) /
    (((1 - 1 / (P.conductorNorm : ℝ)) ^ 2 : ℝ) : ℂ)

theorem normalizedCubicTwistResidueProduct_norm (S : Finset PrimaryPrime) :
    ‖normalizedCubicTwistResidueProduct S‖ = ‖normalizedDilateResidueProduct S‖ := by
  unfold normalizedCubicTwistResidueProduct normalizedDilateResidueProduct
  rw [norm_prod, norm_prod]
  apply prod_congr rfl
  intro P _
  simp only [norm_div, norm_mul, P.twistFactor_norm, mul_one]

/-- Unit Gauss phases preserve the uniform bounds for the cubic-twist residue weights. -/
theorem normalizedCubicTwistResidueProduct_bounds (S : Finset PrimaryPrime) :
    1 ≤ ‖normalizedCubicTwistResidueProduct S‖ ∧
      ‖normalizedCubicTwistResidueProduct S‖ < 4 := by
  rw [normalizedCubicTwistResidueProduct_norm]
  exact normalizedDilateResidueProduct_bounds S

#print axioms PrimaryPrime.eq_or_conj_of_conductorNorm_eq
#print axioms conductorNorm_fiber_card_le_two
#print axioms conductorRatio_product_bounds
#print axioms normalizedDilateProduct_bounds
#print axioms normalizedCubicTwistResidueProduct_bounds
#print axioms conductorSquareConstant_bounds

end GaloisForLFunctions.OrderSixMetaplecticTheory
