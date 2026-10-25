import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerFiniteJetAlgebra
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PositiveMeyerDegreesCanForgetClasses

/-!
# Positive Hermitian degrees discard off-line blocks and higher jets

The actual finite jet algebra contains reflected block identities and nilpotent
monomials. Cauchy–Schwarz kills every off-line block. Descending through the
nilpotent orders kills every positive-order critical jet. Only nonnegative
real weights on critical value classes survive.
-/

noncomputable section
open Complex RHTower
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private theorem hasse_class_congr {rho sigma : XiDivisorSupport} (h : rho = sigma)
    (j : DeningerArithmeticJetIndex rho) (k : DeningerArithmeticJetIndex sigma)
    (hj : j.val = k.val) : meyerHasseJetClass rho j = meyerHasseJetClass sigma k := by
  subst sigma
  exact congrArg (meyerHasseJetClass rho) (Fin.ext hj)

/-- A positive Hermitian degree annihilates every jet in a nonfixed reflection block. -/
theorem meyerPositiveDegree_off_line_jet_zero
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (rho : XiDivisorSupport) (hne : meyerLineReflect rho ≠ rho)
    (j : DeningerArithmeticJetIndex rho) : d (meyerHasseJetClass rho j) = 0 := by
  have hu : (meyerDegreePair d (meyerHasseJetClass rho j) (meyerHasseJetClass rho j)).re = 0 := by
    rw [meyerDegreePair, meyerHasseJetClass_sharp, map_smul,
      meyerHasseJetClass_product_distinct rho (meyerLineReflect rho) (Ne.symm hne),
      smul_zero, map_zero, Complex.zero_re]
  have hp := meyerPositiveDegree_null_pair d hd hpos hu
    (meyerHasseJetClass (meyerLineReflect rho) ⟨0, xiSupportMultiplicity_pos _⟩)
  have hs : meyerCohomologySharp
      (meyerHasseJetClass (meyerLineReflect rho) ⟨0, xiSupportMultiplicity_pos _⟩) =
        meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩ := by
    have he := meyerHasseJetClass_sharp (meyerLineReflect rho)
      ⟨0, xiSupportMultiplicity_pos _⟩
    simp only [pow_zero, one_smul] at he
    exact he.trans (hasse_class_congr (meyerLineReflect_sq rho) _ _ rfl)
  rw [meyerDegreePair, hs, meyerHasseJetClass_product_unit] at hp
  exact hp

private theorem sharp_fixed_jet (rho : XiDivisorSupport) (hfix : meyerLineReflect rho = rho)
    (j : DeningerArithmeticJetIndex rho) :
    meyerCohomologySharp (meyerHasseJetClass rho j) =
      (-1 : ℂ) ^ j.val • meyerHasseJetClass rho j := by
  have he := meyerHasseJetClass_sharp rho j
  rw [hasse_class_congr hfix _ j rfl] at he
  exact he

/-- Every positive-order jet in a critical block is invisible to a positive Hermitian degree. -/
theorem meyerPositiveDegree_higher_jet_zero
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (rho : XiDivisorSupport) (hfix : meyerLineReflect rho = rho)
    (j : DeningerArithmeticJetIndex rho) (hj : 0 < j.val) : d (meyerHasseJetClass rho j) = 0 := by
  have hrec : ∀ n : ℕ, ∀ k : DeningerArithmeticJetIndex rho,
      xiSupportMultiplicity rho - k.val = n → 0 < k.val → d (meyerHasseJetClass rho k) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k hkn hk
      have hnull : (meyerDegreePair d (meyerHasseJetClass rho k) (meyerHasseJetClass rho k)).re = 0 := by
        rw [meyerDegreePair, sharp_fixed_jet rho hfix, map_smul]
        by_cases hlt : k.val + k.val < xiSupportMultiplicity rho
        · rw [meyerHasseJetClass_product_same rho k k hlt, map_smul]
          have hz := ih (xiSupportMultiplicity rho - (k.val + k.val))
            (by have hki := k.isLt; omega) ⟨k.val + k.val, hlt⟩ rfl (by
              change 0 < k.val + k.val
              omega)
          rw [hz, smul_zero, Complex.zero_re]
        · rw [meyerHasseJetClass_product_truncated rho k k (Nat.le_of_not_gt hlt),
            smul_zero, map_zero, Complex.zero_re]
      have hp := meyerPositiveDegree_null_pair d hd hpos hnull
        (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩)
      rw [meyerDegreePair, sharp_fixed_jet rho hfix, pow_zero, one_smul,
        meyerHasseJetClass_product_unit] at hp
      exact hp
  exact hrec (xiSupportMultiplicity rho - j.val) j rfl hj

/-- A critical value class receives a nonnegative real weight. -/
theorem meyerPositiveDegree_critical_value_weight
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (rho : XiDivisorSupport) (hfix : meyerLineReflect rho = rho) :
    0 ≤ (d (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩)).re ∧
      (d (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩)).im = 0 := by
  let e := meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩
  have hs : meyerCohomologySharp e = e := by
    simp only [e, sharp_fixed_jet rho hfix, pow_zero, one_smul]
  have hp := hpos e
  change 0 ≤ (d (deningerMeyerCohomologyConvolution e (meyerCohomologySharp e))).re at hp
  rw [hs, meyerHasseJetClass_product_unit] at hp
  have hh := congrArg Complex.im (hd e)
  rw [hs, Complex.conj_im] at hh
  exact ⟨hp, by linarith only [hh]⟩

/-- The exact degree restriction on every finite sum of actual Hasse classes. -/
theorem meyerPositiveDegree_finite_jet_formula
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (S : Finset XiDivisorSupport) (c : DeningerMeyerFiniteXiJetPacket S) :
    d (∑ q : DeningerMeyerFiniteXiJetSlot S, c q • meyerHasseJetClass q.1.1 q.2) =
      ∑ q : DeningerMeyerFiniteXiJetSlot S,
        if meyerLineReflect q.1.1 = q.1.1 ∧ q.2.val = 0 then
          c q * ((d (meyerHasseJetClass q.1.1 q.2)).re : ℂ) else 0 := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul, smul_eq_mul]
  by_cases hfix : meyerLineReflect q.1.1 = q.1.1
  · by_cases hj : q.2.val = 0
    · rw [if_pos ⟨hfix, hj⟩]
      have hq : q.2 = ⟨0, xiSupportMultiplicity_pos q.1.1⟩ := Fin.ext hj
      have hw := (meyerPositiveDegree_critical_value_weight d hd hpos q.1.1 hfix).2
      rw [hq]
      congr 1
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using hw
    · rw [if_neg (fun h => hj h.2),
        meyerPositiveDegree_higher_jet_zero d hd hpos q.1.1 hfix q.2 (Nat.pos_of_ne_zero hj),
        mul_zero]
  · rw [if_neg (fun h => hfix h.1), meyerPositiveDegree_off_line_jet_zero d hd hpos q.1.1 hfix q.2,
      mul_zero]

/-- The same classification applies directly to the original finite causal section. -/
theorem meyerPositiveDegree_finite_causal_formula
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hd : ∀ u, d (meyerCohomologySharp u) = conj (d u))
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (S : Finset XiDivisorSupport) (c : DeningerMeyerFiniteXiJetPacket S) :
    d (deningerMeyerFiniteXiCausalSection S c) =
      ∑ q : DeningerMeyerFiniteXiJetSlot S,
        if meyerLineReflect q.1.1 = q.1.1 ∧ q.2.val = 0 then
          c q * ((d (meyerHasseJetClass q.1.1 q.2)).re : ℂ) else 0 := by
  rw [meyerFiniteXiCausalSection_eq_hasse_sum,
    meyerPositiveDegree_finite_jet_formula d hd hpos]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs with h
  · rw [h.2]
    simp only [Nat.factorial_zero, Nat.cast_one, div_one]
  · rfl

/-- Finite real weights on actual value degrees define a linear degree on the whole quotient. -/
def meyerFiniteCriticalDegree (S : Finset XiDivisorSupport) (w : XiDivisorSupport → ℝ) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ :=
  ∑ rho ∈ S, (w rho : ℂ) • meyerPointDegree rho

private theorem critical_point_degree_sharp (rho : XiDivisorSupport)
    (hr : (rho : ℂ).re = 1 / 2) (u : DeningerMeyerStrongLogCohomology) :
    meyerPointDegree rho (meyerCohomologySharp u) = conj (meyerPointDegree rho u) := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    have href : star (1 - (rho : ℂ)) = (rho : ℂ) := by
      apply Complex.ext
      · change 1 - (rho : ℂ).re = (rho : ℂ).re
        rw [hr]
        norm_num
      · change -(0 - (rho : ℂ).im) = (rho : ℂ).im
        ring
    rw [meyerCohomologySharp_mk, meyerPointDegree_mk, meyerPointDegree_mk,
      deningerMeyerSourceSharp_mellin, href]
    rfl

/-- Every finite real weighting of critical values is Hermitian on genuine cohomology. -/
theorem meyerFiniteCriticalDegree_hermitian (S : Finset XiDivisorSupport)
    (w : XiDivisorSupport → ℝ) (hcrit : ∀ rho ∈ S, (rho : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    meyerFiniteCriticalDegree S w (meyerCohomologySharp u) =
      conj (meyerFiniteCriticalDegree S w u) := by
  simp only [meyerFiniteCriticalDegree, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro rho hr
  rw [critical_point_degree_sharp rho (hcrit rho hr)]

/-- Nonnegative critical weights give nonnegative sharp-square degree on every actual class. -/
theorem meyerFiniteCriticalDegree_nonnegative (S : Finset XiDivisorSupport)
    (w : XiDivisorSupport → ℝ) (hcrit : ∀ rho ∈ S, (rho : ℂ).re = 1 / 2)
    (hw : ∀ rho ∈ S, 0 ≤ w rho) (u : DeningerMeyerStrongLogCohomology) :
    0 ≤ (meyerDegreePair (meyerFiniteCriticalDegree S w) u u).re := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    simp only [meyerDegreePair, meyerCohomologySharp_mk,
      deningerMeyerCohomologyConvolution_mk, meyerFiniteCriticalDegree,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Complex.re_sum]
    apply Finset.sum_nonneg
    intro rho hr
    rw [meyerPointDegree_sharp_square rho (hcrit rho hr), Complex.re_ofReal_mul,
      Complex.ofReal_re]
    exact mul_nonneg (hw rho hr) (Complex.normSq_nonneg _)

/-- The converse construction has exactly the prescribed finite value weights and no jet weights. -/
theorem meyerFiniteCriticalDegree_hasse_class (S : Finset XiDivisorSupport)
    (w : XiDivisorSupport → ℝ) (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) :
    meyerFiniteCriticalDegree S w (meyerHasseJetClass rho j) =
      if rho ∈ S ∧ j.val = 0 then (w rho : ℂ) else 0 := by
  simp only [meyerFiniteCriticalDegree, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, meyerPointDegree, meyerHasseJetClass_raw_jet]
  by_cases hj : j.val = 0
  · simp [hj]
  · have hj' : (0 : ℕ) ≠ j.val := Ne.symm hj
    simp only [hj', and_false, ↓reduceIte, mul_zero, Finset.sum_const_zero, hj]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

