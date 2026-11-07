import GaloisForLFunctions.ArithmeticScatteringHolography.TheParallelogramLawOfHeights
import GaloisForLFunctions.ArithmeticScatteringHolography.TheCountLawOfTheProbes
import GaloisForLFunctions.RHTower.EllipticCurveHasseBound
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The count law of a true curve

**The count law holds on a true curve, and this reproves Hasse's theorem from the conservation of channels at all probes, without Stepanov.** On the twisted curve over `𝔽_q(T)` there are two
natural points: the generic point `P₀ = (T, 1)` and the Frobenius point `P₁ = (T^q, h(T)^{(q-1)/2})`. The function

  `K(x, y) = ht(y P₀ - x P₁)`

is the degree of `y - x F`. It obeys the parallelogram law because the height does (`height_parallelogram`), with `K(0, 1) = 1` and `K(1, 0) = q`. And `K(1, 1)` is the number of points:

  `X(P₀ - P₁) = N / (T^q - T)²`,  `N = h (1 + h^{(q-1)/2})² - (a + T + T^q)(T^q - T)²`

(`xCoord_sub`), and at a point `c ∈ 𝔽_q` of the `x`-line this fraction loses `1 - χ(h(c))` powers of `T - c` (`numer_factor`): the pole has order `1 + χ(h(c))`, the number of points of the curve above `c`. So
`K(1, 1) = #E(𝔽_q)` (`height_sub_eq`, `manin_countLaw`). Then `CountLaw.universal` gives `t² ≤ 4q` (`hasse_of_countLaw`).

This is Manin's elementary proof of Hasse's theorem, in the language of the black hole: the first instance of the law is the local count of the graph, and the content of the theorem is all the others.
-/

open Polynomial Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

attribute [local instance] Classical.propDecidable

/-! ### The numerator -/

section Numerator

variable {F : Type*} [Field F] [Fintype F]

local notation "q" => Fintype.card F
local notation "M" => (Fintype.card F / 2)

variable (a b c : F)

/-- `1 + h^{(q-1)/2}`. -/
def gFactor : F[X] := 1 + cubicPoly a b c ^ M

/-- `T^q - T`. -/
def dqPoly (F : Type*) [Field F] [Fintype F] : F[X] := X ^ Fintype.card F - X

/-- `a + T + T^q`. -/
def wPoly : F[X] := C a + X + X ^ q

/-- The numerator of `X(P₀ - P₁)`. -/
def numerPoly : F[X] := cubicPoly a b c * gFactor a b c ^ 2 - wPoly a * dqPoly F ^ 2

variable {a b c}

theorem card_eq_of_odd (hF : ringChar F ≠ 2) : q = 2 * M + 1 := by
  have h := FiniteField.odd_card_of_char_ne_two hF
  omega

theorem one_le_half (hF : ringChar F ≠ 2) : 1 ≤ M := by
  have h := card_eq_of_odd hF
  have h1 := Fintype.one_lt_card (α := F)
  omega

/-- **Frobenius on the cubic**: `h^q = h(T^q)`. -/
theorem cubic_pow_card :
    cubicPoly a b c ^ q = (X ^ q) ^ 3 + C a * (X ^ q) ^ 2 + C b * X ^ q + C c := by
  rw [← FiniteField.expand_card]
  simp [cubicPoly, expand_X]

theorem numer_expand (hF : ringChar F ≠ 2) :
    numerPoly a b c = X ^ (2 * q + 1) +
      (X ^ (q + 2) + C (2 * a) * X ^ (q + 1) + C b * X ^ q + 2 * cubicPoly a b c ^ (M + 1) + C b * X +
        C (2 * c)) := by
  have hq := card_eq_of_odd hF
  have hfrob := cubic_pow_card (a := a) (b := b) (c := c)
  have hp : cubicPoly a b c ^ q = cubicPoly a b c * (cubicPoly a b c ^ M) ^ 2 := by
    conv_lhs => rw [hq]
    ring
  rw [hp] at hfrob
  unfold numerPoly gFactor wPoly dqPoly
  rw [pow_add X (2 * q) 1, pow_mul' X 2 q, pow_add X q 2, pow_add X q 1, pow_add (cubicPoly a b c) M 1]
  generalize (X : F[X]) ^ q = Y at *
  generalize hE : cubicPoly a b c ^ M = E at *
  have hC2a : C (2 * a) = 2 * C a := by
    rw [C_mul, map_ofNat]
  have hC2c : C (2 * c) = 2 * C c := by
    rw [C_mul, map_ofNat]
  rw [hC2a, hC2c]
  unfold cubicPoly at hfrob ⊢
  linear_combination hfrob

/-- The numerator is monic of degree `2q + 1`. -/
theorem numer_monic_natDegree (hF : ringChar F ≠ 2) :
    (numerPoly a b c).Monic ∧ (numerPoly a b c).natDegree = 2 * q + 1 := by
  have hq := card_eq_of_odd hF
  have hq1 := Fintype.one_lt_card (α := F)
  set R : F[X] := X ^ (q + 2) + C (2 * a) * X ^ (q + 1) + C b * X ^ q + 2 * cubicPoly a b c ^ (M + 1) +
    C b * X + C (2 * c) with hR
  have hH : (cubicPoly a b c).natDegree ≤ 3 := by
    unfold cubicPoly
    compute_degree
  have hdeg : R.natDegree ≤ 2 * q := by
    have h1 : (X ^ (q + 2) : F[X]).natDegree ≤ 2 * q := by
      rw [natDegree_X_pow]
      omega
    have h2 : (C (2 * a) * X ^ (q + 1) : F[X]).natDegree ≤ 2 * q :=
      (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)
    have h3 : (C b * X ^ q : F[X]).natDegree ≤ 2 * q :=
      (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)
    have h4 : (2 * cubicPoly a b c ^ (M + 1) : F[X]).natDegree ≤ 2 * q := by
      have e : (2 : F[X]) = C 2 := (map_ofNat C 2).symm
      rw [e]
      refine (natDegree_C_mul_le _ _).trans ?_
      refine natDegree_pow_le.trans ?_
      have : (M + 1) * (cubicPoly a b c).natDegree ≤ (M + 1) * 3 := Nat.mul_le_mul_left _ hH
      omega
    have h5 : (C b * X : F[X]).natDegree ≤ 2 * q :=
      (natDegree_C_mul_le _ _).trans (by rw [natDegree_X]; omega)
    have h6 : (C (2 * c) : F[X]).natDegree ≤ 2 * q := by
      rw [natDegree_C]
      omega
    rw [hR]
    exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le h1 h2) h3) h4) h5) h6
  have hlt : R.degree < ((2 * q + 1 : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt (degree_le_of_natDegree_le hdeg) (by exact_mod_cast Nat.lt_succ_self _)
  have e := numer_expand (a := a) (b := b) (c := c) hF
  rw [← hR] at e
  rw [e]
  refine ⟨monic_X_pow_add hlt, ?_⟩
  rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]

/-- `T^q - T` is the product of the `T - c`. -/
theorem dq_eq_prod : dqPoly F = ∏ c : F, (X - Polynomial.C c) := by
  have hq1 := Fintype.one_lt_card (α := F)
  have hmonic : (dqPoly F).Monic := by
    unfold dqPoly
    have hd : (X : F[X]).degree < (q : ℕ) := by
      rw [degree_X]
      exact_mod_cast hq1
    rw [sub_eq_add_neg]
    apply monic_X_pow_add
    rwa [degree_neg]
  have hroots := FiniteField.roots_X_pow_card_sub_X F
  have hcard : Multiset.card (dqPoly F).roots = (dqPoly F).natDegree := by
    unfold dqPoly
    rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq F hq1]
    simp
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  rw [← h]
  unfold dqPoly
  rw [hroots]
  rfl

/-! ### The factorization at the rational places -/

variable (a b c) in
/-- The exponent `1 - χ(h(c))` of `T - c` in the common factor. -/
def lossExp (t : F) : ℕ := (1 - (quadraticChar F ((cubicPoly a b c).eval t) : ℤ)).toNat

theorem lossExp_cases (hF : ringChar F ≠ 2) (t : F) :
    (quadraticChar F ((cubicPoly a b c).eval t) = 1 ∧ lossExp a b c t = 0 ∧
        (cubicPoly a b c).eval t ≠ 0 ∧ (cubicPoly a b c).eval t ^ M = 1) ∨
      (quadraticChar F ((cubicPoly a b c).eval t) = 0 ∧ lossExp a b c t = 1 ∧
        (cubicPoly a b c).eval t = 0) ∨
      (quadraticChar F ((cubicPoly a b c).eval t) = -1 ∧ lossExp a b c t = 2 ∧
        (cubicPoly a b c).eval t ^ M = -1) := by
  have hpow := quadraticChar_eq_pow_of_char_ne_two' hF ((cubicPoly a b c).eval t)
  by_cases h0 : (cubicPoly a b c).eval t = 0
  · right; left
    have hχ := quadraticChar_eq_zero_iff.mpr h0
    refine ⟨hχ, ?_, h0⟩
    simp [lossExp, hχ]
  · rcases quadraticChar_dichotomy h0 with h1 | h1
    · left
      refine ⟨h1, by simp [lossExp, h1], h0, ?_⟩
      rw [h1] at hpow
      simpa using hpow.symm
    · right; right
      refine ⟨h1, by simp [lossExp, h1], ?_⟩
      rw [h1] at hpow
      simpa using hpow.symm

/-- The common factor. -/
def commonFactor (a b c : F) : F[X] := ∏ t : F, (X - Polynomial.C t) ^ lossExp a b c t

/-- The reduced denominator. -/
def reducedDenom (a b c : F) : F[X] := ∏ t : F, (X - Polynomial.C t) ^ (2 - lossExp a b c t)

theorem lossExp_le (hF : ringChar F ≠ 2) (t : F) : lossExp a b c t ≤ 2 := by
  rcases lossExp_cases (a := a) (b := b) (c := c) hF t with h | h | h <;> omega

theorem commonFactor_mul (hF : ringChar F ≠ 2) :
    commonFactor a b c * reducedDenom a b c = dqPoly F ^ 2 := by
  unfold commonFactor reducedDenom
  rw [dq_eq_prod, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [← pow_add, Nat.add_sub_cancel' (lossExp_le hF t)]

theorem commonFactor_monic : (commonFactor a b c).Monic :=
  monic_prod_of_monic _ _ fun t _ => (monic_X_sub_C t).pow _

theorem reducedDenom_monic : (reducedDenom a b c).Monic :=
  monic_prod_of_monic _ _ fun t _ => (monic_X_sub_C t).pow _

theorem natDegree_commonFactor : (commonFactor a b c).natDegree = ∑ t : F, lossExp a b c t := by
  unfold commonFactor
  rw [natDegree_prod_of_monic _ _ fun t _ => (monic_X_sub_C t).pow _]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [(monic_X_sub_C t).natDegree_pow, natDegree_X_sub_C, mul_one]

theorem natDegree_reducedDenom : (reducedDenom a b c).natDegree = ∑ t : F, (2 - lossExp a b c t) := by
  unfold reducedDenom
  rw [natDegree_prod_of_monic _ _ fun t _ => (monic_X_sub_C t).pow _]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [(monic_X_sub_C t).natDegree_pow, natDegree_X_sub_C, mul_one]

theorem eval_dq (t : F) : (dqPoly F).eval t = 0 := by
  unfold dqPoly
  simp [FiniteField.pow_card]

theorem eval_numer (t : F) :
    (numerPoly a b c).eval t = (cubicPoly a b c).eval t * (1 + (cubicPoly a b c).eval t ^ M) ^ 2 := by
  unfold numerPoly gFactor
  simp [eval_dq]

/-- **The common factor divides the numerator.** -/
theorem commonFactor_dvd (hF : ringChar F ≠ 2) : commonFactor a b c ∣ numerPoly a b c := by
  unfold commonFactor
  refine Finset.prod_dvd_of_coprime ?_ fun t _ => ?_
  · intro s _ t _ hst
    exact (pairwise_coprime_X_sub_C (s := fun x : F => x) Function.injective_id hst).pow
  · have hdq : (X - Polynomial.C t) ∣ dqPoly F := dvd_iff_isRoot.mpr (eval_dq t)
    rcases lossExp_cases (a := a) (b := b) (c := c) hF t with ⟨_, he, _, _⟩ | ⟨_, he, h0⟩ | ⟨_, he, hm⟩
    · rw [he, pow_zero]
      exact one_dvd _
    · rw [he, pow_one, dvd_iff_isRoot, IsRoot, eval_numer, h0]
      simp
    · rw [he]
      have hg : (X - Polynomial.C t) ∣ gFactor a b c := by
        rw [dvd_iff_isRoot, IsRoot]
        unfold gFactor
        simp [hm]
      unfold numerPoly
      exact dvd_sub (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hg 2) _)
        (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hdq 2) _)

theorem eval_derivative_numer (t : F) (hdq : (dqPoly F).eval t = 0) :
    (derivative (numerPoly a b c)).eval t =
      (derivative (cubicPoly a b c)).eval t * (gFactor a b c).eval t ^ 2 +
        (cubicPoly a b c).eval t * (2 * (gFactor a b c).eval t * (derivative (gFactor a b c)).eval t) := by
  unfold numerPoly
  rw [derivative_sub, derivative_mul, derivative_mul]
  simp [hdq, derivative_pow]

variable (a b c) in
/-- The numerator after removing the common factor. -/
def reducedNumer (hF : ringChar F ≠ 2) : F[X] := Classical.choose (commonFactor_dvd (a := a) (b := b) (c := c) hF)

theorem reducedNumer_spec (hF : ringChar F ≠ 2) :
    numerPoly a b c = commonFactor a b c * reducedNumer a b c hF :=
  Classical.choose_spec (commonFactor_dvd (a := a) (b := b) (c := c) hF)

/-- **The reduced fraction is primitive**: the numerator keeps exactly the pole of order `1 + χ(h(c))` at `c`. -/
theorem reduced_coprime (hF : ringChar F ≠ 2)
    (hcop : IsCoprime (cubicPoly a b c) (derivative (cubicPoly a b c))) :
    IsCoprime (reducedNumer a b c hF) (reducedDenom a b c) := by
  unfold reducedDenom
  refine IsCoprime.prod_right fun t _ => ?_
  have hspec := reducedNumer_spec (a := a) (b := b) (c := c) hF
  rcases lossExp_cases (a := a) (b := b) (c := c) hF t with ⟨_, he, h0, h1⟩ | ⟨_, he, h0⟩ | ⟨_, he, _⟩
  · -- a point of the line with two rational points above it
    refine IsCoprime.pow_right ?_
    have hne : ¬ (X - Polynomial.C t) ∣ reducedNumer a b c hF := by
      intro hd
      have hroot : (reducedNumer a b c hF).eval t = 0 := dvd_iff_isRoot.mp hd
      have hN := congrArg (eval t) hspec
      rw [eval_numer, eval_mul, hroot, mul_zero, h1] at hN
      have h4 : (1 + 1 : F) ^ 2 ≠ 0 := by
        have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
        rw [one_add_one_eq_two]
        exact pow_ne_zero 2 h2
      exact (mul_ne_zero h0 h4) hN
    exact ((irreducible_X_sub_C t).coprime_iff_not_dvd.mpr hne).symm
  · -- a point of the line with one rational point above it
    refine IsCoprime.pow_right ?_
    have hne : ¬ (X - Polynomial.C t) ∣ reducedNumer a b c hF := by
      intro hd
      have hE : (X - Polynomial.C t) ∣ commonFactor a b c := by
        unfold commonFactor
        refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ t))
        rw [he, pow_one]
      have hsq : (X - Polynomial.C t) ^ 2 ∣ numerPoly a b c := by
        rw [hspec, pow_two]
        exact mul_dvd_mul hE hd
      obtain ⟨k, hk⟩ := hsq
      have hder : (derivative (numerPoly a b c)).eval t = 0 := by
        rw [hk, derivative_mul, derivative_pow]
        simp
      rw [eval_derivative_numer t (eval_dq t), h0, zero_mul, add_zero] at hder
      have hG : (gFactor a b c).eval t = 1 := by
        unfold gFactor
        have hM : M ≠ 0 := Nat.one_le_iff_ne_zero.mp (one_le_half hF)
        simp [h0, hM]
      rw [hG, one_pow, mul_one, derivative_cubicPoly] at hder
      have hs := cubic_sep (RingHom.id F) hcop t (by
        have := h0
        unfold cubicPoly at this
        simpa using this)
      apply hs
      simpa using hder
    exact ((irreducible_X_sub_C t).coprime_iff_not_dvd.mpr hne).symm
  · -- no rational point above: the factor of the denominator is trivial
    rw [he, Nat.sub_self, pow_zero]
    exact isCoprime_one_right

theorem natDegree_reducedNumer (hF : ringChar F ≠ 2) :
    (reducedNumer a b c hF).natDegree + ∑ t : F, lossExp a b c t = 2 * q + 1 := by
  have hspec := reducedNumer_spec (a := a) (b := b) (c := c) hF
  obtain ⟨hm, hd⟩ := numer_monic_natDegree (a := a) (b := b) (c := c) hF
  have hne : reducedNumer a b c hF ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hspec
    exact hm.ne_zero hspec
  have hd' := congrArg natDegree hspec
  rw [natDegree_mul commonFactor_monic.ne_zero hne, natDegree_commonFactor, hd] at hd'
  omega

/-- The sum of the exponents and of their complements is `2q`. -/
theorem sum_exp_add (hF : ringChar F ≠ 2) :
    ∑ t : F, (2 - lossExp a b c t) + ∑ t : F, lossExp a b c t = 2 * q := by
  rw [← Finset.sum_add_distrib]
  have : ∀ t : F, 2 - lossExp a b c t + lossExp a b c t = 2 := fun t =>
    Nat.sub_add_cancel (lossExp_le hF t)
  simp only [this, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

/-- `2 - e(c) = 1 + χ(h(c))`: the number of points of the curve above `c`. -/
theorem sum_compl_eq (hF : ringChar F ≠ 2) :
    ((∑ t : F, (2 - lossExp a b c t) : ℕ) : ℤ) =
      ∑ t : F, quadraticChar F ((cubicPoly a b c).eval t) + (q : ℤ) := by
  have hc : (q : ℤ) = ∑ _t : F, (1 : ℤ) := by simp
  rw [hc, ← Finset.sum_add_distrib]
  push_cast
  refine Finset.sum_congr rfl fun t _ => ?_
  rcases lossExp_cases (a := a) (b := b) (c := c) hF t with ⟨h, he, _, _⟩ | ⟨h, he, _⟩ | ⟨h, he, _⟩ <;>
    · rw [h, he]
      simp

end Numerator

/-! ### The two points -/

section Points

variable {F : Type*} [Field F]

local notation "cast" => algebraMap F[X] (RatFunc F)

/-- A fraction in lowest terms has the degrees of its terms. -/
theorem natDegree_num_denom_div {u v : F[X]} (hcop : IsCoprime u v) (hv : v ≠ 0) :
    (RatFunc.num (cast u / cast v)).natDegree = u.natDegree ∧
      (RatFunc.denom (cast u / cast v)).natDegree = v.natDegree := by
  set Z := cast u / cast v with hZ
  have hcv : cast v ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective F)]
    exact hv
  have hcross : RatFunc.num Z * v = u * RatFunc.denom Z := by
    apply RatFunc.algebraMap_injective F
    rw [map_mul, map_mul, cast_num_eq Z, hZ]
    field_simp
  have hc' := RatFunc.isCoprime_num_denom Z
  have hd1 : u ∣ RatFunc.num Z := hcop.dvd_of_dvd_mul_right ⟨RatFunc.denom Z, hcross⟩
  have hd2 : RatFunc.num Z ∣ u := hc'.dvd_of_dvd_mul_right ⟨v, hcross.symm⟩
  have hd3 : v ∣ RatFunc.denom Z :=
    hcop.symm.dvd_of_dvd_mul_left ⟨RatFunc.num Z, by rw [← hcross]; ring⟩
  have hd4 : RatFunc.denom Z ∣ v :=
    hc'.symm.dvd_of_dvd_mul_left ⟨u, by rw [hcross]; ring⟩
  have hdn := RatFunc.denom_ne_zero Z
  refine ⟨?_, le_antisymm (natDegree_le_of_dvd hd4 hv) (natDegree_le_of_dvd hd3 hdn)⟩
  by_cases hu : u = 0
  · subst hu
    have : RatFunc.num Z = 0 := zero_dvd_iff.mp hd1
    rw [this]
  · have hn : RatFunc.num Z ≠ 0 := by
      intro h0
      rw [h0] at hd2
      exact hu (zero_dvd_iff.mp hd2)
    exact le_antisymm (natDegree_le_of_dvd hd2 hu) (natDegree_le_of_dvd hd1 hn)

variable {a b c : F}

/-- A point of the twisted curve from a solution of `h(T) Y² = h(X)`. -/
theorem frame_nonsingular (h2K : (2 : RatFunc F) ≠ 0) {X₀ Y₀ : RatFunc F}
    (hXY : twistD a b c * Y₀ ^ 2 = X₀ ^ 3 + cast (C a) * X₀ ^ 2 + cast (C b) * X₀ + cast (C c))
    (hY : Y₀ ≠ 0) :
    (twistCurve a b c).toAffine.Nonsingular (twistD a b c * X₀) (twistD a b c ^ 2 * Y₀) := by
  have hD := twistD_ne_zero (a := a) (b := b) (c := c)
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  refine ⟨?_, Or.inr ?_⟩
  · refine (twist_equation (α := cast (C a)) (β := cast (C b)) (γ := cast (C c)) (D := twistD a b c)).mpr ?_
    linear_combination (twistD a b c) ^ 3 * hXY
  · simp only [twistCurve, twistCurveOf]
    intro he
    have h0 : 2 * (twistD a b c ^ 2 * Y₀) = 0 := by
      simp only [zero_mul, sub_zero] at he
      linear_combination he
    exact (mul_ne_zero h2K (mul_ne_zero (pow_ne_zero 2 hD) hY)) h0

theorem cast_cubic : twistD a b c =
    RatFunc.X ^ 3 + cast (C a) * RatFunc.X ^ 2 + cast (C b) * RatFunc.X + cast (C c) := by
  unfold twistD cubicPoly
  simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X]

/-- **The generic point** `(T, 1)`. -/
def genericPoint (h2K : (2 : RatFunc F) ≠ 0) : (twistCurve a b c).toAffine.Point :=
  .some _ _ (frame_nonsingular (a := a) (b := b) (c := c) h2K (X₀ := RatFunc.X) (Y₀ := 1)
    (by rw [one_pow, mul_one]; exact cast_cubic) one_ne_zero)

theorem xPair_frame {X₀ y : RatFunc F}
    (h : (twistCurve a b c).toAffine.Nonsingular (twistD a b c * X₀) y) :
    xPair a b c (.some _ _ h) = (RatFunc.num X₀, RatFunc.denom X₀) := by
  have hD := twistD_ne_zero (a := a) (b := b) (c := c)
  have e : twistD a b c * X₀ / twistD a b c = X₀ := by field_simp
  show (RatFunc.num (twistD a b c * X₀ / twistD a b c), RatFunc.denom (twistD a b c * X₀ / twistD a b c)) = _
  rw [e]

/-- The generic point has height one. -/
theorem height_generic (h2K : (2 : RatFunc F) ≠ 0) : height a b c (genericPoint h2K) = 1 := by
  unfold height genericPoint
  rw [xPair_frame]
  simp [pairDeg, RatFunc.num_X, RatFunc.denom_X]

variable [Fintype F]

local notation "q" => Fintype.card F
local notation "M" => (Fintype.card F / 2)

theorem frobenius_relation (hF : ringChar F ≠ 2) :
    twistD a b c * (twistD a b c ^ M) ^ 2 =
      (RatFunc.X ^ q) ^ 3 + cast (C a) * (RatFunc.X ^ q) ^ 2 + cast (C b) * RatFunc.X ^ q + cast (C c) := by
  have hq := card_eq_of_odd hF
  have h := congrArg cast (cubic_pow_card (a := a) (b := b) (c := c))
  simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X] at h
  rw [← h]
  unfold twistD
  conv_rhs => rw [hq]
  ring

/-- **The Frobenius point** `(T^q, h(T)^{(q-1)/2})`. -/
def frobeniusPoint (hF : ringChar F ≠ 2) (h2K : (2 : RatFunc F) ≠ 0) : (twistCurve a b c).toAffine.Point :=
  .some _ _ (frame_nonsingular (a := a) (b := b) (c := c) h2K (X₀ := RatFunc.X ^ q) (Y₀ := twistD a b c ^ M)
    (frobenius_relation hF) (pow_ne_zero _ twistD_ne_zero))

/-- The Frobenius point has height `q`. -/
theorem height_frobenius (hF : ringChar F ≠ 2) (h2K : (2 : RatFunc F) ≠ 0) :
    height a b c (frobeniusPoint hF h2K) = q := by
  unfold height frobeniusPoint
  rw [xPair_frame]
  have e : (RatFunc.X : RatFunc F) ^ q = cast (X ^ q) := by
    rw [map_pow, RatFunc.algebraMap_X]
  simp only [e, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp [pairDeg]

theorem cast_dq_ne : cast (dqPoly F) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective F)]
  exact FiniteField.X_pow_card_sub_X_ne_zero F Fintype.one_lt_card

theorem cast_dq : cast (dqPoly F) = (RatFunc.X : RatFunc F) ^ q - RatFunc.X := by
  unfold dqPoly
  simp only [map_sub, map_pow, RatFunc.algebraMap_X]

/-- **The `X`-coordinate of `P₀ - P₁`.** -/
theorem xCoord_sub (hF : ringChar F ≠ 2) (h2K : (2 : RatFunc F) ≠ 0) :
    xPair a b c (genericPoint h2K - frobeniusPoint hF h2K) =
      (RatFunc.num (cast (numerPoly a b c) / cast (dqPoly F ^ 2)),
        RatFunc.denom (cast (numerPoly a b c) / cast (dqPoly F ^ 2))) := by
  have hD := twistD_ne_zero (a := a) (b := b) (c := c)
  have hne := cast_dq_ne (F := F)
  rw [cast_dq] at hne
  have hTT : (RatFunc.X : RatFunc F) - RatFunc.X ^ q ≠ 0 := by
    intro h
    apply hne
    linear_combination -h
  have hx : twistD a b c * RatFunc.X ≠ twistD a b c * RatFunc.X ^ q := by
    intro h
    exact hTT (sub_eq_zero.mpr (mul_left_cancel₀ hD h))
  unfold genericPoint frobeniusPoint
  rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  show (RatFunc.num _, RatFunc.denom _) = _
  have hval : (twistCurve a b c).toAffine.addX (twistD a b c * RatFunc.X) (twistD a b c * RatFunc.X ^ q)
      ((twistCurve a b c).toAffine.slope (twistD a b c * RatFunc.X) (twistD a b c * RatFunc.X ^ q)
        (twistD a b c ^ 2 * 1)
        ((twistCurve a b c).toAffine.negY (twistD a b c * RatFunc.X ^ q) (twistD a b c ^ 2 * twistD a b c ^ M))) /
      twistD a b c = cast (numerPoly a b c) / cast (dqPoly F ^ 2) := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    have hneg : (twistCurve a b c).toAffine.negY (twistD a b c * RatFunc.X ^ q)
        (twistD a b c ^ 2 * twistD a b c ^ M) = -(twistD a b c ^ 2 * twistD a b c ^ M) :=
      twist_negY (α := cast (C a)) (β := cast (C b)) (γ := cast (C c)) (D := twistD a b c) _ _
    rw [hneg]
    unfold numerPoly gFactor wPoly
    rw [map_pow, map_sub, map_mul, map_mul, map_pow, map_add, map_one, map_pow, map_pow, map_add, map_add,
      map_pow, cast_dq, RatFunc.algebraMap_X]
    simp only [WeierstrassCurve.Affine.addX, twistCurve, twistCurveOf]
    change _ = (twistD a b c * (1 + twistD a b c ^ M) ^ 2 - _) / _
    generalize twistD a b c ^ M = E
    generalize (RatFunc.X : RatFunc F) ^ q = T' at hTT hne ⊢
    generalize (RatFunc.X : RatFunc F) = T at hTT hne ⊢
    have h1 : T - T' ≠ 0 := hTT
    have h2 : T' - T ≠ 0 := hne
    have e : T * twistD a b c - T' * twistD a b c ≠ 0 := by
      rw [← sub_mul]
      exact mul_ne_zero h1 hD
    have e' : twistD a b c * T - twistD a b c * T' ≠ 0 := by
      rw [← mul_sub]
      exact mul_ne_zero hD h1
    field_simp
    ring
  rw [hval]

/-- **`K(1, 1)` is the number of points**: the height of `P₀ - P₁` is one more than the sum of `1 + χ(h(c))`. -/
theorem height_sub_eq (hF : ringChar F ≠ 2) (h2K : (2 : RatFunc F) ≠ 0)
    (hcop : IsCoprime (cubicPoly a b c) (derivative (cubicPoly a b c))) :
    height a b c (genericPoint h2K - frobeniusPoint hF h2K) = 1 + ∑ t : F, (2 - lossExp a b c t) := by
  unfold height
  rw [xCoord_sub hF h2K]
  have hE : cast (commonFactor a b c) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective F)]
    exact commonFactor_monic.ne_zero
  have hfrac : cast (numerPoly a b c) / cast (dqPoly F ^ 2) =
      cast (reducedNumer a b c hF) / cast (reducedDenom a b c) := by
    rw [reducedNumer_spec hF, ← commonFactor_mul hF, map_mul, map_mul, mul_div_mul_left _ _ hE]
  rw [hfrac]
  obtain ⟨h1, h2⟩ := natDegree_num_denom_div (reduced_coprime hF hcop) reducedDenom_monic.ne_zero
  simp only [pairDeg]
  rw [h1, h2, natDegree_reducedDenom]
  have hu := natDegree_reducedNumer (a := a) (b := b) (c := c) hF
  have hs := sum_exp_add (a := a) (b := b) (c := c) hF
  omega

/-- **The count law on the twisted curve.** -/
theorem manin_countLaw (hF : ringChar F ≠ 2)
    (hcop : IsCoprime (cubicPoly a b c) (derivative (cubicPoly a b c))) :
    ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ K 0 1 = 1 ∧ K 1 0 = q ∧
      K 1 1 = 1 + ∑ t : F, (2 - lossExp a b c t) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h2K := two_ne_zero_ratFunc h2
  set P₀ : (twistCurve a b c).toAffine.Point := genericPoint h2K with hP₀
  set P₁ : (twistCurve a b c).toAffine.Point := frobeniusPoint hF h2K with hP₁
  refine ⟨fun x y => height a b c (y • P₀ - x • P₁), ?_, ?_, ?_, ?_⟩
  · intro x y u v
    have h := height_parallelogram h2 hcop (y • P₀ - x • P₁) (v • P₀ - u • P₁)
    have e1 : (y • P₀ - x • P₁) + (v • P₀ - u • P₁) = (y + v) • P₀ - (x + u) • P₁ := by
      rw [add_zsmul, add_zsmul]
      abel
    have e2 : (y • P₀ - x • P₁) - (v • P₀ - u • P₁) = (y - v) • P₀ - (x - u) • P₁ := by
      rw [sub_zsmul, sub_zsmul]
      abel
    rw [e1, e2] at h
    exact_mod_cast h
  · simp only [one_zsmul, zero_zsmul, sub_zero]
    exact height_generic h2K
  · simp only [one_zsmul, zero_zsmul, zero_sub]
    rw [height_neg]
    exact height_frobenius hF h2K
  · simp only [one_zsmul]
    exact height_sub_eq hF h2K hcop

end Points

/-! ### The true curve -/

section Curve

open RHTower.EllipticHasse

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F)

/-- The monic cubic of a Weierstrass curve in odd characteristic. -/
def monicCubic : F[X] := cubicPoly (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)

omit [Fintype F] in
/-- The `2`-torsion polynomial is `4` times the monic cubic. -/
theorem twoTorsion_eq (hF : ringChar F ≠ 2) : twoTorsionPoly W = Polynomial.C 4 * monicCubic W := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hC4 : Polynomial.C (4 : F) * Polynomial.C (W.b₂ / 4) = Polynomial.C W.b₂ := by
    rw [← Polynomial.C_mul]
    congr 1
    field_simp
  have hC2 : Polynomial.C (4 : F) * Polynomial.C (W.b₄ / 2) = Polynomial.C (2 * W.b₄) := by
    rw [← Polynomial.C_mul]
    congr 1
    field_simp
    ring
  have hC6 : Polynomial.C (4 : F) * Polynomial.C (W.b₆ / 4) = Polynomial.C W.b₆ := by
    rw [← Polynomial.C_mul]
    congr 1
    field_simp
  simp only [twoTorsionPoly, Cubic.toPoly, WeierstrassCurve.twoTorsionPolynomial, monicCubic, cubicPoly]
  have e : ∀ A B D : F[X], Polynomial.C (4 : F) * (X ^ 3 + A * X ^ 2 + B * X + D) =
      Polynomial.C 4 * X ^ 3 + (Polynomial.C 4 * A) * X ^ 2 + (Polynomial.C 4 * B) * X +
        Polynomial.C 4 * D := fun A B D => by ring
  rw [e, hC4, hC2, hC6]

/-- The monic cubic of an elliptic curve is separable. -/
theorem monicCubic_coprime (hF : ringChar F ≠ 2) [W.IsElliptic] :
    IsCoprime (monicCubic W) (derivative (monicCubic W)) := by
  have hsq := squarefree_twoTorsionPoly W hF
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  rw [twoTorsion_eq W hF] at hsq
  have hsq' : Squarefree (monicCubic W) := hsq.squarefree_of_dvd (Dvd.intro_left _ rfl)
  exact (PerfectField.separable_iff_squarefree.mpr hsq')

/-- The count of the affine points is the sum of `1 + χ(h(c))`. -/
theorem card_affine_eq_sum (hF : ringChar F ≠ 2) :
    ((Fintype.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} : ℕ) : ℤ) =
      ∑ t : F, quadraticChar F ((monicCubic W).eval t) + (Fintype.card F : ℤ) := by
  rw [card_equation_eq W hF, GaloisForLFunctions.RHTower.Hyperelliptic.card_points_eq hF]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rw [twoTorsion_eq W hF, eval_mul, eval_C, map_mul]
  have h4 : quadraticChar F 4 = 1 := by
    have := quadraticChar_sq_one' h2
    rwa [show (2 : F) ^ 2 = 4 by norm_num] at this
  rw [h4, one_mul]

/-- **The count law holds on a true curve, independently of Hasse's theorem.** -/
theorem elliptic_has_countLaw (hF : ringChar F ≠ 2) [W.IsElliptic] :
    ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ K 0 1 = 1 ∧ K 1 0 = Fintype.card F ∧
      K 1 1 = Nat.card W.toAffine.Point := by
  obtain ⟨K, hK, h01, h10, h11⟩ := manin_countLaw (a := W.b₂ / 4) (b := W.b₄ / 2) (c := W.b₆ / 4) hF
    (monicCubic_coprime W hF)
  refine ⟨K, hK, h01, h10, ?_⟩
  rw [h11]
  have hcard : Nat.card W.toAffine.Point =
      Fintype.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} + 1 := by
    rw [Nat.card_congr (WeierstrassCurve.Affine.pointEquiv W.toAffine), WithZero,
      Finite.card_option, Nat.card_eq_fintype_card]
  have hsum := sum_compl_eq (a := W.b₂ / 4) (b := W.b₄ / 2) (c := W.b₆ / 4) hF
  have haff := card_affine_eq_sum W hF
  have e : ((∑ t : F, (2 - lossExp (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4) t) : ℕ) : ℤ) =
      ((Fintype.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} : ℕ) : ℤ) := by
    rw [hsum, haff]
    rfl
  rw [hcard]
  have e' : ∑ t : F, (2 - lossExp (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4) t) =
      Fintype.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} := by
    exact_mod_cast e
  omega

/-- **Hasse's theorem from the count law.** Manin's proof: the conservation of channels at every probe forces `t² ≤ 4q`. It uses neither Stepanov's auxiliary section nor any character
sum. -/
theorem hasse_of_countLaw (hF : ringChar F ≠ 2) [W.IsElliptic] :
    ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by
  obtain ⟨K, hK, h01, h10, h11⟩ := elliptic_has_countLaw W hF
  refine hK.universal (q := Fintype.card F) (t := (Fintype.card F : ℤ) + 1 - Nat.card W.toAffine.Point)
    h01 (by exact_mod_cast h10) ?_
  rw [h11]
  ring

/-- **The black hole of a curve lies in the Hasse window, by the count law.** -/
theorem elliptic_trace_sq_le_of_countLaw (hF : ringChar F ≠ 2) [W.IsElliptic] :
    (ellipticChannels W).traceR ^ 2 ≤ 4 * ((ellipticChannels W).q : ℝ) := by
  obtain ⟨K, hK, h01, h10, h11⟩ := elliptic_has_countLaw W hF
  refine (ellipticChannels W).universal_iff_countLaw.mp ⟨K, hK, h01, h10, ?_⟩
  rw [h11, Nat.card_eq_fintype_card]

/-- **Universal damping on a true curve, from the count law.** Every mode of the black hole of `W` has the rate `¼`, with no input other than the parallelogram law of heights and the count at
`1 - π`. -/
theorem elliptic_universal_damping_of_countLaw (hF : ringChar F ≠ 2) [W.IsElliptic] {a : ℂ}
    (ha : a ^ 2 - ((ellipticChannels W).traceR : ℂ) * a + ((ellipticChannels W).q : ℂ) = 0) :
    dampingRate (ellipticChannels W).q a = 1 / 4 := by
  have hq2 := (ellipticChannels W).q_pos
  have hq0 : (0 : ℝ) < (ellipticChannels W).q := by linarith
  have hq1 : (1 : ℝ) < (ellipticChannels W).q := by linarith
  have h := (modes_on_circle_iff hq0).mpr (elliptic_trace_sq_le_of_countLaw W hF) a (by exact_mod_cast ha)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Complex.normSq_zero] at h
    linarith
  rw [dampingRate_eq_quarter_iff hq1 ha0, ← Complex.normSq_eq_norm_sq]
  exact h

end Curve

end GaloisForLFunctions.ArithmeticScatteringHolography

end
