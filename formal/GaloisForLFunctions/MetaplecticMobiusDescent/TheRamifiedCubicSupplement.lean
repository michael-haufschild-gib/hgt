/-
The ramified comparison and supplementary law are adapted from OpenAI’s
formalization, Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicJacobiSymbols
import GaloisForLFunctions.MetaplecticMobiusDescent.EisensteinCoordinates

/-!
# The ramified cubic supplementary law

For a primary prime `p = 1 + 3A + 3Bω`, the cubic symbols of `ω` and `ω−1`
are `ω^(2A−B)` and `ω^A`. Euler's exponent and the norm form give the first.
For the second, reciprocity compares `p` with the fixed primary primes `−2`
and `1+3ω`; explicit factorizations cover all nine coordinate classes.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent
namespace CubicRamified
open Eisenstein CubicJacobi
private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

lemma lambda_def : lambda = omega - 1 := rfl

private theorem omega_sq_for_norm : omega ^ 2 = -omega - 1 := by
  simpa [omega] using IsCyclotomicExtension.Rat.Three.eta_sq
    (IsCyclotomicExtension.zeta_spec 3 ℚ K)

theorem lambda_sq_eq : lambda ^ 2 = -3 * omega := by
  rw [lambda_def]
  linear_combination omega_sq_for_norm

private theorem prime_generator_not_mem_of_ne (P Q : Ideal O)
    [P.IsMaximal] [Q.IsMaximal] (hne : P ≠ Q)
    (q : O) (hQ : Q = Ideal.span {q}) : q ∉ P := by
  intro hq
  have hle : Q ≤ P := by
    rw [hQ]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hq
  exact hne (Ideal.IsMaximal.eq_of_le (inferInstance : Q.IsMaximal)
    (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)) hle).symm

/-- Euler’s residue exponent evaluates the symbol of the cubic root. -/
theorem cubicChar_omega (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) =
      omega ^ ((Nat.card (O ⧸ P) - 1) / 3) := by
  let χ := cubicChar P hgood
  have hx : (χ (Ideal.Quotient.mk P omega)) ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
    exact MulChar.one_apply ((omega_reduced_primitive P hgood).isUnit (by decide))
  have hy : (omega ^ ((Nat.card (O ⧸ P) - 1) / 3)) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, omega_primitive.pow_eq_one, one_pow]
  apply cubic_roots_reduce_injective P hgood hx hy
  rw [map_pow]
  exact cubicChar_reduce P hgood (Ideal.Quotient.mk P omega)

/-- Reciprocity cancels the primary factor in the difference of two primary primes. -/
theorem ramified_comparison
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hqP : q ∉ P) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r) :
    (cubicChar P hgP (Ideal.Quotient.mk P lambda)) ^ 2 *
        cubicChar P hgP (Ideal.Quotient.mk P u) =
      (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) := by
  have hpP : p ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have hqQ : q ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have hrP : r ∉ P := by
    intro hrP
    have hd : p - q ∈ P := by rw [hfactor]; exact P.mul_mem_left _ hrP
    have hmem := P.sub_mem hpP hd
    exact hqP (by convert hmem using 1 ; ring)
  have hrr : cubicChar P hgP (Ideal.Quotient.mk P r) =
      cubicChar Q hgQ (Ideal.Quotient.mk Q r) := by
    have heq : symbol p r = symbol q r := symbol_congr
      (by rw [hfactor]; exact dvd_mul_left r _)
    have h := (symbol_reciprocity r p hr hp).trans
      (heq.trans (symbol_reciprocity q r hq hr))
    simpa only [symbol, ← hP, ← hQ, idealSymbol_prime _ hgP,
      idealSymbol_prime _ hgQ] using h
  have heq : cubicChar P hgP (Ideal.Quotient.mk P (p - q)) =
      cubicChar Q hgQ (Ideal.Quotient.mk Q (p - q)) := by
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hpP, zero_sub,
      neg_eq_neg_one_mul, map_mul, cubicChar_neg_one P hgP, one_mul,
      map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hqQ, sub_zero]
    exact cubic_reciprocity_primary P Q hgP hgQ p q hP hQ hp hq
  simp only [hfactor, map_mul, map_pow] at heq
  rw [← hrr] at heq
  exact mul_right_cancel₀ (cubicValue_ne_zero P hgP r hrP) heq

/-- A comparison prime of norm seven. -/
def sevenPrime : O := 1 + 3 * omega
def sevenIdeal : Ideal O := Ideal.span {sevenPrime}

theorem sevenPrime_ne_zero : sevenPrime ≠ 0 := by
  intro hz
  change Coordinates.eval 1 3 = 0 at hz
  have hh : Coordinates.eval 1 3 =
      Coordinates.eval 0 0 :=
    hz.trans (by simp [Coordinates.eval])
  have h := (Coordinates.unique_coordinates hh).1
  norm_num at h

theorem sevenIdeal_norm : Ideal.absNorm sevenIdeal = 7 := by
  rw [sevenIdeal, Ideal.absNorm_span_singleton,
    show sevenPrime = Coordinates.eval 1 3 by simp [sevenPrime, Coordinates.eval],
    Coordinates.norm_eval]
  norm_num

instance sevenIdeal_isMaximal : sevenIdeal.IsMaximal := by
  have hp : sevenIdeal.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by
    rw [sevenIdeal_norm, Nat.irreducible_iff_nat_prime]
    decide)
  exact hp.isMaximal (Ideal.span_singleton_eq_bot.not.mpr sevenPrime_ne_zero)

theorem sevenPrime_primary : lambda ^ 2 ∣ sevenPrime - 1 := by
  refine ⟨-1, ?_⟩
  rw [lambda_def]
  dsimp [sevenPrime]
  linear_combination omega_sq_for_norm

theorem sevenIdeal_good : lambda ∉ sevenIdeal :=
  primary_maximal_divisor_good sevenPrime sevenPrime_primary sevenIdeal
    (Ideal.subset_span (by simp []))

theorem twoIdeal_card : Nat.card (O ⧸ cubicTwoIdeal) = 4 := cubicTwoIdeal_absNorm

theorem sevenIdeal_card : Nat.card (O ⧸ sevenIdeal) = 7 := sevenIdeal_norm

theorem cubicValue_lambda_two :
    cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal lambda) =
      omega ^ 2 := by
  have heq : Ideal.Quotient.mk cubicTwoIdeal lambda =
      Ideal.Quotient.mk cubicTwoIdeal (omega ^ 2) := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    rw [cubicTwoIdeal, Ideal.mem_span_singleton]
    refine ⟨-omega, ?_⟩
    rw [lambda_def]
    linear_combination -omega_sq_for_norm
  rw [heq, map_pow, map_pow, cubicChar_omega, twoIdeal_card]
  norm_num

theorem cubicValue_lambda_seven :
    cubicChar sevenIdeal sevenIdeal_good (Ideal.Quotient.mk sevenIdeal lambda) = 1 := by
  apply cubic_roots_reduce_injective sevenIdeal sevenIdeal_good
    (cubicValue_cube sevenIdeal sevenIdeal_good lambda sevenIdeal_good) (by simp)
  rw [cubicChar_reduce, sevenIdeal_card]
  norm_num only [Nat.reduceSub, Nat.reduceDiv]
  rw [← map_pow]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [sevenIdeal, Ideal.mem_span_singleton]
  refine ⟨-1, ?_⟩
  rw [lambda_def]
  dsimp [sevenPrime]
  linear_combination omega_sq_for_norm

/-- Integral coordinates of a primary element. -/
def primaryCoord (A B : ℤ) : O := Coordinates.eval (1 + 3 * A) (3 * B)

theorem primaryCoord_eq (A B : ℤ) :
    primaryCoord A B = 1 + 3 * (A : O) + 3 * (B : O) * omega := by
  simp only [primaryCoord, Coordinates.eval]
  push_cast
  rfl

theorem primaryCoord_primary (A B : ℤ) : lambda ^ 2 ∣ primaryCoord A B - 1 := by
  rw [primaryCoord_eq]
  apply lambda_sq_dvd_three.trans
  exact ⟨(A : O) + (B : O) * omega, by ring⟩

theorem primaryCoord_ne_zero (A B : ℤ) : primaryCoord A B ≠ 0 := by
  intro hz
  have hcoord : Coordinates.eval (1 + 3 * A) (3 * B) =
      Coordinates.eval 0 0 := by
    exact hz.trans (by simp [Coordinates.eval])
  have h := (Coordinates.unique_coordinates hcoord).1
  omega

lemma primary_card_exponent (N : ℕ) (A B : ℤ) (hN : 1 < N)
    (hn : (N : ℤ) = 1 + 9*(A^2-A*B+B^2)+3*(2*A-B)) :
    ((N-1)/3)%3 = ((2*A-B)%3).toNat %3 := by
  have hsub : ((N-1 : ℕ) : ℤ) = (N : ℤ)-1 := by omega
  have hdiv : (((N-1)/3 : ℕ) : ℤ) = 3*(A^2-A*B+B^2)+(2*A-B) := by
    rw [Int.natCast_ediv, hsub]
    have hh : (N : ℤ)-1 = 3*(3*(A^2-A*B+B^2)+(2*A-B)) := by omega
    rw [hh]
    omega
  have hrem : (((2*A-B)%3).toNat : ℤ) = (2*A-B)%3 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  omega

/-- The norm form fixes the unit symbol from the primary coordinates modulo three. -/
theorem cubicValue_omega_primary (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ) (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P omega) =
      omega ^ ((2 * A - B) % 3).toNat := by
  have hn : (Nat.card (O ⧸ P) : ℤ) =
      (1 + 3 * A)^2 - (1 + 3 * A)*(3 * B) + (3 * B)^2 := by
    have h := primary_generator_mul_conj_eq_card P hg (primaryCoord A B) hP
      (primaryCoord_primary A B)
    rw [primaryCoord, Coordinates.eval_mul_conj] at h
    exact_mod_cast h.symm
  have hn' : (Nat.card (O ⧸ P) : ℤ) =
      1 + 9*(A^2 - A*B + B^2) + 3*(2*A-B) := by nlinarith only [hn]
  rw [cubicChar_omega]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : 1 < Nat.card (O ⧸ P) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  exact primary_card_exponent (Nat.card (O ⧸ P)) A B hcard hn'

/-- A nonzero difference factorization supplies the distinctness needed for cancellation. -/
theorem ramified_comparison_of_factor
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hu : u ≠ 0) (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r) :
    (cubicChar P hgP (Ideal.Quotient.mk P lambda)) ^ 2 *
        cubicChar P hgP (Ideal.Quotient.mk P u) =
      (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) := by
  have hlam : lambda ≠ 0 := fun hz => hgP (hz ▸ P.zero_mem)
  have hne : P ≠ Q := by
    intro heq
    have hpq : p = q := primary_associated_eq p q
      (Ideal.span_singleton_eq_span_singleton.mp (hP.symm.trans (heq.trans hQ))) hp hq
    have hz : lambda ^ 2 * u * r = 0 := by rw [← hfactor, hpq, sub_self]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hlam) hu) hr0 hz
  exact ramified_comparison P Q hgP hgQ p q u r hP hQ hp hq
    (prime_generator_not_mem_of_ne P Q hne q hQ) hr hfactor

lemma omega_ne_zero : omega ≠ 0 := omega_primitive.ne_zero (by decide)
lemma omega_isUnit : IsUnit omega := omega_primitive.isUnit (by decide)
lemma omega_four : omega ^ 4 = omega := by
  calc
    _ = omega ^ 3 * omega := by ring
    _ = omega := by rw [omega_primitive.pow_eq_one, one_mul]
lemma omega_five : omega ^ 5 = omega ^ 2 := by
  calc
    _ = omega ^ 3 * omega ^ 2 := by ring
    _ = _ := by rw [omega_primitive.pow_eq_one, one_mul]

lemma cubicValue_neg (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P) (x : O) :
    cubicChar P hg (Ideal.Quotient.mk P (-x)) =
      cubicChar P hg (Ideal.Quotient.mk P x) := by
  rw [map_neg, neg_eq_neg_one_mul, map_mul, cubicChar_neg_one, one_mul]

lemma cubicValue_omega_two :
    cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal omega) =
      omega := by rw [cubicChar_omega, twoIdeal_card] ; norm_num
lemma cubicValue_omega_seven :
    cubicChar sevenIdeal sevenIdeal_good (Ideal.Quotient.mk sevenIdeal omega) =
      omega ^ 2 := by rw [cubicChar_omega, sevenIdeal_card]

lemma eq_of_cube_one_of_sq_eq (z w : O) (hz : z ^ 3 = 1)
    (hw : w ^ 3 = 1) (hsq : z ^ 2 = w ^ 2) : z = w := by
  have hw0 : w ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at hw; exact zero_ne_one hw
  apply mul_right_cancel₀ (pow_ne_zero 2 hw0)
  calc
    z * w ^ 2 = z ^ 3 := by rw [← hsq]; ring
    _ = 1 := hz
    _ = w * w ^ 2 := by rw [← hw]; ring

/-- Squaring is injective on cubic roots, so a comparison determines the ramified symbol. -/
lemma supplement_of_factor
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hu : IsUnit u) (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r)
    (j : ℕ)
    (hscalar : (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) =
      (omega ^ j)^2 * cubicChar P hgP (Ideal.Quotient.mk P u)) :
    cubicChar P hgP (Ideal.Quotient.mk P lambda) = omega ^ j := by
  apply eq_of_cube_one_of_sq_eq
  · exact cubicValue_cube P hgP lambda hgP
  · rw [← pow_mul, Nat.mul_comm j, pow_mul, omega_primitive.pow_eq_one, one_pow]
  · apply mul_right_cancel₀ (cubicValue_ne_zero P hgP u (Ideal.notMem_of_isUnit P hu))
    exact (ramified_comparison_of_factor P Q hgP hgQ p q u r hP hQ hp hq
      hu.ne_zero hr0 hr hfactor).trans hscalar

lemma omega_six : omega ^ 6 = 1 := by
  calc
    _ = omega ^ 3 * omega ^ 3 := by ring
    _ = 1 := by rw [omega_primitive.pow_eq_one, one_mul]

lemma omega_seven : omega ^ 7 = omega := by
  calc
    _ = omega ^ 3 * omega ^ 4 := by ring
    _ = omega := by rw [omega_primitive.pow_eq_one, one_mul] ; exact omega_four

lemma omega_eight : omega ^ 8 = omega ^ 2 := by
  calc
    _ = omega ^ 3 * omega ^ 5 := by ring
    _ = omega ^ 2 := by rw [omega_primitive.pow_eq_one, one_mul] ; exact omega_five

/-- The nine coordinate classes admit primary difference factorizations against two fixed primes. -/
private theorem supplement_case00 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+0) (3*l+0)) (-2) (-(omega ^ 2))
    (primaryCoord (k) (l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 2).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg, map_pow, cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, ]
    all_goals ring_nf
    all_goals simp only [  omega_six,
      ]

private theorem supplement_case01 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+0) (3*l+1)) (-2) (omega ^ 1)
    (primaryCoord (l) (-k + l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 1) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [  cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]

private theorem supplement_case02 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+0) (3*l+2)) sevenPrime (-(omega ^ 0))
    (primaryCoord (-k + l) (-k)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 0).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_seven,
        pow_zero,  map_one]

private theorem supplement_case10 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+1) (3*l+0)) (-2) (omega ^ 2)
    (primaryCoord (-k - 1) (-l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 2) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [ map_pow, cubicValue_lambda_two,
      cubicValue_omega_two, hw,  pow_one]
    all_goals ring_nf

private theorem supplement_case11 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+1) (3*l+1)) sevenPrime (-(omega ^ 2))
    (primaryCoord (k) (l)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 2).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg, map_pow, cubicValue_lambda_seven,
      cubicValue_omega_seven, hw,  pow_one]
    all_goals ring_nf

private theorem supplement_case12 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+1) (3*l+2)) (-2) (-(omega ^ 1))
    (primaryCoord (-l - 1) (k - l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 1).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]

private theorem supplement_case20 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+2) (3*l+0)) sevenPrime (-(omega ^ 1))
    (primaryCoord (-l) (k - l + 1)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 1).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_seven,
      cubicValue_omega_seven, hw,  pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]

private theorem supplement_case21 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+2) (3*l+1)) (-2) (-(omega ^ 0))
    (primaryCoord (-k + l - 1) (-k - 1)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 0).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_two,
        pow_zero,  map_one]

private theorem supplement_case22 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+2) (3*l+2)) (-2) (omega ^ 0)
    (primaryCoord (k - l) (k + 1)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 0) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [  cubicValue_lambda_two,
        pow_zero,  map_one]

/-- The ramified cubic symbol of `1+3A+3Bω` is `ω^A`, with exponent read modulo three. -/
theorem cubicValue_lambda_primary (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ)
    (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ (A % 3).toNat := by
  have hA : A = 3 * (A / 3) + A % 3 := by omega
  have hB : B = 3 * (B / 3) + B % 3 := by omega
  have hAa : A % 3 = 0 ∨ A % 3 = 1 ∨ A % 3 = 2 := by omega
  have hBb : B % 3 = 0 ∨ B % 3 = 1 ∨ B % 3 = 2 := by omega
  rcases hAa with ha | ha | ha <;> rcases hBb with hb | hb | hb
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case00 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case01 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case02 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case10 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case11 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case12 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case20 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case21 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case22 P hg (A/3) (B/3) hp


end CubicRamified
end GaloisForLFunctions.MetaplecticMobiusDescent

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicRamified.cubicChar_omega
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicRamified.ramified_comparison
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicRamified.cubicValue_omega_primary
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.CubicRamified.cubicValue_lambda_primary
