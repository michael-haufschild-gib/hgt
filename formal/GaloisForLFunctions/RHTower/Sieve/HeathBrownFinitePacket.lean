import GaloisForLFunctions.RHTower.Sieve.HeathBrownIdentity
import GaloisForLFunctions.RHTower.Sieve.LSeriesBlockDecomposition

/-!
# Finite analytic realization of the Heath--Brown packet

The compressed Heath--Brown identity is an identity of arithmetic functions, but analytic
mean-value arguments require genuinely finite Dirichlet polynomials.  Sharp coefficient truncation
is compatible with Dirichlet convolution on an initial interval: divisors of `n ≤ X` also lie below
`X`.  Consequently every zeta and logarithm factor in the compressed packet may be cut off at `X`
without changing any coefficient through `X`.

This file isolates that divisor-closed locality principle, constructs the finite packet, and proves
the exact finite identity consumed by dyadic Dirichlet-polynomial decompositions.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped zeta Moebius

/-- Sharp upper truncation of an arithmetic function. -/
def coeffTrunc {R : Type*} [Zero R] (F : ArithmeticFunction R) (X : ℕ) :
    ArithmeticFunction R where
  toFun n := if n ≤ X then F n else 0
  map_zero' := by simp

@[simp] theorem coeffTrunc_apply {R : Type*} [Zero R]
    (F : ArithmeticFunction R) (X n : ℕ) :
    coeffTrunc F X n = if n ≤ X then F n else 0 := rfl

theorem coeffTrunc_apply_of_le {R : Type*} [Zero R]
    (F : ArithmeticFunction R) {X n : ℕ} (hn : n ≤ X) :
    coeffTrunc F X n = F n := by
  simp [coeffTrunc, hn]

theorem coeffTrunc_apply_of_lt {R : Type*} [Zero R]
    (F : ArithmeticFunction R) {X n : ℕ} (hn : X < n) :
    coeffTrunc F X n = 0 := by
  simp [coeffTrunc, Nat.not_le.mpr hn]

/-- Two arithmetic functions agree on the divisor-closed initial interval through `X`. -/
def AgreeUpTo {R : Type*} [Zero R]
    (F G : ArithmeticFunction R) (X : ℕ) : Prop :=
  ∀ n, n ≤ X → F n = G n

theorem agreeUpTo_refl {R : Type*} [Zero R]
    (F : ArithmeticFunction R) (X : ℕ) : AgreeUpTo F F X := by
  intro n hn
  rfl

theorem coeffTrunc_agreeUpTo {R : Type*} [Zero R]
    (F : ArithmeticFunction R) (X : ℕ) : AgreeUpTo (coeffTrunc F X) F X := by
  intro n hn
  exact coeffTrunc_apply_of_le F hn

theorem AgreeUpTo.add {R : Type*} [AddMonoid R]
    {F F' G G' : ArithmeticFunction R} {X : ℕ}
    (hF : AgreeUpTo F F' X) (hG : AgreeUpTo G G' X) :
    AgreeUpTo (F + G) (F' + G') X := by
  intro n hn
  simp only [ArithmeticFunction.add_apply]
  rw [hF n hn, hG n hn]

/-- Initial-interval agreement is preserved by Dirichlet convolution.  This is the key locality
fact: every coordinate in the divisor antidiagonal of positive `n` is itself at most `n`. -/
theorem AgreeUpTo.mul {R : Type*} [CommSemiring R]
    {F F' G G' : ArithmeticFunction R} {X : ℕ}
    (hF : AgreeUpTo F F' X) (hG : AgreeUpTo G G' X) :
    AgreeUpTo (F * G) (F' * G') X := by
  intro n hn
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp
  · simp only [ArithmeticFunction.mul_apply]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxprod : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hx1dvd : x.1 ∣ n := ⟨x.2, hxprod⟩
    have hx2dvd : x.2 ∣ n := ⟨x.1, by rw [Nat.mul_comm, hxprod]⟩
    have hx1 : x.1 ≤ X := (Nat.le_of_dvd hnpos hx1dvd).trans hn
    have hx2 : x.2 ≤ X := (Nat.le_of_dvd hnpos hx2dvd).trans hn
    rw [hF x.1 hx1, hG x.2 hx2]

theorem AgreeUpTo.pow {R : Type*} [CommSemiring R]
    {F G : ArithmeticFunction R} {X : ℕ} (h : AgreeUpTo F G X) (k : ℕ) :
    AgreeUpTo (F ^ k) (G ^ k) X := by
  induction k with
  | zero => exact agreeUpTo_refl 1 X
  | succ k ih => simpa [pow_succ] using ih.mul h

theorem agreeUpTo_sum {R ι : Type*} [CommSemiring R]
    {s : Finset ι} {F G : ι → ArithmeticFunction R} {X : ℕ}
    (h : ∀ i ∈ s, AgreeUpTo (F i) (G i) X) :
    AgreeUpTo (∑ i ∈ s, F i) (∑ i ∈ s, G i) X := by
  intro n hn
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => h i hi n hn

/-- Finite version of the compressed packet: zeta and logarithm factors are cut off sharply at
`X`.  Every factor now has finite support. -/
def heathBrownFiniteCompressedPacket (L X k : ℕ) : ArithmeticFunction ℝ :=
  ∑ m ∈ Finset.range k,
    (-1 : ArithmeticFunction ℝ) ^ (m + k + 1) *
      (k.choose m : ArithmeticFunction ℝ) *
      (truncatedMoebius L) ^ (k - m) *
      (coeffTrunc (zeta : ArithmeticFunction ℝ) X) ^ (k - m - 1) *
      coeffTrunc ArithmeticFunction.log X

/-- Cutting every infinite factor at `X` leaves the compressed packet unchanged through `X`. -/
theorem heathBrownFiniteCompressedPacket_agreeUpTo (L X k : ℕ) :
    AgreeUpTo (heathBrownFiniteCompressedPacket L X k)
      (heathBrownCompressedPacket L k) X := by
  rw [heathBrownFiniteCompressedPacket, heathBrownCompressedPacket]
  refine agreeUpTo_sum fun m hm => ?_
  exact (((agreeUpTo_refl ((-1 : ArithmeticFunction ℝ) ^ (m + k + 1)) X).mul
      (agreeUpTo_refl (k.choose m : ArithmeticFunction ℝ) X)).mul
      (agreeUpTo_refl ((truncatedMoebius L) ^ (k - m)) X)).mul
      ((coeffTrunc_agreeUpTo (zeta : ArithmeticFunction ℝ) X).pow (k - m - 1))).mul
      (coeffTrunc_agreeUpTo ArithmeticFunction.log X)

/-- **Exact finite Heath--Brown identity.**  If `n` lies both in the support range of the algebraic
identity and below the analytic cutoff, then `Λ(n)` is the coefficient of a genuinely finite
`k`-term packet. -/
theorem heathBrown_finite_compressed_identity
    (L X k n : ℕ) (hnX : n ≤ X) (hnL : n < (L + 1) ^ k) :
    vonMangoldt n = heathBrownFiniteCompressedPacket L X k n := by
  rw [heathBrownFiniteCompressedPacket_agreeUpTo L X k n hnX]
  exact heathBrown_compressed_identity_of_lt_pow L k n hnL

/-- Every nonzero coefficient of a sharp truncation lies in `[1, X]`. -/
theorem coeffTrunc_support_Icc {R : Type*} [Zero R]
    (F : ArithmeticFunction R) {X n : ℕ} (hn : coeffTrunc F X n ≠ 0) :
    n ∈ Finset.Icc 1 X := by
  have hnX : n ≤ X := by
    by_contra h
    exact hn (coeffTrunc_apply_of_lt F (Nat.lt_of_not_ge h))
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    exact hn (map_zero F)
  exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, hnX⟩

/-- Complex coefficient sequence attached to a real arithmetic function. -/
def complexCoeff (F : ArithmeticFunction ℝ) : ℕ → ℂ :=
  fun n => (F n : ℂ)

@[simp] theorem complexCoeff_apply (F : ArithmeticFunction ℝ) (n : ℕ) :
    complexCoeff F n = (F n : ℂ) := rfl

/-- Each finite zeta factor is already eligible for the corpus's dyadic L-series decomposition. -/
theorem LSeries_coeffTrunc_zeta_eq_sum_dyadic_blocks (X : ℕ) (s : ℂ) :
    LSeries (complexCoeff (coeffTrunc (zeta : ArithmeticFunction ℝ) X)) s =
      ∑ j ∈ Finset.range (Nat.log 2 X + 1),
        LSeries
          (coeffBlock (complexCoeff (coeffTrunc (zeta : ArithmeticFunction ℝ) X))
            (fun n => Nat.log 2 n) j) s := by
  apply LSeries_eq_sum_dyadic_blocks
  intro n hn
  exact coeffTrunc_support_Icc _ (by simpa [complexCoeff] using hn)

/-- Each finite logarithm factor is already eligible for the corpus's dyadic L-series
decomposition. -/
theorem LSeries_coeffTrunc_log_eq_sum_dyadic_blocks (X : ℕ) (s : ℂ) :
    LSeries (complexCoeff (coeffTrunc ArithmeticFunction.log X)) s =
      ∑ j ∈ Finset.range (Nat.log 2 X + 1),
        LSeries
          (coeffBlock (complexCoeff (coeffTrunc ArithmeticFunction.log X))
            (fun n => Nat.log 2 n) j) s := by
  apply LSeries_eq_sum_dyadic_blocks
  intro n hn
  exact coeffTrunc_support_Icc _ (by simpa [complexCoeff] using hn)

end RHTower.Sieve
