import GaloisForLFunctions.RHTower.Sieve.HeathBrownIdentity
import GaloisForLFunctions.RHTower.Sieve.LSeriesBlockDecomposition
import GaloisForLFunctions.RHTower.Sieve.ProductFirstMoment

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
    have hx1dvd : x.1 ∣ n := ⟨x.2, hxprod.symm⟩
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
  classical
  induction s using Finset.induction_on with
  | empty => simp [AgreeUpTo]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      apply AgreeUpTo.add
      · exact h a (Finset.mem_insert_self a s)
      · apply ih
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)

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
  have hsign := agreeUpTo_refl ((-1 : ArithmeticFunction ℝ) ^ (m + k + 1)) X
  have hchoose := agreeUpTo_refl (k.choose m : ArithmeticFunction ℝ) X
  have hM := agreeUpTo_refl ((truncatedMoebius L) ^ (k - m)) X
  have hZ := (coeffTrunc_agreeUpTo (zeta : ArithmeticFunction ℝ) X).pow (k - m - 1)
  have hlog := coeffTrunc_agreeUpTo ArithmeticFunction.log X
  exact ((((hsign.mul hchoose).mul hM).mul hZ).mul hlog)

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
    exact hn (by simp)
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
  have hn' : coeffTrunc (zeta : ArithmeticFunction ℝ) X n ≠ 0 := by
    intro hzero
    apply hn
    rw [complexCoeff_apply, hzero, Complex.ofReal_zero]
  exact coeffTrunc_support_Icc (zeta : ArithmeticFunction ℝ) hn'

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
  have hn' : coeffTrunc (ArithmeticFunction.log : ArithmeticFunction ℝ) X n ≠ 0 := by
    intro hzero
    apply hn
    rw [complexCoeff_apply, hzero, Complex.ofReal_zero]
  exact coeffTrunc_support_Icc (ArithmeticFunction.log : ArithmeticFunction ℝ) hn'

/-- The truncated Möbius factor is likewise a finite dyadic Dirichlet-polynomial sum. -/
theorem LSeries_truncatedMoebius_eq_sum_dyadic_blocks (L : ℕ) (s : ℂ) :
    LSeries (complexCoeff (truncatedMoebius L)) s =
      ∑ j ∈ Finset.range (Nat.log 2 L + 1),
        LSeries
          (coeffBlock (complexCoeff (truncatedMoebius L))
            (fun n => Nat.log 2 n) j) s := by
  apply LSeries_eq_sum_dyadic_blocks
  intro n hn
  have hn' : truncatedMoebius L n ≠ 0 := by
    intro hzero
    apply hn
    rw [complexCoeff_apply, hzero, Complex.ofReal_zero]
  have hnL : n ≤ L := by
    by_contra h
    apply hn'
    rw [truncatedMoebius_apply, if_neg h]
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    exact hn' (by simp)
  exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, hnL⟩

/-- Complexification carries arithmetic-function convolution to ordinary complex-sequence
convolution. -/
theorem complexCoeff_mul (F G : ArithmeticFunction ℝ) :
    complexCoeff (F * G) = LSeries.convolution (complexCoeff F) (complexCoeff G) := by
  funext n
  simp only [complexCoeff_apply, ArithmeticFunction.mul_apply, LSeries.convolution_def]
  push_cast
  rfl

theorem complexCoeff_add (F G : ArithmeticFunction ℝ) :
    complexCoeff (F + G) = complexCoeff F + complexCoeff G := by
  funext n
  simp [complexCoeff]

/-- Complexification commutes with finite sums of arithmetic functions. -/
theorem complexCoeff_sum {ι : Type*} (u : Finset ι)
    (F : ι → ArithmeticFunction ℝ) :
    complexCoeff (∑ i ∈ u, F i) = ∑ i ∈ u, complexCoeff (F i) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
      funext n
      simp [complexCoeff]
  | @insert a u ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, complexCoeff_add, ih]

/-- A sharply truncated real arithmetic function has an absolutely convergent L-series at every
complex argument. -/
theorem LSeriesSummable_complexCoeff_coeffTrunc
    (F : ArithmeticFunction ℝ) (X : ℕ) (s : ℂ) :
    LSeriesSummable (complexCoeff (coeffTrunc F X)) s := by
  apply LSeriesSummable_of_support (s := Finset.Icc 1 X)
  intro n hn
  have hn' : coeffTrunc F X n ≠ 0 := by
    intro hzero
    apply hn
    rw [complexCoeff_apply, hzero, Complex.ofReal_zero]
  exact coeffTrunc_support_Icc F hn'

/-- The Möbius cutoff is exactly sharp coefficient truncation of the real Möbius arithmetic
function. -/
theorem truncatedMoebius_eq_coeffTrunc (L : ℕ) :
    truncatedMoebius L =
      coeffTrunc (((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)) L := by
  ext n
  rfl

theorem LSeriesSummable_complexCoeff_truncatedMoebius (L : ℕ) (s : ℂ) :
    LSeriesSummable (complexCoeff (truncatedMoebius L)) s := by
  rw [truncatedMoebius_eq_coeffTrunc]
  exact LSeriesSummable_complexCoeff_coeffTrunc _ L s

/-- Summability is multiplicative for complexified real arithmetic functions. -/
theorem LSeriesSummable_complexCoeff_mul {F G : ArithmeticFunction ℝ} {s : ℂ}
    (hF : LSeriesSummable (complexCoeff F) s)
    (hG : LSeriesSummable (complexCoeff G) s) :
    LSeriesSummable (complexCoeff (F * G)) s := by
  rw [complexCoeff_mul]
  exact hF.convolution hG

/-- L-series factorization of a real arithmetic-function convolution, under summability. -/
theorem LSeries_complexCoeff_mul {F G : ArithmeticFunction ℝ} {s : ℂ}
    (hF : LSeriesSummable (complexCoeff F) s)
    (hG : LSeriesSummable (complexCoeff G) s) :
    LSeries (complexCoeff (F * G)) s =
      LSeries (complexCoeff F) s * LSeries (complexCoeff G) s := by
  rw [complexCoeff_mul, LSeries_convolution' hF hG]

theorem complexCoeff_one :
    complexCoeff (1 : ArithmeticFunction ℝ) = LSeries.delta := by
  funext n
  by_cases hn : n = 1
  · subst n
    simp [complexCoeff, LSeries.delta]
  · simp [complexCoeff, LSeries.delta, hn]

theorem LSeriesSummable_complexCoeff_one (s : ℂ) :
    LSeriesSummable (complexCoeff (1 : ArithmeticFunction ℝ)) s := by
  apply LSeriesSummable_of_support (s := {1})
  intro n hn
  rw [Finset.mem_singleton]
  by_contra hn1
  apply hn
  rw [complexCoeff_apply, ArithmeticFunction.one_apply_ne hn1, Complex.ofReal_zero]

theorem LSeries_complexCoeff_one (s : ℂ) :
    LSeries (complexCoeff (1 : ArithmeticFunction ℝ)) s = 1 := by
  rw [complexCoeff_one, LSeries_delta]
  rfl

/-- Evaluation at one coefficient as an additive homomorphism. -/
def arithmeticEvalAddHom (n : ℕ) : ArithmeticFunction ℝ →+ ℝ where
  toFun F := F n
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem arithmeticEvalAddHom_apply (n : ℕ) (F : ArithmeticFunction ℝ) :
    arithmeticEvalAddHom n F = F n := rfl

/-- Complex coefficients of an integer scalar arithmetic function are a scalar multiple of the
Dirichlet delta sequence. -/
theorem complexCoeff_intCast (z : ℤ) :
    complexCoeff (z : ArithmeticFunction ℝ) = (z : ℂ) • LSeries.delta := by
  have hcast : (z : ArithmeticFunction ℝ) = z • (1 : ArithmeticFunction ℝ) :=
    (zsmul_one z).symm
  rw [hcast]
  funext n
  change ((arithmeticEvalAddHom n (z • (1 : ArithmeticFunction ℝ)) : ℝ) : ℂ) = _
  rw [map_zsmul]
  by_cases hn : n = 1
  · subst n
    simp [LSeries.delta]
  · simp [LSeries.delta, hn]

theorem LSeriesSummable_complexCoeff_intCast (z : ℤ) (s : ℂ) :
    LSeriesSummable (complexCoeff (z : ArithmeticFunction ℝ)) s := by
  rw [complexCoeff_intCast]
  have hdelta : LSeriesSummable LSeries.delta s := by
    rw [← complexCoeff_one]
    exact LSeriesSummable_complexCoeff_one s
  exact hdelta.smul (z : ℂ)

theorem LSeries_complexCoeff_intCast (z : ℤ) (s : ℂ) :
    LSeries (complexCoeff (z : ArithmeticFunction ℝ)) s = (z : ℂ) := by
  rw [complexCoeff_intCast, LSeries_smul, LSeries_delta]
  simp

/-- Natural scalar version of the preceding finite delta identity. -/
theorem complexCoeff_natCast (a : ℕ) :
    complexCoeff (a : ArithmeticFunction ℝ) = (a : ℂ) • LSeries.delta := by
  have hcast : (a : ArithmeticFunction ℝ) = a • (1 : ArithmeticFunction ℝ) :=
    (nsmul_one a).symm
  rw [hcast]
  funext n
  change ((arithmeticEvalAddHom n (a • (1 : ArithmeticFunction ℝ)) : ℝ) : ℂ) = _
  rw [map_nsmul]
  by_cases hn : n = 1
  · subst n
    simp [LSeries.delta]
  · simp [LSeries.delta, hn]

theorem LSeriesSummable_complexCoeff_natCast (a : ℕ) (s : ℂ) :
    LSeriesSummable (complexCoeff (a : ArithmeticFunction ℝ)) s := by
  rw [complexCoeff_natCast]
  have hdelta : LSeriesSummable LSeries.delta s := by
    rw [← complexCoeff_one]
    exact LSeriesSummable_complexCoeff_one s
  exact hdelta.smul (a : ℂ)

theorem LSeries_complexCoeff_natCast (a : ℕ) (s : ℂ) :
    LSeries (complexCoeff (a : ArithmeticFunction ℝ)) s = (a : ℂ) := by
  rw [complexCoeff_natCast, LSeries_smul, LSeries_delta]
  simp

/-- Every convolution power of a summable finite arithmetic function remains summable. -/
theorem LSeriesSummable_complexCoeff_pow {F : ArithmeticFunction ℝ} {s : ℂ}
    (hF : LSeriesSummable (complexCoeff F) s) (j : ℕ) :
    LSeriesSummable (complexCoeff (F ^ j)) s := by
  induction j with
  | zero => simpa using LSeriesSummable_complexCoeff_one s
  | succ j ih =>
      rw [pow_succ]
      exact LSeriesSummable_complexCoeff_mul ih hF

/-- L-series factorization of a convolution power. -/
theorem LSeries_complexCoeff_pow {F : ArithmeticFunction ℝ} {s : ℂ}
    (hF : LSeriesSummable (complexCoeff F) s) (j : ℕ) :
    LSeries (complexCoeff (F ^ j)) s = LSeries (complexCoeff F) s ^ j := by
  induction j with
  | zero => exact LSeries_complexCoeff_one s
  | succ j ih =>
      rw [pow_succ, LSeries_complexCoeff_mul
        (LSeriesSummable_complexCoeff_pow hF j) hF, ih, pow_succ]

/-- Degree-`j` analytic core of one compressed Heath--Brown term. -/
def heathBrownFiniteCore (L X j : ℕ) : ArithmeticFunction ℝ :=
  (truncatedMoebius L) ^ j *
    (coeffTrunc (zeta : ArithmeticFunction ℝ) X) ^ (j - 1) *
    coeffTrunc ArithmeticFunction.log X

theorem LSeriesSummable_heathBrownFiniteCore (L X j : ℕ) (s : ℂ) :
    LSeriesSummable (complexCoeff (heathBrownFiniteCore L X j)) s := by
  have hM := LSeriesSummable_complexCoeff_truncatedMoebius L s
  have hZ := LSeriesSummable_complexCoeff_coeffTrunc
    (zeta : ArithmeticFunction ℝ) X s
  have hlog := LSeriesSummable_complexCoeff_coeffTrunc ArithmeticFunction.log X s
  rw [heathBrownFiniteCore]
  exact LSeriesSummable_complexCoeff_mul
    (LSeriesSummable_complexCoeff_mul
      (LSeriesSummable_complexCoeff_pow hM j)
      (LSeriesSummable_complexCoeff_pow hZ (j - 1))) hlog

/-- **Exact Dirichlet-polynomial factorization of one Heath--Brown core.**  No half-plane condition
is needed because every factor is finite. -/
theorem LSeries_heathBrownFiniteCore (L X j : ℕ) (s : ℂ) :
    LSeries (complexCoeff (heathBrownFiniteCore L X j)) s =
      LSeries (complexCoeff (truncatedMoebius L)) s ^ j *
        LSeries (complexCoeff (coeffTrunc (zeta : ArithmeticFunction ℝ) X)) s ^ (j - 1) *
        LSeries (complexCoeff (coeffTrunc ArithmeticFunction.log X)) s := by
  have hM := LSeriesSummable_complexCoeff_truncatedMoebius L s
  have hZ := LSeriesSummable_complexCoeff_coeffTrunc
    (zeta : ArithmeticFunction ℝ) X s
  have hlog := LSeriesSummable_complexCoeff_coeffTrunc ArithmeticFunction.log X s
  have hMpow := LSeriesSummable_complexCoeff_pow hM j
  have hZpow := LSeriesSummable_complexCoeff_pow hZ (j - 1)
  rw [heathBrownFiniteCore,
    LSeries_complexCoeff_mul (LSeriesSummable_complexCoeff_mul hMpow hZpow) hlog,
    LSeries_complexCoeff_mul hMpow hZpow,
    LSeries_complexCoeff_pow hM j,
    LSeries_complexCoeff_pow hZ (j - 1)]

/-- One complete finite compressed term, including its signed binomial coefficient. -/
def heathBrownFiniteTerm (L X k m : ℕ) : ArithmeticFunction ℝ :=
  (-1 : ArithmeticFunction ℝ) ^ (m + k + 1) *
    (k.choose m : ArithmeticFunction ℝ) *
    heathBrownFiniteCore L X (k - m)

theorem heathBrownFiniteCompressedPacket_eq_sum_terms (L X k : ℕ) :
    heathBrownFiniteCompressedPacket L X k =
      ∑ m ∈ Finset.range k, heathBrownFiniteTerm L X k m := by
  simp only [heathBrownFiniteCompressedPacket, heathBrownFiniteTerm, heathBrownFiniteCore]
  refine Finset.sum_congr rfl fun m hm => ?_
  ring

/-- **Complete finite product factorization of a compressed Heath--Brown term.** -/
theorem LSeries_heathBrownFiniteTerm (L X k m : ℕ) (s : ℂ) :
    LSeries (complexCoeff (heathBrownFiniteTerm L X k m)) s =
      (-1 : ℂ) ^ (m + k + 1) * (k.choose m : ℂ) *
        (LSeries (complexCoeff (truncatedMoebius L)) s ^ (k - m) *
          LSeries (complexCoeff (coeffTrunc (zeta : ArithmeticFunction ℝ) X)) s ^
            (k - m - 1) *
          LSeries (complexCoeff (coeffTrunc ArithmeticFunction.log X)) s) := by
  have hneg : LSeriesSummable
      (complexCoeff (-1 : ArithmeticFunction ℝ)) s := by
    simpa using LSeriesSummable_complexCoeff_intCast (-1) s
  have hnegSeries :
      LSeries (complexCoeff (-1 : ArithmeticFunction ℝ)) s = (-1 : ℂ) := by
    simpa using LSeries_complexCoeff_intCast (-1) s
  have hnegpow := LSeriesSummable_complexCoeff_pow hneg (m + k + 1)
  have hchoose := LSeriesSummable_complexCoeff_natCast (k.choose m) s
  have hcore := LSeriesSummable_heathBrownFiniteCore L X (k - m) s
  rw [heathBrownFiniteTerm]
  rw [LSeries_complexCoeff_mul (LSeriesSummable_complexCoeff_mul hnegpow hchoose) hcore,
    LSeries_complexCoeff_mul hnegpow hchoose,
    LSeries_complexCoeff_pow hneg (m + k + 1),
    hnegSeries,
    LSeries_complexCoeff_natCast (k.choose m) s,
    LSeries_heathBrownFiniteCore]

theorem LSeriesSummable_heathBrownFiniteTerm (L X k m : ℕ) (s : ℂ) :
    LSeriesSummable (complexCoeff (heathBrownFiniteTerm L X k m)) s := by
  have hneg : LSeriesSummable
      (complexCoeff (-1 : ArithmeticFunction ℝ)) s := by
    simpa using LSeriesSummable_complexCoeff_intCast (-1) s
  have hchoose := LSeriesSummable_complexCoeff_natCast (k.choose m) s
  have hcore := LSeriesSummable_heathBrownFiniteCore L X (k - m) s
  rw [heathBrownFiniteTerm]
  exact LSeriesSummable_complexCoeff_mul
    (LSeriesSummable_complexCoeff_mul
      (LSeriesSummable_complexCoeff_pow hneg (m + k + 1)) hchoose) hcore

theorem LSeriesSummable_heathBrownFiniteCompressedPacket (L X k : ℕ) (s : ℂ) :
    LSeriesSummable (complexCoeff (heathBrownFiniteCompressedPacket L X k)) s := by
  rw [heathBrownFiniteCompressedPacket_eq_sum_terms, complexCoeff_sum]
  apply LSeriesSummable.sum
  intro m hm
  exact LSeriesSummable_heathBrownFiniteTerm L X k m s

/-- **Complete finite Heath--Brown L-series expansion.**  The finite packet is a `k`-term sum of
explicit products, with one product for each degree `1 ≤ j ≤ k`. -/
theorem LSeries_heathBrownFiniteCompressedPacket (L X k : ℕ) (s : ℂ) :
    LSeries (complexCoeff (heathBrownFiniteCompressedPacket L X k)) s =
      ∑ m ∈ Finset.range k,
        (-1 : ℂ) ^ (m + k + 1) * (k.choose m : ℂ) *
          (LSeries (complexCoeff (truncatedMoebius L)) s ^ (k - m) *
            LSeries (complexCoeff (coeffTrunc (zeta : ArithmeticFunction ℝ) X)) s ^
              (k - m - 1) *
            LSeries (complexCoeff (coeffTrunc ArithmeticFunction.log X)) s) := by
  rw [heathBrownFiniteCompressedPacket_eq_sum_terms, complexCoeff_sum]
  rw [LSeries_sum (fun m hm => LSeriesSummable_heathBrownFiniteTerm L X k m s)]
  refine Finset.sum_congr rfl fun m hm => ?_
  exact LSeries_heathBrownFiniteTerm L X k m s

end RHTower.Sieve
