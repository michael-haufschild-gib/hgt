import GaloisForLFunctions.RHTower.Sieve.BivariatePowerSeriesConvolution

/-!
# Bivariate additive convolution over an arbitrary coefficient semiring

The original bivariate power-series layer is specialized to real coefficients.  Logarithmic jets
need the same algebra with coefficient ring `PowerSeries ℝ`; this file supplies the generic form.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

def bivariateCoefficientSeriesOver {R : Type*} [Semiring R]
    (f : ℕ → ℕ → R) : PowerSeries (PowerSeries R) :=
  PowerSeries.mk (fun i => PowerSeries.mk (f i))

@[simp] theorem coeff_bivariateCoefficientSeriesOver {R : Type*} [Semiring R]
    (f : ℕ → ℕ → R) (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i (bivariateCoefficientSeriesOver f)) = f i j := by
  simp [bivariateCoefficientSeriesOver]

def additiveBivariateConvolutionOver {R : Type*} [Semiring R]
    (f g : ℕ → ℕ → R) (i j : ℕ) : R :=
  ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
    f a b * g (i - a) (j - b)

theorem coeff_mul_bivariateCoefficientSeriesOver {R : Type*} [Semiring R]
    (f g : ℕ → ℕ → R) (i j : ℕ) :
    PowerSeries.coeff j
        (PowerSeries.coeff i
          (bivariateCoefficientSeriesOver f * bivariateCoefficientSeriesOver g)) =
      additiveBivariateConvolutionOver f g i j := by
  rw [PowerSeries.coeff_mul]
  simp only [map_sum]
  rw [show (∑ x ∈ Finset.HasAntidiagonal.antidiagonal i,
      PowerSeries.coeff j
        (PowerSeries.coeff x.1 (bivariateCoefficientSeriesOver f) *
          PowerSeries.coeff x.2 (bivariateCoefficientSeriesOver g))) =
      ∑ a ∈ Finset.range (i + 1), PowerSeries.coeff j
        (PowerSeries.coeff a (bivariateCoefficientSeriesOver f) *
          PowerSeries.coeff (i - a) (bivariateCoefficientSeriesOver g)) by
      simpa using Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff j
          (PowerSeries.coeff a (bivariateCoefficientSeriesOver f) *
            PowerSeries.coeff b (bivariateCoefficientSeriesOver g))) i]
  simp only [PowerSeries.coeff_mul, coeff_bivariateCoefficientSeriesOver]
  rw [additiveBivariateConvolutionOver]
  apply Finset.sum_congr rfl
  intro a ha
  simpa using Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun b c => f a b * g (i - a) c) j

theorem bivariateCoefficientSeriesOver_convolution {R : Type*} [Semiring R]
    (f g : ℕ → ℕ → R) :
    bivariateCoefficientSeriesOver (additiveBivariateConvolutionOver f g) =
      bivariateCoefficientSeriesOver f * bivariateCoefficientSeriesOver g := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  rw [coeff_bivariateCoefficientSeriesOver, coeff_mul_bivariateCoefficientSeriesOver]

theorem bivariateCoefficientSeriesOver_injective {R : Type*} [Semiring R] :
    Function.Injective (bivariateCoefficientSeriesOver :
      (ℕ → ℕ → R) → PowerSeries (PowerSeries R)) := by
  intro f g h
  funext i j
  have hc := congrArg (fun F => PowerSeries.coeff j (PowerSeries.coeff i F)) h
  simpa using hc

def additiveBivariateOneOver {R : Type*} [Semiring R] (i j : ℕ) : R :=
  if i = 0 ∧ j = 0 then 1 else 0

def additiveBivariateMonomialOver {R : Type*} [Semiring R]
    (a b : ℕ) (c : R) (i j : ℕ) : R :=
  if i = a ∧ j = b then c else 0

theorem bivariateCoefficientSeriesOver_monomial {R : Type*} [Semiring R]
    (a b : ℕ) (c : R) :
    bivariateCoefficientSeriesOver (additiveBivariateMonomialOver a b c) =
      PowerSeries.monomial a (PowerSeries.monomial b c) := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  by_cases hi : i = a
  · subst i
    simp [additiveBivariateMonomialOver, PowerSeries.coeff_monomial]
  · simp [additiveBivariateMonomialOver, PowerSeries.coeff_monomial, hi]

theorem additiveBivariateConvolutionOver_monomial {R : Type*} [CommSemiring R]
    (a b c d : ℕ) (x y : R) :
    additiveBivariateConvolutionOver
        (additiveBivariateMonomialOver a b x)
        (additiveBivariateMonomialOver c d y) =
      additiveBivariateMonomialOver (a + c) (b + d) (x * y) := by
  apply bivariateCoefficientSeriesOver_injective
  rw [bivariateCoefficientSeriesOver_convolution,
    bivariateCoefficientSeriesOver_monomial,
    bivariateCoefficientSeriesOver_monomial,
    PowerSeries.monomial_mul_monomial,
    PowerSeries.monomial_mul_monomial,
    bivariateCoefficientSeriesOver_monomial]

theorem bivariateCoefficientSeriesOver_one {R : Type*} [Semiring R] :
    bivariateCoefficientSeriesOver (additiveBivariateOneOver : ℕ → ℕ → R) = 1 := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  rw [coeff_bivariateCoefficientSeriesOver, PowerSeries.coeff_one]
  by_cases hi : i = 0
  · rw [if_pos hi, PowerSeries.coeff_one]
    simp [additiveBivariateOneOver, hi]
  · rw [if_neg hi]
    simp [additiveBivariateOneOver, hi]

theorem bivariateCoefficientSeriesOver_add {R : Type*} [Semiring R]
    (f g : ℕ → ℕ → R) :
    bivariateCoefficientSeriesOver (fun i j => f i j + g i j) =
      bivariateCoefficientSeriesOver f + bivariateCoefficientSeriesOver g := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp

theorem bivariateCoefficientSeriesOver_sub {R : Type*} [Ring R]
    (f g : ℕ → ℕ → R) :
    bivariateCoefficientSeriesOver (fun i j => f i j - g i j) =
      bivariateCoefficientSeriesOver f - bivariateCoefficientSeriesOver g := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp

theorem additiveBivariateConvolutionOver_assoc {R : Type*} [CommSemiring R]
    (f g h : ℕ → ℕ → R) :
    additiveBivariateConvolutionOver (additiveBivariateConvolutionOver f g) h =
      additiveBivariateConvolutionOver f (additiveBivariateConvolutionOver g h) := by
  apply bivariateCoefficientSeriesOver_injective
  rw [bivariateCoefficientSeriesOver_convolution, bivariateCoefficientSeriesOver_convolution,
    bivariateCoefficientSeriesOver_convolution, bivariateCoefficientSeriesOver_convolution,
    mul_assoc]

theorem additiveBivariateConvolutionOver_comm {R : Type*} [CommSemiring R]
    (f g : ℕ → ℕ → R) :
    additiveBivariateConvolutionOver f g = additiveBivariateConvolutionOver g f := by
  apply bivariateCoefficientSeriesOver_injective
  rw [bivariateCoefficientSeriesOver_convolution, bivariateCoefficientSeriesOver_convolution,
    mul_comm]

theorem additiveBivariateConvolutionOver_one_left {R : Type*} [Semiring R]
    (f : ℕ → ℕ → R) :
    additiveBivariateConvolutionOver additiveBivariateOneOver f = f := by
  apply bivariateCoefficientSeriesOver_injective
  rw [bivariateCoefficientSeriesOver_convolution, bivariateCoefficientSeriesOver_one, one_mul]

theorem additiveBivariateConvolutionOver_one_right {R : Type*} [CommSemiring R]
    (f : ℕ → ℕ → R) :
    additiveBivariateConvolutionOver f additiveBivariateOneOver = f := by
  rw [additiveBivariateConvolutionOver_comm, additiveBivariateConvolutionOver_one_left]

theorem additiveBivariateConvolutionOver_add_left {R : Type*} [CommSemiring R]
    (f g h : ℕ → ℕ → R) :
    additiveBivariateConvolutionOver (fun i j => f i j + g i j) h =
      fun i j => additiveBivariateConvolutionOver f h i j +
        additiveBivariateConvolutionOver g h i j := by
  apply bivariateCoefficientSeriesOver_injective
  rw [bivariateCoefficientSeriesOver_convolution, bivariateCoefficientSeriesOver_add,
    bivariateCoefficientSeriesOver_add, bivariateCoefficientSeriesOver_convolution,
    bivariateCoefficientSeriesOver_convolution]
  ring

theorem additiveBivariateConvolutionOver_add_right {R : Type*} [CommSemiring R]
    (f g h : ℕ → ℕ → R) :
    additiveBivariateConvolutionOver f (fun i j => g i j + h i j) =
      fun i j => additiveBivariateConvolutionOver f g i j +
        additiveBivariateConvolutionOver f h i j := by
  rw [additiveBivariateConvolutionOver_comm,
    additiveBivariateConvolutionOver_add_left]
  funext i j
  rw [additiveBivariateConvolutionOver_comm f g,
    additiveBivariateConvolutionOver_comm f h]

theorem additiveBivariateConvolutionOver_sub_left {R : Type*} [CommRing R]
    (f g h : ℕ → ℕ → R) :
    additiveBivariateConvolutionOver (fun i j => f i j - g i j) h =
      fun i j => additiveBivariateConvolutionOver f h i j -
        additiveBivariateConvolutionOver g h i j := by
  apply bivariateCoefficientSeriesOver_injective
  rw [bivariateCoefficientSeriesOver_convolution, bivariateCoefficientSeriesOver_sub,
    bivariateCoefficientSeriesOver_sub, bivariateCoefficientSeriesOver_convolution,
    bivariateCoefficientSeriesOver_convolution]
  ring

theorem additiveBivariateConvolutionOver_sub_right {R : Type*} [CommRing R]
    (f g h : ℕ → ℕ → R) :
    additiveBivariateConvolutionOver f (fun i j => g i j - h i j) =
      fun i j => additiveBivariateConvolutionOver f g i j -
        additiveBivariateConvolutionOver f h i j := by
  rw [additiveBivariateConvolutionOver_comm,
    additiveBivariateConvolutionOver_sub_left]
  funext i j
  rw [additiveBivariateConvolutionOver_comm f g,
    additiveBivariateConvolutionOver_comm f h]

def additiveBivariateDiagonalMonomialOver {R : Type*} [Semiring R]
    (c : R) (i j : ℕ) : R :=
  if i = 1 ∧ j = 1 then c else 0

def additiveBivariateDiagonalShiftOver {R : Type*} [Semiring R]
    (c : R) (f : ℕ → ℕ → R) (i j : ℕ) : R :=
  if i = 0 ∨ j = 0 then 0 else c * f (i - 1) (j - 1)

theorem additiveBivariateConvolutionOver_diagonalMonomial_left
    {R : Type*} [CommSemiring R] (c : R) (f : ℕ → ℕ → R) :
    additiveBivariateConvolutionOver (additiveBivariateDiagonalMonomialOver c) f =
      additiveBivariateDiagonalShiftOver c f := by
  funext i j
  rw [additiveBivariateConvolutionOver]
  rcases i.eq_zero_or_pos with rfl | hi
  · simp [additiveBivariateDiagonalMonomialOver, additiveBivariateDiagonalShiftOver]
  rcases j.eq_zero_or_pos with rfl | hj
  · simp [additiveBivariateDiagonalMonomialOver, additiveBivariateDiagonalShiftOver]
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  rw [additiveBivariateDiagonalShiftOver, if_neg (by omega)]
  rw [Finset.sum_eq_single 1]
  · rw [Finset.sum_eq_single 1]
    · simp [additiveBivariateDiagonalMonomialOver]
    · intro b hb hb1
      simp [additiveBivariateDiagonalMonomialOver, hb1]
    · intro h
      exact (h (by simp)).elim
  · intro a ha ha1
    rw [Finset.sum_eq_zero]
    intro b hb
    simp [additiveBivariateDiagonalMonomialOver, ha1]
  · intro h
    exact (h (by simp)).elim

theorem additiveBivariateConvolutionOver_diagonalMonomial_right
    {R : Type*} [CommSemiring R] (f : ℕ → ℕ → R) (c : R) :
    additiveBivariateConvolutionOver f (additiveBivariateDiagonalMonomialOver c) =
      additiveBivariateDiagonalShiftOver c f := by
  rw [additiveBivariateConvolutionOver_comm,
    additiveBivariateConvolutionOver_diagonalMonomial_left]

private theorem sum_divisor_subtype_eq_sum_over {M : Type*} [AddCommMonoid M]
    (s : Finset ℕ) (f : ℕ → M) :
    (∑ x : {x // x ∈ s}, f x.1) = ∑ x ∈ s, f x := by
  change (∑ x ∈ s.attach, f x.1) = _
  exact Finset.sum_attach s f

/-- Prime-power reduction of bivariate Dirichlet convolution over any commutative semiring. -/
theorem bivariateDirichletConvolution_prime_pow_over
    {R : Type*} [CommSemiring R] (f g : ℕ → ℕ → R)
    {p i j : ℕ} (hp : p.Prime) :
    bivariateDirichletConvolution f g (p ^ i) (p ^ j) =
      additiveBivariateConvolutionOver
        (fun a b => f (p ^ a) (p ^ b))
        (fun a b => g (p ^ a) (p ^ b)) i j := by
  rw [bivariateDirichletConvolution, if_neg (by simp [hp.ne_zero]),
    Fintype.sum_prod_type]
  change (∑ x : {x // x ∈ (p ^ i).divisors},
      ∑ y : {y // y ∈ (p ^ j).divisors},
        f x.1 y.1 * g ((p ^ i) / x.1) ((p ^ j) / y.1)) = _
  have houter := sum_divisor_subtype_eq_sum_over (p ^ i).divisors
    (fun x => ∑ y : {y // y ∈ (p ^ j).divisors},
      f x y.1 * g ((p ^ i) / x) ((p ^ j) / y.1))
  rw [houter]
  have hinner :
      (∑ x ∈ (p ^ i).divisors, ∑ y : {y // y ∈ (p ^ j).divisors},
        f x y.1 * g ((p ^ i) / x) ((p ^ j) / y.1)) =
      ∑ x ∈ (p ^ i).divisors, ∑ y ∈ (p ^ j).divisors,
        f x y * g ((p ^ i) / x) ((p ^ j) / y) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact sum_divisor_subtype_eq_sum_over (p ^ j).divisors
      (fun y => f x y * g ((p ^ i) / x) ((p ^ j) / y))
  rw [hinner, Nat.sum_divisors_prime_pow hp, additiveBivariateConvolutionOver]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro b hb
  have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  rw [Nat.pow_div hai hp.pos, Nat.pow_div hbj hp.pos]

end


end RHTower.Sieve
