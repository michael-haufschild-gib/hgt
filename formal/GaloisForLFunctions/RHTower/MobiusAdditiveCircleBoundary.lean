import GaloisForLFunctions.RHTower.BourgainFiniteFourierParseval
import GaloisForLFunctions.RHTower.MobiusExponentialGibbsBoundary

/-!
# Additive-circle boundary normalization for the Möbius source

The damped Möbius series is evaluated at the distinguished additive-circle point `1`.  Finite
Parseval identifies its root-mean-square carrier exactly, while a flat polynomial proves that no
coefficient-blind point-evaluation inequality can supply the missing half power.  The resulting
subpower lattice-evaluation predicate is source-exact in the forward direction needed by Route E.

This module also records the arithmetic sign identity behind the Lambert-dilation Gram kernel.
No cancellation estimate, zero-free hypothesis, or form of RH is assumed.
-/

open Complex Filter
open scoped BigOperators Polynomial Topology

namespace RHTower

noncomputable section

private theorem sum_filter_identity_eq
    {α R : Type*} [DecidableEq α] [AddCommMonoid R]
    (s : Finset α) (w : α → R) {a : α} (ha : a ∈ s) :
    ∑ i ∈ s.filter (fun i => i = a), w i = w a := by
  have hfilter : s.filter (fun i => i = a) = {a} := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hi).2
    · intro hi
      have hia : i = a := Finset.mem_singleton.mp hi
      subst i
      exact Finset.mem_filter.mpr ⟨ha, rfl⟩
  rw [hfilter]
  simp

/-- Coefficient of the finite exponentially damped Möbius circle polynomial. -/
def finiteDampedMobiusCircleCoefficient (x : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
    Complex.exp (-((n : ℝ) * x : ℝ))

/-- Finite additive-circle carrier `sum_{1 <= n <= N} mu(n)e^{-nx}z^n`. -/
def finiteDampedMobiusCirclePolynomial (N : ℕ) (x : ℝ) : ℂ[X] :=
  finiteFrequencyPolynomial (Finset.Icc 1 N) id
    (finiteDampedMobiusCircleCoefficient x)

/-- Evaluation at the distinguished lattice point is the finite damped Möbius sum. -/
theorem finiteDampedMobiusCirclePolynomial_eval_one (N : ℕ) (x : ℝ) :
    (finiteDampedMobiusCirclePolynomial N x).eval 1 =
      ∑ n ∈ Finset.Icc 1 N, finiteDampedMobiusCircleCoefficient x n := by
  rw [finiteDampedMobiusCirclePolynomial, finiteFrequencyPolynomial,
    Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Polynomial.eval_monomial]
  simp

/-- Exact finite Parseval law for the damped Möbius circle carrier. -/
theorem circleAverage_finiteDampedMobiusCirclePolynomial_norm_sq (N : ℕ) (x : ℝ) :
    Real.circleAverage
        (fun z => ‖(finiteDampedMobiusCirclePolynomial N x).eval z‖ ^ (2 : ℕ))
        0 1 =
      ∑ n ∈ Finset.Icc 1 N, ‖finiteDampedMobiusCircleCoefficient x n‖ ^ (2 : ℕ) := by
  classical
  rw [finiteDampedMobiusCirclePolynomial]
  have hparse := circleAverage_finiteFrequencyPolynomial_norm_sq
    (Finset.Icc 1 N) id (finiteDampedMobiusCircleCoefficient x)
  rw [Finset.image_id] at hparse
  rw [hparse]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [id_eq]
  rw [sum_filter_identity_eq (Finset.Icc 1 N)
    (finiteDampedMobiusCircleCoefficient x) hn]

/-- Flat finite circle polynomial, the hostile model for coefficient-blind evaluation bounds. -/
def flatCirclePolynomial (N : ℕ) : ℂ[X] :=
  finiteFrequencyPolynomial (Finset.range N) id (fun _ => (1 : ℂ))

/-- The flat polynomial has value `N` at the distinguished lattice point. -/
theorem flatCirclePolynomial_eval_one (N : ℕ) :
    (flatCirclePolynomial N).eval 1 = (N : ℂ) := by
  rw [flatCirclePolynomial, finiteFrequencyPolynomial, Polynomial.eval_finsetSum]
  simp [Polynomial.eval_monomial]

/-- The flat polynomial has squared circle RMS exactly `N`. -/
theorem circleAverage_flatCirclePolynomial_norm_sq (N : ℕ) :
    Real.circleAverage
        (fun z => ‖(flatCirclePolynomial N).eval z‖ ^ (2 : ℕ)) 0 1 = N := by
  classical
  rw [flatCirclePolynomial]
  have hparse := circleAverage_finiteFrequencyPolynomial_norm_sq
    (Finset.range N) id (fun _ : ℕ => (1 : ℂ))
  rw [Finset.image_id] at hparse
  rw [hparse]
  calc
    (∑ n ∈ Finset.range N,
        ‖∑ i ∈ (Finset.range N).filter (fun i => i = n), (1 : ℂ)‖ ^ (2 : ℕ)) =
        ∑ _n ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [sum_filter_identity_eq (Finset.range N) (fun _ : ℕ => (1 : ℂ)) hn]
      norm_num
    _ = N := by simp

/-- Positive `L²` energy of the damped Möbius circle series.  Parseval identifies this with
`sum mu(n)^(2 : ℕ) exp(-2nx)`. -/
def mobiusAdditiveCircleEnergy (x : ℝ) : ℝ :=
  mobiusSquarefreeExponentialPartition (2 * x)

theorem mobiusAdditiveCircleEnergy_pos {x : ℝ} (hx : 0 < x) :
    0 < mobiusAdditiveCircleEnergy x := by
  change 0 < mobiusSquarefreeExponentialPartition (2 * x)
  exact mobiusSquarefreeExponentialPartition_pos (by positivity)

/-- Elementary energy ceiling at the critical RMS scale. -/
theorem mobiusAdditiveCircleEnergy_le_inv {x : ℝ} (hx : 0 < x) :
    mobiusAdditiveCircleEnergy x ≤ 1 / (2 * x) := by
  change mobiusSquarefreeExponentialPartition (2 * x) ≤ 1 / (2 * x)
  exact mobiusSquarefreeExponentialPartition_le_inv (by positivity)

/-- The square root of the exact circle energy is at most the critical half-power. -/
theorem sqrt_mobiusAdditiveCircleEnergy_le_rpow_neg_half {x : ℝ} (hx : 0 < x) :
    Real.sqrt (mobiusAdditiveCircleEnergy x) ≤ x ^ (-(1 / 2 : ℝ)) := by
  have hE : mobiusAdditiveCircleEnergy x ≤ 1 / x := by
    refine (mobiusAdditiveCircleEnergy_le_inv hx).trans ?_
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  calc
    Real.sqrt (mobiusAdditiveCircleEnergy x) ≤ Real.sqrt (1 / x) :=
      Real.sqrt_le_sqrt hE
    _ = x ^ (-(1 / 2 : ℝ)) := by
      rw [one_div, Real.sqrt_inv, Real.sqrt_eq_rpow, Real.rpow_neg hx.le]

/-- Source-exact additive-lattice delocalization conjecture: the distinguished value exceeds the
circle RMS by at most a subpower.  This is deliberately Möbius-specific; the flat polynomial above
rules out a coefficient-blind version. -/
def MobiusAdditiveLatticeSubpowerEvaluation : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖mobiusDiscreteLaplaceTransform x‖ ≤
        C * x ^ (-ε) * Real.sqrt (mobiusAdditiveCircleEnergy x)

/-- Unconditional consumer: additive-lattice subpower evaluation supplies every strict
half-power Möbius--Laplace bound. -/
theorem mobiusDiscreteLaplaceAllStrictHalfPowerDecay_of_additiveLatticeEvaluation
    (hdeloc : MobiusAdditiveLatticeSubpowerEvaluation) :
    MobiusDiscreteLaplaceAllStrictHalfPowerDecay := by
  intro b hb
  let ε : ℝ := b - 1 / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hbound⟩ := hdeloc ε hε
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx0 hx1
  have hx : 0 < x := hx0
  have hP := hbound x hx hx1.le
  have hE := sqrt_mobiusAdditiveCircleEnergy_le_rpow_neg_half hx
  calc
    ‖mobiusDiscreteLaplaceTransform x‖ ≤
        C * x ^ (-ε) * Real.sqrt (mobiusAdditiveCircleEnergy x) := hP
    _ ≤ C * x ^ (-ε) * x ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hE (mul_nonneg hC (Real.rpow_nonneg hx.le _))
    _ = C * x ^ (-b) := by
      rw [mul_assoc, ← Real.rpow_add hx]
      congr 2
      dsimp [ε]
      ring
    _ = C * ‖x ^ (-b)‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)]

/-- Unconditional consumer: a proof of Möbius additive-lattice delocalization proves RH. -/
theorem riemannHypothesis_of_mobiusAdditiveLatticeSubpowerEvaluation
    (hdeloc : MobiusAdditiveLatticeSubpowerEvaluation) :
    RiemannHypothesis :=
  mobiusDiscreteLaplaceAllStrictHalfPowerDecay_implies_riemannHypothesis
    (mobiusDiscreteLaplaceAllStrictHalfPowerDecay_of_additiveLatticeEvaluation hdeloc)

/-! ## Arithmetic sign of the dilation Gram entries -/

/-- If the coprime quotient directions `a,b` and the residual direction `r` have disjoint prime
support, the two Möbius coefficients in a dilation resonance factor into the orientation
`mu(ab)` times the positive squarefree coefficient `mu(r)^(2 : ℕ)`. -/
theorem mobius_coprime_dilation_pair_product
    {a b r : ℕ} (hab : a.Coprime b) (hqr : (a * b).Coprime r) :
    ArithmeticFunction.moebius (b * r) * ArithmeticFunction.moebius (a * r) =
      ArithmeticFunction.moebius (a * b) * ArithmeticFunction.moebius r ^ 2 := by
  have hbr : b.Coprime r :=
    Nat.Coprime.of_dvd_left (dvd_mul_left b a) hqr
  have har : a.Coprime r :=
    Nat.Coprime.of_dvd_left (dvd_mul_right a b) hqr
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hbr,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime har,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab]
  ring

/-- A nonsquarefree quotient direction annihilates every corresponding dilation Gram entry. -/
theorem mobius_dilation_pair_product_eq_zero_of_not_squarefree_left
    {a b r : ℕ} (ha : ¬Squarefree a) :
    ArithmeticFunction.moebius (b * r) * ArithmeticFunction.moebius (a * r) = 0 := by
  have hzero : ArithmeticFunction.moebius (a * r) = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun har =>
      ha ((Nat.squarefree_mul (Nat.coprime_of_squarefree_mul har)).mp har).1
  rw [hzero, mul_zero]

/-- Symmetric nonsquarefree quotient annihilation. -/
theorem mobius_dilation_pair_product_eq_zero_of_not_squarefree_right
    {a b r : ℕ} (hb : ¬Squarefree b) :
    ArithmeticFunction.moebius (b * r) * ArithmeticFunction.moebius (a * r) = 0 := by
  have hzero : ArithmeticFunction.moebius (b * r) = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun hbr =>
      hb ((Nat.squarefree_mul (Nat.coprime_of_squarefree_mul hbr)).mp hbr).1
  rw [hzero, zero_mul]

end

end RHTower
