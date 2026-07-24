import GaloisForLFunctions.HTGeometry.BivariateMarginalTraceLock
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# Weighted bivariate marginal lock

A diagonal density on each factor does not remove the conservation law behind ordinary partial
trace.  If a finite product kernel is contracted with a source weight and a jet weight, then the
jet marginal paired with the jet weight equals the source marginal paired with the source weight.

The statement uses no positivity, symmetry, normalization, or nondegeneracy.  Weights may vanish
or have arbitrary sign.
-/

open scoped BigOperators
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Diagonal weighted trace of a finite square kernel. -/
def diagonalWeightedTrace
    {I R : Type*} [Fintype I] [CommSemiring R]
    (weight : I → R) (A : Matrix I I R) : R :=
  ∑ i, weight i * A i i

/-- Jet marginal obtained by contracting the source diagonal against a source weight. -/
def weightedBivariateJetMarginal
    {P J R : Type*} [Fintype P] [Fintype J] [CommSemiring R]
    (sourceWeight : P → R) (C : Matrix (P × J) (P × J) R) :
    Matrix J J R :=
  fun i j => ∑ p, sourceWeight p * C (p, i) (p, j)

/-- Source marginal obtained by contracting the jet diagonal against a jet weight. -/
def weightedBivariateSourceMarginal
    {P J R : Type*} [Fintype P] [Fintype J] [CommSemiring R]
    (jetWeight : J → R) (C : Matrix (P × J) (P × J) R) :
    Matrix P P R :=
  fun p q => ∑ i, jetWeight i * C (p, i) (q, i)

/-- **Universal weighted bivariate marginal lock.**  Pairing either weighted coordinate marginal
with the weight on the other factor gives the same scalar. -/
theorem diagonalWeightedTrace_weightedBivariateJetMarginal_eq
    {P J R : Type*} [Fintype P] [Fintype J] [CommSemiring R]
    (sourceWeight : P → R) (jetWeight : J → R)
    (C : Matrix (P × J) (P × J) R) :
    diagonalWeightedTrace jetWeight
        (weightedBivariateJetMarginal sourceWeight C) =
      diagonalWeightedTrace sourceWeight
        (weightedBivariateSourceMarginal jetWeight C) := by
  change (∑ i : J, jetWeight i * ∑ p : P,
      sourceWeight p * C (p, i) (p, i)) =
    ∑ p : P, sourceWeight p * ∑ i : J,
      jetWeight i * C (p, i) (p, i)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro i hi
  ac_rfl

/-- Trace pairing of a finite observable against an arbitrary matrix density. -/
def matrixDensityPair
    {I R : Type*} [Fintype I] [CommSemiring R]
    (density observable : Matrix I I R) : R :=
  ∑ i, ∑ j, density j i * observable i j

/-- Jet marginal obtained by contracting both source coordinates against a matrix density. -/
def densityBivariateJetMarginal
    {P J R : Type*} [Fintype P] [Fintype J] [CommSemiring R]
    (sourceDensity : Matrix P P R)
    (C : Matrix (P × J) (P × J) R) : Matrix J J R :=
  fun i j => ∑ p, ∑ q, sourceDensity q p * C (p, i) (q, j)

/-- Source marginal obtained by contracting both jet coordinates against a matrix density. -/
def densityBivariateSourceMarginal
    {P J R : Type*} [Fintype P] [Fintype J] [CommSemiring R]
    (jetDensity : Matrix J J R)
    (C : Matrix (P × J) (P × J) R) : Matrix P P R :=
  fun p q => ∑ i, ∑ j, jetDensity j i * C (p, i) (q, j)

/-- **Full-density bivariate marginal lock.**  The conservation law persists for arbitrary
matrix densities on both tensor factors, not only diagonal weights. -/
theorem matrixDensityPair_densityBivariateJetMarginal_eq
    {P J R : Type*} [Fintype P] [Fintype J] [CommSemiring R]
    (sourceDensity : Matrix P P R) (jetDensity : Matrix J J R)
    (C : Matrix (P × J) (P × J) R) :
    matrixDensityPair jetDensity
        (densityBivariateJetMarginal sourceDensity C) =
      matrixDensityPair sourceDensity
        (densityBivariateSourceMarginal jetDensity C) := by
  change (∑ i : J, ∑ j : J, jetDensity j i *
      ∑ p : P, ∑ q : P, sourceDensity q p * C (p, i) (q, j)) =
    ∑ p : P, ∑ q : P, sourceDensity q p *
      ∑ i : J, ∑ j : J, jetDensity j i * C (p, i) (q, j)
  simp_rw [Finset.mul_sum]
  calc
    (∑ i : J, ∑ j : J, ∑ p : P, ∑ q : P,
        jetDensity j i * (sourceDensity q p * C (p, i) (q, j))) =
        ∑ i : J, ∑ p : P, ∑ j : J, ∑ q : P,
          jetDensity j i * (sourceDensity q p * C (p, i) (q, j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ p : P, ∑ i : J, ∑ j : J, ∑ q : P,
          jetDensity j i * (sourceDensity q p * C (p, i) (q, j)) := by
      rw [Finset.sum_comm]
    _ = ∑ p : P, ∑ i : J, ∑ q : P, ∑ j : J,
          jetDensity j i * (sourceDensity q p * C (p, i) (q, j)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ p : P, ∑ q : P, ∑ i : J, ∑ j : J,
          jetDensity j i * (sourceDensity q p * C (p, i) (q, j)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = ∑ p : P, ∑ q : P, ∑ i : J, ∑ j : J,
          sourceDensity q p * (jetDensity j i * C (p, i) (q, j)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ac_rfl

/-- A density reader is cyclic against a clock when the clock may be moved across every observed
matrix without changing the density pairing. -/
def MatrixDensityClockCyclic
    {I : Type*} [Fintype I] [DecidableEq I]
    (density : Matrix I I ℝ) (clock : I → ℝ) : Prop :=
  ∀ A : Matrix I I ℝ,
    matrixDensityPair density (Matrix.diagonal clock * A) =
      matrixDensityPair density (A * Matrix.diagonal clock)

@[simp] theorem matrixDensityPair_single
    {I : Type*} [Fintype I] [DecidableEq I]
    (density : Matrix I I ℝ) (i j : I) (x : ℝ) :
    matrixDensityPair density (Matrix.single i j x) = density j i * x := by
  unfold matrixDensityPair
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [Ne.symm hbj]
    · simp
  · intro a ha hai
    apply Finset.sum_eq_zero
    intro b hb
    simp [Ne.symm hai]
  · simp

/-- Cyclicity against one simple-spectrum clock already forces the density to be diagonal in that
clock basis.  Full-matrix cyclicity is not required. -/
theorem matrixDensityClockCyclic_offDiagonal_eq_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (density : Matrix I I ℝ) (clock : I → ℝ)
    (hclock : Function.Injective clock)
    (hcyc : MatrixDensityClockCyclic density clock)
    {i j : I} (hij : i ≠ j) :
    density i j = 0 := by
  have h := hcyc (Matrix.single j i 1)
  have hleft :
      Matrix.diagonal clock * Matrix.single j i 1 =
        Matrix.single j i (clock j) := by
    ext a b
    rw [Matrix.diagonal_mul]
    by_cases hja : j = a <;> by_cases hib : i = b <;>
      simp [hja, hib]
  have hright :
      Matrix.single j i 1 * Matrix.diagonal clock =
        Matrix.single j i (clock i) := by
    ext a b
    rw [Matrix.mul_diagonal]
    by_cases hja : j = a <;> by_cases hib : i = b <;>
      simp [hja, hib]
  rw [hleft, hright, matrixDensityPair_single, matrixDensityPair_single] at h
  have hne : clock j - clock i ≠ 0 := sub_ne_zero.mpr (hclock.ne hij.symm)
  have hzero : (clock j - clock i) * density i j = 0 := by
    linarith
  exact (mul_eq_zero.mp hzero).resolve_left hne

/-- Canonical normalized counterweight for a Hankel moment sequence.  At stage `n+1`, the new
coefficient is the unique scalar which cancels the opening flux, provided `moment (n+3) ≠ 0`. -/
noncomputable def hankelToeplitzCounterweight (moment : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      -(moment (2 * (n + 1) + 2) +
          2 * ∑ j : Fin n,
            hankelToeplitzCounterweight moment
                ((n + 1) - ((j : ℕ) + 1)) *
              moment ((n + 1) + ((j : ℕ) + 1) + 2)) /
        (2 * moment (n + 3))
termination_by n => n
decreasing_by omega

theorem hankelToeplitzCounterweight_succ
    (moment : ℕ → ℝ) (n : ℕ) :
    hankelToeplitzCounterweight moment (n + 1) =
      -(moment (2 * (n + 1) + 2) +
          2 * ∑ j : Fin n,
            hankelToeplitzCounterweight moment
                ((n + 1) - ((j : ℕ) + 1)) *
              moment ((n + 1) + ((j : ℕ) + 1) + 2)) /
        (2 * moment (n + 3)) := by
  rw [hankelToeplitzCounterweight]

/-- The recursively selected coefficient cancels the next Hankel trace opening exactly. -/
theorem hankelToeplitzCounterweight_opening_cancellation
    (moment : ℕ → ℝ) (n : ℕ) (hmoment : moment (n + 3) ≠ 0) :
    moment (2 * (n + 1) + 2) +
        2 * ∑ i : Fin (n + 1),
          hankelToeplitzCounterweight moment
              ((n + 1) - (i : ℕ)) *
            moment ((n + 1) + (i : ℕ) + 2) = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.sub_zero, add_zero, Fin.val_succ]
  rw [hankelToeplitzCounterweight_succ]
  field_simp
  ring

/-- Symmetric Toeplitz density canonically generated by the Hankel counterweight sequence. -/
noncomputable def hankelToeplitzCounterDensity
    (moment : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i ≤ j then
    hankelToeplitzCounterweight moment (j - i)
  else
    hankelToeplitzCounterweight moment (i - j)

theorem hankelToeplitzCounterDensity_self
    (moment : ℕ → ℝ) (i : ℕ) :
    hankelToeplitzCounterDensity moment i i = 1 := by
  simp [hankelToeplitzCounterDensity, hankelToeplitzCounterweight]

theorem hankelToeplitzCounterDensity_boundary
    (moment : ℕ → ℝ) (N : ℕ) (i : Fin N) :
    hankelToeplitzCounterDensity moment N i =
        hankelToeplitzCounterweight moment (N - (i : ℕ)) ∧
      hankelToeplitzCounterDensity moment i N =
        hankelToeplitzCounterweight moment (N - (i : ℕ)) := by
  constructor
  · rw [hankelToeplitzCounterDensity, if_neg]
    omega
  · rw [hankelToeplitzCounterDensity, if_pos]
    omega

/-- **Universal Hankel--Toeplitz countertrace law.**  Every nonvanishing Hankel moment sequence
canonically determines a normalized symmetric Toeplitz density whose new boundary row cancels the
next finite-section trace opening. -/
theorem hankelToeplitzCounterDensity_opening_cancellation
    (moment : ℕ → ℝ) (n : ℕ) (hmoment : moment (n + 3) ≠ 0) :
    hankelToeplitzCounterDensity moment (n + 1) (n + 1) *
          moment (2 * (n + 1) + 2) +
        ∑ i : Fin (n + 1),
          (hankelToeplitzCounterDensity moment (n + 1) i +
              hankelToeplitzCounterDensity moment i (n + 1)) *
            moment ((n + 1) + i + 2) = 0 := by
  rw [hankelToeplitzCounterDensity_self]
  simp_rw [hankelToeplitzCounterDensity_boundary]
  rw [one_mul]
  calc
    moment (2 * (n + 1) + 2) +
        ∑ i : Fin (n + 1),
          (hankelToeplitzCounterweight moment (n + 1 - (i : ℕ)) +
              hankelToeplitzCounterweight moment (n + 1 - (i : ℕ))) *
            moment (n + 1 + (i : ℕ) + 2) =
      moment (2 * (n + 1) + 2) +
        2 * ∑ i : Fin (n + 1),
          hankelToeplitzCounterweight moment (n + 1 - (i : ℕ)) *
            moment (n + 1 + (i : ℕ) + 2) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 :=
      hankelToeplitzCounterweight_opening_cancellation moment n hmoment

/-- Counterweight recursion is continuous under pointwise convergence of moment sequences as long
as limiting pivots remain nonzero.  Thus source truncations cannot select an unrelated cofinal
countertrace. -/
theorem tendsto_hankelToeplitzCounterweight
    {ι : Type*} {l : Filter ι}
    (momentApprox : ι → ℕ → ℝ) (moment : ℕ → ℝ)
    (hmoment : ∀ q : ℕ,
      Tendsto (fun a => momentApprox a q) l (nhds (moment q)))
    (hnonzero : ∀ n : ℕ, moment (n + 3) ≠ 0) :
    ∀ n : ℕ,
      Tendsto
        (fun a => hankelToeplitzCounterweight (momentApprox a) n)
        l
        (nhds (hankelToeplitzCounterweight moment n)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simpa [hankelToeplitzCounterweight] using
            (tendsto_const_nhds :
              Tendsto (fun _a : ι => (1 : ℝ)) l (nhds 1))
      | succ n =>
          have hsum :
              Tendsto
                (fun a =>
                  ∑ j : Fin n,
                    hankelToeplitzCounterweight (momentApprox a)
                        ((n + 1) - ((j : ℕ) + 1)) *
                      momentApprox a ((n + 1) + ((j : ℕ) + 1) + 2))
                l
                (nhds
                  (∑ j : Fin n,
                    hankelToeplitzCounterweight moment
                        ((n + 1) - ((j : ℕ) + 1)) *
                      moment ((n + 1) + ((j : ℕ) + 1) + 2))) := by
            apply tendsto_finsetSum
            intro j hj
            exact
              (ih ((n + 1) - ((j : ℕ) + 1)) (by omega)).mul
                (hmoment ((n + 1) + ((j : ℕ) + 1) + 2))
          have hnum :
              Tendsto
                (fun a =>
                  -(momentApprox a (2 * (n + 1) + 2) +
                    2 * ∑ j : Fin n,
                      hankelToeplitzCounterweight (momentApprox a)
                          ((n + 1) - ((j : ℕ) + 1)) *
                        momentApprox a ((n + 1) + ((j : ℕ) + 1) + 2)))
                l
                (nhds
                  (-(moment (2 * (n + 1) + 2) +
                    2 * ∑ j : Fin n,
                      hankelToeplitzCounterweight moment
                          ((n + 1) - ((j : ℕ) + 1)) *
                        moment ((n + 1) + ((j : ℕ) + 1) + 2)))) :=
            ((hmoment (2 * (n + 1) + 2)).add
              (tendsto_const_nhds.mul hsum)).neg
          have hden :
              Tendsto
                (fun a => 2 * momentApprox a (n + 3))
                l
                (nhds (2 * moment (n + 3))) :=
            tendsto_const_nhds.mul (hmoment (n + 3))
          have hdenzero : 2 * moment (n + 3) ≠ 0 :=
            mul_ne_zero (by norm_num) (hnonzero n)
          simpa only [hankelToeplitzCounterweight_succ] using
            hnum.div hden hdenzero

/-- Uniqueness of the normalized Toeplitz countertrace.  Every weight sequence with initial value
one that cancels every Hankel opening is forced coefficient-by-coefficient by the source moments.
-/
theorem hankelToeplitzCounterweight_unique
    (moment weight : ℕ → ℝ)
    (hweight0 : weight 0 = 1)
    (hnonzero : ∀ n : ℕ, moment (n + 3) ≠ 0)
    (hcancel : ∀ n : ℕ,
      moment (2 * (n + 1) + 2) +
        2 * ∑ i : Fin (n + 1),
          weight ((n + 1) - (i : ℕ)) *
            moment ((n + 1) + (i : ℕ) + 2) = 0) :
    weight = hankelToeplitzCounterweight moment := by
  funext k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero =>
          simpa [hankelToeplitzCounterweight] using hweight0
      | succ n =>
          have hc := hcancel n
          rw [Fin.sum_univ_succ] at hc
          simp only [Fin.val_zero, Nat.sub_zero, add_zero, Fin.val_succ] at hc
          have htail :
              (∑ j : Fin n,
                weight ((n + 1) - ((j : ℕ) + 1)) *
                  moment ((n + 1) + ((j : ℕ) + 1) + 2)) =
                ∑ j : Fin n,
                  hankelToeplitzCounterweight moment
                      ((n + 1) - ((j : ℕ) + 1)) *
                    moment ((n + 1) + ((j : ℕ) + 1) + 2) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [ih ((n + 1) - ((j : ℕ) + 1)) (by omega)]
          rw [htail] at hc
          rw [hankelToeplitzCounterweight_succ]
          apply (eq_div_iff (mul_ne_zero (by norm_num) (hnonzero n))).2
          linarith

/-- Restriction of an infinite matrix density to its first `N` coordinates. -/
def finiteDensitySection
    (density : ℕ → ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => density i j

/-- Finite Hankel section with the order-two shift used by the countertrace law. -/
noncomputable def shiftedMomentHankelMatrix
    (moment : ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => moment ((i : ℕ) + (j : ℕ) + 2)

/-- Exact opening law for pairing an arbitrary inclusion-compatible density with shifted Hankel
sections. -/
theorem matrixDensityPair_shiftedMomentHankelMatrix_succ
    (moment : ℕ → ℝ) (N : ℕ) (density : ℕ → ℕ → ℝ) :
    matrixDensityPair (finiteDensitySection density (N + 1))
        (shiftedMomentHankelMatrix moment (N + 1)) =
      matrixDensityPair (finiteDensitySection density N)
          (shiftedMomentHankelMatrix moment N) +
        density N N * moment (2 * N + 2) +
        ∑ i : Fin N, (density N i + density i N) *
          moment (N + i + 2) := by
  unfold matrixDensityPair finiteDensitySection shiftedMomentHankelMatrix
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  simp_rw [add_mul, Finset.sum_add_distrib]
  have hcross :
      (∑ i : Fin N, density N i * moment (i + N + 2)) =
        ∑ i : Fin N, density N i * moment (N + i + 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    omega
  rw [hcross]
  ring_nf

/-- Consecutive nonempty Hankel sections have equal countertrace value. -/
theorem hankelToeplitzCounterDensity_pair_succ
    (moment : ℕ → ℝ) (n : ℕ) (hmoment : moment (n + 3) ≠ 0) :
    matrixDensityPair
        (finiteDensitySection (hankelToeplitzCounterDensity moment) (n + 2))
        (shiftedMomentHankelMatrix moment (n + 2)) =
      matrixDensityPair
        (finiteDensitySection (hankelToeplitzCounterDensity moment) (n + 1))
        (shiftedMomentHankelMatrix moment (n + 1)) := by
  have hopen :=
    matrixDensityPair_shiftedMomentHankelMatrix_succ
      moment (n + 1) (hankelToeplitzCounterDensity moment)
  have hcancel :=
    hankelToeplitzCounterDensity_opening_cancellation moment n hmoment
  linarith

/-- **Universal normalized Hankel--Toeplitz countertrace theorem.**  The canonical symmetric
Toeplitz density pairs every nonempty shifted Hankel section to the same first value `moment 2`.
-/
theorem hankelToeplitzCounterDensity_pair_constant
    (moment : ℕ → ℝ)
    (hmoment : ∀ n : ℕ, moment (n + 3) ≠ 0)
    (N : ℕ) :
    matrixDensityPair
        (finiteDensitySection (hankelToeplitzCounterDensity moment) (N + 1))
        (shiftedMomentHankelMatrix moment (N + 1)) =
      moment 2 := by
  induction N with
  | zero =>
      simp [matrixDensityPair, finiteDensitySection, shiftedMomentHankelMatrix,
        hankelToeplitzCounterDensity_self]
  | succ N ih =>
      rw [hankelToeplitzCounterDensity_pair_succ moment N (hmoment N)]
      exact ih

end GaloisForLFunctions.HTGeometry
