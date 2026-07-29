import GaloisForLFunctions.RHTower.FiniteWindowRecurrenceInstability
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Parity-conditioned forecasting instability

Parity conditioning of a fair binomial spectrum produces a continuum of
finite nonnegative-energy clocks. Their energy moments agree to arbitrarily
high finite order, their complete survival records converge exponentially on
every strict pre-return window, and their target return probabilities fill
the entire interval `[0,1]`.
-/

open scoped BigOperators
open Complex

noncomputable section

namespace RHTower.ParityForecast

private theorem alternating_binomial_moment_zero
    {n k : ℕ} (hk : k < n) :
    ∑ j : Fin (n + 1),
        ((-1 : ℝ) ^ (n - (j : ℕ))) *
          (n.choose j : ℝ) * (j : ℝ) ^ k = 0 := by
  have hzero :=
    congrFun
      (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) hk) 0
  rw [fwdDiff_iter_eq_sum_shift] at hzero
  rw [Fin.sum_univ_eq_sum_range
    (fun j =>
      ((-1 : ℝ) ^ (n - j)) *
        (n.choose j : ℝ) * (j : ℝ) ^ k) (n + 1)]
  norm_num at hzero ⊢
  simpa [Int.cast_pow, Int.cast_neg, Int.cast_one,
    mul_assoc] using hzero

/-- Full fair-binomial spectral weight. -/
def fullWeight (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  RHTower.FiniteWindow.binomialWeight n j

/--
Parity-conditioned binomial weight.  The factor is two on the parity class
of `n` and zero on the opposite class.
-/
def parityWeight (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  fullWeight n j * (1 + (-1 : ℝ) ^ (n - (j : ℕ)))

/-- Common nonnegative half-lattice energy. -/
def halfLatticeEnergy (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  (j : ℝ) / 2

theorem fullWeight_nonneg (n : ℕ) (j : Fin (n + 1)) :
    0 ≤ fullWeight n j :=
  RHTower.FiniteWindow.binomialWeight_nonneg n j

theorem parityWeight_nonneg (n : ℕ) (j : Fin (n + 1)) :
    0 ≤ parityWeight n j := by
  rcases neg_one_pow_eq_or ℝ (n - (j : ℕ)) with h | h
  · simp [parityWeight, h, fullWeight_nonneg]
  · simp [parityWeight, h]

theorem halfLatticeEnergy_nonneg (n : ℕ) (j : Fin (n + 1)) :
    0 ≤ halfLatticeEnergy n j := by
  exact div_nonneg (Nat.cast_nonneg _) (by norm_num)

private theorem signed_fullWeight_moment_zero
    {n k : ℕ} (hk : k < n) :
    ∑ j : Fin (n + 1),
        fullWeight n j * (-1 : ℝ) ^ (n - (j : ℕ)) *
          (j : ℝ) ^ k = 0 := by
  rw [show
      (∑ j : Fin (n + 1),
        fullWeight n j * (-1 : ℝ) ^ (n - (j : ℕ)) *
          (j : ℝ) ^ k) =
      (∑ j : Fin (n + 1),
        (-1 : ℝ) ^ (n - (j : ℕ)) *
          (n.choose j : ℝ) * (j : ℝ) ^ k) / 2 ^ n by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    unfold fullWeight RHTower.FiniteWindow.binomialWeight
    ring]
  rw [alternating_binomial_moment_zero hk]
  simp

/-- Parity conditioning preserves every raw moment of order below `n`. -/
theorem parity_rawMoment_eq_full
    {n k : ℕ} (hk : k < n) :
    ∑ j : Fin (n + 1), parityWeight n j * (j : ℝ) ^ k =
      ∑ j : Fin (n + 1), fullWeight n j * (j : ℝ) ^ k := by
  calc
    (∑ j : Fin (n + 1), parityWeight n j * (j : ℝ) ^ k) =
        ∑ j : Fin (n + 1),
          (fullWeight n j * (j : ℝ) ^ k +
            fullWeight n j * (-1 : ℝ) ^ (n - (j : ℕ)) *
              (j : ℝ) ^ k) := by
      apply Finset.sum_congr rfl
      intro j _hj
      unfold parityWeight
      ring
    _ = (∑ j : Fin (n + 1), fullWeight n j * (j : ℝ) ^ k) +
        ∑ j : Fin (n + 1),
          fullWeight n j * (-1 : ℝ) ^ (n - (j : ℕ)) *
            (j : ℝ) ^ k := by
      rw [Finset.sum_add_distrib]
    _ = ∑ j : Fin (n + 1), fullWeight n j * (j : ℝ) ^ k := by
      rw [signed_fullWeight_moment_zero hk, add_zero]

/-- The two physical energy moments agree through every order below `n`. -/
theorem parity_energyMoment_eq_full
    {n k : ℕ} (hk : k < n) :
    ∑ j : Fin (n + 1),
        parityWeight n j * halfLatticeEnergy n j ^ k =
      ∑ j : Fin (n + 1),
        fullWeight n j * halfLatticeEnergy n j ^ k := by
  simp only [halfLatticeEnergy, div_pow]
  rw [show
      (∑ j : Fin (n + 1),
        parityWeight n j * ((j : ℝ) ^ k / 2 ^ k)) =
      ∑ j : Fin (n + 1),
        (parityWeight n j * (j : ℝ) ^ k) / 2 ^ k by
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  rw [show
      (∑ j : Fin (n + 1),
        fullWeight n j * ((j : ℝ) ^ k / 2 ^ k)) =
      ∑ j : Fin (n + 1),
        (fullWeight n j * (j : ℝ) ^ k) / 2 ^ k by
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  rw [← Finset.sum_div, ← Finset.sum_div,
    parity_rawMoment_eq_full hk]

theorem fullWeight_sum (n : ℕ) :
    ∑ j : Fin (n + 1), fullWeight n j = 1 :=
  RHTower.FiniteWindow.binomialWeight_sum n

theorem parityWeight_sum {n : ℕ} (hn : 0 < n) :
    ∑ j : Fin (n + 1), parityWeight n j = 1 := by
  have h := parity_rawMoment_eq_full (n := n) (k := 0) hn
  simpa [fullWeight_sum] using h

/-- Full fair-binomial survival amplitude on the half lattice. -/
def fullAmplitude (n : ℕ) (t : ℝ) : ℂ :=
  (((1 : ℂ) + Complex.exp (((Real.pi * t : ℝ) : ℂ) * I)) / 2) ^ n

/-- Parity-conditioned survival amplitude. -/
def parityAmplitude (n : ℕ) (t : ℝ) : ℂ :=
  fullAmplitude n t +
    ((Complex.exp (((Real.pi * t : ℝ) : ℂ) * I) - 1) / 2) ^ n

/-- Dynamical phase generated by the nonnegative half-lattice energy. -/
def halfLatticePhase (n : ℕ) (t : ℝ) (j : Fin (n + 1)) : ℂ :=
  Complex.exp
    (((2 * Real.pi * halfLatticeEnergy n j * t : ℝ) : ℂ) * I)

theorem halfLatticePhase_norm
    (n : ℕ) (t : ℝ) (j : Fin (n + 1)) :
    ‖halfLatticePhase n t j‖ = 1 := by
  rw [halfLatticePhase, Complex.norm_exp]
  simp [Complex.mul_re]

private theorem halfLatticePhase_eq_power
    (n : ℕ) (t : ℝ) (j : Fin (n + 1)) :
    halfLatticePhase n t j =
      Complex.exp (((Real.pi * t : ℝ) : ℂ) * I) ^ (j : ℕ) := by
  rw [halfLatticePhase, halfLatticeEnergy, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem signed_fullWeight_generating (n : ℕ) (z : ℂ) :
    ∑ j : Fin (n + 1),
        (fullWeight n j : ℂ) *
          (-1 : ℂ) ^ (n - (j : ℕ)) * z ^ (j : ℕ) =
      ((z - 1) / 2) ^ n := by
  have hfin :
      (∑ j : Fin (n + 1),
        (n.choose j : ℂ) *
          z ^ (j : ℕ) * (-1 : ℂ) ^ (n - (j : ℕ))) =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * z ^ j * (-1 : ℂ) ^ (n - j) := by
    exact Fin.sum_univ_eq_sum_range
      (fun j =>
        (n.choose j : ℂ) * z ^ j * (-1 : ℂ) ^ (n - j)) (n + 1)
  unfold fullWeight RHTower.FiniteWindow.binomialWeight
  push_cast
  rw [show
      (∑ j : Fin (n + 1),
        ((n.choose j : ℂ) / (2 : ℂ) ^ n) *
          (-1 : ℂ) ^ (n - (j : ℕ)) * z ^ (j : ℕ)) =
      (∑ j : Fin (n + 1),
        (n.choose j : ℂ) * z ^ (j : ℕ) *
          (-1 : ℂ) ^ (n - (j : ℕ))) / (2 : ℂ) ^ n by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  rw [hfin]
  have h := add_pow z (-1 : ℂ) n
  have hsum :
      (∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * z ^ j * (-1 : ℂ) ^ (n - j)) =
        (z - 1) ^ n := by
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h.symm
  rw [hsum, div_pow]

theorem full_weighted_phase_sum (n : ℕ) (t : ℝ) :
    ∑ j : Fin (n + 1),
        (fullWeight n j : ℂ) * halfLatticePhase n t j =
      fullAmplitude n t := by
  simp_rw [halfLatticePhase_eq_power]
  exact RHTower.FiniteWindow.binomialWeight_generating n _

theorem parity_weighted_phase_sum (n : ℕ) (t : ℝ) :
    ∑ j : Fin (n + 1),
        (parityWeight n j : ℂ) * halfLatticePhase n t j =
      parityAmplitude n t := by
  simp_rw [halfLatticePhase_eq_power]
  let z := Complex.exp (((Real.pi * t : ℝ) : ℂ) * I)
  change
    (∑ j : Fin (n + 1),
      (parityWeight n j : ℂ) * z ^ (j : ℕ)) =
      parityAmplitude n t
  rw [show
      (∑ j : Fin (n + 1),
        (parityWeight n j : ℂ) * z ^ (j : ℕ)) =
      (∑ j : Fin (n + 1),
        (fullWeight n j : ℂ) * z ^ (j : ℕ)) +
      ∑ j : Fin (n + 1),
        (fullWeight n j : ℂ) *
          (-1 : ℂ) ^ (n - (j : ℕ)) * z ^ (j : ℕ) by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    unfold parityWeight
    push_cast
    ring]
  have hfull :
      (∑ j : Fin (n + 1),
        (fullWeight n j : ℂ) * z ^ (j : ℕ)) =
        ((1 + z) / 2) ^ n := by
    unfold fullWeight
    exact RHTower.FiniteWindow.binomialWeight_generating n z
  rw [hfull, signed_fullWeight_generating]
  rfl

@[simp] theorem fullAmplitude_zero (n : ℕ) :
    fullAmplitude n 0 = 1 := by
  simp [fullAmplitude]

@[simp] theorem parityAmplitude_zero {n : ℕ} (hn : 0 < n) :
    parityAmplitude n 0 = 1 := by
  simp [parityAmplitude, fullAmplitude, zero_pow hn.ne']

@[simp] theorem fullAmplitude_one {n : ℕ} (hn : 0 < n) :
    fullAmplitude n 1 = 0 := by
  rw [fullAmplitude]
  norm_num [zero_pow hn.ne']

theorem parityAmplitude_one {n : ℕ} (hn : 0 < n) :
    parityAmplitude n 1 = (-1 : ℂ) ^ n := by
  rw [parityAmplitude, fullAmplitude]
  norm_num [zero_pow hn.ne']

theorem parityAmplitude_one_norm {n : ℕ} (hn : 0 < n) :
    ‖parityAmplitude n 1‖ = 1 := by
  rw [parityAmplitude_one hn, norm_pow]
  norm_num

theorem amplitude_difference_exact (n : ℕ) (t : ℝ) :
    parityAmplitude n t - fullAmplitude n t =
      ((Complex.exp (((Real.pi * t : ℝ) : ℂ) * I) - 1) / 2) ^ n := by
  unfold parityAmplitude
  ring

private theorem norm_exp_sub_one_div_two (x : ℝ) :
    ‖(Complex.exp ((x : ℂ) * I) - 1) / 2‖ =
      |Real.sin (x / 2)| := by
  rw [norm_div,
    show (x : ℂ) * I = I * (x : ℂ) by ring,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  simp [Real.norm_eq_abs]

theorem amplitude_difference_norm (n : ℕ) (t : ℝ) :
    ‖parityAmplitude n t - fullAmplitude n t‖ =
      |Real.sin (Real.pi * t / 2)| ^ n := by
  rw [amplitude_difference_exact, norm_pow,
    norm_exp_sub_one_div_two]

private theorem abs_sin_half_pi_le
    {t ρ : ℝ} (hρ1 : ρ ≤ 1) (ht : |t| ≤ ρ) :
    |Real.sin (Real.pi * t / 2)| ≤
      Real.sin (Real.pi * ρ / 2) := by
  have ht_abs :
      |Real.pi * t / 2| = Real.pi * |t| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  have ht_arg_nonneg : 0 ≤ |Real.pi * t / 2| := abs_nonneg _
  have ht_arg_le :
      |Real.pi * t / 2| ≤ Real.pi * ρ / 2 := by
    rw [ht_abs]
    nlinarith [Real.pi_pos]
  have hρ_arg_le : Real.pi * ρ / 2 ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have ht_pi : |Real.pi * t / 2| ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi ht_pi]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two
    (by nlinarith [Real.pi_pos]) hρ_arg_le ht_arg_le

/--
Exact exponential control on every strict subperiod: throughout
`|t| ≤ ρ ≤ 1`, the amplitude discrepancy is at most
`sin (πρ/2)^n`.
-/
theorem amplitude_difference_window_bound
    (n : ℕ) {t ρ : ℝ} (hρ1 : ρ ≤ 1)
    (ht : |t| ≤ ρ) :
    ‖parityAmplitude n t - fullAmplitude n t‖ ≤
      Real.sin (Real.pi * ρ / 2) ^ n := by
  rw [amplitude_difference_norm]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_sin_half_pi_le hρ1 ht) n

private theorem sin_half_pi_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) :
    0 ≤ Real.sin (Real.pi * ρ / 2) := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

private theorem sin_half_pi_lt_one {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) :
    Real.sin (Real.pi * ρ / 2) < 1 := by
  rw [← Real.sin_pi_div_two]
  apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
  · nlinarith [Real.pi_pos]
  · exact le_rfl
  · nlinarith [Real.pi_pos]

/--
Universal unscaled law.  For every requested moment order, every strict
pre-return fraction, and every positive precision, one finite positive
spectrum supports two normalized clocks that agree in all energy moments
through that order and uniformly throughout the whole observed interval,
but end at exact return and exact orthogonality.
-/
theorem exists_every_order_every_strict_window
    (m : ℕ) {ρ ε : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hε : 0 < ε) :
    ∃ n : ℕ,
      m < n ∧
      (∀ k : ℕ, k ≤ m →
        ∑ j : Fin (n + 1),
            parityWeight n j * halfLatticeEnergy n j ^ k =
          ∑ j : Fin (n + 1),
            fullWeight n j * halfLatticeEnergy n j ^ k) ∧
      (∀ t : ℝ, |t| ≤ ρ →
        ‖parityAmplitude n t - fullAmplitude n t‖ < ε) ∧
      ‖parityAmplitude n 1‖ = 1 ∧
      fullAmplitude n 1 = 0 := by
  let q := Real.sin (Real.pi * ρ / 2)
  have hq0 : 0 ≤ q :=
    sin_half_pi_nonneg hρ0 hρ1.le
  have hq1 : q < 1 :=
    sin_half_pi_lt_one hρ0 hρ1
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one hε hq1
  let n := max (m + 1) a
  have hm1n : m + 1 ≤ n := le_max_left _ _
  have han : a ≤ n := le_max_right _ _
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ m) hm1n
  refine ⟨n, by omega, ?_, ?_, parityAmplitude_one_norm hn0,
    fullAmplitude_one hn0⟩
  · intro k hk
    exact parity_energyMoment_eq_full (lt_of_le_of_lt hk (by omega))
  · intro t ht
    have hwindow :=
      amplitude_difference_window_bound n hρ1.le ht
    have hpow : q ^ n ≤ q ^ a :=
      pow_le_pow_of_le_one hq0 hq1.le han
    exact lt_of_le_of_lt
      (hwindow.trans (by simpa [q] using hpow)) ha

theorem fullAmplitude_norm_le_one (n : ℕ) (t : ℝ) :
    ‖fullAmplitude n t‖ ≤ 1 := by
  rw [← full_weighted_phase_sum]
  calc
    ‖∑ j : Fin (n + 1),
        (fullWeight n j : ℂ) * halfLatticePhase n t j‖ ≤
        ∑ j : Fin (n + 1),
          ‖(fullWeight n j : ℂ) * halfLatticePhase n t j‖ :=
      norm_sum_le _ _
    _ = ∑ j : Fin (n + 1), fullWeight n j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [norm_mul, halfLatticePhase_norm]
      simp [Real.norm_eq_abs, abs_of_nonneg (fullWeight_nonneg n j)]
    _ = 1 := fullWeight_sum n

theorem parityAmplitude_norm_le_one {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖parityAmplitude n t‖ ≤ 1 := by
  rw [← parity_weighted_phase_sum]
  calc
    ‖∑ j : Fin (n + 1),
        (parityWeight n j : ℂ) * halfLatticePhase n t j‖ ≤
        ∑ j : Fin (n + 1),
          ‖(parityWeight n j : ℂ) * halfLatticePhase n t j‖ :=
      norm_sum_le _ _
    _ = ∑ j : Fin (n + 1), parityWeight n j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [norm_mul, halfLatticePhase_norm]
      simp [Real.norm_eq_abs, abs_of_nonneg (parityWeight_nonneg n j)]
    _ = 1 := parityWeight_sum hn

/-- Directly observable return probability for the full-binomial clock. -/
def fullProbability (n : ℕ) (t : ℝ) : ℝ :=
  ‖fullAmplitude n t‖ ^ 2

/-- Directly observable return probability for the parity clock. -/
def parityProbability (n : ℕ) (t : ℝ) : ℝ :=
  ‖parityAmplitude n t‖ ^ 2

/-- Convex spectral interpolation from the full clock to the parity clock. -/
def interpolatedWeight
    (n : ℕ) (θ : ℝ) (j : Fin (n + 1)) : ℝ :=
  (1 - θ) * fullWeight n j + θ * parityWeight n j

/-- Its survival amplitude, written in closed affine form. -/
def interpolatedAmplitude (n : ℕ) (θ t : ℝ) : ℂ :=
  (1 - θ) * fullAmplitude n t + θ * parityAmplitude n t

/-- Its directly observable return probability. -/
def interpolatedProbability (n : ℕ) (θ t : ℝ) : ℝ :=
  ‖interpolatedAmplitude n θ t‖ ^ 2

theorem interpolatedWeight_nonneg
    (n : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (j : Fin (n + 1)) :
    0 ≤ interpolatedWeight n θ j := by
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr hθ1) (fullWeight_nonneg n j))
    (mul_nonneg hθ0 (parityWeight_nonneg n j))

theorem interpolatedWeight_sum
    {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    ∑ j : Fin (n + 1), interpolatedWeight n θ j = 1 := by
  rw [show
      (∑ j : Fin (n + 1), interpolatedWeight n θ j) =
        (1 - θ) * (∑ j : Fin (n + 1), fullWeight n j) +
          θ * ∑ j : Fin (n + 1), parityWeight n j by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    rfl]
  rw [fullWeight_sum, parityWeight_sum hn]
  ring

theorem interpolated_energyMoment_eq_full
    {n k : ℕ} (hk : k < n) (θ : ℝ) :
    ∑ j : Fin (n + 1),
        interpolatedWeight n θ j * halfLatticeEnergy n j ^ k =
      ∑ j : Fin (n + 1),
        fullWeight n j * halfLatticeEnergy n j ^ k := by
  rw [show
      (∑ j : Fin (n + 1),
        interpolatedWeight n θ j * halfLatticeEnergy n j ^ k) =
        (1 - θ) *
            (∑ j : Fin (n + 1),
              fullWeight n j * halfLatticeEnergy n j ^ k) +
          θ *
            ∑ j : Fin (n + 1),
              parityWeight n j * halfLatticeEnergy n j ^ k by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    unfold interpolatedWeight
    ring]
  rw [parity_energyMoment_eq_full hk]
  ring

theorem interpolated_weighted_phase_sum
    (n : ℕ) (θ t : ℝ) :
    ∑ j : Fin (n + 1),
        (interpolatedWeight n θ j : ℂ) *
          halfLatticePhase n t j =
      interpolatedAmplitude n θ t := by
  rw [show
      (∑ j : Fin (n + 1),
        (interpolatedWeight n θ j : ℂ) *
          halfLatticePhase n t j) =
        (1 - (θ : ℂ)) *
            (∑ j : Fin (n + 1),
              (fullWeight n j : ℂ) * halfLatticePhase n t j) +
          (θ : ℂ) *
            ∑ j : Fin (n + 1),
              (parityWeight n j : ℂ) * halfLatticePhase n t j by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    unfold interpolatedWeight
    push_cast
    ring]
  rw [full_weighted_phase_sum, parity_weighted_phase_sum]
  rfl

theorem interpolatedAmplitude_target
    {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    interpolatedAmplitude n θ 1 = (θ : ℂ) * (-1 : ℂ) ^ n := by
  rw [interpolatedAmplitude, fullAmplitude_one hn,
    parityAmplitude_one hn]
  ring

theorem interpolatedProbability_target
    {n : ℕ} (hn : 0 < n) {θ : ℝ} (hθ0 : 0 ≤ θ) :
    interpolatedProbability n θ 1 = θ ^ 2 := by
  rw [interpolatedProbability, interpolatedAmplitude_target hn,
    norm_mul, norm_pow]
  simp [Real.norm_eq_abs, abs_of_nonneg hθ0]

theorem interpolatedAmplitude_difference_norm
    (n : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (t : ℝ) :
    ‖interpolatedAmplitude n θ t - fullAmplitude n t‖ =
      θ * ‖parityAmplitude n t - fullAmplitude n t‖ := by
  rw [show
      interpolatedAmplitude n θ t - fullAmplitude n t =
        (θ : ℂ) * (parityAmplitude n t - fullAmplitude n t) by
    unfold interpolatedAmplitude
    ring,
    norm_mul]
  simp [Real.norm_eq_abs, abs_of_nonneg hθ0]

theorem interpolatedAmplitude_norm_le_one
    {n : ℕ} (hn : 0 < n) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ) :
    ‖interpolatedAmplitude n θ t‖ ≤ 1 := by
  rw [← interpolated_weighted_phase_sum]
  calc
    ‖∑ j : Fin (n + 1),
        (interpolatedWeight n θ j : ℂ) *
          halfLatticePhase n t j‖ ≤
        ∑ j : Fin (n + 1),
          ‖(interpolatedWeight n θ j : ℂ) *
            halfLatticePhase n t j‖ :=
      norm_sum_le _ _
    _ = ∑ j : Fin (n + 1), interpolatedWeight n θ j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [norm_mul, halfLatticePhase_norm]
      simp [Real.norm_eq_abs,
        abs_of_nonneg (interpolatedWeight_nonneg n hθ0 hθ1 j)]
    _ = 1 := interpolatedWeight_sum hn θ

theorem interpolated_probability_difference_le_amplitude
    {n : ℕ} (hn : 0 < n) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ) :
    |interpolatedProbability n θ t - fullProbability n t| ≤
      2 * ‖interpolatedAmplitude n θ t - fullAmplitude n t‖ := by
  let a := interpolatedAmplitude n θ t
  let b := fullAmplitude n t
  have ha : ‖a‖ ≤ 1 :=
    interpolatedAmplitude_norm_le_one hn hθ0 hθ1 t
  have hb : ‖b‖ ≤ 1 := fullAmplitude_norm_le_one n t
  have hab : |‖a‖ - ‖b‖| ≤ ‖a - b‖ :=
    abs_norm_sub_norm_le a b
  have hsum : |‖a‖ + ‖b‖| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    linarith
  rw [interpolatedProbability, fullProbability,
    show ‖interpolatedAmplitude n θ t‖ ^ 2 -
        ‖fullAmplitude n t‖ ^ 2 =
      (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by
        dsimp [a, b]
        ring,
    abs_mul]
  calc
    |‖a‖ - ‖b‖| * |‖a‖ + ‖b‖| ≤ ‖a - b‖ * 2 :=
      mul_le_mul hab hsum (abs_nonneg _) (norm_nonneg _)
    _ = 2 *
        ‖interpolatedAmplitude n θ t - fullAmplitude n t‖ := by
      dsimp [a, b]
      ring

/--
Complete future interval: one finite `n` works simultaneously for every
prescribed terminal return probability `p ∈ [0,1]`.  Each corresponding
clock matches the same first `m` energy moments and stays close to the full
clock throughout the strict pre-return window.
-/
theorem exists_every_future_probability_every_strict_window
    (m : ℕ) {ρ ε : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hε : 0 < ε) :
    ∃ n : ℕ,
      m < n ∧
      ∀ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 →
        (∀ k : ℕ, k ≤ m →
          ∑ j : Fin (n + 1),
              interpolatedWeight n (Real.sqrt p) j *
                halfLatticeEnergy n j ^ k =
            ∑ j : Fin (n + 1),
              fullWeight n j * halfLatticeEnergy n j ^ k) ∧
        (∀ t : ℝ, |t| ≤ ρ →
          ‖interpolatedAmplitude n (Real.sqrt p) t -
            fullAmplitude n t‖ < ε) ∧
        (∀ t : ℝ, |t| ≤ ρ →
          |interpolatedProbability n (Real.sqrt p) t -
            fullProbability n t| < 2 * ε) ∧
        interpolatedProbability n (Real.sqrt p) 1 = p := by
  obtain ⟨n, hmn, _hmom, hamp, _hparity, _hfull⟩ :=
    exists_every_order_every_strict_window m hρ0 hρ1 hε
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le m) hmn
  refine ⟨n, hmn, ?_⟩
  intro p hp
  have hθ0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hθ1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    exact interpolated_energyMoment_eq_full
      (lt_of_le_of_lt hk hmn) _
  · intro t ht
    rw [interpolatedAmplitude_difference_norm n hθ0]
    have hclose := hamp t ht
    have hmul :
        Real.sqrt p *
            ‖parityAmplitude n t - fullAmplitude n t‖ ≤
          ‖parityAmplitude n t - fullAmplitude n t‖ := by
      nlinarith [norm_nonneg (parityAmplitude n t - fullAmplitude n t)]
    exact lt_of_le_of_lt hmul hclose
  · intro t ht
    have hclose :
        ‖interpolatedAmplitude n (Real.sqrt p) t -
          fullAmplitude n t‖ < ε := by
      rw [interpolatedAmplitude_difference_norm n hθ0]
      have hparityClose := hamp t ht
      have hmul :
          Real.sqrt p *
              ‖parityAmplitude n t - fullAmplitude n t‖ ≤
            ‖parityAmplitude n t - fullAmplitude n t‖ := by
        nlinarith [norm_nonneg
          (parityAmplitude n t - fullAmplitude n t)]
      exact lt_of_le_of_lt hmul hparityClose
    exact lt_of_le_of_lt
      (interpolated_probability_difference_le_amplitude
        hn hθ0 hθ1 t)
      (by nlinarith)
  · rw [interpolatedProbability_target hn hθ0,
      Real.sq_sqrt hp.1]

@[simp] theorem fullProbability_one {n : ℕ} (hn : 0 < n) :
    fullProbability n 1 = 0 := by
  rw [fullProbability, fullAmplitude_one hn]
  norm_num

@[simp] theorem parityProbability_one {n : ℕ} (hn : 0 < n) :
    parityProbability n 1 = 1 := by
  rw [parityProbability, parityAmplitude_one_norm hn]
  norm_num

theorem fullProbability_mem_Icc (n : ℕ) (t : ℝ) :
    fullProbability n t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact sq_nonneg _
  · unfold fullProbability
    nlinarith [norm_nonneg (fullAmplitude n t),
      fullAmplitude_norm_le_one n t]

theorem parityProbability_mem_Icc {n : ℕ} (hn : 0 < n) (t : ℝ) :
    parityProbability n t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact sq_nonneg _
  · unfold parityProbability
    nlinarith [norm_nonneg (parityAmplitude n t),
      parityAmplitude_norm_le_one hn t]

/--
Return probability is 2-Lipschitz in survival amplitude for these normalized
clocks.
-/
theorem probability_difference_le_amplitude
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    |parityProbability n t - fullProbability n t| ≤
      2 * ‖parityAmplitude n t - fullAmplitude n t‖ := by
  let a := parityAmplitude n t
  let b := fullAmplitude n t
  have ha : ‖a‖ ≤ 1 := parityAmplitude_norm_le_one hn t
  have hb : ‖b‖ ≤ 1 := fullAmplitude_norm_le_one n t
  have hab : |‖a‖ - ‖b‖| ≤ ‖a - b‖ :=
    abs_norm_sub_norm_le a b
  have hsum : |‖a‖ + ‖b‖| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    linarith
  rw [parityProbability, fullProbability,
    show ‖parityAmplitude n t‖ ^ 2 - ‖fullAmplitude n t‖ ^ 2 =
      (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by
        dsimp [a, b]
        ring,
    abs_mul]
  calc
    |‖a‖ - ‖b‖| * |‖a‖ + ‖b‖| ≤ ‖a - b‖ * 2 :=
      mul_le_mul hab hsum (abs_nonneg _) (norm_nonneg _)
    _ = 2 * ‖parityAmplitude n t - fullAmplitude n t‖ := by
      dsimp [a, b]
      ring

theorem probability_difference_window_bound
    {n : ℕ} (hn : 0 < n) {t ρ : ℝ}
    (hρ1 : ρ ≤ 1) (ht : |t| ≤ ρ) :
    |parityProbability n t - fullProbability n t| ≤
      2 * Real.sin (Real.pi * ρ / 2) ^ n := by
  exact (probability_difference_le_amplitude hn t).trans
    (mul_le_mul_of_nonneg_left
      (amplitude_difference_window_bound n hρ1 ht)
      (by norm_num))

/-! ## Sharp spectral support threshold -/

/--
On `r` distinct energy levels, the first `r` moments determine all spectral
weights.  This is the Vandermonde obstruction behind the optimality of the
construction.
-/
theorem weights_eq_of_first_moments_on_distinct_nodes
    {r : ℕ} {energy weight₁ weight₂ : Fin r → ℝ}
    (henergy : Function.Injective energy)
    (hmoment : ∀ k : Fin r,
      ∑ j : Fin r, weight₁ j * energy j ^ (k : ℕ) =
        ∑ j : Fin r, weight₂ j * energy j ^ (k : ℕ)) :
    weight₁ = weight₂ := by
  have hzero : ∀ k : Fin r,
      ∑ j : Fin r,
        (weight₁ j - weight₂ j) * energy j ^ (k : ℕ) = 0 := by
    intro k
    calc
      (∑ j : Fin r,
        (weight₁ j - weight₂ j) * energy j ^ (k : ℕ)) =
          ∑ j : Fin r,
            (weight₁ j * energy j ^ (k : ℕ) -
              weight₂ j * energy j ^ (k : ℕ)) := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = (∑ j : Fin r, weight₁ j * energy j ^ (k : ℕ)) -
          ∑ j : Fin r, weight₂ j * energy j ^ (k : ℕ) :=
        by rw [Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr (hmoment k)
  have hdiff :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero henergy hzero
  funext j
  have hj := congrFun hdiff j
  exact sub_eq_zero.mp hj

/--
Consequently, at most `n` distinct levels cannot support two different
spectral measures whose moments agree through order `n-1`.
-/
theorem no_nontrivial_n_moment_match_on_at_most_n_nodes
    {r n : ℕ} (hrn : r ≤ n)
    {energy weight₁ weight₂ : Fin r → ℝ}
    (henergy : Function.Injective energy)
    (hmoment : ∀ k : ℕ, k < n →
      ∑ j : Fin r, weight₁ j * energy j ^ k =
        ∑ j : Fin r, weight₂ j * energy j ^ k) :
    weight₁ = weight₂ := by
  apply weights_eq_of_first_moments_on_distinct_nodes henergy
  intro k
  exact hmoment k (lt_of_lt_of_le k.isLt hrn)

theorem halfLatticeEnergy_injective (n : ℕ) :
    Function.Injective (halfLatticeEnergy n) := by
  intro i j hij
  apply Fin.ext
  unfold halfLatticeEnergy at hij
  exact_mod_cast (by linarith : (i : ℝ) = (j : ℝ))

theorem parityWeight_ne_fullWeight {n : ℕ} (hn : 0 < n) :
    parityWeight n ≠ fullWeight n := by
  intro hweight
  have hsum := congrArg
    (fun weight : Fin (n + 1) → ℝ =>
      ∑ j : Fin (n + 1),
        (weight j : ℂ) * halfLatticePhase n 1 j)
    hweight
  dsimp at hsum
  rw [parity_weighted_phase_sum, full_weighted_phase_sum,
    parityAmplitude_one hn, fullAmplitude_one hn] at hsum
  have hnonzero : ((-1 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact hnonzero hsum

/--
Sharpness: the parity/full pair is nonidentical, agrees in its first `n`
moments, and uses the minimum possible number `n+1` of distinct levels.
-/
theorem parity_pair_attains_minimal_spectral_support
    {n : ℕ} (hn : 0 < n) :
    Function.Injective (halfLatticeEnergy n) ∧
    parityWeight n ≠ fullWeight n ∧
    (∀ k : ℕ, k < n →
      ∑ j : Fin (n + 1),
          parityWeight n j * halfLatticeEnergy n j ^ k =
        ∑ j : Fin (n + 1),
          fullWeight n j * halfLatticeEnergy n j ^ k) :=
  ⟨halfLatticeEnergy_injective n, parityWeight_ne_fullWeight hn,
    fun _ hk => parity_energyMoment_eq_full hk⟩

/--
The terminal separation is extremal: no two return probabilities can differ
by more than one, and this pair attains one exactly.
-/
theorem parity_pair_attains_maximal_probability_separation
    {n : ℕ} (hn : 0 < n) :
    |parityProbability n 1 - fullProbability n 1| = 1 ∧
    (∀ t : ℝ,
      |parityProbability n t - fullProbability n t| ≤ 1) := by
  constructor
  · rw [parityProbability_one hn, fullProbability_one hn]
    norm_num
  · intro t
    rcases parityProbability_mem_Icc hn t with ⟨hp0, hp1⟩
    rcases fullProbability_mem_Icc n t with ⟨hf0, hf1⟩
    rw [abs_le]
    constructor <;> linarith

/-! ## Explicit same-Hamiltonian realization -/

/-- Shared finite-dimensional Hilbert space. -/
abbrev ClockSpace (n : ℕ) := FiniteIndexClockSpace (Fin (n + 1))

/-- Shared diagonal Hamiltonian with nonnegative half-lattice energies. -/
def clockHamiltonian (n : ℕ) :
    ClockSpace n →L[ℂ] ClockSpace n :=
  finiteIndexDiagonalHamiltonian (halfLatticeEnergy n)

/-- Full-binomial initial state. -/
def fullClock (n : ℕ) : ClockSpace n :=
  finiteIndexWeightKet (fullWeight n)

/-- Parity-conditioned initial state. -/
def parityClock (n : ℕ) : ClockSpace n :=
  finiteIndexWeightKet (parityWeight n)

def interpolatedClock (n : ℕ) (θ : ℝ) : ClockSpace n :=
  finiteIndexWeightKet (interpolatedWeight n θ)

def fullClockAt (n : ℕ) (t : ℝ) : ClockSpace n :=
  finiteIndexPhasedWeightKet (fullWeight n) (halfLatticePhase n t)

def parityClockAt (n : ℕ) (t : ℝ) : ClockSpace n :=
  finiteIndexPhasedWeightKet (parityWeight n) (halfLatticePhase n t)

def interpolatedClockAt
    (n : ℕ) (θ t : ℝ) : ClockSpace n :=
  finiteIndexPhasedWeightKet
    (interpolatedWeight n θ) (halfLatticePhase n t)

theorem clockHamiltonian_selfAdjoint (n : ℕ) :
    ContinuousLinearMap.adjoint (clockHamiltonian n) =
      clockHamiltonian n :=
  finiteIndexDiagonalHamiltonian_selfAdjoint _

@[simp] theorem fullClock_norm (n : ℕ) :
    ‖fullClock n‖ = 1 :=
  finiteIndexWeightKet_norm_eq_one _
    (fullWeight_nonneg n) (fullWeight_sum n)

@[simp] theorem parityClock_norm {n : ℕ} (hn : 0 < n) :
    ‖parityClock n‖ = 1 :=
  finiteIndexWeightKet_norm_eq_one _
    (parityWeight_nonneg n) (parityWeight_sum hn)

@[simp] theorem interpolatedClock_norm
    {n : ℕ} (hn : 0 < n) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖interpolatedClock n θ‖ = 1 :=
  finiteIndexWeightKet_norm_eq_one _
    (interpolatedWeight_nonneg n hθ0 hθ1)
    (interpolatedWeight_sum hn θ)

theorem fullClock_survivalAmplitude (n : ℕ) (t : ℝ) :
    inner ℂ (fullClock n) (fullClockAt n t) =
      fullAmplitude n t := by
  rw [fullClock, fullClockAt,
    finiteIndexWeightKet_inner_phasedWeightKet
      _ _ (fullWeight_nonneg n)]
  exact full_weighted_phase_sum n t

theorem parityClock_survivalAmplitude (n : ℕ) (t : ℝ) :
    inner ℂ (parityClock n) (parityClockAt n t) =
      parityAmplitude n t := by
  rw [parityClock, parityClockAt,
    finiteIndexWeightKet_inner_phasedWeightKet
      _ _ (parityWeight_nonneg n)]
  exact parity_weighted_phase_sum n t

theorem interpolatedClock_survivalAmplitude
    (n : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ) :
    inner ℂ (interpolatedClock n θ)
        (interpolatedClockAt n θ t) =
      interpolatedAmplitude n θ t := by
  rw [interpolatedClock, interpolatedClockAt,
    finiteIndexWeightKet_inner_phasedWeightKet
      _ _ (interpolatedWeight_nonneg n hθ0 hθ1)]
  exact interpolated_weighted_phase_sum n θ t

/-! ## Every positive target time -/

def scaledEnergy (T : ℝ) (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  halfLatticeEnergy n j / T

/-- Angular energies corresponding to the scaled cyclic frequencies. -/
def angularEnergy (T : ℝ) (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  2 * Real.pi * scaledEnergy T n j

theorem angularEnergy_eq
    (T : ℝ) (n : ℕ) (j : Fin (n + 1)) :
    angularEnergy T n j = Real.pi * (j : ℝ) / T := by
  simp only [angularEnergy, scaledEnergy, halfLatticeEnergy]
  ring

/-- One shared diagonal Hamiltonian at target time `T`. -/
def scaledClockHamiltonian (T : ℝ) (n : ℕ) :
    ClockSpace n →L[ℂ] ClockSpace n :=
  finiteIndexDiagonalHamiltonian (angularEnergy T n)

def scaledPhase (T : ℝ) (n : ℕ) (t : ℝ)
    (j : Fin (n + 1)) : ℂ :=
  Complex.exp
    (((2 * Real.pi * scaledEnergy T n j * t : ℝ) : ℂ) * I)

theorem scaledPhase_eq_angular
    (T : ℝ) (n : ℕ) (t : ℝ) (j : Fin (n + 1)) :
    scaledPhase T n t j =
      Complex.exp ((((angularEnergy T n j * t : ℝ) : ℂ)) * I) := by
  rfl

def scaledInterpolatedClockAt
    (T : ℝ) (n : ℕ) (θ t : ℝ) : ClockSpace n :=
  finiteIndexPhasedWeightKet
    (interpolatedWeight n θ) (scaledPhase T n t)

def scaledFullAmplitude (T : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  fullAmplitude n (t / T)

def scaledParityAmplitude (T : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  parityAmplitude n (t / T)

def scaledInterpolatedAmplitude
    (T : ℝ) (n : ℕ) (θ t : ℝ) : ℂ :=
  interpolatedAmplitude n θ (t / T)

def scaledFullProbability (T : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  fullProbability n (t / T)

def scaledParityProbability (T : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  parityProbability n (t / T)

def scaledInterpolatedProbability
    (T : ℝ) (n : ℕ) (θ t : ℝ) : ℝ :=
  interpolatedProbability n θ (t / T)

theorem scaledEnergy_nonneg {T : ℝ} (hT : 0 < T)
    (n : ℕ) (j : Fin (n + 1)) :
    0 ≤ scaledEnergy T n j :=
  div_nonneg (halfLatticeEnergy_nonneg n j) hT.le

theorem angularEnergy_nonneg {T : ℝ} (hT : 0 < T)
    (n : ℕ) (j : Fin (n + 1)) :
    0 ≤ angularEnergy T n j :=
  mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
    (scaledEnergy_nonneg hT n j)

theorem scaledClockHamiltonian_selfAdjoint (T : ℝ) (n : ℕ) :
    ContinuousLinearMap.adjoint (scaledClockHamiltonian T n) =
      scaledClockHamiltonian T n :=
  finiteIndexDiagonalHamiltonian_selfAdjoint _

private theorem scaledPhase_eq
    {T : ℝ} (hT : 0 < T) (n : ℕ) (t : ℝ)
    (j : Fin (n + 1)) :
    scaledPhase T n t j = halfLatticePhase n (t / T) j := by
  rw [scaledPhase, halfLatticePhase, scaledEnergy]
  congr 1
  push_cast
  field_simp [hT.ne']

theorem scaledPhase_norm
    {T : ℝ} (hT : 0 < T) (n : ℕ) (t : ℝ)
    (j : Fin (n + 1)) :
    ‖scaledPhase T n t j‖ = 1 := by
  rw [scaledPhase_eq hT]
  exact halfLatticePhase_norm n (t / T) j

@[simp] theorem scaledInterpolatedClockAt_norm
    {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ) :
    ‖scaledInterpolatedClockAt T n θ t‖ = 1 := by
  have hsq :=
    finiteIndexPhasedWeightKet_norm_sq
      (interpolatedWeight n θ) (scaledPhase T n t)
      (interpolatedWeight_nonneg n hθ0 hθ1)
      (scaledPhase_norm hT n t)
  rw [interpolatedWeight_sum hn] at hsq
  change
    ‖finiteIndexPhasedWeightKet
      (interpolatedWeight n θ) (scaledPhase T n t)‖ = 1
  nlinarith
    [norm_nonneg
      (finiteIndexPhasedWeightKet
        (interpolatedWeight n θ) (scaledPhase T n t))]

theorem scaled_full_weighted_phase_sum
    {T : ℝ} (hT : 0 < T) (n : ℕ) (t : ℝ) :
    ∑ j : Fin (n + 1),
        (fullWeight n j : ℂ) * scaledPhase T n t j =
      scaledFullAmplitude T n t := by
  simp_rw [scaledPhase_eq hT]
  exact full_weighted_phase_sum n (t / T)

theorem scaledInterpolatedClock_survivalAmplitude
    {T : ℝ} (hT : 0 < T) (n : ℕ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ) :
    inner ℂ (interpolatedClock n θ)
        (scaledInterpolatedClockAt T n θ t) =
      scaledInterpolatedAmplitude T n θ t := by
  rw [interpolatedClock, scaledInterpolatedClockAt,
    finiteIndexWeightKet_inner_phasedWeightKet
      _ _ (interpolatedWeight_nonneg n hθ0 hθ1)]
  simp_rw [scaledPhase_eq hT]
  exact interpolated_weighted_phase_sum n θ (t / T)

theorem scaled_parity_weighted_phase_sum
    {T : ℝ} (hT : 0 < T) (n : ℕ) (t : ℝ) :
    ∑ j : Fin (n + 1),
        (parityWeight n j : ℂ) * scaledPhase T n t j =
      scaledParityAmplitude T n t := by
  simp_rw [scaledPhase_eq hT]
  exact parity_weighted_phase_sum n (t / T)

theorem scaled_energyMoment_eq
    {T : ℝ} {n k : ℕ} (hk : k < n) :
    ∑ j : Fin (n + 1),
        parityWeight n j * scaledEnergy T n j ^ k =
      ∑ j : Fin (n + 1),
        fullWeight n j * scaledEnergy T n j ^ k := by
  simp only [scaledEnergy, div_pow]
  rw [show
      (∑ j : Fin (n + 1),
        parityWeight n j *
          (halfLatticeEnergy n j ^ k / T ^ k)) =
      (∑ j : Fin (n + 1),
        parityWeight n j * halfLatticeEnergy n j ^ k) / T ^ k by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  rw [show
      (∑ j : Fin (n + 1),
        fullWeight n j *
          (halfLatticeEnergy n j ^ k / T ^ k)) =
      (∑ j : Fin (n + 1),
        fullWeight n j * halfLatticeEnergy n j ^ k) / T ^ k by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  rw [parity_energyMoment_eq_full hk]

theorem scaled_interpolated_energyMoment_eq
    {T : ℝ} {n k : ℕ} (hk : k < n) (θ : ℝ) :
    ∑ j : Fin (n + 1),
        interpolatedWeight n θ j * scaledEnergy T n j ^ k =
      ∑ j : Fin (n + 1),
        fullWeight n j * scaledEnergy T n j ^ k := by
  simp only [scaledEnergy, div_pow]
  rw [show
      (∑ j : Fin (n + 1),
        interpolatedWeight n θ j *
          (halfLatticeEnergy n j ^ k / T ^ k)) =
      (∑ j : Fin (n + 1),
        interpolatedWeight n θ j *
          halfLatticeEnergy n j ^ k) / T ^ k by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  rw [show
      (∑ j : Fin (n + 1),
        fullWeight n j *
          (halfLatticeEnergy n j ^ k / T ^ k)) =
      (∑ j : Fin (n + 1),
        fullWeight n j * halfLatticeEnergy n j ^ k) / T ^ k by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    ring]
  rw [interpolated_energyMoment_eq_full hk]

@[simp] theorem scaledFullProbability_target
    {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n) :
    scaledFullProbability T n T = 0 := by
  rw [scaledFullProbability, div_self hT.ne', fullProbability_one hn]

@[simp] theorem scaledParityProbability_target
    {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n) :
    scaledParityProbability T n T = 1 := by
  rw [scaledParityProbability, div_self hT.ne',
    parityProbability_one hn]

@[simp] theorem scaledInterpolatedProbability_target
    {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    {θ : ℝ} (hθ0 : 0 ≤ θ) :
    scaledInterpolatedProbability T n θ T = θ ^ 2 := by
  rw [scaledInterpolatedProbability, div_self hT.ne',
    interpolatedProbability_target hn hθ0]

/--
Universal positive-time law.  It quantifies simultaneously over target
time, complete observation horizon, precision, and number of exactly
matched energy moments.
-/
theorem universal_positive_energy_forecasting_instability
    (m : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ,
      m < n ∧
      (∀ k : ℕ, k ≤ m →
        ∑ j : Fin (n + 1),
            parityWeight n j * scaledEnergy T n j ^ k =
          ∑ j : Fin (n + 1),
            fullWeight n j * scaledEnergy T n j ^ k) ∧
      (∀ t : ℝ, |t| ≤ H →
        ‖scaledParityAmplitude T n t -
          scaledFullAmplitude T n t‖ < ε) ∧
      (∀ t : ℝ, |t| ≤ H →
        |scaledParityProbability T n t -
          scaledFullProbability T n t| < 2 * ε) ∧
      scaledParityProbability T n T = 1 ∧
      scaledFullProbability T n T = 0 := by
  have hρ0 : 0 ≤ H / T := div_nonneg hH0 hT.le
  have hρ1 : H / T < 1 := (div_lt_one hT).2 hHT
  obtain ⟨n, hmn, _hmom, hamp, _hparity, _hfull⟩ :=
    exists_every_order_every_strict_window m hρ0 hρ1 hε
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le m) hmn
  refine ⟨n, hmn, ?_, ?_, ?_, scaledParityProbability_target hT hn,
    scaledFullProbability_target hT hn⟩
  · intro k hk
    exact scaled_energyMoment_eq (lt_of_le_of_lt hk hmn)
  · intro t ht
    apply hamp
    rw [abs_div, abs_of_pos hT]
    exact (div_le_div_iff_of_pos_right hT).2 ht
  · intro t ht
    have ha : ‖scaledParityAmplitude T n t -
        scaledFullAmplitude T n t‖ < ε := by
      apply hamp
      rw [abs_div, abs_of_pos hT]
      exact (div_le_div_iff_of_pos_right hT).2 ht
    have hp :=
      probability_difference_le_amplitude hn (t / T)
    change
      ‖parityAmplitude n (t / T) -
        fullAmplitude n (t / T)‖ < ε at ha
    change
      |parityProbability n (t / T) -
        fullProbability n (t / T)| < 2 * ε
    exact lt_of_le_of_lt hp (by nlinarith)

/--
Strongest universal form: the same finite positive Hamiltonian and one
baseline record are compatible, at the target time, with every return
probability in the entire interval `[0,1]`, while matching any prescribed
finite energy-moment jet.
-/
theorem universal_every_future_return_probability
    (m : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ,
      m < n ∧
      ∀ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 →
        (∀ k : ℕ, k ≤ m →
          ∑ j : Fin (n + 1),
              interpolatedWeight n (Real.sqrt p) j *
                scaledEnergy T n j ^ k =
            ∑ j : Fin (n + 1),
              fullWeight n j * scaledEnergy T n j ^ k) ∧
        (∀ t : ℝ, |t| ≤ H →
          ‖scaledInterpolatedAmplitude T n (Real.sqrt p) t -
            scaledFullAmplitude T n t‖ < ε) ∧
        (∀ t : ℝ, |t| ≤ H →
          |scaledInterpolatedProbability T n (Real.sqrt p) t -
            scaledFullProbability T n t| < 2 * ε) ∧
        scaledInterpolatedProbability T n (Real.sqrt p) T = p := by
  have hρ0 : 0 ≤ H / T := div_nonneg hH0 hT.le
  have hρ1 : H / T < 1 := (div_lt_one hT).2 hHT
  obtain ⟨n, hmn, hall⟩ :=
    exists_every_future_probability_every_strict_window
      m hρ0 hρ1 hε
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le m) hmn
  refine ⟨n, hmn, ?_⟩
  intro p hp
  obtain ⟨_hmom, hamp, hprob, _htarget⟩ := hall p hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    exact scaled_interpolated_energyMoment_eq
      (lt_of_le_of_lt hk hmn) _
  · intro t ht
    apply hamp
    rw [abs_div, abs_of_pos hT]
    exact (div_le_div_iff_of_pos_right hT).2 ht
  · intro t ht
    apply hprob
    rw [abs_div, abs_of_pos hT]
    exact (div_le_div_iff_of_pos_right hT).2 ht
  · rw [scaledInterpolatedProbability_target
      hT hn (Real.sqrt_nonneg p), Real.sq_sqrt hp.1]

/--
Headline common-record law: one return-probability history is uniformly
compatible with every exact future value in `[0,1]`.
-/
theorem one_record_compatible_with_every_future_probability
    (m : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ,
      m < n ∧
      ∀ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 →
        (∀ k : ℕ, k ≤ m →
          ∑ j : Fin (n + 1),
              interpolatedWeight n (Real.sqrt p) j *
                scaledEnergy T n j ^ k =
            ∑ j : Fin (n + 1),
              fullWeight n j * scaledEnergy T n j ^ k) ∧
        (∀ t : ℝ, |t| ≤ H →
          |scaledInterpolatedProbability T n (Real.sqrt p) t -
            scaledFullProbability T n t| < δ) ∧
        scaledInterpolatedProbability T n (Real.sqrt p) T = p := by
  have hhalf : 0 < δ / 2 := by linarith
  obtain ⟨n, hmn, hall⟩ :=
    universal_every_future_return_probability
      m T H hT hH0 hHT hhalf
  refine ⟨n, hmn, ?_⟩
  intro p hp
  obtain ⟨hmom, _hamp, hprob, htarget⟩ := hall p hp
  refine ⟨hmom, ?_, htarget⟩
  intro t ht
  have := hprob t ht
  have heq : 2 * (δ / 2) = δ := by ring
  simpa only [heq] using this

/-- One finite-precision probability record shared by both models. -/
def scaledMidpointProbability
    (T : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (scaledParityProbability T n t +
    scaledFullProbability T n t) / 2

/--
One observed record, at any positive error radius, is compatible with both
terminal extremes while the models match any prescribed finite moment jet.
-/
theorem one_record_allows_opposite_exact_futures
    (m : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ,
      m < n ∧
      (∀ k : ℕ, k ≤ m →
        ∑ j : Fin (n + 1),
            parityWeight n j * scaledEnergy T n j ^ k =
          ∑ j : Fin (n + 1),
            fullWeight n j * scaledEnergy T n j ^ k) ∧
      (∀ t : ℝ, |t| ≤ H →
        |scaledParityProbability T n t -
          scaledMidpointProbability T n t| < δ) ∧
      (∀ t : ℝ, |t| ≤ H →
        |scaledFullProbability T n t -
          scaledMidpointProbability T n t| < δ) ∧
      scaledParityProbability T n T = 1 ∧
      scaledFullProbability T n T = 0 := by
  obtain ⟨n, hmn, hmom, _hamp, hprob, hparity, hfull⟩ :=
    universal_positive_energy_forecasting_instability
      m T H hT hH0 hHT hδ
  refine ⟨n, hmn, hmom, ?_, ?_, hparity, hfull⟩
  · intro t ht
    have hp := hprob t ht
    rw [scaledMidpointProbability]
    rw [show
        scaledParityProbability T n t -
            (scaledParityProbability T n t +
              scaledFullProbability T n t) / 2 =
          (scaledParityProbability T n t -
            scaledFullProbability T n t) / 2 by ring,
      abs_div]
    norm_num
    linarith
  · intro t ht
    have hp := hprob t ht
    rw [scaledMidpointProbability]
    rw [show
        scaledFullProbability T n t -
            (scaledParityProbability T n t +
              scaledFullProbability T n t) / 2 =
          -(scaledParityProbability T n t -
            scaledFullProbability T n t) / 2 by ring,
      abs_div, abs_neg]
    norm_num
    linarith

/--
Algorithm-independent minimax consequence: every forecaster receiving the
common record incurs terminal absolute error at least one half on one of
the two compatible clocks.
-/
theorem every_forecaster_has_half_error
    (forecast : (ℝ → ℝ) → ℝ)
    (m : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ,
      m < n ∧
      (∀ t : ℝ, |t| ≤ H →
        |scaledParityProbability T n t -
          scaledMidpointProbability T n t| < δ) ∧
      (∀ t : ℝ, |t| ≤ H →
        |scaledFullProbability T n t -
          scaledMidpointProbability T n t| < δ) ∧
      scaledParityProbability T n T = 1 ∧
      scaledFullProbability T n T = 0 ∧
      ((1 : ℝ) / 2 ≤
          |forecast (scaledMidpointProbability T n) - 1| ∨
        (1 : ℝ) / 2 ≤
          |forecast (scaledMidpointProbability T n) - 0|) := by
  obtain ⟨n, hmn, _hmom, hparityRecord, hfullRecord,
      hparity, hfull⟩ :=
    one_record_allows_opposite_exact_futures
      m T H hT hH0 hHT hδ
  refine ⟨n, hmn, hparityRecord, hfullRecord,
    hparity, hfull, ?_⟩
  let y := forecast (scaledMidpointProbability T n)
  by_cases hy : y ≤ (1 : ℝ) / 2
  · left
    have hneg := neg_le_abs (y - 1)
    change (1 : ℝ) / 2 ≤ |y - 1|
    nlinarith
  · right
    have hpos := le_abs_self y
    change (1 : ℝ) / 2 ≤ |y - 0|
    simp only [sub_zero]
    nlinarith

/-! ## Fixed-preparation and fixed-return-projector realization -/

/-- One fixed initial state for every member of the Hamiltonian family. -/
def fixedClock (n : ℕ) : ClockSpace n :=
  EuclideanSpace.basisFun (Fin (n + 1)) ℂ 0

@[simp] theorem fixedClock_norm (n : ℕ) :
    ‖fixedClock n‖ = 1 := by
  simp [fixedClock]

/--
Every interpolated clock state is the unitary image of the same fixed clock.
The construction extends the singleton orthonormal family to a full basis.
-/
theorem exists_unitary_fixedClock_to_interpolatedClock
    {n : ℕ} (hn : 0 < n) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n,
      U (fixedClock n) = interpolatedClock n θ := by
  let v : Fin (n + 1) → ClockSpace n :=
    fun _ => interpolatedClock n θ
  let s : Set (Fin (n + 1)) := {0}
  have hv : Orthonormal ℂ (s.restrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    simp only [Set.restrict_apply, v]
    exact interpolatedClock_norm hn hθ0 hθ1
  have hcard :
      Module.finrank ℂ (ClockSpace n) =
        Fintype.card (Fin (n + 1)) := by
    simp [ClockSpace]
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq hcard
  let U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n :=
    (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).equiv b
      (Equiv.refl (Fin (n + 1)))
  refine ⟨U, ?_⟩
  change
    ((EuclideanSpace.basisFun (Fin (n + 1)) ℂ).equiv b
      (Equiv.refl (Fin (n + 1))))
        (EuclideanSpace.basisFun (Fin (n + 1)) ℂ 0) =
      interpolatedClock n θ
  rw [OrthonormalBasis.equiv_apply_basis]
  exact hb 0 (by simp [s])

/--
Move preparation uncertainty into the generator: every member is a unitary
conjugate of the same diagonal Hamiltonian.
-/
def fixedProtocolHamiltonian
    (T : ℝ) (n : ℕ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n) :
    ClockSpace n →L[ℂ] ClockSpace n :=
  (U.symm : ClockSpace n →L[ℂ] ClockSpace n) ∘L
    scaledClockHamiltonian T n ∘L
      (U : ClockSpace n →L[ℂ] ClockSpace n)

theorem fixedProtocolHamiltonian_selfAdjoint
    (T : ℝ) (n : ℕ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n) :
    ContinuousLinearMap.adjoint
        (fixedProtocolHamiltonian T n U) =
      fixedProtocolHamiltonian T n U := by
  simp only [fixedProtocolHamiltonian,
    ContinuousLinearMap.adjoint_comp]
  rw [LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.adjoint_eq_symm,
    scaledClockHamiltonian_selfAdjoint]
  rw [LinearIsometryEquiv.symm_symm]
  rw [ContinuousLinearMap.comp_assoc]

/-- Exact unitary intertwining, hence a common spectrum for the family. -/
@[simp] theorem fixedProtocolHamiltonian_intertwines
    (T : ℝ) (n : ℕ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n)
    (x : ClockSpace n) :
    U (fixedProtocolHamiltonian T n U x) =
      scaledClockHamiltonian T n (U x) := by
  simp [fixedProtocolHamiltonian]

theorem finiteIndexDiagonalHamiltonian_pow_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℝ) (k : ℕ)
    (x : FiniteIndexClockSpace ι) (i : ι) :
    ((finiteIndexDiagonalHamiltonian energy) ^ k) x i =
      ((energy i : ℂ) ^ k) * x i := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_apply_eq_comp,
        ih, finiteIndexDiagonalHamiltonian_apply]
      ring

theorem finiteIndexWeightKet_diagonal_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (k : ℕ) :
    inner ℂ (finiteIndexWeightKet weight)
        (((finiteIndexDiagonalHamiltonian energy) ^ k)
          (finiteIndexWeightKet weight)) =
      (∑ i : ι, weight i * energy i ^ k : ℝ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  push_cast
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← ContinuousLinearMap.coe_pow']
  change
    (((finiteIndexDiagonalHamiltonian energy) ^ k)
        (finiteIndexWeightKet weight)) i *
        star (finiteIndexWeightKet weight i) =
      (weight i : ℂ) * (energy i : ℂ) ^ k
  rw [finiteIndexDiagonalHamiltonian_pow_apply]
  simp only [finiteIndexWeightKet_apply]
  rw [Complex.star_def, Complex.conj_ofReal, mul_assoc]
  rw [show
      (Real.sqrt (weight i) : ℂ) *
          (Real.sqrt (weight i) : ℂ) =
        (weight i : ℂ) by
      norm_cast
      simpa [pow_two] using Real.sq_sqrt (hw i)]
  ring

theorem fixedProtocolHamiltonian_pow_intertwines
    (T : ℝ) (n k : ℕ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n)
    (x : ClockSpace n) :
    U (((fixedProtocolHamiltonian T n U) ^ k) x) =
      ((scaledClockHamiltonian T n) ^ k) (U x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_apply_eq_comp, ih,
        fixedProtocolHamiltonian_intertwines,
        pow_succ, mul_apply_eq_comp]

theorem fixedProtocol_energyMoment
    (T : ℝ) (n k : ℕ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n}
    (hU : U (fixedClock n) = interpolatedClock n θ) :
    inner ℂ (fixedClock n)
        (((fixedProtocolHamiltonian T n U) ^ k)
          (fixedClock n)) =
      (∑ j : Fin (n + 1),
        interpolatedWeight n θ j *
          angularEnergy T n j ^ k : ℝ) := by
  calc
    inner ℂ (fixedClock n)
        (((fixedProtocolHamiltonian T n U) ^ k)
          (fixedClock n)) =
        inner ℂ (U (fixedClock n))
          (U (((fixedProtocolHamiltonian T n U) ^ k)
            (fixedClock n))) := by
              symm
              exact U.inner_map_map _ _
    _ = inner ℂ (interpolatedClock n θ)
          (((scaledClockHamiltonian T n) ^ k)
            (interpolatedClock n θ)) := by
              rw [fixedProtocolHamiltonian_pow_intertwines,
                hU]
    _ = (∑ j : Fin (n + 1),
          interpolatedWeight n θ j *
            angularEnergy T n j ^ k : ℝ) := by
      exact finiteIndexWeightKet_diagonal_moment
        (angularEnergy T n) (interpolatedWeight n θ)
        (interpolatedWeight_nonneg n hθ0 hθ1) k

theorem angular_interpolated_energyMoment_eq_full
    {T : ℝ} {n k : ℕ} (hk : k < n) (θ : ℝ) :
    ∑ j : Fin (n + 1),
        interpolatedWeight n θ j *
          angularEnergy T n j ^ k =
      ∑ j : Fin (n + 1),
        fullWeight n j * angularEnergy T n j ^ k := by
  simp_rw [show ∀ j : Fin (n + 1),
      angularEnergy T n j ^ k =
        (2 * Real.pi) ^ k *
          scaledEnergy T n j ^ k by
    intro j
    rw [angularEnergy, mul_pow]]
  calc
    (∑ j : Fin (n + 1),
        interpolatedWeight n θ j *
          ((2 * Real.pi) ^ k *
            scaledEnergy T n j ^ k)) =
        (2 * Real.pi) ^ k *
          ∑ j : Fin (n + 1),
            interpolatedWeight n θ j *
              scaledEnergy T n j ^ k := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _hj
                ring
    _ = (2 * Real.pi) ^ k *
          ∑ j : Fin (n + 1),
            fullWeight n j *
              scaledEnergy T n j ^ k := by
              rw [scaled_interpolated_energyMoment_eq hk]
    _ = ∑ j : Fin (n + 1),
        fullWeight n j *
          ((2 * Real.pi) ^ k *
            scaledEnergy T n j ^ k) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring

theorem fixedProtocol_energyMoment_eq_full
    {T : ℝ} {n k : ℕ} (hk : k < n) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n}
    (hU : U (fixedClock n) = interpolatedClock n θ) :
    inner ℂ (fixedClock n)
        (((fixedProtocolHamiltonian T n U) ^ k)
          (fixedClock n)) =
      (∑ j : Fin (n + 1),
        fullWeight n j * angularEnergy T n j ^ k : ℝ) := by
  rw [fixedProtocol_energyMoment
    T n k hθ0 hθ1 hU]
  norm_cast
  exact angular_interpolated_energyMoment_eq_full hk θ

/-- Fixed-state evolution transported back from the diagonal realization. -/
def fixedProtocolClockAt
    (T : ℝ) (n : ℕ) (θ t : ℝ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n) :
    ClockSpace n :=
  U.symm (scaledInterpolatedClockAt T n θ t)

@[simp] theorem fixedProtocolClockAt_norm
    {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n) :
    ‖fixedProtocolClockAt T n θ t U‖ = 1 := by
  rw [fixedProtocolClockAt, LinearIsometryEquiv.norm_map,
    scaledInterpolatedClockAt_norm hT hn hθ0 hθ1]

theorem fixedProtocolClock_survivalAmplitude
    {T : ℝ} (hT : 0 < T) (n : ℕ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ)
    {U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n}
    (hU : U (fixedClock n) = interpolatedClock n θ) :
    inner ℂ (fixedClock n)
        (fixedProtocolClockAt T n θ t U) =
      scaledInterpolatedAmplitude T n θ t := by
  calc
    inner ℂ (fixedClock n)
        (fixedProtocolClockAt T n θ t U) =
        inner ℂ (U (fixedClock n))
          (U (fixedProtocolClockAt T n θ t U)) := by
            symm
            exact U.inner_map_map _ _
    _ = inner ℂ (interpolatedClock n θ)
          (scaledInterpolatedClockAt T n θ t) := by
            rw [hU]
            simp [fixedProtocolClockAt]
    _ = scaledInterpolatedAmplitude T n θ t :=
      scaledInterpolatedClock_survivalAmplitude
        hT n hθ0 hθ1 t

/-- Return probability for the one fixed preparation and projector. -/
def fixedProtocolProbability
    (T : ℝ) (n : ℕ) (θ t : ℝ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n) : ℝ :=
  ‖inner ℂ (fixedClock n)
      (fixedProtocolClockAt T n θ t U)‖ ^ 2

theorem fixedProtocolProbability_eq
    {T : ℝ} (hT : 0 < T) (n : ℕ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ)
    {U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n}
    (hU : U (fixedClock n) = interpolatedClock n θ) :
    fixedProtocolProbability T n θ t U =
      scaledInterpolatedProbability T n θ t := by
  rw [fixedProtocolProbability,
    fixedProtocolClock_survivalAmplitude
      hT n hθ0 hθ1 t hU]
  rfl

/--
Fixed-protocol universal law. One fixed normalized initial state and its
fixed return projector are compatible with every terminal probability.
Only the Hamiltonian varies, and every Hamiltonian is unitarily equivalent
to the same nonnegative diagonal Hamiltonian. The corresponding spectral
weights retain every prescribed finite moment match.
-/
theorem one_fixed_return_protocol_every_future_probability
    (m : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ,
      m < n ∧
      ‖fixedClock n‖ = 1 ∧
      ∀ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 →
        ∃ U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n,
          U (fixedClock n) =
              interpolatedClock n (Real.sqrt p) ∧
          (∀ k : ℕ, k ≤ m →
            inner ℂ (fixedClock n)
                (((fixedProtocolHamiltonian T n U) ^ k)
                  (fixedClock n)) =
              (∑ j : Fin (n + 1),
                fullWeight n j *
                  angularEnergy T n j ^ k : ℝ)) ∧
          ContinuousLinearMap.adjoint
              (fixedProtocolHamiltonian T n U) =
            fixedProtocolHamiltonian T n U ∧
          (∀ x : ClockSpace n,
            U (fixedProtocolHamiltonian T n U x) =
              scaledClockHamiltonian T n (U x)) ∧
          (∀ t : ℝ, |t| ≤ H →
            |fixedProtocolProbability
                T n (Real.sqrt p) t U -
              scaledFullProbability T n t| < δ) ∧
          fixedProtocolProbability
              T n (Real.sqrt p) T U = p := by
  obtain ⟨n, hmn, hall⟩ :=
    one_record_compatible_with_every_future_probability
      m T H hT hH0 hHT hδ
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le m) hmn
  refine ⟨n, hmn, fixedClock_norm n, ?_⟩
  intro p hp
  obtain ⟨_hmom, hwindow, htarget⟩ := hall p hp
  have hθ0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hθ1 : Real.sqrt p ≤ 1 :=
    Real.sqrt_le_one.mpr hp.2
  obtain ⟨U, hU⟩ :=
    exists_unitary_fixedClock_to_interpolatedClock
      hn hθ0 hθ1
  refine ⟨U, hU, ?_,
    fixedProtocolHamiltonian_selfAdjoint T n U,
    fixedProtocolHamiltonian_intertwines T n U, ?_, ?_⟩
  · intro k hk
    exact fixedProtocol_energyMoment_eq_full
      (lt_of_le_of_lt hk hmn) hθ0 hθ1 hU
  · intro t ht
    rw [fixedProtocolProbability_eq
      hT n hθ0 hθ1 t hU]
    exact hwindow t ht
  · rw [fixedProtocolProbability_eq
      hT n hθ0 hθ1 T hU]
    exact htarget

end RHTower.ParityForecast
