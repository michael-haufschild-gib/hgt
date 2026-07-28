import GaloisForLFunctions.RHTower.FiniteMixedSpikeRealization
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Finite-window instability of quantum recurrence

Two explicit finite positive-energy clocks evolve under one self-adjoint
diagonal Hamiltonian.  One has an integer binomial spectrum.  The second
splits every binomial weight equally between an integer energy and its
half-integer translate.  At one period the first clock returns exactly and
the second is orthogonal.  Nevertheless their complete survival amplitudes
are uniformly arbitrarily close on the preceding half-period as the finite
dimension grows.
-/

open scoped BigOperators InnerProductSpace
open Complex

noncomputable section

namespace RHTower.FiniteWindow

/-- Shared finite spectral index: integer and half-integer copies. -/
abbrev ClockIndex (N : ℕ) :=
  Sum (Fin (N + 1)) (Fin (N + 1))

/-- Fair binomial probability weight. -/
def binomialWeight (N : ℕ) (k : Fin (N + 1)) : ℝ :=
  (N.choose k : ℝ) / 2 ^ N

/-- Returning clock: all mass lies on integer energies. -/
def returningWeight (N : ℕ) : ClockIndex N → ℝ
  | Sum.inl k => binomialWeight N k
  | Sum.inr _ => 0

/-- Orthogonal clock: each binomial weight is split across a half-step. -/
def orthogonalWeight (N : ℕ) : ClockIndex N → ℝ
  | Sum.inl k => binomialWeight N k / 2
  | Sum.inr k => binomialWeight N k / 2

/-- Shared nonnegative energy list. -/
def clockEnergy (N : ℕ) : ClockIndex N → ℝ
  | Sum.inl k => k
  | Sum.inr k => k + 1 / 2

theorem binomialWeight_nonneg (N : ℕ) (k : Fin (N + 1)) :
    0 ≤ binomialWeight N k :=
  div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

theorem binomialWeight_sum (N : ℕ) :
    ∑ k, binomialWeight N k = 1 := by
  have hfin :
      (∑ k : Fin (N + 1), (N.choose k : ℝ)) =
        ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) := by
    exact Fin.sum_univ_eq_sum_range
      (fun k => (N.choose k : ℝ)) (N + 1)
  simp only [binomialWeight]
  rw [← Finset.sum_div, hfin]
  have h := add_pow (1 : ℝ) 1 N
  norm_num at h
  rw [← h]
  field_simp

theorem returningWeight_nonneg (N : ℕ) (i : ClockIndex N) :
    0 ≤ returningWeight N i := by
  cases i with
  | inl k => exact binomialWeight_nonneg N k
  | inr _ => exact le_rfl

theorem orthogonalWeight_nonneg (N : ℕ) (i : ClockIndex N) :
    0 ≤ orthogonalWeight N i := by
  cases i with
  | inl k =>
      exact div_nonneg (binomialWeight_nonneg N k) (by norm_num)
  | inr k =>
      exact div_nonneg (binomialWeight_nonneg N k) (by norm_num)

theorem returningWeight_sum (N : ℕ) :
    ∑ i, returningWeight N i = 1 := by
  rw [Fintype.sum_sum_type]
  simp [returningWeight, binomialWeight_sum]

theorem orthogonalWeight_sum (N : ℕ) :
    ∑ i, orthogonalWeight N i = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [orthogonalWeight]
  have hhalf :
      (∑ k : Fin (N + 1), binomialWeight N k / 2) = 1 / 2 := by
    calc
      (∑ k : Fin (N + 1), binomialWeight N k / 2) =
          (∑ k : Fin (N + 1), binomialWeight N k) / 2 := by
        exact
          (Finset.sum_div Finset.univ (binomialWeight N) 2).symm
      _ = 1 / 2 := by rw [binomialWeight_sum]
  rw [hhalf]
  norm_num

theorem clockEnergy_nonneg (N : ℕ) (i : ClockIndex N) :
    0 ≤ clockEnergy N i := by
  cases i with
  | inl _ => exact Nat.cast_nonneg _
  | inr _ =>
      dsimp [clockEnergy]
      positivity

/-- Exact return-clock amplitude. -/
def returningAmplitude (N : ℕ) (t : ℝ) : ℂ :=
  (((1 : ℂ) +
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I)) / 2) ^ N

/-- Exact orthogonal-clock amplitude. -/
def orthogonalAmplitude (N : ℕ) (t : ℝ) : ℂ :=
  returningAmplitude N t *
    (((1 : ℂ) +
      Complex.exp (((Real.pi * t : ℝ) : ℂ) * I)) / 2)

/-- Survival amplitude of one equally weighted two-level spin. -/
def singleSpinAmplitude (frequency t : ℝ) : ℂ :=
  ((1 : ℂ) +
    Complex.exp (((2 * Real.pi * frequency * t : ℝ) : ℂ) * I)) / 2

/--
Exact noninteracting-spin factorization: `N` identical unit-frequency
two-level factors, with the orthogonal clock carrying one additional
half-frequency factor.
-/
theorem amplitudes_factor_as_noninteracting_spins (N : ℕ) (t : ℝ) :
    returningAmplitude N t = singleSpinAmplitude 1 t ^ N ∧
    orthogonalAmplitude N t =
      singleSpinAmplitude 1 t ^ N * singleSpinAmplitude (1 / 2) t := by
  have hreturn :
      returningAmplitude N t = singleSpinAmplitude 1 t ^ N := by
    simp [returningAmplitude, singleSpinAmplitude]
  refine ⟨hreturn, ?_⟩
  · unfold orthogonalAmplitude singleSpinAmplitude
    rw [hreturn]
    congr 1
    congr 2
    push_cast
    ring_nf

@[simp] theorem returningAmplitude_zero (N : ℕ) :
    returningAmplitude N 0 = 1 := by
  simp [returningAmplitude]

@[simp] theorem orthogonalAmplitude_zero (N : ℕ) :
    orthogonalAmplitude N 0 = 1 := by
  simp [orthogonalAmplitude]

@[simp] theorem returningAmplitude_one (N : ℕ) :
    returningAmplitude N 1 = 1 := by
  rw [returningAmplitude]
  norm_num

@[simp] theorem orthogonalAmplitude_one (N : ℕ) :
    orthogonalAmplitude N 1 = 0 := by
  rw [orthogonalAmplitude, returningAmplitude_one]
  norm_num

theorem binomialWeight_generating (N : ℕ) (z : ℂ) :
    ∑ k : Fin (N + 1),
        (binomialWeight N k : ℂ) * z ^ (k : ℕ) =
      ((1 + z) / 2) ^ N := by
  have hfin :
      (∑ k : Fin (N + 1),
        (N.choose k : ℂ) * z ^ (k : ℕ)) =
      ∑ k ∈ Finset.range (N + 1),
        (N.choose k : ℂ) * z ^ k := by
    exact Fin.sum_univ_eq_sum_range
      (fun k => (N.choose k : ℂ) * z ^ k) (N + 1)
  simp only [binomialWeight]
  push_cast
  rw [show
      (∑ k : Fin (N + 1),
        ((N.choose k : ℂ) / (2 : ℂ) ^ N) * z ^ (k : ℕ)) =
      (∑ k : Fin (N + 1),
        (N.choose k : ℂ) * z ^ (k : ℕ)) / (2 : ℂ) ^ N by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _hk
    ring]
  rw [hfin]
  have h := add_pow z (1 : ℂ) N
  simp only [one_pow, mul_one] at h
  have hsum :
      (∑ k ∈ Finset.range (N + 1),
        (N.choose k : ℂ) * z ^ k) = (1 + z) ^ N := by
    simpa [mul_comm, add_comm] using h.symm
  rw [hsum, div_pow]

/-- Coordinate phase generated by the shared real energy list. -/
def clockPhase (N : ℕ) (t : ℝ) (i : ClockIndex N) : ℂ :=
  Complex.exp
    (((2 * Real.pi * clockEnergy N i * t : ℝ) : ℂ) * I)

theorem clockPhase_norm (N : ℕ) (t : ℝ) (i : ClockIndex N) :
    ‖clockPhase N t i‖ = 1 := by
  rw [clockPhase, Complex.norm_exp]
  simp [Complex.mul_re]

private theorem integer_clockPhase
    (N : ℕ) (t : ℝ) (k : Fin (N + 1)) :
    clockPhase N t (Sum.inl k) =
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I) ^ (k : ℕ) := by
  rw [clockPhase, clockEnergy, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem halfInteger_clockPhase
    (N : ℕ) (t : ℝ) (k : Fin (N + 1)) :
    clockPhase N t (Sum.inr k) =
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I) ^ (k : ℕ) *
        Complex.exp (((Real.pi * t : ℝ) : ℂ) * I) := by
  rw [clockPhase, clockEnergy, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem returning_weighted_phase_sum (N : ℕ) (t : ℝ) :
    ∑ i : ClockIndex N,
        (returningWeight N i : ℂ) * clockPhase N t i =
      returningAmplitude N t := by
  rw [Fintype.sum_sum_type]
  simp only [returningWeight, ofReal_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  simp_rw [integer_clockPhase]
  exact binomialWeight_generating N _

theorem orthogonal_weighted_phase_sum (N : ℕ) (t : ℝ) :
    ∑ i : ClockIndex N,
        (orthogonalWeight N i : ℂ) * clockPhase N t i =
      orthogonalAmplitude N t := by
  rw [Fintype.sum_sum_type]
  simp only [orthogonalWeight]
  simp_rw [integer_clockPhase, halfInteger_clockPhase]
  let z := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I)
  let h := Complex.exp (((Real.pi * t : ℝ) : ℂ) * I)
  have hleft :
      (∑ k : Fin (N + 1),
        ((binomialWeight N k / 2 : ℝ) : ℂ) * z ^ (k : ℕ)) =
        returningAmplitude N t / 2 := by
    calc
      (∑ k : Fin (N + 1),
          ((binomialWeight N k / 2 : ℝ) : ℂ) * z ^ (k : ℕ)) =
          ∑ k : Fin (N + 1),
            ((binomialWeight N k : ℂ) * z ^ (k : ℕ)) / 2 := by
        apply Finset.sum_congr rfl
        intro k _hk
        push_cast
        ring
      _ = (∑ k : Fin (N + 1),
          (binomialWeight N k : ℂ) * z ^ (k : ℕ)) / 2 := by
        exact
          (Finset.sum_div Finset.univ
            (fun k : Fin (N + 1) =>
              (binomialWeight N k : ℂ) * z ^ (k : ℕ)) 2).symm
      _ = returningAmplitude N t / 2 := by
        rw [binomialWeight_generating]
        rfl
  have hright :
      (∑ k : Fin (N + 1),
        ((binomialWeight N k / 2 : ℝ) : ℂ) *
          (z ^ (k : ℕ) * h)) =
        returningAmplitude N t * h / 2 := by
    calc
      (∑ k : Fin (N + 1),
          ((binomialWeight N k / 2 : ℝ) : ℂ) *
            (z ^ (k : ℕ) * h)) =
          (∑ k : Fin (N + 1),
            ((binomialWeight N k / 2 : ℝ) : ℂ) *
              z ^ (k : ℕ)) * h := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ = returningAmplitude N t * h / 2 := by rw [hleft]; ring
  change
    (∑ k : Fin (N + 1),
      ((binomialWeight N k / 2 : ℝ) : ℂ) * z ^ (k : ℕ)) +
    (∑ k : Fin (N + 1),
      ((binomialWeight N k / 2 : ℝ) : ℂ) *
        (z ^ (k : ℕ) * h)) =
      orthogonalAmplitude N t
  rw [hleft, hright]
  unfold orthogonalAmplitude h
  ring

/-! ## Uniform finite-window instability -/

private theorem pow_mul_one_sub_le_inv_succ
    (m : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    y ^ m * (1 - y) ≤ 1 / (m + 1 : ℕ) := by
  let S : ℝ := ∑ k ∈ Finset.range (m + 1), y ^ k
  have hterm :
      ∀ k ∈ Finset.range (m + 1), y ^ m ≤ y ^ k := by
    intro k hk
    exact pow_le_pow_of_le_one hy0 hy1
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hsum : (m + 1 : ℝ) * y ^ m ≤ S := by
    have h := Finset.sum_le_sum hterm
    simpa [S] using h
  have hone : S * (1 - y) ≤ 1 := by
    rw [show S * (1 - y) = 1 - y ^ (m + 1) by
      simpa [S] using geom_sum_mul_neg y (m + 1)]
    nlinarith [pow_nonneg hy0 (m + 1)]
  have hmul :
      ((m + 1 : ℝ) * y ^ m) * (1 - y) ≤ S * (1 - y) :=
    mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hy1)
  have htotal :
      (m + 1 : ℝ) * (y ^ m * (1 - y)) ≤ 1 := by
    calc
      (m + 1 : ℝ) * (y ^ m * (1 - y)) =
          ((m + 1 : ℝ) * y ^ m) * (1 - y) := by ring
      _ ≤ S * (1 - y) := hmul
      _ ≤ 1 := hone
  apply
    (le_div_iff₀
      (by positivity : (0 : ℝ) < (m + 1 : ℕ))).2
  simpa [mul_comm] using htotal

private theorem one_add_exp_two_mul_I_div_two (x : ℝ) :
    ((1 : ℂ) + Complex.exp (((2 * x : ℝ) : ℂ) * I)) / 2 =
      Complex.exp ((x : ℂ) * I) * (Real.cos x : ℂ) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp [Real.cos_two_mul, Real.sin_two_mul,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      pow_two, Complex.mul_re, Complex.mul_im]
  · simp [Real.cos_two_mul, Real.sin_two_mul,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      pow_two, Complex.mul_re, Complex.mul_im]
    ring

private theorem norm_one_sub_mean_exp (x : ℝ) :
    ‖(1 : ℂ) -
      ((1 : ℂ) + Complex.exp ((x : ℂ) * I)) / 2‖ =
        |Real.sin (x / 2)| := by
  rw [show
      (1 : ℂ) -
        ((1 : ℂ) + Complex.exp ((x : ℂ) * I)) / 2 =
      -(Complex.exp ((x : ℂ) * I) - 1) / 2 by ring]
  rw [norm_div, norm_neg,
    show (x : ℂ) * I = I * (x : ℂ) by ring,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  simp [Real.norm_eq_abs]

theorem returningAmplitude_norm_sq (N : ℕ) (t : ℝ) :
    ‖returningAmplitude N t‖ ^ 2 =
      Real.cos (Real.pi * t) ^ (2 * N) := by
  rw [returningAmplitude]
  rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring,
    one_add_exp_two_mul_I_div_two]
  rw [norm_pow, norm_mul]
  simp only [Complex.norm_exp_ofReal_mul_I, one_mul, norm_real,
    Real.norm_eq_abs]
  rw [mul_comm 2 N, pow_mul, ← abs_pow, sq_abs]

private theorem mean_exp_norm_sq (x : ℝ) :
    ‖((1 : ℂ) + Complex.exp ((x : ℂ) * I)) / 2‖ ^ 2 =
      (1 + Real.cos x) / 2 := by
  rw [show
      ((1 : ℂ) + Complex.exp ((x : ℂ) * I)) / 2 =
        Complex.exp (((x / 2 : ℝ) : ℂ) * I) *
          (Real.cos (x / 2) : ℂ) by
    rw [← one_add_exp_two_mul_I_div_two]
    congr 2
    push_cast
    ring_nf]
  rw [norm_mul]
  simp only [Complex.norm_exp_ofReal_mul_I, one_mul, norm_real,
    Real.norm_eq_abs]
  rw [sq_abs, Real.cos_sq]
  rw [show 2 * (x / 2) = x by ring_nf]
  ring_nf

/-- Directly observable return probability of the returning clock. -/
def returningProbability (N : ℕ) (t : ℝ) : ℝ :=
  ‖returningAmplitude N t‖ ^ 2

/-- Directly observable return probability of the orthogonal clock. -/
def orthogonalProbability (N : ℕ) (t : ℝ) : ℝ :=
  ‖orthogonalAmplitude N t‖ ^ 2

/--
The exact amplitude-discrepancy law is also exactly the separation of the
two directly observable return probabilities.
-/
theorem survival_probability_difference (N : ℕ) (t : ℝ) :
    returningProbability N t - orthogonalProbability N t =
      Real.cos (Real.pi * t) ^ (2 * N) *
        (1 - Real.cos (Real.pi * t)) / 2 := by
  rw [returningProbability, orthogonalProbability, orthogonalAmplitude,
    norm_mul, mul_pow, returningAmplitude_norm_sq,
    mean_exp_norm_sq]
  ring_nf

theorem amplitude_difference_norm_sq
    (N : ℕ) (t : ℝ) :
    ‖returningAmplitude N t - orthogonalAmplitude N t‖ ^ 2 =
      Real.cos (Real.pi * t) ^ (2 * N) *
        (1 - Real.cos (Real.pi * t)) / 2 := by
  rw [orthogonalAmplitude]
  rw [show
      returningAmplitude N t -
        returningAmplitude N t *
          (((1 : ℂ) +
            Complex.exp (((Real.pi * t : ℝ) : ℂ) * I)) / 2) =
      returningAmplitude N t *
        (1 - (((1 : ℂ) +
          Complex.exp (((Real.pi * t : ℝ) : ℂ) * I)) / 2)) by ring]
  rw [returningAmplitude]
  rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring,
    one_add_exp_two_mul_I_div_two]
  rw [norm_mul, norm_pow, norm_one_sub_mean_exp]
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I,
    one_mul, norm_real, Real.norm_eq_abs]
  rw [mul_pow, sq_abs, Real.sin_sq_eq_half_sub]
  ring_nf
  rw [show
      |Real.cos (Real.pi * t)| ^ (N * 2) =
        Real.cos (Real.pi * t) ^ (N * 2) by
    rw [mul_comm N 2, pow_mul, pow_mul, sq_abs]]
  ring

/-- Explicit dimension-dependent uniform bound on the preceding half-period. -/
theorem amplitude_difference_uniform_bound
    (N : ℕ) {t : ℝ} (ht : |t| ≤ (1 : ℝ) / 2) :
    ‖returningAmplitude N t - orthogonalAmplitude N t‖ ^ 2 ≤
      1 / (4 * N + 2 : ℕ) := by
  rw [amplitude_difference_norm_sq N t]
  have hcos0 : 0 ≤ Real.cos (Real.pi * t) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;>
      nlinarith [Real.pi_pos, (abs_le.mp ht).1, (abs_le.mp ht).2]
  have h :=
    pow_mul_one_sub_le_inv_succ
      (2 * N) hcos0 (Real.cos_le_one _)
  calc
    Real.cos (Real.pi * t) ^ (2 * N) *
          (1 - Real.cos (Real.pi * t)) / 2 ≤
        (1 / ((2 * N + 1 : ℕ) : ℝ)) / 2 := by
      gcongr
    _ = 1 / ((4 * N + 2 : ℕ) : ℝ) := by
      push_cast
      field_simp
      ring

/--
Away from the return time, the negative-cosine part of the record is
uniformly controlled by its value at the endpoint of the observation
window.
-/
theorem amplitude_difference_tail_bound
    (N : ℕ) {ρ t : ℝ}
    (hρhalf : (1 : ℝ) / 2 ≤ ρ) (hρone : ρ < 1)
    (htlow : (1 : ℝ) / 2 ≤ |t|) (hthigh : |t| ≤ ρ) :
    ‖returningAmplitude N t - orthogonalAmplitude N t‖ ^ 2 ≤
      (-Real.cos (Real.pi * ρ)) ^ (2 * N) := by
  have hρnonneg : 0 ≤ ρ := by linarith
  have harg_nonneg : 0 ≤ Real.pi * |t| := mul_nonneg Real.pi_pos.le (abs_nonneg t)
  have harg_le_pi : Real.pi * |t| ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hhalf_arg : Real.pi / 2 ≤ Real.pi * |t| := by
    nlinarith [Real.pi_pos]
  have harg_le_ρ : Real.pi * |t| ≤ Real.pi * ρ :=
    mul_le_mul_of_nonneg_left hthigh Real.pi_pos.le
  have hρarg_le_pi : Real.pi * ρ ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hcos_abs_arg :
      Real.cos (Real.pi * t) = Real.cos (Real.pi * |t|) := by
    calc
      Real.cos (Real.pi * t) = Real.cos |Real.pi * t| :=
        (Real.cos_abs _).symm
      _ = Real.cos (Real.pi * |t|) := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
  have hcos_nonpos : Real.cos (Real.pi * t) ≤ 0 := by
    rw [hcos_abs_arg]
    simpa [Real.cos_pi_div_two] using
      Real.cos_le_cos_of_nonneg_of_le_pi
        (by positivity : 0 ≤ Real.pi / 2)
        harg_le_pi hhalf_arg
  have hcos_endpoint :
      Real.cos (Real.pi * ρ) ≤ Real.cos (Real.pi * t) := by
    rw [hcos_abs_arg]
    exact Real.cos_le_cos_of_nonneg_of_le_pi
      harg_nonneg hρarg_le_pi harg_le_ρ
  have hendpoint_nonpos : Real.cos (Real.pi * ρ) ≤ 0 := by
    have hρhalf_arg : Real.pi / 2 ≤ Real.pi * ρ := by
      nlinarith [Real.pi_pos]
    simpa [Real.cos_pi_div_two] using
      Real.cos_le_cos_of_nonneg_of_le_pi
        (by positivity : 0 ≤ Real.pi / 2)
        hρarg_le_pi hρhalf_arg
  have hq_nonneg : 0 ≤ -Real.cos (Real.pi * ρ) := neg_nonneg.mpr hendpoint_nonpos
  have habs_bound :
      |Real.cos (Real.pi * t)| ≤ -Real.cos (Real.pi * ρ) := by
    rw [abs_of_nonpos hcos_nonpos]
    linarith
  rw [amplitude_difference_norm_sq]
  rw [show
      Real.cos (Real.pi * t) ^ (2 * N) =
        |Real.cos (Real.pi * t)| ^ (2 * N) by
    rw [pow_mul, pow_mul, sq_abs]]
  have hpow :
      |Real.cos (Real.pi * t)| ^ (2 * N) ≤
        (-Real.cos (Real.pi * ρ)) ^ (2 * N) :=
    pow_le_pow_left₀ (abs_nonneg _) habs_bound _
  have hoffset : (1 - Real.cos (Real.pi * t)) / 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_cos (Real.pi * t)]
  have hpow_nonneg :
      0 ≤ |Real.cos (Real.pi * t)| ^ (2 * N) := by positivity
  calc
    |Real.cos (Real.pi * t)| ^ (2 * N) *
          (1 - Real.cos (Real.pi * t)) / 2 =
        |Real.cos (Real.pi * t)| ^ (2 * N) *
          ((1 - Real.cos (Real.pi * t)) / 2) := by ring
    _ ≤ |Real.cos (Real.pi * t)| ^ (2 * N) := by
      simpa using mul_le_of_le_one_right hpow_nonneg hoffset
    _ ≤ (-Real.cos (Real.pi * ρ)) ^ (2 * N) := hpow

/--
Quantitative bound on every strict pre-return window.  The first term
controls the neighborhood of the initial time; the second controls the
remainder of the window.
-/
theorem amplitude_difference_uniform_before_return
    (N : ℕ) {ρ t : ℝ}
    (hρhalf : (1 : ℝ) / 2 ≤ ρ) (hρone : ρ < 1)
    (ht : |t| ≤ ρ) :
    ‖returningAmplitude N t - orthogonalAmplitude N t‖ ^ 2 ≤
      max ((1 : ℝ) / (4 * N + 2 : ℕ))
        ((-Real.cos (Real.pi * ρ)) ^ (2 * N)) := by
  by_cases ht_half : |t| ≤ (1 : ℝ) / 2
  · exact (amplitude_difference_uniform_bound N ht_half).trans
      (le_max_left _ _)
  · exact
      (amplitude_difference_tail_bound N hρhalf hρone
        (le_of_lt (lt_of_not_ge ht_half)) ht).trans
          (le_max_right _ _)

/--
For every nonzero observational tolerance there is a finite dimension in
which the complete survival records are uniformly closer than that tolerance
through the preceding half-period, although their values at the next period
are exactly one and zero.
-/
theorem exists_finite_positive_clocks_uniformly_indistinguishable
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ,
      (∀ t : ℝ, |t| ≤ (1 : ℝ) / 2 →
        ‖returningAmplitude N t - orthogonalAmplitude N t‖ < ε) ∧
      returningAmplitude N 1 = 1 ∧
      orthogonalAmplitude N 1 = 0 := by
  obtain ⟨n, hn⟩ :=
    exists_nat_one_div_lt (sq_pos_of_pos hε)
  refine ⟨n + 1, ?_, returningAmplitude_one _, orthogonalAmplitude_one _⟩
  intro t ht
  have hs := amplitude_difference_uniform_bound (n + 1) ht
  have hden :
      (1 : ℝ) / (4 * (n + 1) + 2 : ℕ) ≤
        1 / (n + 1 : ℕ) := by
    gcongr
    omega
  have hn' :
      (1 : ℝ) / (n + 1 : ℕ) < ε ^ 2 := by
    norm_cast at hn ⊢
  have hsq :
      ‖returningAmplitude (n + 1) t -
        orthogonalAmplitude (n + 1) t‖ ^ 2 < ε ^ 2 :=
    lt_of_le_of_lt (hs.trans hden) hn'
  nlinarith
    [norm_nonneg
      (returningAmplitude (n + 1) t -
        orthogonalAmplitude (n + 1) t)]

/--
The observation window may occupy any strict fraction of the recurrence
period.  At every nonzero precision, a finite positive spectrum suffices to
make the two complete survival records uniformly indistinguishable
throughout that window while preserving the exact return/orthogonality
dichotomy at the period.
-/
theorem exists_finite_positive_clocks_indistinguishable_before_return
    {ρ ε : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hε : 0 < ε) :
    ∃ N : ℕ,
      (∀ t : ℝ, |t| ≤ ρ →
        ‖returningAmplitude N t - orthogonalAmplitude N t‖ < ε) ∧
      returningAmplitude N 1 = 1 ∧
      orthogonalAmplitude N 1 = 0 := by
  by_cases hρhalf : ρ ≤ (1 : ℝ) / 2
  · obtain ⟨N, hclose, hreturn, horth⟩ :=
      exists_finite_positive_clocks_uniformly_indistinguishable hε
    exact ⟨N, fun t ht => hclose t (ht.trans hρhalf), hreturn, horth⟩
  · have hhalfρ : (1 : ℝ) / 2 ≤ ρ := le_of_lt (lt_of_not_ge hρhalf)
    have hρarg_le_pi : Real.pi * ρ ≤ Real.pi := by
      nlinarith [Real.pi_pos]
    have hendpoint_nonpos : Real.cos (Real.pi * ρ) ≤ 0 := by
      have hρhalf_arg : Real.pi / 2 ≤ Real.pi * ρ := by
        nlinarith [Real.pi_pos]
      simpa [Real.cos_pi_div_two] using
        Real.cos_le_cos_of_nonneg_of_le_pi
          (by positivity : 0 ≤ Real.pi / 2)
          hρarg_le_pi hρhalf_arg
    let q : ℝ := -Real.cos (Real.pi * ρ)
    have hq0 : 0 ≤ q := by
      dsimp [q]
      exact neg_nonneg.mpr hendpoint_nonpos
    have hq1 : q < 1 := by
      have harg_lt_pi : Real.pi * ρ < Real.pi :=
        by nlinarith [Real.pi_pos]
      have hcosgt : -1 < Real.cos (Real.pi * ρ) := by
        rw [← Real.cos_pi]
        exact Real.cos_lt_cos_of_nonneg_of_le_pi
          (mul_nonneg Real.pi_pos.le hρ0) le_rfl harg_lt_pi
      dsimp [q]
      linarith
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sq_pos_of_pos hε)
    obtain ⟨m, hm⟩ :=
      exists_pow_lt_of_lt_one (sq_pos_of_pos hε) hq1
    let N := max (n + 1) m
    have hnN : n + 1 ≤ N := by exact le_max_left _ _
    have hmN : m ≤ N := by exact le_max_right _ _
    refine ⟨N, ?_, returningAmplitude_one _, orthogonalAmplitude_one _⟩
    intro t ht
    have hsq :
        ‖returningAmplitude N t - orthogonalAmplitude N t‖ ^ 2 <
          ε ^ 2 := by
      by_cases ht_half : |t| ≤ (1 : ℝ) / 2
      · have hs := amplitude_difference_uniform_bound N ht_half
        have hden :
            (1 : ℝ) / (4 * N + 2 : ℕ) ≤
              1 / (n + 1 : ℕ) := by
          gcongr
          omega
        have hn' :
            (1 : ℝ) / (n + 1 : ℕ) < ε ^ 2 := by
          norm_cast at hn ⊢
        exact lt_of_le_of_lt (hs.trans hden) hn'
      · have htail :=
          amplitude_difference_tail_bound N hhalfρ hρ1
            (le_of_lt (lt_of_not_ge ht_half)) ht
        have hpow :
            q ^ (2 * N) ≤ q ^ m :=
          pow_le_pow_of_le_one hq0 hq1.le (by omega)
        exact lt_of_le_of_lt (htail.trans hpow) hm
    nlinarith
      [norm_nonneg
        (returningAmplitude N t - orthogonalAmplitude N t)]

/-- Returning amplitude at an arbitrary positive recurrence time `T`. -/
def scaledReturningAmplitude (T : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  returningAmplitude N (t / T)

/-- Orthogonal amplitude at an arbitrary positive recurrence time `T`. -/
def scaledOrthogonalAmplitude (T : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  orthogonalAmplitude N (t / T)

/-- One observation record lying exactly midway between the two clocks. -/
def scaledMidpointAmplitude (T : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  (scaledReturningAmplitude T N t +
    scaledOrthogonalAmplitude T N t) / 2

/-- Scaled return probability of the returning clock. -/
def scaledReturningProbability (T : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  returningProbability N (t / T)

/-- Scaled return probability of the orthogonal clock. -/
def scaledOrthogonalProbability (T : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  orthogonalProbability N (t / T)

/-- One real observation record midway between both return probabilities. -/
def scaledMidpointProbability (T : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (scaledReturningProbability T N t +
    scaledOrthogonalProbability T N t) / 2

/--
The finite-window instability occurs at every positive time scale.  For any
precision, the two full survival records can be made uniformly
indistinguishable on the entire half-period before one returns and the other
becomes orthogonal.
-/
theorem instability_at_every_positive_time_scale
    (T : ℝ) (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ,
      (∀ t : ℝ, |t| ≤ T / 2 →
        ‖scaledReturningAmplitude T N t -
          scaledOrthogonalAmplitude T N t‖ < ε) ∧
      scaledReturningAmplitude T N T = 1 ∧
      scaledOrthogonalAmplitude T N T = 0 := by
  obtain ⟨N, hclose, hreturn, horth⟩ :=
    exists_finite_positive_clocks_uniformly_indistinguishable hε
  refine ⟨N, ?_, ?_, ?_⟩
  · intro t ht
    apply hclose
    rw [abs_div, abs_of_pos hT]
    apply (div_le_iff₀ hT).2
    nlinarith
  · rw [scaledReturningAmplitude, div_self hT.ne']
    exact hreturn
  · rw [scaledOrthogonalAmplitude, div_self hT.ne']
    exact horth

/--
Universal finite-horizon form: for every positive target time, every
observation horizon strictly before it, and every positive precision, two
finite clocks with nonnegative spectra have uniformly indistinguishable
survival records through the whole horizon but attain the opposite extreme
outcomes—exact return and exact orthogonality—at the target time.
-/
theorem instability_on_every_strict_pre_return_window
    (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H) (hHT : H < T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ,
      (∀ t : ℝ, |t| ≤ H →
        ‖scaledReturningAmplitude T N t -
          scaledOrthogonalAmplitude T N t‖ < ε) ∧
      scaledReturningAmplitude T N T = 1 ∧
      scaledOrthogonalAmplitude T N T = 0 := by
  have hρ0 : 0 ≤ H / T := div_nonneg hH0 hT.le
  have hρ1 : H / T < 1 := (div_lt_one hT).2 hHT
  obtain ⟨N, hclose, hreturn, horth⟩ :=
    exists_finite_positive_clocks_indistinguishable_before_return
      hρ0 hρ1 hε
  refine ⟨N, ?_, ?_, ?_⟩
  · intro t ht
    apply hclose
    rw [abs_div, abs_of_pos hT]
    exact (div_le_div_iff_of_pos_right hT).2 ht
  · rw [scaledReturningAmplitude, div_self hT.ne']
    exact hreturn
  · rw [scaledOrthogonalAmplitude, div_self hT.ne']
    exact horth

/--
Operational ambiguity form.  For every positive error radius, the same
finite-window observation record is compatible, pointwise and uniformly,
with both clocks, although those clocks attain orthogonal extreme outcomes
at the target time.
-/
theorem one_noisy_record_allows_opposite_exact_futures
    (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H) (hHT : H < T)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ,
      (∀ t : ℝ, |t| ≤ H →
        ‖scaledReturningAmplitude T N t -
          scaledMidpointAmplitude T N t‖ < δ ∧
        ‖scaledOrthogonalAmplitude T N t -
          scaledMidpointAmplitude T N t‖ < δ) ∧
      scaledReturningAmplitude T N T = 1 ∧
      scaledOrthogonalAmplitude T N T = 0 := by
  have h2δ : 0 < 2 * δ := by positivity
  obtain ⟨N, hclose, hreturn, horth⟩ :=
    instability_on_every_strict_pre_return_window
      T H hT hH0 hHT h2δ
  refine ⟨N, ?_, hreturn, horth⟩
  intro t ht
  have hd := hclose t ht
  constructor
  · rw [scaledMidpointAmplitude]
    rw [show
        scaledReturningAmplitude T N t -
            (scaledReturningAmplitude T N t +
              scaledOrthogonalAmplitude T N t) / 2 =
          (scaledReturningAmplitude T N t -
            scaledOrthogonalAmplitude T N t) / 2 by ring]
    rw [norm_div]
    norm_num
    nlinarith
  · rw [scaledMidpointAmplitude]
    rw [show
        scaledOrthogonalAmplitude T N t -
            (scaledReturningAmplitude T N t +
              scaledOrthogonalAmplitude T N t) / 2 =
          -(scaledReturningAmplitude T N t -
            scaledOrthogonalAmplitude T N t) / 2 by ring]
    rw [norm_div, norm_neg]
    norm_num
    nlinarith

/--
Direct-observable form: return probabilities, not only complex amplitudes,
can be made uniformly arbitrarily close on every strict pre-return window
while attaining one and zero at the target time.
-/
theorem probability_instability_on_every_strict_pre_return_window
    (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H) (hHT : H < T)
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ,
      (∀ t : ℝ, |t| ≤ H →
        |scaledReturningProbability T N t -
          scaledOrthogonalProbability T N t| < η) ∧
      scaledReturningProbability T N T = 1 ∧
      scaledOrthogonalProbability T N T = 0 := by
  have hsqrt : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  obtain ⟨N, hclose, hreturn, horth⟩ :=
    instability_on_every_strict_pre_return_window
      T H hT hH0 hHT hsqrt
  refine ⟨N, ?_, ?_, ?_⟩
  · intro t ht
    have hc := hclose t ht
    have heq :
        scaledReturningProbability T N t -
            scaledOrthogonalProbability T N t =
          ‖scaledReturningAmplitude T N t -
            scaledOrthogonalAmplitude T N t‖ ^ 2 := by
      rw [scaledReturningProbability, scaledOrthogonalProbability,
        scaledReturningAmplitude, scaledOrthogonalAmplitude,
        survival_probability_difference,
        amplitude_difference_norm_sq]
    rw [heq, abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sq_sqrt hη.le,
      norm_nonneg
        (scaledReturningAmplitude T N t -
          scaledOrthogonalAmplitude T N t)]
  · rw [scaledReturningProbability, div_self hT.ne',
      returningProbability, returningAmplitude_one]
    norm_num
  · rw [scaledOrthogonalProbability, div_self hT.ne',
      orthogonalProbability, orthogonalAmplitude_one]
    norm_num

/--
One noisy real-valued return-probability record is uniformly compatible
with both opposite-future clocks at every positive error radius.
-/
theorem one_noisy_probability_record_allows_opposite_exact_futures
    (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H) (hHT : H < T)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ,
      (∀ t : ℝ, |t| ≤ H →
        |scaledReturningProbability T N t -
          scaledMidpointProbability T N t| < δ ∧
        |scaledOrthogonalProbability T N t -
          scaledMidpointProbability T N t| < δ) ∧
      scaledReturningProbability T N T = 1 ∧
      scaledOrthogonalProbability T N T = 0 := by
  have h2δ : 0 < 2 * δ := by positivity
  obtain ⟨N, hclose, hreturn, horth⟩ :=
    probability_instability_on_every_strict_pre_return_window
      T H hT hH0 hHT h2δ
  refine ⟨N, ?_, hreturn, horth⟩
  intro t ht
  have hd := hclose t ht
  have horder :
      scaledOrthogonalProbability T N t ≤
        scaledReturningProbability T N t := by
    apply sub_nonneg.mp
    rw [scaledReturningProbability, scaledOrthogonalProbability,
      survival_probability_difference]
    rw [mul_comm 2 N, pow_mul]
    exact div_nonneg
      (mul_nonneg (sq_nonneg _)
        (sub_nonneg.mpr (Real.cos_le_one _))) (by norm_num)
  have hd' :
      scaledReturningProbability T N t -
          scaledOrthogonalProbability T N t < 2 * δ :=
    (le_abs_self _).trans_lt hd
  constructor
  · rw [scaledMidpointProbability]
    rw [show
        scaledReturningProbability T N t -
            (scaledReturningProbability T N t +
              scaledOrthogonalProbability T N t) / 2 =
          (scaledReturningProbability T N t -
            scaledOrthogonalProbability T N t) / 2 by ring]
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (sub_nonneg.mpr horder)]
    nlinarith [hd']
  · rw [scaledMidpointProbability]
    rw [show
        scaledOrthogonalProbability T N t -
            (scaledReturningProbability T N t +
              scaledOrthogonalProbability T N t) / 2 =
          -(scaledReturningProbability T N t -
            scaledOrthogonalProbability T N t) / 2 by ring]
    rw [abs_div, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (sub_nonneg.mpr horder)]
    nlinarith [hd']

/--
Algorithm-independent minimax consequence.  Every real-valued forecaster
fed the common finite-window record has absolute terminal error at least
one half for one of the two admissible exact futures.
-/
theorem every_return_forecaster_has_half_scale_worst_case_error
    (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H) (hHT : H < T)
    {δ : ℝ} (hδ : 0 < δ)
    (forecast : (ℝ → ℝ) → ℝ) :
    ∃ N : ℕ,
      (∀ t : ℝ, |t| ≤ H →
        |scaledReturningProbability T N t -
          scaledMidpointProbability T N t| < δ ∧
        |scaledOrthogonalProbability T N t -
          scaledMidpointProbability T N t| < δ) ∧
      scaledReturningProbability T N T = 1 ∧
      scaledOrthogonalProbability T N T = 0 ∧
      ((1 : ℝ) / 2 ≤
          |forecast (scaledMidpointProbability T N) - 1| ∨
        (1 : ℝ) / 2 ≤
          |forecast (scaledMidpointProbability T N) - 0|) := by
  obtain ⟨N, hrecord, hreturn, horth⟩ :=
    one_noisy_probability_record_allows_opposite_exact_futures
      T H hT hH0 hHT hδ
  refine ⟨N, hrecord, hreturn, horth, ?_⟩
  let y := forecast (scaledMidpointProbability T N)
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

/-! ## Same-Hamiltonian realization -/

/-- Shared self-adjoint diagonal Hamiltonian. -/
def clockHamiltonian (N : ℕ) :
    FiniteIndexClockSpace (ClockIndex N) →L[ℂ]
      FiniteIndexClockSpace (ClockIndex N) :=
  finiteIndexDiagonalHamiltonian (clockEnergy N)

/-- Returning unit clock at time zero. -/
def returningClock (N : ℕ) : FiniteIndexClockSpace (ClockIndex N) :=
  finiteIndexWeightKet (returningWeight N)

/-- Orthogonal unit clock at time zero. -/
def orthogonalClock (N : ℕ) : FiniteIndexClockSpace (ClockIndex N) :=
  finiteIndexWeightKet (orthogonalWeight N)

/-- Returning clock with its exact coordinatewise dynamical phases. -/
def returningClockAt (N : ℕ) (t : ℝ) :
    FiniteIndexClockSpace (ClockIndex N) :=
  finiteIndexPhasedWeightKet (returningWeight N) (clockPhase N t)

/-- Orthogonal clock with its exact coordinatewise dynamical phases. -/
def orthogonalClockAt (N : ℕ) (t : ℝ) :
    FiniteIndexClockSpace (ClockIndex N) :=
  finiteIndexPhasedWeightKet (orthogonalWeight N) (clockPhase N t)

theorem clockHamiltonian_selfAdjoint (N : ℕ) :
    ContinuousLinearMap.adjoint (clockHamiltonian N) =
      clockHamiltonian N :=
  finiteIndexDiagonalHamiltonian_selfAdjoint _

@[simp] theorem returningClock_norm (N : ℕ) :
    ‖returningClock N‖ = 1 :=
  finiteIndexWeightKet_norm_eq_one _ (returningWeight_nonneg N)
    (returningWeight_sum N)

@[simp] theorem orthogonalClock_norm (N : ℕ) :
    ‖orthogonalClock N‖ = 1 :=
  finiteIndexWeightKet_norm_eq_one _ (orthogonalWeight_nonneg N)
    (orthogonalWeight_sum N)

@[simp] theorem returningClockAt_norm (N : ℕ) (t : ℝ) :
    ‖returningClockAt N t‖ = 1 := by
  have hsq :=
    finiteIndexPhasedWeightKet_norm_sq
      (returningWeight N) (clockPhase N t)
      (returningWeight_nonneg N) (clockPhase_norm N t)
  rw [returningWeight_sum] at hsq
  change
    ‖finiteIndexPhasedWeightKet
      (returningWeight N) (clockPhase N t)‖ = 1
  nlinarith
    [norm_nonneg
      (finiteIndexPhasedWeightKet
        (returningWeight N) (clockPhase N t))]

@[simp] theorem orthogonalClockAt_norm (N : ℕ) (t : ℝ) :
    ‖orthogonalClockAt N t‖ = 1 := by
  have hsq :=
    finiteIndexPhasedWeightKet_norm_sq
      (orthogonalWeight N) (clockPhase N t)
      (orthogonalWeight_nonneg N) (clockPhase_norm N t)
  rw [orthogonalWeight_sum] at hsq
  change
    ‖finiteIndexPhasedWeightKet
      (orthogonalWeight N) (clockPhase N t)‖ = 1
  nlinarith
    [norm_nonneg
      (finiteIndexPhasedWeightKet
        (orthogonalWeight N) (clockPhase N t))]

theorem returningClock_survivalAmplitude (N : ℕ) (t : ℝ) :
    inner ℂ (returningClock N) (returningClockAt N t) =
      returningAmplitude N t := by
  rw [returningClock, returningClockAt,
    finiteIndexWeightKet_inner_phasedWeightKet
      _ _ (returningWeight_nonneg N)]
  exact returning_weighted_phase_sum N t

theorem orthogonalClock_survivalAmplitude (N : ℕ) (t : ℝ) :
    inner ℂ (orthogonalClock N) (orthogonalClockAt N t) =
      orthogonalAmplitude N t := by
  rw [orthogonalClock, orthogonalClockAt,
    finiteIndexWeightKet_inner_phasedWeightKet
      _ _ (orthogonalWeight_nonneg N)]
  exact orthogonal_weighted_phase_sum N t

/-! ## Dual realization with one shared initial state -/

/--
Returning energy list for the dual realization: both branches carry the
same integer energy.
-/
def sharedStateReturningEnergy (N : ℕ) : ClockIndex N → ℝ
  | Sum.inl k => k
  | Sum.inr k => k

/-- Coordinate phase of the returning dynamics in the shared-state model. -/
def sharedStateReturningPhase
    (N : ℕ) (t : ℝ) (i : ClockIndex N) : ℂ :=
  Complex.exp
    (((2 * Real.pi * sharedStateReturningEnergy N i * t : ℝ) : ℂ) * I)

theorem sharedStateReturningEnergy_nonneg
    (N : ℕ) (i : ClockIndex N) :
    0 ≤ sharedStateReturningEnergy N i := by
  cases i <;> exact Nat.cast_nonneg _

theorem sharedStateReturningPhase_norm
    (N : ℕ) (t : ℝ) (i : ClockIndex N) :
    ‖sharedStateReturningPhase N t i‖ = 1 := by
  rw [sharedStateReturningPhase, Complex.norm_exp]
  simp [Complex.mul_re]

private theorem sharedStateReturningPhase_inl
    (N : ℕ) (t : ℝ) (k : Fin (N + 1)) :
    sharedStateReturningPhase N t (Sum.inl k) =
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I) ^ (k : ℕ) := by
  rw [sharedStateReturningPhase, sharedStateReturningEnergy,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem sharedStateReturningPhase_inr
    (N : ℕ) (t : ℝ) (k : Fin (N + 1)) :
    sharedStateReturningPhase N t (Sum.inr k) =
      Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I) ^ (k : ℕ) := by
  rw [sharedStateReturningPhase, sharedStateReturningEnergy,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem sharedState_returning_weighted_phase_sum (N : ℕ) (t : ℝ) :
    ∑ i : ClockIndex N,
        (orthogonalWeight N i : ℂ) *
          sharedStateReturningPhase N t i =
      returningAmplitude N t := by
  rw [Fintype.sum_sum_type]
  simp only [orthogonalWeight]
  simp_rw [
    show ∀ k : Fin (N + 1),
        sharedStateReturningPhase N t (Sum.inl k) =
          Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I) ^ (k : ℕ) by
      intro k
      exact sharedStateReturningPhase_inl N t k,
    show ∀ k : Fin (N + 1),
        sharedStateReturningPhase N t (Sum.inr k) =
          Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I) ^ (k : ℕ) by
      intro k
      exact sharedStateReturningPhase_inr N t k]
  let z := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I)
  have hhalf :
      (∑ k : Fin (N + 1),
          ((binomialWeight N k / 2 : ℝ) : ℂ) * z ^ (k : ℕ)) =
        returningAmplitude N t / 2 := by
    calc
      (∑ k : Fin (N + 1),
          ((binomialWeight N k / 2 : ℝ) : ℂ) * z ^ (k : ℕ)) =
          ∑ k : Fin (N + 1),
            ((binomialWeight N k : ℂ) * z ^ (k : ℕ)) / 2 := by
        apply Finset.sum_congr rfl
        intro k _hk
        push_cast
        ring
      _ = (∑ k : Fin (N + 1),
          (binomialWeight N k : ℂ) * z ^ (k : ℕ)) / 2 := by
        exact
          (Finset.sum_div Finset.univ
            (fun k : Fin (N + 1) =>
              (binomialWeight N k : ℂ) * z ^ (k : ℕ)) 2).symm
      _ = returningAmplitude N t / 2 := by
        rw [binomialWeight_generating]
        rfl
  change
    (∑ k : Fin (N + 1),
      ((binomialWeight N k / 2 : ℝ) : ℂ) * z ^ (k : ℕ)) +
    (∑ k : Fin (N + 1),
      ((binomialWeight N k / 2 : ℝ) : ℂ) * z ^ (k : ℕ)) =
      returningAmplitude N t
  rw [hhalf]
  ring

/-- Shared initial state in the dual two-Hamiltonian realization. -/
def sharedInitialClock (N : ℕ) :
    FiniteIndexClockSpace (ClockIndex N) :=
  finiteIndexWeightKet (orthogonalWeight N)

/-- Integer-branch Hamiltonian producing exact return of the shared state. -/
def sharedStateReturningHamiltonian (N : ℕ) :
    FiniteIndexClockSpace (ClockIndex N) →L[ℂ]
      FiniteIndexClockSpace (ClockIndex N) :=
  finiteIndexDiagonalHamiltonian (sharedStateReturningEnergy N)

/-- Shared initial state evolved by the returning Hamiltonian. -/
def sharedInitialClockReturningAt (N : ℕ) (t : ℝ) :
    FiniteIndexClockSpace (ClockIndex N) :=
  finiteIndexPhasedWeightKet
    (orthogonalWeight N) (sharedStateReturningPhase N t)

theorem sharedStateReturningHamiltonian_selfAdjoint (N : ℕ) :
    ContinuousLinearMap.adjoint (sharedStateReturningHamiltonian N) =
      sharedStateReturningHamiltonian N :=
  finiteIndexDiagonalHamiltonian_selfAdjoint _

@[simp] theorem sharedInitialClock_norm (N : ℕ) :
    ‖sharedInitialClock N‖ = 1 :=
  finiteIndexWeightKet_norm_eq_one _ (orthogonalWeight_nonneg N)
    (orthogonalWeight_sum N)

theorem sharedInitialClock_returning_survivalAmplitude
    (N : ℕ) (t : ℝ) :
    inner ℂ (sharedInitialClock N)
        (sharedInitialClockReturningAt N t) =
      returningAmplitude N t := by
  rw [sharedInitialClock, sharedInitialClockReturningAt,
    finiteIndexWeightKet_inner_phasedWeightKet
      _ _ (orthogonalWeight_nonneg N)]
  exact sharedState_returning_weighted_phase_sum N t

/--
One and the same initial pure state has exact return under the integer
Hamiltonian and exact orthogonality under the half-shift Hamiltonian at the
target time.
-/
theorem one_initial_state_opposite_exact_hamiltonian_futures (N : ℕ) :
    inner ℂ (sharedInitialClock N)
        (sharedInitialClockReturningAt N 1) = 1 ∧
    inner ℂ (sharedInitialClock N)
        (orthogonalClockAt N 1) = 0 := by
  constructor
  · rw [sharedInitialClock_returning_survivalAmplitude,
      returningAmplitude_one]
  · change
      inner ℂ (orthogonalClock N) (orthogonalClockAt N 1) = 0
    rw [orthogonalClock_survivalAmplitude, orthogonalAmplitude_one]

end RHTower.FiniteWindow
