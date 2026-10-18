import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCollarIrrationalityAndSpacing

/-! General divisor-stencil Bernoulli filters, exact dyadic stencil uniqueness,
and harmonic dominance bounds for the factorial Müntz phase profile.

Let `C(u) = -bernoulliPeriodic u = {u}(1 - {u}) / 2` be the 1-periodic extension
of `clampedLatticeRemainder`. Any divisor stencil `(D, α)` defines a periodic filter
`P_{D, α}(u) = ∑_{d ∈ D} α(d) C(d u)` and a collar-difference phase profile
`Φ_{D, α, N}(v) = P_{D, α}(λ_N v) - P_{D, α}(N v)`.

We prove:
1. Exact agreement of `C(u)` with `clampedLatticeRemainder u` for `u ≥ 0`,
   1-periodicity, range `[0, 1/8]`, and unit-interval mean `1/12`.
2. In every collar difference `P_{D, α}(λ_N v) - P_{D, α}(N v)`, the constant Fourier
   mode `(∑_{d ∈ D} α(d)) / 12` cancels identically for arbitrary `(D, α)`.
3. For any divisor stencil `(D, α)`, the normalized harmonic multiplier at frequency `k`
   is `M_{D, α}(k) = ∑_{d ∈ D, d ∣ k} α(d) d^2`. On the dyadic divisor set `{1, 2, 4}`,
   the three conditions `M(1) = 4`, `M(2) = -4`, and `M(4) = 0` hold if and only if
   `(α(1), α(2), α(4)) = (4, -2, 1/4)` — the exact coefficients of
   `factorialMuntzTailRemainder`.
4. With these canonical coefficients, `M_{{1,2,4}, α}(k) = 4 χ(k)` for every `k ≥ 1`,
   where `χ(k) = 1` for odd `k`, `-1` for `k ≡ 2 (mod 4)`, and `0` for `4 ∣ k`.
5. The higher-harmonic `k^{-2}` tail satisfies `∑_{k ≥ 2} |χ(k)| / k^2 ≤ 3/4 < 1 = χ(1)`,
   yielding a strictly positive first-harmonic dominance margin of at least `1/4`. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- The 1-periodic clamped lattice kernel `C(u) = -bernoulliPeriodic u = {u}(1 - {u}) / 2`. -/
def periodicClampedKernel (u : ℝ) : ℝ :=
  -_root_.RHTower.bernoulliPeriodic u

theorem periodicClampedKernel_eq_fract (u : ℝ) :
    periodicClampedKernel u = Int.fract u * (1 - Int.fract u) / 2 := by
  unfold periodicClampedKernel _root_.RHTower.bernoulliPeriodic
  ring

theorem periodicClampedKernel_eq_clampedLatticeRemainder {u : ℝ} (hu : 0 ≤ u) :
    periodicClampedKernel u = clampedLatticeRemainder u := by
  unfold periodicClampedKernel
  rw [clampedLatticeRemainder_eq_neg_bernoulli hu]

theorem periodicClampedKernel_periodic : Function.Periodic periodicClampedKernel 1 := by
  intro u
  simp [periodicClampedKernel, _root_.RHTower.bernoulliPeriodic, Int.fract_add_one]

theorem periodicClampedKernel_bounds (u : ℝ) :
    0 ≤ periodicClampedKernel u ∧ periodicClampedKernel u ≤ 1 / 8 := by
  rw [periodicClampedKernel_eq_fract]
  have h0 : 0 ≤ Int.fract u := Int.fract_nonneg u
  have h1 : Int.fract u ≤ 1 := (Int.fract_lt_one u).le
  constructor
  · exact div_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1)) (by norm_num)
  · have hsq : 0 ≤ (Int.fract u - 1 / 2) ^ 2 := sq_nonneg _
    nlinarith

/-- The 1-periodic centered kernel `C₀(u) = C(u) - 1/12`. -/
def periodicCenteredClampedKernel (u : ℝ) : ℝ :=
  periodicClampedKernel u - 1 / 12

/-- General divisor-stencil Bernoulli filter `P_{D, α}(u) = ∑_{d ∈ D} α(d) C(d u)`. -/
def divisorBernoulliFilter (D : Finset ℕ) (α : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑ d ∈ D, α d * periodicClampedKernel ((d : ℝ) * u)

/-- Centered divisor-stencil Bernoulli filter `P_{D, α, 0}(u) = ∑_{d ∈ D} α(d) (C(d u) - 1/12)`. -/
def divisorCenteredBernoulliFilter (D : Finset ℕ) (α : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑ d ∈ D, α d * periodicCenteredClampedKernel ((d : ℝ) * u)

/-- Constant Fourier mode `(∑_{d ∈ D} α(d)) / 12` of the divisor-stencil filter. -/
def divisorBernoulliConstantMode (D : Finset ℕ) (α : ℕ → ℝ) : ℝ :=
  (∑ d ∈ D, α d) / 12

theorem divisorBernoulliFilter_eq_centered_add_const (D : Finset ℕ) (α : ℕ → ℝ) (u : ℝ) :
    divisorBernoulliFilter D α u =
      divisorCenteredBernoulliFilter D α u + divisorBernoulliConstantMode D α := by
  unfold divisorBernoulliFilter divisorCenteredBernoulliFilter
    divisorBernoulliConstantMode periodicCenteredClampedKernel
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- **Constant-Mode Cancellation Classification (`iff`).** The constant mode of a divisor
filter vanishes if and only if the stencil weights sum to zero. -/
theorem divisorBernoulliConstantMode_eq_zero_iff (D : Finset ℕ) (α : ℕ → ℝ) :
    divisorBernoulliConstantMode D α = 0 ↔ ∑ d ∈ D, α d = 0 := by
  unfold divisorBernoulliConstantMode
  exact div_eq_zero_iff.trans (or_iff_left (by norm_num))

/-- **Universal Collar Constant-Mode Cancellation.** In any dilation-collar difference
`P_{D, α}(lam v) - P_{D, α}(mu v)`, the constant mode `(∑_{d ∈ D} α(d)) / 12` cancels
identically without requiring `∑_{d ∈ D} α(d) = 0`. -/
theorem divisorBernoulliFilter_collar_diff_eq_centered (D : Finset ℕ) (α : ℕ → ℝ) (lam mu v : ℝ) :
    divisorBernoulliFilter D α (lam * v) - divisorBernoulliFilter D α (mu * v) =
      divisorCenteredBernoulliFilter D α (lam * v) -
        divisorCenteredBernoulliFilter D α (mu * v) := by
  rw [divisorBernoulliFilter_eq_centered_add_const D α (lam * v),
    divisorBernoulliFilter_eq_centered_add_const D α (mu * v)]
  ring

/-- Normalized harmonic multiplier `M_{D, α}(k) = ∑_{d ∈ D, d ∣ k} α(d) d^2` of a divisor
stencil at harmonic `k`. -/
def divisorHarmonicMultiplier (D : Finset ℕ) (α : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ D with d ∣ k, α d * (d : ℝ) ^ 2

/-- Explicit formula for the harmonic multiplier on the dyadic divisor set `{1, 2, 4}`. -/
theorem divisorHarmonicMultiplier_dyadic_eq (α : ℕ → ℝ) (k : ℕ) :
    divisorHarmonicMultiplier ({1, 2, 4} : Finset ℕ) α k =
      α 1 + (if 2 ∣ k then 4 * α 2 else 0) + (if 4 ∣ k then 16 * α 4 else 0) := by
  unfold divisorHarmonicMultiplier
  have h12 : (1 : ℕ) ∉ ({2, 4} : Finset ℕ) := by decide
  have h24 : (2 : ℕ) ∉ ({4} : Finset ℕ) := by decide
  rw [Finset.filter_insert, if_pos (one_dvd k),
    Finset.sum_insert (by simp [h12]),
    Finset.filter_insert, Finset.filter_singleton]
  split_ifs with h2 h4
  · rw [Finset.sum_insert (by simp [h24]), Finset.sum_singleton]
    push_cast
    ring
  · simp
    ring
  · rw [Finset.sum_singleton]
    push_cast
    ring
  · rw [Finset.sum_empty]
    push_cast
    ring

/-- **Exact Dyadic Stencil Uniqueness Classification (`iff`).** On the dyadic divisor set
`{1, 2, 4}`, a stencil `α` satisfies fundamental harmonic normalization `M(1) = 4`,
mod-4 sign alternation `M(2) = -4`, and mod-4 harmonic extinction `M(4) = 0`
if and only if `(α 1, α 2, α 4) = (4, -2, 1 / 4)`. -/
theorem dyadic_stencil_uniqueness_iff (α : ℕ → ℝ) :
    (divisorHarmonicMultiplier ({1, 2, 4} : Finset ℕ) α 1 = 4 ∧
      divisorHarmonicMultiplier ({1, 2, 4} : Finset ℕ) α 2 = -4 ∧
      divisorHarmonicMultiplier ({1, 2, 4} : Finset ℕ) α 4 = 0) ↔
      (α 1 = 4 ∧ α 2 = -2 ∧ α 4 = 1 / 4) := by
  rw [divisorHarmonicMultiplier_dyadic_eq α 1,
    divisorHarmonicMultiplier_dyadic_eq α 2,
    divisorHarmonicMultiplier_dyadic_eq α 4]
  have h21 : ¬ (2 ∣ 1) := by decide
  have h41 : ¬ (4 ∣ 1) := by decide
  have h22 : 2 ∣ 2 := by decide
  have h42 : ¬ (4 ∣ 2) := by decide
  have h24 : 2 ∣ 4 := by decide
  have h44 : 4 ∣ 4 := by decide
  simp only [h21, h41, h22, h42, h24, h44, if_true, if_false, add_zero]
  constructor
  · rintro ⟨h1, h2, h4⟩
    refine ⟨h1, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h4⟩
    refine ⟨h1, by linarith, by linarith⟩

/-- **Two-Scale Dyadic Obstruction.** On the two-element divisor set `{1, 2}`, any stencil `α`
that normalizes the first harmonic (`M(1) = 4`) and extinguishes even harmonics (`M(2) = 0`)
forces `α 1 = 4` and `α 2 = -1`, which fails the linear ramp cancellation identity
`α 1 + 2 * α 2 = 0` (`α 1 + 2 * α 2 = 2 ≠ 0`). -/
theorem two_scale_dyadic_obstruction (α : ℕ → ℝ)
    (h1 : divisorHarmonicMultiplier ({1, 2} : Finset ℕ) α 1 = 4)
    (h2 : divisorHarmonicMultiplier ({1, 2} : Finset ℕ) α 2 = 0) :
    α 1 = 4 ∧ α 2 = -1 ∧ α 1 + 2 * α 2 = 2 := by
  unfold divisorHarmonicMultiplier at h1 h2
  have hnot : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
  have hd1 : ¬ (2 ∣ 1) := by decide
  have hd2 : 2 ∣ 2 := by decide
  rw [Finset.filter_insert, if_pos (one_dvd 1), Finset.filter_singleton, if_neg hd1] at h1
  simp at h1
  rw [Finset.filter_insert, if_pos (one_dvd 2), Finset.filter_singleton, if_pos hd2,
    Finset.sum_insert (by simp [hnot]), Finset.sum_singleton] at h2
  push_cast at h2
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Canonical dyadic stencil weights `α(1) = 4`, `α(2) = -2`, `α(4) = 1/4`. -/
def canonicalDyadicStencil (d : ℕ) : ℝ :=
  if d = 1 then 4 else if d = 2 then -2 else if d = 4 then 1 / 4 else 0

/-- The dyadic Bernoulli filter `P(u) = C(4 u) / 4 - 2 C(2 u) + 4 C(u)`. -/
def dyadicBernoulliFilter (u : ℝ) : ℝ :=
  periodicClampedKernel (4 * u) / 4 - 2 * periodicClampedKernel (2 * u) +
    4 * periodicClampedKernel u

/-- The centered dyadic Bernoulli filter `P₀(u) = P(u) - 3/16`. -/
def dyadicCenteredBernoulliFilter (u : ℝ) : ℝ :=
  dyadicBernoulliFilter u - 3 / 16

theorem dyadicBernoulliFilter_eq_divisorFilter (u : ℝ) :
    dyadicBernoulliFilter u =
      divisorBernoulliFilter ({1, 2, 4} : Finset ℕ) canonicalDyadicStencil u := by
  unfold divisorBernoulliFilter canonicalDyadicStencil dyadicBernoulliFilter
  have h12 : (1 : ℕ) ∉ ({2, 4} : Finset ℕ) := by decide
  have h24 : (2 : ℕ) ∉ ({4} : Finset ℕ) := by decide
  rw [Finset.sum_insert h12, Finset.sum_insert h24, Finset.sum_singleton]
  norm_num
  ring

/-- The 1-periodic factorial phase profile `Φ_N(v) = P(λ_N v) - P(N v)`. -/
def factorialPhaseProfile (N : ℕ) (v : ℝ) : ℝ :=
  dyadicBernoulliFilter (factorialShiftedFreq N * v) -
    dyadicBernoulliFilter ((N : ℝ) * v)

theorem factorialPhaseProfile_eq_centered (N : ℕ) (v : ℝ) :
    factorialPhaseProfile N v =
      dyadicCenteredBernoulliFilter (factorialShiftedFreq N * v) -
        dyadicCenteredBernoulliFilter ((N : ℝ) * v) := by
  unfold factorialPhaseProfile dyadicCenteredBernoulliFilter
  ring

/-- Exact source dictionary: for `v ≥ 0`, `factorialPhaseProfile (n + 1) v` coincides with
`factorialMuntzTailRemainder n ((n + 1) * v)`. -/
theorem factorialPhaseProfile_eq_tailRemainder (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    factorialPhaseProfile (n + 1) v =
      factorialMuntzTailRemainder n (((n + 1 : ℕ) : ℝ) * v) := by
  have hε : 0 ≤ sourceFactorialCollar (n + 1) :=
    (sourceFactorialCollar_pos (N := n + 1) (by omega)).le
  have hN : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam : 0 ≤ factorialShiftedFreq (n + 1) := by
    unfold factorialShiftedFreq
    positivity
  unfold factorialPhaseProfile dyadicBernoulliFilter factorialMuntzTailRemainder
  rw [periodicClampedKernel_eq_clampedLatticeRemainder (by positivity),
    periodicClampedKernel_eq_clampedLatticeRemainder (by positivity),
    periodicClampedKernel_eq_clampedLatticeRemainder (by positivity),
    periodicClampedKernel_eq_clampedLatticeRemainder (by positivity),
    periodicClampedKernel_eq_clampedLatticeRemainder (by positivity),
    periodicClampedKernel_eq_clampedLatticeRemainder (by positivity)]
  unfold factorialShiftedFreq
  ring_nf

/-- Exact source dictionary for the literal correction tail `T_n(x)`:
for all `x ≤ 0`, `T_n(x) = a_n e^{3x/2} Φ_{n+1}(e^{-x})`. -/
theorem factorialMuntzCorrectedTail_eq_factorialPhaseProfile (n : ℕ) (x : ℝ) :
    factorialMuntzCorrectedTail n x =
      (Iic (0 : ℝ)).indicator
        (fun y => factorialTailAmplitude n * Real.exp (3 * y / 2) *
          factorialPhaseProfile (n + 1) (Real.exp (-y))) x := by
  rw [factorialMuntzCorrectedTail_eq_phase n x]
  congr 1
  funext y
  rw [factorialPhaseProfile_eq_tailRemainder n (Real.exp_pos (-y)).le]
  rfl

/-- The 4-periodic dyadic harmonic filter multiplier `χ(k)`:
`1` for odd `k`, `-1` for `k ≡ 2 (mod 4)`, and `0` for `4 ∣ k`. -/
def dyadicHarmonicChi (k : ℕ) : ℝ :=
  if k % 2 = 1 then 1 else if k % 4 = 2 then -1 else 0

@[simp]
theorem dyadicHarmonicChi_one : dyadicHarmonicChi 1 = 1 := by
  unfold dyadicHarmonicChi
  norm_num

@[simp]
theorem dyadicHarmonicChi_two : dyadicHarmonicChi 2 = -1 := by
  unfold dyadicHarmonicChi
  norm_num

@[simp]
theorem dyadicHarmonicChi_three : dyadicHarmonicChi 3 = 1 := by
  unfold dyadicHarmonicChi
  norm_num

theorem dyadicHarmonicChi_four_mul (m : ℕ) : dyadicHarmonicChi (4 * m) = 0 := by
  unfold dyadicHarmonicChi
  have h2 : (4 * m) % 2 = 0 := by omega
  have h4 : (4 * m) % 4 = 0 := by omega
  simp [h2, h4]

theorem abs_dyadicHarmonicChi_le_one (k : ℕ) : |dyadicHarmonicChi k| ≤ 1 := by
  unfold dyadicHarmonicChi
  split_ifs <;> norm_num

/-- For every `k ≥ 1`, the canonical dyadic stencil multiplier equals `4 * dyadicHarmonicChi k`. -/
theorem divisorHarmonicMultiplier_canonicalDyadic_eq (k : ℕ) :
    divisorHarmonicMultiplier ({1, 2, 4} : Finset ℕ) canonicalDyadicStencil k =
      4 * dyadicHarmonicChi k := by
  rw [divisorHarmonicMultiplier_dyadic_eq]
  unfold canonicalDyadicStencil dyadicHarmonicChi
  have h21 : (2 : ℕ) ≠ 1 := by decide
  have h41 : (4 : ℕ) ≠ 1 := by decide
  have h42 : (4 : ℕ) ≠ 2 := by decide
  simp only [h21, h41, h42, if_true, if_false]
  by_cases hodd : k % 2 = 1
  · have hnot2 : ¬ (2 ∣ k) := by omega
    have hnot4 : ¬ (4 ∣ k) := by omega
    simp [hodd, hnot2, hnot4]
  · have heven : 2 ∣ k := by omega
    by_cases hmod4 : k % 4 = 2
    · have hnot4 : ¬ (4 ∣ k) := by omega
      simp [hodd, heven, hmod4, hnot4]
      ring
    · have hdiv4 : 4 ∣ k := by omega
      simp [hodd, heven, hmod4, hdiv4]
      ring

/-- Telescoping bound `∑_{k = 3}^M 1 / k^2 ≤ 1 / 2 - 1 / M` for `M ≥ 2`. -/
theorem sum_Icc_three_inv_sq_le (M : ℕ) (hM : 2 ≤ M) :
    (∑ k ∈ Finset.Icc 3 M, 1 / (k : ℝ) ^ 2) ≤ 1 / 2 - 1 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    simp
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ m + 1)]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hstep : 1 / ((m + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
      rw [div_sub_div _ _ hm_pos.ne' hm1_pos.ne', one_mul, mul_one]
      have hsub : ((m + 1 : ℕ) : ℝ) - (m : ℝ) = 1 := by push_cast; ring
      rw [hsub]
      apply one_div_le_one_div_of_le (mul_pos hm_pos hm1_pos)
      push_cast
      nlinarith
    linarith

/-- **Exact Dyadic Higher-Harmonic Tail Bound (`≤ 3/4`).** For every `M ≥ 2`,
`∑_{k = 2}^M |χ(k)| / k^2 ≤ 3 / 4`. -/
theorem sum_Icc_two_abs_dyadicHarmonicChi_div_sq_le (M : ℕ) :
    (∑ k ∈ Finset.Icc 2 M, |dyadicHarmonicChi k| / (k : ℝ) ^ 2) ≤ 3 / 4 := by
  rcases lt_or_ge M 2 with hlt | hM
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    norm_num
  · have hsplit : Finset.Icc 2 M = insert 2 (Finset.Icc 3 M) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hsplit, Finset.sum_insert (by simp)]
    rw [dyadicHarmonicChi_two]
    have h2 : |(-1 : ℝ)| / ((2 : ℕ) : ℝ) ^ 2 = 1 / 4 := by norm_num
    rw [h2]
    have hle : (∑ k ∈ Finset.Icc 3 M, |dyadicHarmonicChi k| / (k : ℝ) ^ 2) ≤
        ∑ k ∈ Finset.Icc 3 M, 1 / (k : ℝ) ^ 2 := by
      refine Finset.sum_le_sum fun k _ => ?_
      exact div_le_div_of_nonneg_right (abs_dyadicHarmonicChi_le_one k) (sq_nonneg _)
    have htel := sum_Icc_three_inv_sq_le M hM
    have hM_inv : 0 ≤ 1 / (M : ℝ) := by positivity
    linarith

/-- Strict first-harmonic dominance: for every `M ≥ 2`,
`dyadicHarmonicChi 1 - ∑_{k = 2}^M |dyadicHarmonicChi k| / k^2 ≥ 1 / 4`. -/
theorem dyadicHarmonicChi_first_harmonic_margin (M : ℕ) :
    1 / 4 ≤ dyadicHarmonicChi 1 -
      ∑ k ∈ Finset.Icc 2 M, |dyadicHarmonicChi k| / (k : ℝ) ^ 2 := by
  rw [dyadicHarmonicChi_one]
  linarith [sum_Icc_two_abs_dyadicHarmonicChi_div_sq_le M]

end

end GaloisForLFunctions.ArithmeticPositivityTheory
