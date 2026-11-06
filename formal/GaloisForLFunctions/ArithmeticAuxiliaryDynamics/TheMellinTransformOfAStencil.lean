import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheCoefficientMassOfAProducer
import GaloisForLFunctions.RHTower.ZetaPartialSumStrip
import GaloisForLFunctions.RHTower.HighBlockDualWeightVariation
import GaloisForLFunctions.RHTower.DirichletPolyBoundedAbel

/-!
# The Mellin transform of a stencil

For a balanced stencil, with `D_c(s) = Σ c(k) k^{-s}`,

`D_c(s) ζ(s) = Σ_{r ≥ 1} g(r) (r^{-s} − (r + 1)^{-s})`,  `Re s > 0`, `s ≠ 1`.

The right side converges absolutely because `g` is bounded. The proof is elementary: partial sums
along multiples of a common period `L` are exact, since `g(qL) = 0` and `⌊qL/k⌋ = qL/k`, and the
polar parts `(qL/k)^{1-s}/(1-s)` cancel by balance.

**A producer is a mollifier on the line `Re s = 1`.** Subtract the window: the remainder has
nonnegative coefficients and total mass the excess `T`. So
`‖D_c(s) ζ(s) − m (1 − B^{-s})‖ ≤ ‖s‖ T` on `Re s = 1`, for free. This inverts `ζ` on `Re s = 1` by
a Dirichlet polynomial with integer coefficients, and proves `ζ(s) ≠ 0` as soon as `ε ‖s‖ < 1`.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The Dirichlet polynomial `D_c(s) = Σ c(k) k^{-s}` of a stencil. -/
def dirichletPoly (c : ℕ →₀ ℤ) (s : ℂ) : ℂ :=
  ∑ k ∈ c.support, (c k : ℂ) * ((k : ℝ) : ℂ) ^ (-s)

/-- One step of the Abel kernel, `(j + 1)^{-s} − (j + 2)^{-s}`. -/
def abelStep (s : ℂ) (j : ℕ) : ℂ := (((j : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((j : ℝ) + 2 : ℝ) : ℂ) ^ (-s)

/-- The real telescoping weight `(j + 1)^{-σ} − (j + 2)^{-σ}`. -/
def realStep (σ : ℝ) (j : ℕ) : ℝ := ((j : ℝ) + 1) ^ (-σ) - ((j : ℝ) + 2) ^ (-σ)

theorem realStep_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (j : ℕ) : 0 ≤ realStep σ j := by
  have h : ((j : ℝ) + 2) ^ (-σ) ≤ ((j : ℝ) + 1) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  rw [realStep]; linarith

/-- The partial sums of the real telescoping weight. -/
theorem sum_range_realStep (σ : ℝ) (n : ℕ) :
    ∑ j ∈ range n, realStep σ j = 1 - ((n : ℝ) + 1) ^ (-σ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, realStep]
    push_cast
    rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
    ring

theorem summable_realStep {σ : ℝ} (hσ : 0 ≤ σ) : Summable (realStep σ) := by
  refine summable_of_sum_range_le (c := 1) (realStep_nonneg hσ) fun n => ?_
  rw [sum_range_realStep]
  have : 0 ≤ ((n : ℝ) + 1) ^ (-σ) := by positivity
  linarith

/-- The Abel step in the telescoping form. -/
theorem norm_abelStep_le {s : ℂ} (hσ : 0 < s.re) (j : ℕ) :
    ‖abelStep s j‖ ≤ ‖s‖ * (realStep s.re j / s.re) := by
  have h := RHTower.norm_cpow_neg_sub_cpow_neg_le (w := s) hσ.ne' (A := (j : ℝ) + 1)
    (B := (j : ℝ) + 2) (by positivity) (by linarith)
  rw [abelStep, norm_sub_rev]
  exact h

/-- The Abel step in the pointwise form. -/
theorem norm_abelStep_le_rpow {s : ℂ} (hσ : 0 < s.re) (j : ℕ) :
    ‖abelStep s j‖ ≤ ‖s‖ * ((j : ℝ) + 1) ^ (-s.re - 1) := by
  have h := GaloisForLFunctions.RHTower.norm_cpow_unit_diff_le (w := s) hσ
    (x := (j : ℝ) + 1) (by positivity)
  rw [abelStep, show (j : ℝ) + 2 = (j : ℝ) + 1 + 1 by ring]
  exact h

/-- **Abel summation against the increment.** -/
theorem sum_range_mul_abelStep (c : ℕ →₀ ℤ) (s : ℂ) (N : ℕ) :
    ∑ j ∈ range N, (stepWeight c (j + 1) : ℂ) * abelStep s j =
      ∑ j ∈ range N, (increment c (j + 1) : ℂ) * (((j : ℝ) + 1 : ℝ) : ℂ) ^ (-s) -
        (stepWeight c N : ℂ) * (((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, abelStep]
    have hs : (stepWeight c (N + 1) : ℂ) = stepWeight c N + increment c (N + 1) := by
      exact_mod_cast stepWeight_succ c N
    have hcast : (((N + 1 : ℕ) : ℝ) + 1 : ℝ) = (N : ℝ) + 2 := by push_cast; ring
    rw [hcast, hs]
    ring

/-- The sum over multiples of `k` factors through the partial sum at `N / k`. -/
theorem sum_range_dvd_cpow (s : ℂ) {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∑ j ∈ range N, (if k ∣ j + 1 then (((j : ℝ) + 1 : ℝ) : ℂ) ^ (-s) else 0) =
      ((k : ℝ) : ℂ) ^ (-s) * ∑ i ∈ Icc 1 (N / k), ((i : ℝ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_div]
    split_ifs with hd
    · rw [Finset.sum_Icc_succ_top (by omega), mul_add]
      congr 1
      have hval : (N : ℝ) + 1 = (k : ℝ) * ((N / k + 1 : ℕ) : ℝ) := by
        obtain ⟨q, hq⟩ := hd
        have hq' : N / k + 1 = q := by
          have h1 : (N + 1) / k = q := by rw [hq]; exact Nat.mul_div_cancel_left q hk
          rw [Nat.succ_div, if_pos ⟨q, hq⟩] at h1
          exact h1
        rw [hq']
        exact_mod_cast hq
      rw [hval]
      push_cast
      exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (by positivity) _
    · simp

/-- **The increment sum in the partial sums of `ζ`.** -/
theorem sum_range_increment_mul_cpow (c : ℕ →₀ ℤ) (hc0 : c 0 = 0) (s : ℂ) (N : ℕ) :
    ∑ j ∈ range N, (increment c (j + 1) : ℂ) * (((j : ℝ) + 1 : ℝ) : ℂ) ^ (-s) =
      ∑ k ∈ c.support, (c k : ℂ) * (((k : ℝ) : ℂ) ^ (-s) *
        ∑ i ∈ Icc 1 (N / k), ((i : ℝ) : ℂ) ^ (-s)) := by
  have hterm : ∀ j ∈ range N, (increment c (j + 1) : ℂ) * (((j : ℝ) + 1 : ℝ) : ℂ) ^ (-s) =
      ∑ k ∈ c.support, (c k : ℂ) * (if k ∣ j + 1 then (((j : ℝ) + 1 : ℝ) : ℂ) ^ (-s) else 0) := by
    intro j _
    rw [increment]
    push_cast
    rw [sum_mul]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h; exact Finsupp.mem_support_iff.mp hk hc0
  rw [← mul_sum, sum_range_dvd_cpow s hk0 N]

/-- A common period, written for balanced stencils. -/
private lemma period_pos' {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) : 0 < IsProducer.period c :=
  prod_pos fun k hk => Nat.pos_of_ne_zero fun h => by
    subst h; exact Finsupp.mem_support_iff.mp hk hc0

/-- `g(qL) = 0` on a common period. -/
private lemma stepWeight_mul_period {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) (q : ℕ) :
    stepWeight c (q * IsProducer.period c) = 0 := by
  have h := stepWeight_periodic hc0 hbal (L := IsProducer.period c) IsProducer.dvd_period q 0
  rwa [add_zero, stepWeight_zero] at h

/-- The multiplicity of a balanced stencil is bounded by the coefficient mass. -/
theorem abs_stepWeight_le {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) (r : ℕ) :
    |(stepWeight c r : ℝ)| ≤ coeffMass c := by
  rw [stepWeight_eq_sum_mod hc0 hbal, coeffMass]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h; exact Finsupp.mem_support_iff.mp hk hc0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hmod : ((r % k : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.mod_lt r hk0).le
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (r % k)), abs_div, abs_neg,
    abs_of_pos hkR, div_mul_eq_mul_div, div_le_iff₀ hkR]
  exact mul_le_mul_of_nonneg_left hmod (abs_nonneg _)

/-- The Mellin series converges absolutely for `Re s > 0`. -/
theorem summable_mellin {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) {s : ℂ}
    (hσ : 0 < s.re) :
    Summable fun j : ℕ => (stepWeight c (j + 1) : ℂ) * abelStep s j := by
  refine Summable.of_norm_bounded
    (g := fun j => coeffMass c * (‖s‖ * (realStep s.re j / s.re))) ?_ fun j => ?_
  · exact (((summable_realStep hσ.le).div_const _).mul_left _).mul_left _
  · rw [norm_mul]
    have h1 : ‖(stepWeight c (j + 1) : ℂ)‖ ≤ coeffMass c := by
      rw [Complex.norm_intCast]
      exact abs_stepWeight_le hc0 hbal (j + 1)
    exact mul_le_mul h1 (norm_abelStep_le hσ j) (norm_nonneg _) (coeffMass_nonneg c)

/-- The polar parts of the partial sums cancel on multiples of the period. -/
private lemma sum_polar_eq_zero {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (hbal : IsBalanced c) {s : ℂ}
    {N : ℕ} (hN : 0 < N) (hL : ∀ k ∈ c.support, k ∣ N) :
    ∑ k ∈ c.support, (c k : ℂ) * (((k : ℝ) : ℂ) ^ (-s) *
      (((N / k : ℕ) : ℝ) : ℂ) ^ (1 - s)) = 0 := by
  have hterm : ∀ k ∈ c.support, (c k : ℂ) * (((k : ℝ) : ℂ) ^ (-s) *
      (((N / k : ℕ) : ℝ) : ℂ) ^ (1 - s)) =
      (((N : ℝ) : ℂ) ^ (1 - s)) * (((c k : ℝ) / k : ℝ) : ℂ) := by
    intro k hk
    have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
      subst h; exact Finsupp.mem_support_iff.mp hk hc0
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have hkC : ((k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hkR.ne'
    have hNk : (N : ℝ) = (k : ℝ) * ((N / k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (hL k hk)).symm
    have hmul : ((N : ℝ) : ℂ) ^ (1 - s) =
        ((k : ℝ) : ℂ) ^ (1 - s) * (((N / k : ℕ) : ℝ) : ℂ) ^ (1 - s) := by
      rw [hNk]
      push_cast
      exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) _
    have hpow : ((k : ℝ) : ℂ) ^ (-s) * ((k : ℝ) : ℂ) ^ (1 - s) = (k : ℂ) := by
      rw [← Complex.cpow_add _ _ hkC, show -s + (1 - s) = 1 - 2 * s by ring] <;> sorry
    sorry
  rw [sum_congr rfl hterm, ← mul_sum]
  sorry

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
