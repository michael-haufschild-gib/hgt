import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Harmonic diagonal sums with a smooth cutoff

Let `φ : ℝ → ℂ` be a cutoff with `‖φ(y)‖ ≤ A/y` and `‖φ(y) − 1‖ ≤ A y^{1/4}` for `y > 0`. For
`N, X > 0` the diagonal sum

`Σ_{j ≥ 1} j^{−1} φ(N j²/X)`

equals `½ log(X/N)` up to `1 + 4A` when `N ≤ X` (`norm_diagSum_sub_half_log_le`), and is at most
`2A` when `N > X` (`norm_diagSum_le_of_lt`). In the approximate functional equation the cutoff
restricts `j` to `j ≲ √(X/N)`, and the sum is the harmonic number there.

**Proof.** Put `y = √(X/N)` and `J = ⌊y⌋`.
- The head `j ≤ J` is `H_J` minus `Σ j^{−1}(1 − φ)`. The latter is at most
  `A y^{−1/2} Σ_{j ≤ J} j^{−1/2} ≤ 2A`.
- The tail `j > J` is at most `A y² Σ_{j > J} j^{−3} ≤ 2A`.
- `log y ≤ H_J ≤ 1 + log y`.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Finset

/-- The harmonic diagonal sum `Σ_{j ≥ 1} j^{−1} φ(N j²/X)`. -/
def diagSum (φ : ℝ → ℂ) (N X : ℝ) : ℂ :=
  ∑' j : ℕ, (((j + 1 : ℝ))⁻¹ : ℂ) * φ (N * (j + 1 : ℝ) ^ 2 / X)

/-- `Σ_{j < J} (j+1)^{−1/2} ≤ 2√J`. -/
theorem sum_range_inv_sqrt_le (J : ℕ) :
    ∑ j ∈ range J, (Real.sqrt (j + 1))⁻¹ ≤ 2 * Real.sqrt J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ]
    have hJ1 : (0 : ℝ) < Real.sqrt ((J : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hstep : (Real.sqrt ((J : ℝ) + 1))⁻¹ ≤ 2 * Real.sqrt ((J : ℝ) + 1) - 2 * Real.sqrt J := by
      have hsq : Real.sqrt ((J : ℝ) + 1) ^ 2 = (J : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have hsq' : Real.sqrt (J : ℝ) ^ 2 = J := Real.sq_sqrt (by positivity)
      have hle : Real.sqrt (J : ℝ) ≤ Real.sqrt ((J : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
      have h0 : 0 ≤ Real.sqrt (J : ℝ) := Real.sqrt_nonneg _
      rw [inv_eq_one_div, div_le_iff₀ hJ1]
      nlinarith
    push_cast
    linarith

/-- `Σ_{J < j ≤ M} j^{−3} ≤ 1/(2J²)` for `J ≥ 1`. -/
theorem sum_Ico_inv_cube_le {J : ℕ} (hJ : 1 ≤ J) (M : ℕ) :
    ∑ j ∈ range M, ((j + J + 1 : ℝ) ^ 3)⁻¹ ≤ 1 / (2 * (J : ℝ) ^ 2) := by
  have hstep : ∀ j : ℕ, ((j + J + 1 : ℝ) ^ 3)⁻¹ ≤
      1 / (2 * ((j : ℝ) + J) ^ 2) - 1 / (2 * ((j : ℝ) + J + 1) ^ 2) := by
    intro j
    have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have ha : (0 : ℝ) < (j : ℝ) + J := by positivity
    have hb : (0 : ℝ) < (j : ℝ) + J + 1 := by positivity
    rw [show 1 / (2 * ((j : ℝ) + J) ^ 2) - 1 / (2 * ((j : ℝ) + J + 1) ^ 2) =
      (2 * ((j : ℝ) + J) + 1) / (2 * ((j : ℝ) + J) ^ 2 * ((j : ℝ) + J + 1) ^ 2) by
        field_simp; ring]
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hx : (0 : ℝ) ≤ (j : ℝ) + J := ha.le
    nlinarith [mul_nonneg hx hx, mul_nonneg (mul_nonneg hx hx) hx]
  calc ∑ j ∈ range M, ((j + J + 1 : ℝ) ^ 3)⁻¹
      ≤ ∑ j ∈ range M, (1 / (2 * ((j : ℝ) + J) ^ 2) - 1 / (2 * ((j : ℝ) + J + 1) ^ 2)) :=
        sum_le_sum fun j _ => hstep j
    _ = 1 / (2 * (J : ℝ) ^ 2) - 1 / (2 * ((M : ℝ) + J) ^ 2) := by
        have := sum_range_sub' (fun j : ℕ => 1 / (2 * ((j : ℝ) + J) ^ 2)) M
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] at this
        rw [← this]
        refine sum_congr rfl fun j _ => ?_
        ring
    _ ≤ 1 / (2 * (J : ℝ) ^ 2) := by
        have : 0 ≤ 1 / (2 * ((M : ℝ) + J) ^ 2) := by positivity
        linarith

theorem summable_inv_cube_shift (J : ℕ) :
    Summable (fun j : ℕ => ((j + J + 1 : ℝ) ^ 3)⁻¹) := by
  have h := (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 3)).comp_injective
    (add_left_injective (J + 1))
  refine h.congr fun j => ?_
  simp only [Function.comp_apply]
  push_cast
  ring_nf

theorem tsum_inv_cube_shift_le {J : ℕ} (hJ : 1 ≤ J) :
    ∑' j : ℕ, ((j + J + 1 : ℝ) ^ 3)⁻¹ ≤ 1 / (2 * (J : ℝ) ^ 2) :=
  Real.tsum_le_of_sum_range_le (fun j => by positivity) (sum_Ico_inv_cube_le hJ)

theorem tsum_inv_cube_le_two : ∑' j : ℕ, ((j + 1 : ℝ) ^ 3)⁻¹ ≤ 2 := by
  have hs : Summable (fun j : ℕ => ((j + 1 : ℝ) ^ 3)⁻¹) := by
    simpa using summable_inv_cube_shift 0
  rw [← hs.sum_add_tsum_nat_add 1]
  have htail := tsum_inv_cube_shift_le (J := 1) le_rfl
  have heq : ∑' j : ℕ, ((((j + 1 : ℕ) : ℝ) + 1) ^ 3)⁻¹ =
      ∑' j : ℕ, (((j : ℝ) + ((1 : ℕ) : ℝ) + 1) ^ 3)⁻¹ := by
    congr 1
    funext j
    push_cast
    ring
  rw [heq]
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_add, one_pow, inv_one]
  norm_num at htail ⊢
  linarith

variable {φ : ℝ → ℂ} {A : ℝ}

/-- Termwise envelope and summability of the diagonal sum. -/
theorem norm_diagSum_term_le (hφ1 : ∀ y > 0, ‖φ y‖ ≤ A / y) {N X : ℝ} (hN : 0 < N) (hX : 0 < X)
    (j : ℕ) :
    ‖(((j + 1 : ℝ))⁻¹ : ℂ) * φ (N * (j + 1 : ℝ) ^ 2 / X)‖ ≤ A * (X / N) * ((j + 1 : ℝ) ^ 3)⁻¹ := by
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hj]
  have hy : 0 < N * ((j : ℝ) + 1) ^ 2 / X := by positivity
  have hb := hφ1 _ hy
  calc ((j : ℝ) + 1)⁻¹ * ‖φ (N * ((j : ℝ) + 1) ^ 2 / X)‖
      ≤ ((j : ℝ) + 1)⁻¹ * (A / (N * ((j : ℝ) + 1) ^ 2 / X)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = A * (X / N) * (((j : ℝ) + 1) ^ 3)⁻¹ := by
        field_simp

theorem summable_diagSum (hφ1 : ∀ y > 0, ‖φ y‖ ≤ A / y) {N X : ℝ} (hN : 0 < N)
    (hX : 0 < X) :
    Summable (fun j : ℕ => (((j + 1 : ℝ))⁻¹ : ℂ) * φ (N * (j + 1 : ℝ) ^ 2 / X)) := by
  refine Summable.of_norm_bounded (g := fun j : ℕ => A * (X / N) * ((j + 1 : ℝ) ^ 3)⁻¹) ?_
    (fun j => norm_diagSum_term_le hφ1 hN hX j)
  have hs : Summable (fun j : ℕ => ((j + 1 : ℝ) ^ 3)⁻¹) := by
    simpa using summable_inv_cube_shift 0
  exact hs.mul_left _

/-- **Large `N`**: the diagonal sum is at most `2A·X/N`. -/
theorem norm_diagSum_le_of_lt (hA : 0 ≤ A) (hφ1 : ∀ y > 0, ‖φ y‖ ≤ A / y) {N X : ℝ} (hN : 0 < N)
    (hX : 0 < X) : ‖diagSum φ N X‖ ≤ 2 * A * (X / N) := by
  unfold diagSum
  have hs : Summable (fun j : ℕ => ((j + 1 : ℝ) ^ 3)⁻¹) := by
    simpa using summable_inv_cube_shift 0
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact (summable_diagSum hφ1 hN hX).norm
  · calc ∑' j : ℕ, ‖(((j + 1 : ℝ))⁻¹ : ℂ) * φ (N * (j + 1 : ℝ) ^ 2 / X)‖
        ≤ ∑' j : ℕ, A * (X / N) * ((j + 1 : ℝ) ^ 3)⁻¹ :=
          (summable_diagSum hφ1 hN hX).norm.tsum_le_tsum (fun j => norm_diagSum_term_le hφ1 hN hX j)
            (hs.mul_left _)
      _ = A * (X / N) * ∑' j : ℕ, ((j + 1 : ℝ) ^ 3)⁻¹ := tsum_mul_left
      _ ≤ A * (X / N) * 2 := mul_le_mul_of_nonneg_left tsum_inv_cube_le_two (by positivity)
      _ = 2 * A * (X / N) := by ring

/-- **The harmonic main term**: for `0 < N ≤ X`, `‖Σ j^{−1} φ(Nj²/X) − ½ log(X/N)‖ ≤ 1 + 4A`. -/
theorem norm_diagSum_sub_half_log_le (hA : 0 ≤ A) (hφ1 : ∀ y > 0, ‖φ y‖ ≤ A / y)
    (hφ2 : ∀ y > 0, ‖φ y - 1‖ ≤ A * y ^ (1 / 4 : ℝ)) {N X : ℝ} (hN : 0 < N) (hNX : N ≤ X) :
    ‖diagSum φ N X - ((Real.log (X / N) / 2 : ℝ) : ℂ)‖ ≤ 1 + 4 * A := by
  have hX : 0 < X := lt_of_lt_of_le hN hNX
  set y : ℝ := Real.sqrt (X / N) with hy
  have hXN : 1 ≤ X / N := (one_le_div hN).mpr hNX
  have hy1 : 1 ≤ y := by rw [hy]; exact Real.one_le_sqrt.mpr hXN
  have hy0 : 0 < y := by linarith
  have hy2 : y ^ 2 = X / N := Real.sq_sqrt (by linarith)
  set J : ℕ := ⌊y⌋₊ with hJ
  have hJ1 : 1 ≤ J := Nat.le_floor (by exact_mod_cast hy1)
  have hJy : (J : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyJ : y < J + 1 := Nat.lt_floor_add_one y
  have hs := summable_diagSum hφ1 hN hX
  set f : ℕ → ℂ := fun j => (((j + 1 : ℝ))⁻¹ : ℂ) * φ (N * (j + 1 : ℝ) ^ 2 / X) with hf
  unfold diagSum
  rw [← hs.sum_add_tsum_nat_add J]
  -- the head
  have hhead : ‖∑ j ∈ range J, f j - ((harmonic J : ℝ) : ℂ)‖ ≤ 2 * A := by
    have hH : ((harmonic J : ℝ) : ℂ) = ∑ j ∈ range J, (((j + 1 : ℝ))⁻¹ : ℂ) := by
      rw [harmonic]
      push_cast
      rfl
    rw [hH, ← sum_sub_distrib]
    calc ‖∑ j ∈ range J, (f j - (((j + 1 : ℝ))⁻¹ : ℂ))‖
        ≤ ∑ j ∈ range J, ‖f j - (((j + 1 : ℝ))⁻¹ : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range J, A / Real.sqrt y * (Real.sqrt (j + 1))⁻¹ := by
          refine sum_le_sum fun j _ => ?_
          have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
          have hyarg : N * ((j : ℝ) + 1) ^ 2 / X = (((j : ℝ) + 1) / y) ^ 2 := by
            rw [div_pow, hy2]
            field_simp
          simp only [hf]
          rw [show (((j + 1 : ℝ))⁻¹ : ℂ) * φ (N * (j + 1 : ℝ) ^ 2 / X) - (((j + 1 : ℝ))⁻¹ : ℂ)
              = (((j + 1 : ℝ))⁻¹ : ℂ) * (φ (N * (j + 1 : ℝ) ^ 2 / X) - 1) by ring,
            norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hj, hyarg]
          have hb := hφ2 _ (by positivity : 0 < N * ((j : ℝ) + 1) ^ 2 / X)
          rw [hyarg] at hb
          have hrpow : ((((j : ℝ) + 1) / y) ^ 2) ^ (1 / 4 : ℝ) = Real.sqrt (((j : ℝ) + 1) / y) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
          rw [hrpow] at hb
          calc ((j : ℝ) + 1)⁻¹ * ‖φ ((((j : ℝ) + 1) / y) ^ 2) - 1‖
              ≤ ((j : ℝ) + 1)⁻¹ * (A * Real.sqrt (((j : ℝ) + 1) / y)) :=
                mul_le_mul_of_nonneg_left hb (by positivity)
            _ = A / Real.sqrt y * (Real.sqrt ((j : ℝ) + 1) / ((j : ℝ) + 1)) := by
                rw [Real.sqrt_div' _ hy0.le]
                ring
            _ = A / Real.sqrt y * (Real.sqrt ((j : ℝ) + 1))⁻¹ := by
                rw [Real.sqrt_div_self', one_div]
      _ = A / Real.sqrt y * ∑ j ∈ range J, (Real.sqrt (j + 1))⁻¹ := by rw [mul_sum]
      _ ≤ A / Real.sqrt y * (2 * Real.sqrt J) :=
          mul_le_mul_of_nonneg_left (sum_range_inv_sqrt_le J) (by positivity)
      _ ≤ A / Real.sqrt y * (2 * Real.sqrt y) := by
          gcongr
      _ = 2 * A := by
          have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
          field_simp
  -- the tail
  have htail : ‖∑' j : ℕ, f (j + J)‖ ≤ 2 * A := by
    have hterm : ∀ j : ℕ, ‖f (j + J)‖ ≤ A * (X / N) * ((j + J + 1 : ℝ) ^ 3)⁻¹ := by
      intro j
      have h := norm_diagSum_term_le hφ1 hN hX (j + J)
      simp only [hf]
      push_cast at h ⊢
      exact h
    refine (norm_tsum_le_tsum_norm ((hs.comp_injective (add_left_injective J)).norm)).trans ?_
    calc ∑' j : ℕ, ‖f (j + J)‖ ≤ ∑' j : ℕ, A * (X / N) * ((j + J + 1 : ℝ) ^ 3)⁻¹ :=
          (hs.comp_injective (add_left_injective J)).norm.tsum_le_tsum hterm
            ((summable_inv_cube_shift J).mul_left _)
      _ = A * (X / N) * ∑' j : ℕ, ((j + J + 1 : ℝ) ^ 3)⁻¹ := tsum_mul_left
      _ ≤ A * (X / N) * (1 / (2 * (J : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (tsum_inv_cube_shift_le hJ1) (by positivity)
      _ ≤ 2 * A := by
          rw [← hy2]
          have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ1
          have hy2J : y ^ 2 ≤ 4 * (J : ℝ) ^ 2 := by
            have : y ≤ 2 * J := by
              have : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
              linarith
            nlinarith
          rw [show A * y ^ 2 * (1 / (2 * (J : ℝ) ^ 2)) = A * (y ^ 2 / (2 * (J : ℝ) ^ 2)) by ring]
          have hq : y ^ 2 / (2 * (J : ℝ) ^ 2) ≤ 2 := by
            rw [div_le_iff₀ (by positivity)]
            linarith
          nlinarith
  -- the harmonic number
  have hharm : |(harmonic J : ℝ) - Real.log (X / N) / 2| ≤ 1 := by
    have hlogy : Real.log y = Real.log (X / N) / 2 := by
      rw [hy, Real.log_sqrt (by linarith)]
    have h1 := log_le_harmonic_floor y hy0.le
    have h2 := harmonic_floor_le_one_add_log y hy1
    rw [← hJ] at h1 h2
    rw [abs_le]
    constructor <;> linarith
  calc ‖∑ j ∈ range J, f j + ∑' j : ℕ, f (j + J) - ((Real.log (X / N) / 2 : ℝ) : ℂ)‖
      = ‖(∑ j ∈ range J, f j - ((harmonic J : ℝ) : ℂ)) + ∑' j : ℕ, f (j + J) +
          (((harmonic J : ℝ) - Real.log (X / N) / 2 : ℝ) : ℂ)‖ := by
        congr 1
        push_cast
        ring
    _ ≤ ‖∑ j ∈ range J, f j - ((harmonic J : ℝ) : ℂ)‖ + ‖∑' j : ℕ, f (j + J)‖ +
          ‖(((harmonic J : ℝ) - Real.log (X / N) / 2 : ℝ) : ℂ)‖ := norm_add₃_le
    _ ≤ 2 * A + 2 * A + 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith
    _ = 1 + 4 * A := by ring

end RHTower.ZetaNotch
