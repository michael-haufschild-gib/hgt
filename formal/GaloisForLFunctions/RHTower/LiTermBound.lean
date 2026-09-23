import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

/-!
# The paired Li summand

Li's coefficients are `λ_n = Σ_ρ [1 - (1-1/ρ)^n]`, a sum that converges only after the zeros are
paired.  Writing `w := 1 - 1/ρ`, the involution `ρ ↦ 1 - ρ` sends `w ↦ w⁻¹`, so the *paired*
summand is

`liTerm w n = 2 - wⁿ - w⁻ⁿ = -w⁻ⁿ (wⁿ - 1)²`,

and `Σ_ρ liTerm (w_ρ) n = 2 λ_n` for a divisor symmetric under `ρ ↦ 1-ρ`.  Unlike Li's own
summand this one is `O(n² Mⁿ |w-1|²)`, so the sum converges absolutely as soon as
`Σ_ρ |ρ|⁻² < ∞`.

On the unit circle `w⁻¹ = conj w`, so `liTerm w n = 2 - 2 Re(wⁿ) ≥ 0`: that is the easy half of
Li's criterion.
-/

open Complex Finset

namespace RHTower

/-- The paired Li summand `2 - wⁿ - w⁻ⁿ`. -/
def liTerm (w : ℂ) (n : ℕ) : ℂ := 2 - w ^ n - (w⁻¹) ^ n

@[simp] theorem liTerm_zero (w : ℂ) : liTerm w 0 = 0 := by
  simp only [liTerm, pow_zero]
  norm_num

/-- The summand is `-w⁻ⁿ (wⁿ - 1)²`: a perfect square up to the unimodular factor. -/
theorem liTerm_eq_neg_mul_sq {w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    liTerm w n = -((w⁻¹) ^ n * (w ^ n - 1) ^ (2 : ℕ)) := by
  have hwn : (w ^ n) ≠ 0 := pow_ne_zero n hw
  have hp : (w⁻¹) ^ n = (w ^ n)⁻¹ := inv_pow w n
  rw [liTerm, hp]
  field_simp
  ring

/-- The summand is invariant under `w ↦ w⁻¹`, which is the involution `ρ ↦ 1 - ρ`. -/
theorem liTerm_inv (w : ℂ) (n : ℕ) : liTerm w⁻¹ n = liTerm w n := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [liTerm]
  · rw [liTerm, liTerm, inv_inv]
    ring

/-- On the unit circle the summand is `2 - 2 Re(wⁿ)`, hence a nonnegative real. -/
theorem liTerm_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) (n : ℕ) :
    liTerm w n = ((2 - 2 * (w ^ n).re : ℝ) : ℂ) := by
  have h := Complex.mul_conj w
  have hn : (Complex.normSq w : ℂ) = 1 := by
    rw [← Complex.sq_norm, hw]
    norm_num
  rw [hn] at h
  have hinv : w⁻¹ = (starRingEnd ℂ) w := inv_eq_of_mul_eq_one_right h
  have hre : ((starRingEnd ℂ) w ^ n).re = (w ^ n).re := by
    rw [← map_pow, Complex.conj_re]
  have him : ((starRingEnd ℂ) w ^ n).im = -(w ^ n).im := by
    rw [← map_pow, Complex.conj_im]
  rw [liTerm, hinv]
  refine Complex.ext ?_ ?_
  · simp [hre]
    ring
  · simp [him]

theorem re_liTerm_nonneg_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) (n : ℕ) :
    0 ≤ (liTerm w n).re := by
  rw [liTerm_of_norm_eq_one hw n, Complex.ofReal_re]
  have h1 : (w ^ n).re ≤ ‖w ^ n‖ := Complex.re_le_norm _
  have h2 : ‖w ^ n‖ = 1 := by rw [norm_pow, hw, one_pow]
  linarith


/-! ## The size of the paired summand -/


/-- The geometric factor `(max 1 a)² / a` is exactly `max a a⁻¹`, bounded by it in particular. -/
theorem inv_mul_max_sq_le_max {a : ℝ} (ha : 0 < a) :
    a⁻¹ * max 1 a ^ (2 : ℕ) ≤ max a a⁻¹ := by
  rcases le_or_gt 1 a with h | h
  · rw [max_eq_right h]
    have : a⁻¹ * a ^ (2 : ℕ) = a := by field_simp
    rw [this]
    exact le_max_left _ _
  · rw [max_eq_left h.le, one_pow, mul_one]
    exact le_max_right _ _

/-- `‖wⁿ - 1‖ ≤ n (max 1 ‖w‖)ⁿ ‖w - 1‖`. -/
theorem norm_pow_sub_one_le (w : ℂ) (n : ℕ) :
    ‖w ^ n - 1‖ ≤ (n : ℝ) * max 1 ‖w‖ ^ n * ‖w - 1‖ := by
  have hgeom : (∑ k ∈ Finset.range n, w ^ k) * (w - 1) = w ^ n - 1 := geom_sum_mul w n
  have hsum : ‖∑ k ∈ Finset.range n, w ^ k‖ ≤ (n : ℝ) * max 1 ‖w‖ ^ n := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ k ∈ Finset.range n, ‖w ^ k‖ ≤ max 1 ‖w‖ ^ n := by
      intro k hk
      rw [norm_pow]
      have h1 : ‖w‖ ^ k ≤ max 1 ‖w‖ ^ k :=
        pow_le_pow_left₀ (norm_nonneg w) (le_max_right _ _) k
      have h2 : max 1 ‖w‖ ^ k ≤ max 1 ‖w‖ ^ n :=
        pow_le_pow_right₀ (le_max_left _ _) (le_of_lt (Finset.mem_range.mp hk))
      linarith
    calc ∑ k ∈ Finset.range n, ‖w ^ k‖
        ≤ ∑ _k ∈ Finset.range n, max 1 ‖w‖ ^ n := Finset.sum_le_sum hterm
      _ = (n : ℝ) * max 1 ‖w‖ ^ n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ‖w ^ n - 1‖ = ‖∑ k ∈ Finset.range n, w ^ k‖ * ‖w - 1‖ := by
        rw [← hgeom, norm_mul]
    _ ≤ ((n : ℝ) * max 1 ‖w‖ ^ n) * ‖w - 1‖ := by
        exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

/-- **The paired Li summand is `O(n² Mⁿ ‖w-1‖²)`**, with `M = max(‖w‖, ‖w‖⁻¹)`. -/
theorem norm_liTerm_le {w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    ‖liTerm w n‖ ≤ (n : ℝ) ^ (2 : ℕ) * max ‖w‖ ‖w‖⁻¹ ^ n * ‖w - 1‖ ^ (2 : ℕ) := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hmax : 0 ≤ max 1 ‖w‖ := le_trans zero_le_one (le_max_left _ _)
  rw [liTerm_eq_neg_mul_sq hw n, norm_neg, norm_mul, norm_pow, norm_pow, norm_inv]
  have h1 : ‖w ^ n - 1‖ ^ (2 : ℕ) ≤ ((n : ℝ) * max 1 ‖w‖ ^ n * ‖w - 1‖) ^ (2 : ℕ) := by
    have := norm_pow_sub_one_le w n
    have hnn : (0:ℝ) ≤ ‖w ^ n - 1‖ := norm_nonneg _
    nlinarith
  have h2 : ‖w‖⁻¹ ^ n * ‖w ^ n - 1‖ ^ (2 : ℕ)
      ≤ ‖w‖⁻¹ ^ n * ((n : ℝ) * max 1 ‖w‖ ^ n * ‖w - 1‖) ^ (2 : ℕ) := by
    have : (0:ℝ) ≤ ‖w‖⁻¹ ^ n := by positivity
    exact mul_le_mul_of_nonneg_left h1 this
  refine le_trans h2 ?_
  have hgeo : ‖w‖⁻¹ ^ n * (max 1 ‖w‖ ^ n) ^ (2 : ℕ) ≤ max ‖w‖ ‖w‖⁻¹ ^ n := by
    have hfac : ‖w‖⁻¹ ^ n * (max 1 ‖w‖ ^ n) ^ (2 : ℕ)
        = (‖w‖⁻¹ * max 1 ‖w‖ ^ (2 : ℕ)) ^ n := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      ring
    rw [hfac]
    exact pow_le_pow_left₀ (by positivity) (inv_mul_max_sq_le_max hpos) n
  have hexp : ‖w‖⁻¹ ^ n * ((n : ℝ) * max 1 ‖w‖ ^ n * ‖w - 1‖) ^ (2 : ℕ)
      = ((n : ℝ) ^ (2 : ℕ) * ‖w - 1‖ ^ (2 : ℕ)) * (‖w‖⁻¹ ^ n * (max 1 ‖w‖ ^ n) ^ (2 : ℕ)) := by ring
  rw [hexp]
  have hnn : (0:ℝ) ≤ (n : ℝ) ^ (2 : ℕ) * ‖w - 1‖ ^ (2 : ℕ) := by positivity
  calc ((n : ℝ) ^ (2 : ℕ) * ‖w - 1‖ ^ (2 : ℕ)) * (‖w‖⁻¹ ^ n * (max 1 ‖w‖ ^ n) ^ (2 : ℕ))
      ≤ ((n : ℝ) ^ (2 : ℕ) * ‖w - 1‖ ^ (2 : ℕ)) * max ‖w‖ ‖w‖⁻¹ ^ n :=
        mul_le_mul_of_nonneg_left hgeo hnn
    _ = (n : ℝ) ^ (2 : ℕ) * max ‖w‖ ‖w‖⁻¹ ^ n * ‖w - 1‖ ^ (2 : ℕ) := by ring

/-! ## Absolute convergence of the paired Li sum -/

/-- **The paired Li sum converges absolutely.**  A family of `w`'s with a common bound on
`max(‖w‖, ‖w‖⁻¹)` and with `Σ ‖w - 1‖² < ∞` gives an absolutely summable family of Li summands at
every order. -/
theorem summable_liTerm {ι : Type*} {w : ι → ℂ} {M : ℝ}
    (hw : ∀ i, w i ≠ 0) (hb : ∀ i, max ‖w i‖ ‖w i‖⁻¹ ≤ M)
    (hs : Summable fun i => ‖w i - 1‖ ^ (2 : ℕ)) (n : ℕ) :
    Summable fun i => liTerm (w i) n := by
  refine Summable.of_norm_bounded (hs.mul_left ((n : ℝ) ^ (2 : ℕ) * M ^ n)) fun i => ?_
  refine le_trans (norm_liTerm_le (hw i) n) ?_
  have hM0 : (0 : ℝ) ≤ max ‖w i‖ ‖w i‖⁻¹ := le_trans (norm_nonneg _) (le_max_left _ _)
  have h1 : max ‖w i‖ ‖w i‖⁻¹ ^ n ≤ M ^ n := pow_le_pow_left₀ hM0 (hb i) n
  rw [mul_assoc, mul_assoc]
  gcongr

/-- **The easy half of Li's criterion.**  If every `w` is unimodular then every paired Li sum is a
nonnegative real. -/
theorem re_tsum_liTerm_nonneg {ι : Type*} {w : ι → ℂ}
    (hw : ∀ i, ‖w i‖ = 1) (hsum : Summable fun i => liTerm (w i) n) :
    0 ≤ (∑' i, liTerm (w i) n).re := by
  rw [Complex.re_tsum hsum]
  exact tsum_nonneg fun i => re_liTerm_nonneg_of_norm_eq_one (hw i) n

end RHTower
