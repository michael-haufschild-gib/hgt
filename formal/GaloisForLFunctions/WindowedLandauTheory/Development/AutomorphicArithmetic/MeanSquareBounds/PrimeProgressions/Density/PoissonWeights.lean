import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Poisson coefficients and their small-argument and large-argument bounds. -/

noncomputable section

namespace QH.PrimeProgressions

def pw (k : ℕ) (u : ℝ) : ℝ := u ^ k / (k.factorial : ℝ) * Real.exp (-u)

lemma pw_nonneg (k : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ pw k u := by
  unfold pw; positivity

lemma pw_le (k : ℕ) {u θ : ℝ} (hu : 0 ≤ u) (hθ : 0 < θ) :
    pw k u ≤ θ ^ k * Real.exp (u / θ - u) := by
  have h := Real.pow_div_factorial_le_exp (u / θ) (by positivity) k
  have e : pw k u = θ ^ k * ((u / θ) ^ k / (k.factorial : ℝ) * Real.exp (-u)) := by
    unfold pw; rw [div_pow]; field_simp
  rw [e, sub_eq_add_neg, Real.exp_add]
  gcongr

lemma pw_le_one (k : ℕ) {u : ℝ} (hu : 0 ≤ u) : pw k u ≤ 1 := by
  simpa using pw_le k hu one_pos

lemma pw_small (K k : ℕ) {u δ : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u) (h : u ≤ δ / 3 * K) (hK : K ≤ k) :
    pw k u ≤ δ ^ k * Real.exp (-(u / 2)) := by
  have h1 := pw_le k hu (θ := δ / 3) (by positivity)
  have h2 : u / (δ / 3) ≤ k := by
    rw [div_le_iff₀ (by positivity)]
    have : (K : ℝ) ≤ k := by exact_mod_cast hK
    nlinarith
  have h3 : Real.exp (u / (δ / 3) - u) ≤ 3 ^ k * Real.exp (-(u / 2)) := by
    have h4 : Real.exp k ≤ 3 ^ k := by
      rw [← mul_one (k : ℝ), Real.exp_nat_mul]
      gcongr
      exact (Real.exp_one_lt_d9.trans (by norm_num)).le
    calc _ ≤ Real.exp (k + -(u / 2)) := by gcongr; linarith
      _ ≤ _ := by rw [Real.exp_add]; gcongr
  calc _ ≤ (δ / 3) ^ k * (3 ^ k * Real.exp (-(u / 2))) := h1.trans (by gcongr)
    _ = _ := by rw [div_pow]; field_simp

lemma pw_large (K k : ℕ) {u δ : ℝ} (hδ : 0 < δ) (h : 32 / δ * K ≤ u) (hK : k ≤ 2 * K) :
    pw k u ≤ δ ^ k * Real.exp (-(u / 2)) := by
  have hu : 0 ≤ u := le_trans (by positivity) h
  have h1 := pw_le k hu (θ := 4) (by positivity)
  have hK' : (k : ℝ) ≤ 2 * K := by exact_mod_cast hK
  have h2 : (4 / δ) ^ k ≤ Real.exp (u / 4) := by
    calc (4 / δ) ^ k ≤ Real.exp (4 / δ) ^ k := by
          gcongr; linarith [Real.add_one_le_exp (4 / δ)]
      _ = Real.exp (k * (4 / δ)) := by rw [Real.exp_nat_mul]
      _ ≤ _ := by
          gcongr
          have : k * (4 / δ) ≤ 2 * K * (4 / δ) := by gcongr
          have e : 32 / δ * K = 4 * (2 * K * (4 / δ)) := by ring
          linarith
  have e : Real.exp (-(u / 2)) = Real.exp (u / 4) * Real.exp (u / 4 - u) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ ≤ _ := h1
    _ = δ ^ k * ((4 / δ) ^ k * Real.exp (u / 4 - u)) := by rw [div_pow]; field_simp
    _ ≤ _ := by rw [e]; gcongr

lemma pw_pp (k : ℕ) {v r : ℝ} (hr : 0 < r) (hv : 0 ≤ v) :
    pw k (r * v) ≤ (4 * r) ^ k * Real.exp (v / 4) := by
  have h1 := pw_le k (u := r * v) (by positivity) (θ := 4 * r) (by positivity)
  refine h1.trans ?_
  have : r * v / (4 * r) = v / 4 := by field_simp
  rw [this]
  gcongr
  have : 0 ≤ r * v := by positivity
  linarith

lemma hasDerivAt_pw (m : ℕ) (u : ℝ) : HasDerivAt (pw (m + 1)) (pw m u - pw (m + 1) u) u := by
  have h1 := ((hasDerivAt_pow (m + 1) u).div_const ((m + 1).factorial : ℝ)).mul
    (hasDerivAt_neg u).exp
  refine HasDerivAt.congr_deriv (f := pw (m + 1)) h1 ?_
  unfold pw
  rw [Nat.factorial_succ]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

lemma continuous_pw (k : ℕ) : Continuous (pw k) := by
  unfold pw; fun_prop

end QH.PrimeProgressions
