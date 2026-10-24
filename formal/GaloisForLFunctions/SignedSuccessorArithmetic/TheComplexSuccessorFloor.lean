import GaloisForLFunctions.SignedSuccessorArithmetic.TheFloorIsAttainedAtConductorThree
import Mathlib.Analysis.Complex.Basic

/-!
# The complex successor floor

For a completely multiplicative `f : ℕ → ℂ` with `|f(n)| = 1` the successor phase is
`σ(n) = f̄(n) f(n+1)`, and the dilation cocycle at `m = 2` reads `σ(2n) σ(2n+1) = σ(n)`
(`unitSuccPhase_two_mul_mul`). For unit complex numbers `u, v`,

  `(Re u + Re v)² ≤ 2 (1 + Re(uv))`  (`sq_re_add_re_le`),

so a step with phase `σ(n)` forces `Re σ(2n) + Re σ(2n+1) ≥ −√(2(1 + Re σ(n)))`. Summed with the
weights `1/n` and Cauchy–Schwarz this gives the **complex floor**
`Σ_{n ≤ M} Re σ(n)/n ≥ −(1/2) log M − 3` (`complex_log_floor`). The conductor-three twins, viewed
as unimodular functions, have mean `−1/3`, so the complex floor lies in `[−1/2, −1/3]`.

The value `−1/2` would require `σ(n) ∈ {e^{±2πi/3}}` at every step, hence `f` with values in the
cube roots of unity and consecutive values distinct. Catalan's pair forbids it: `f(8) = f(2)³ = 1`,
and distinctness up to `4` forces `f(3) = 1`, so `f(9) = f(3)² = 1 = f(8)`
(`no_cubeRoot_successor_coloring`).
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open Finset

/-- A completely multiplicative function of modulus one on the positive integers. -/
structure CMUnit where
  /-- The function. -/
  toFun : ℕ → ℂ
  norm_eq_one' : ∀ {n : ℕ}, 0 < n → ‖toFun n‖ = 1
  map_one' : toFun 1 = 1
  map_mul' : ∀ {m n : ℕ}, 0 < m → 0 < n → toFun (m * n) = toFun m * toFun n

instance : CoeFun CMUnit (fun _ => ℕ → ℂ) := ⟨CMUnit.toFun⟩

/-- The successor phase `σ(n) = f̄(n) f(n+1)`. -/
noncomputable def unitSuccPhase (f : ℕ → ℂ) (n : ℕ) : ℂ := (starRingEnd ℂ) (f n) * f (n + 1)

theorem conj_mul_self_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : (starRingEnd ℂ) z * z = 1 := by
  rw [Complex.conj_mul', hz]; norm_num

/-- The dilation cocycle at `m = 2` for unit phases. -/
theorem unitSuccPhase_two_mul_mul (f : CMUnit) {n : ℕ} (hn : 0 < n) :
    unitSuccPhase f (2 * n) * unitSuccPhase f (2 * n + 1) = unitSuccPhase f n := by
  have h1 := conj_mul_self_of_norm_one (f.norm_eq_one' (n := 2 * n + 1) (by omega))
  have h2 := conj_mul_self_of_norm_one (f.norm_eq_one' (n := 2) (by norm_num))
  have e1 : f (2 * n) = f 2 * f n := f.map_mul' (by norm_num) hn
  have e2 : f (2 * n + 1 + 1) = f 2 * f (n + 1) := by
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring]; exact f.map_mul' (by norm_num) (by omega)
  simp only [unitSuccPhase]
  rw [e1, e2, map_mul]
  linear_combination ((starRingEnd ℂ) (f 2) * f 2 * (starRingEnd ℂ) (f n) * f (n + 1)) * h1 +
    ((starRingEnd ℂ) (f n) * f (n + 1)) * h2

theorem norm_unitSuccPhase (f : CMUnit) {n : ℕ} (hn : 0 < n) : ‖unitSuccPhase f n‖ = 1 := by
  rw [unitSuccPhase, norm_mul, Complex.norm_conj, f.norm_eq_one' hn, f.norm_eq_one' (by omega),
    one_mul]

/-- **Two unit vectors.** `(Re u + Re v)² ≤ 2 (1 + Re(uv))`. -/
theorem sq_re_add_re_le {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (u.re + v.re) ^ 2 ≤ 2 * (1 + (u * v).re) := by
  have hu2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have := Complex.normSq_eq_norm_sq u
    rw [hu, Complex.normSq_apply] at this; nlinarith
  have hv2 : v.re ^ 2 + v.im ^ 2 = 1 := by
    have := Complex.normSq_eq_norm_sq v
    rw [hv, Complex.normSq_apply] at this; nlinarith
  rw [Complex.mul_re]
  nlinarith [sq_nonneg (u.im - v.im)]

/-- The per-step bound `Re σ(2n) + Re σ(2n+1) ≥ −√(2(1 + Re σ(n)))`. -/
theorem re_two_mul_add_re_ge (f : CMUnit) {n : ℕ} (hn : 0 < n) :
    -Real.sqrt (2 * (1 + (unitSuccPhase f n).re)) ≤
      (unitSuccPhase f (2 * n)).re + (unitSuccPhase f (2 * n + 1)).re := by
  have h := sq_re_add_re_le (norm_unitSuccPhase f (n := 2 * n) (by omega))
    (norm_unitSuccPhase f (n := 2 * n + 1) (by omega))
  rw [unitSuccPhase_two_mul_mul f hn] at h
  have := Real.abs_le_sqrt h
  linarith [neg_abs_le ((unitSuccPhase f (2 * n)).re + (unitSuccPhase f (2 * n + 1)).re)]

theorem abs_re_unitSuccPhase_le (f : CMUnit) {n : ℕ} (hn : 0 < n) :
    |(unitSuccPhase f n).re| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (norm_unitSuccPhase f hn).le

/-- The logarithmic successor mass `X(N) = Σ_{n ≤ N} Re σ(n)/n`. -/
noncomputable def logUnitCorr (f : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (unitSuccPhase f n).re / n

/-- **Cauchy–Schwarz.** `Σ_{n ≤ N} √(2(1+xₙ))/n ≤ √(H_N · 2(H_N + X(N)))`. -/
theorem sum_sqrt_le (f : CMUnit) (N : ℕ) :
    ∑ n ∈ Icc 1 N, Real.sqrt (2 * (1 + (unitSuccPhase f n).re)) / n ≤
      Real.sqrt ((harmonic N : ℝ) * (2 * ((harmonic N : ℝ) + logUnitCorr f N))) := by
  have hnonneg : ∀ n ∈ Icc 1 N, 0 ≤ 2 * (1 + (unitSuccPhase f n).re) := fun n hn => by
    have := abs_re_unitSuccPhase_le f (n := n) (by simp at hn; omega)
    linarith [neg_abs_le (unitSuccPhase f n).re]
  have hterm : ∀ n ∈ Icc 1 N, Real.sqrt (2 * (1 + (unitSuccPhase f n).re)) / n =
      Real.sqrt (1 / n) * Real.sqrt (2 * (1 + (unitSuccPhase f n).re) / n) := fun n hn => by
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by simp at hn; omega)
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 1 / n by positivity),
      show (1 : ℝ) / n * (2 * (1 + (unitSuccPhase f n).re) / n)
        = 2 * (1 + (unitSuccPhase f n).re) / n ^ 2 by ring,
      Real.sqrt_div' _ (show (0 : ℝ) ≤ (n : ℝ) ^ 2 by positivity), Real.sqrt_sq hn'.le]
  have hH0 : (0 : ℝ) ≤ harmonic N := by rw [harmonic_eq_sum]; positivity
  have h1 : ∑ n ∈ Icc 1 N, Real.sqrt (1 / n) ^ 2 = harmonic N := by
    rw [harmonic_eq_sum]
    exact sum_congr rfl fun n _ => Real.sq_sqrt (by positivity)
  have h2 : ∑ n ∈ Icc 1 N, Real.sqrt (2 * (1 + (unitSuccPhase f n).re) / n) ^ 2 =
      2 * (harmonic N + logUnitCorr f N) := by
    rw [sum_congr rfl fun n hn => Real.sq_sqrt (div_nonneg (hnonneg n hn) (Nat.cast_nonneg n)),
      harmonic_eq_sum, logUnitCorr, ← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun n _ => by ring
  rw [sum_congr rfl hterm]
  refine (sum_mul_le_sqrt_mul_sqrt _ _ _).trans_eq ?_
  rw [h1, h2, ← Real.sqrt_mul hH0]

/-- Adding `k` terms past `N` lowers `X` by at most `k/(N+1)`. -/
theorem logUnitCorr_add_ge (f : CMUnit) (N k : ℕ) :
    logUnitCorr f N - k / (N + 1) ≤ logUnitCorr f (N + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, logUnitCorr, sum_Icc_succ_top (by omega), ← logUnitCorr]
    have hb := abs_le.mp (abs_re_unitSuccPhase_le f (n := N + k + 1) (by omega))
    have hpos : (0 : ℝ) < ((N + k + 1 : ℕ) : ℝ) := by positivity
    have h1 : -(1 / ((N : ℝ) + 1)) ≤ (unitSuccPhase f (N + k + 1)).re / ((N + k + 1 : ℕ) : ℝ) := by
      have : -1 / ((N + k + 1 : ℕ) : ℝ) ≤ (unitSuccPhase f (N + k + 1)).re / ((N + k + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hb.1 hpos.le
      have h2 : -(1 / ((N : ℝ) + 1)) ≤ -1 / ((N + k + 1 : ℕ) : ℝ) := by
        rw [neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by push_cast; linarith)
      linarith
    push_cast at ih ⊢
    have : ((k : ℝ) + 1) / ((N : ℝ) + 1) = k / (N + 1) + 1 / (N + 1) := by ring
    linarith

/-- `X(2N+1) ≥ −H_N/2 − 3/2`. -/
theorem logUnitCorr_two_mul_add_one_ge (f : CMUnit) (N : ℕ) :
    -((harmonic N : ℝ) / 2) - 3 / 2 ≤ logUnitCorr f (2 * N + 1) := by
  set x : ℕ → ℝ := fun n => (unitSuccPhase f n).re
  have hx : ∀ n, 0 < n → |x n| ≤ 1 := fun n hn => abs_re_unitSuccPhase_le f hn
  have hsplit : logUnitCorr f (2 * N + 1) = x 1 / 1 +
      ∑ n ∈ Icc 1 N, (x (2 * n) / ((2 * n : ℕ) : ℝ) + x (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
    rw [logUnitCorr, sum_Icc_two_mul_add_one (fun k => x k / k)]
    simp
  have hpair : ∀ n ∈ Icc 1 N, -(Real.sqrt (2 * (1 + x n)) / n) / 2 - 1 / (2 * n * (2 * n + 1)) ≤
      x (2 * n) / ((2 * n : ℕ) : ℝ) + x (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
    intro n hn
    have hn1 : 0 < n := by simp at hn; omega
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hstep := re_two_mul_add_re_ge f hn1
    have hb := abs_le.mp (hx (2 * n + 1) (by omega))
    push_cast
    have e1 : x (2 * n + 1) / (2 * n) - 1 / (2 * n * (2 * n + 1)) ≤ x (2 * n + 1) / (2 * n + 1) := by
      have h3 : x (2 * n + 1) / (2 * n) - x (2 * n + 1) / (2 * n + 1) =
          x (2 * n + 1) / (2 * n * (2 * n + 1)) := by field_simp; ring
      have h4 : x (2 * n + 1) / (2 * n * (2 * n + 1)) ≤ 1 / (2 * n * (2 * n + 1)) :=
        div_le_div_of_nonneg_right hb.2 (by positivity)
      linarith
    have e2 : -(Real.sqrt (2 * (1 + x n)) / n) / 2 ≤ (x (2 * n) + x (2 * n + 1)) / (2 * n) := by
      rw [show -(Real.sqrt (2 * (1 + x n)) / n) / 2 = -Real.sqrt (2 * (1 + x n)) / (2 * n) by
        field_simp]
      exact div_le_div_of_nonneg_right hstep (by positivity)
    rw [add_div] at e2
    linarith
  have hsum := sum_le_sum hpair
  have hlin : ∑ n ∈ Icc 1 N, (-(Real.sqrt (2 * (1 + x n)) / n) / 2 - 1 / (2 * n * (2 * n + 1))) =
      -(∑ n ∈ Icc 1 N, Real.sqrt (2 * (1 + x n)) / n) / 2 -
        ∑ n ∈ Icc 1 N, (1 : ℝ) / (2 * n * (2 * n + 1)) := by
    rw [sum_sub_distrib, ← sum_div, sum_neg_distrib]
  rw [hlin] at hsum
  have hcs := sum_sqrt_le f N
  have htel := sum_inv_two_mul_two_mul_add_one_le N
  have hmono := logUnitCorr_add_ge f N (N + 1)
  rw [show N + (N + 1) = 2 * N + 1 by ring] at hmono
  have hk : ((N + 1 : ℕ) : ℝ) / ((N : ℝ) + 1) = 1 := by push_cast; field_simp
  rw [hk] at hmono
  obtain ⟨hx1, -⟩ := abs_le.mp (hx 1 one_pos)
  have hNpos : (0 : ℝ) ≤ 1 / (2 * ((N : ℝ) + 1)) := by positivity
  set Y := logUnitCorr f (2 * N + 1)
  set h := (harmonic N : ℝ)
  have hH0 : 0 ≤ h := by simp only [h]; rw [harmonic_eq_sum]; positivity
  -- `Y ≥ −3/2 − √(2h(h + Y + 1))/2`
  have hsqrt_mono : Real.sqrt (h * (2 * (h + logUnitCorr f N))) ≤
      Real.sqrt (h * (2 * (h + Y + 1))) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hY : -(3 / 2) - Real.sqrt (h * (2 * (h + Y + 1))) / 2 ≤ Y := by
    rw [hsplit]
    simp only [x, div_one] at hsum hx1 ⊢
    linarith
  by_contra hcon
  push Not at hcon
  set Z := -Y - 3 / 2
  have hZ : h / 2 < Z := by simp only [Z]; linarith
  have hZ' : 2 * Z ≤ Real.sqrt (h * (2 * (h + Y + 1))) := by simp only [Z]; linarith
  by_cases hA : 0 ≤ h * (2 * (h + Y + 1))
  · have h2 : (2 * Z) ^ 2 ≤ h * (2 * (h + Y + 1)) := by
      calc (2 * Z) ^ 2 ≤ Real.sqrt (h * (2 * (h + Y + 1))) ^ 2 :=
            pow_le_pow_left₀ (by linarith) hZ' 2
        _ = _ := Real.sq_sqrt hA
    have hYZ : Y = -Z - 3 / 2 := by simp only [Z]; ring
    rw [hYZ] at h2
    nlinarith
  · rw [Real.sqrt_eq_zero'.mpr (le_of_lt (not_le.mp hA))] at hZ'
    linarith

/-- **The complex successor floor.** For a completely multiplicative function of modulus one,
`Σ_{n ≤ M} Re(f̄(n) f(n+1))/n ≥ −(1/2) log M − 3`. -/
theorem complex_log_floor (f : CMUnit) {M : ℕ} (hM : 0 < M) :
    -(Real.log M / 2) - 3 ≤ logUnitCorr f M := by
  obtain ⟨N, hN⟩ : ∃ N, M = 2 * N + 1 ∨ M = 2 * N + 2 := ⟨(M - 1) / 2, by omega⟩
  have hbase := logUnitCorr_two_mul_add_one_ge f N
  have hH : (harmonic N : ℝ) ≤ 1 + Real.log M := by
    rcases Nat.eq_zero_or_pos N with h0 | hN0
    · rw [h0]; simp only [harmonic_zero, Rat.cast_zero]
      have : (0 : ℝ) ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
      linarith
    · have := harmonic_le_one_add_log N
      have : Real.log N ≤ Real.log M :=
        Real.log_le_log (by exact_mod_cast hN0) (by exact_mod_cast (show N ≤ M by omega))
      linarith
  rcases hN with rfl | rfl
  · linarith
  · have h1 := logUnitCorr_add_ge f (2 * N + 1) 1
    rw [show 2 * N + 1 + 1 = 2 * N + 2 by ring] at h1
    have : ((1 : ℕ) : ℝ) / (((2 * N + 1 : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
      push_cast; rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [Nat.cast_nonneg (α := ℝ) N]
    linarith

/-- **Catalan's pair forbids the cube-root extremal.** No completely multiplicative function with
values in the cube roots of unity changes its value at every step from `1` to `9`. -/
theorem no_cubeRoot_successor_coloring (f : CMUnit) (hcube : ∀ n, 0 < n → f n ^ 3 = 1) :
    ¬ ∀ n, 1 ≤ n → n ≤ 8 → f n ≠ f (n + 1) := by
  intro hdist
  set g := f 2
  set c := f 3
  have h4 : f 4 = g * g := f.map_mul' (m := 2) (n := 2) (by norm_num) (by norm_num)
  have h8 : f 8 = g * f 4 := f.map_mul' (m := 2) (n := 4) (by norm_num) (by norm_num)
  have h9 : f 9 = c * c := f.map_mul' (m := 3) (n := 3) (by norm_num) (by norm_num)
  have hg3 : g ^ 3 = 1 := hcube 2 (by norm_num)
  have hc3 : c ^ 3 = 1 := hcube 3 (by norm_num)
  have hg1 : g ≠ 1 := fun h => hdist 1 le_rfl (by norm_num) (by rw [f.map_one']; exact h.symm)
  have hcg : c ≠ g := fun h => hdist 2 (by norm_num) (by norm_num) h.symm
  have hcg2 : c ≠ g * g := fun h => hdist 3 (by norm_num) (by norm_num)
    (by rw [show (3 : ℕ) + 1 = 4 from rfl, h4]; exact h)
  have hsum : 1 + g + g ^ 2 = 0 := by
    have : (g - 1) * (1 + g + g ^ 2) = 0 := by linear_combination hg3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hg1)
  have hc1 : c = 1 := by
    have hprod : (c - 1) * (c - g) * (c - g * g) = 0 := by
      linear_combination hc3 - hg3 - (c ^ 2 - c * g) * hsum
    rcases mul_eq_zero.mp hprod with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact sub_eq_zero.mp h
      · exact absurd (sub_eq_zero.mp h) hcg
    · exact absurd (sub_eq_zero.mp h) hcg2
  apply hdist 8 (by norm_num) (by norm_num)
  rw [h8, h4, show (8 : ℕ) + 1 = 9 from rfl, h9, hc1]
  linear_combination hg3

end GaloisForLFunctions.SignedSuccessorArithmetic
