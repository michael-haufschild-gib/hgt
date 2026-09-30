import GaloisForLFunctions.RHTower.JitteredUnitCellIntegrals
import GaloisForLFunctions.RHTower.JitteredDiscreteWeilPositive

/-!
# Unit cells: variances, covariances and cumulant bounds

For the unit-cell term `Y_k(v) = unitTerm k v t = wave t (k+1+v) − m_k(t)` with `v` uniform on
`[0, 1]`:

* `cellVar_eq`: `Var Y_k = ∫_{k+1}^{k+2} wave_t² − m_k²`, and `cellCov_eq` likewise for the
  covariance of two heights;
* `fieldVar_ge`, `fieldVar_le`: the variance of `Σ_{k<K} Y_k` is `½ log t + O(1)` (the integrals
  telescope to `½ log(K₀+1) + sin(2t log(K₀+1))/(4t)` and `m_k² ≤ 16(k+2)/t²`);
* `abs_fieldCov_le`: the covariance at heights `|t − t'| ≥ 1` in `[T, 2T]` is bounded;
* `log_integral_exp_le`, `log_integral_exp_ge`: for `|λ| R ≤ 1`,
  `|log ∫₀¹ e^{λY} − λ² Var Y/2| ≤ (2/9)|λ|³ R Var Y + λ⁴ (Var Y)²` (from
  `|e^x − 1 − x − x²/2| ≤ (2/9)|x|³` on `|x| ≤ 1`).
-/

open Real MeasureTheory Set

noncomputable section

namespace RHTower
namespace RandomCellWeil

/-- The mean `∫_{k+1}^{k+2} wave_t` of the wave over the `k`-th unit cell. -/
def cellMean (k : ℕ) (t : ℝ) : ℝ := ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), wave t x

/-- The variance `∫₀¹ Y_k(v)²` of a unit-cell term. -/
def cellVar (k : ℕ) (t : ℝ) : ℝ := ∫ v in (0 : ℝ)..1, unitTerm k v t ^ 2

/-- The covariance `∫₀¹ Y_k(v,t) Y_k(v,t')` of a unit-cell term at two heights. -/
def cellCov (k : ℕ) (t t' : ℝ) : ℝ := ∫ v in (0 : ℝ)..1, unitTerm k v t * unitTerm k v t'

theorem unitTerm_eq_sub (k : ℕ) (v t : ℝ) :
    unitTerm k v t = wave t ((k : ℝ) + 1 + v) - cellMean k t := rfl

theorem shift_pos (k : ℕ) {v : ℝ} (hv : 0 ≤ v) : 0 < (k : ℝ) + 1 + v := by
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem continuousOn_wave_shift (k : ℕ) (t : ℝ) :
    ContinuousOn (fun v => wave t ((k : ℝ) + 1 + v)) (Icc 0 1) := by
  apply (continuousOn_wave t).comp (by fun_prop)
  intro v hv
  exact shift_pos k hv.1

theorem continuousOn_unitTerm (k : ℕ) (t : ℝ) :
    ContinuousOn (fun v => unitTerm k v t) (Icc 0 1) :=
  (continuousOn_wave_shift k t).sub continuousOn_const

theorem intervalIntegrable_of_continuousOn_Icc {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    IntervalIntegrable f volume 0 1 :=
  hf.intervalIntegrable_of_Icc zero_le_one

theorem integral_shift (k : ℕ) (g : ℝ → ℝ) :
    ∫ v in (0 : ℝ)..1, g ((k : ℝ) + 1 + v) = ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), g x := by
  have h := intervalIntegral.integral_comp_add_left g ((k : ℝ) + 1) (a := 0) (b := 1)
  rw [show (k : ℝ) + 1 + 0 = (k : ℝ) + 1 by ring,
    show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring] at h
  exact h

theorem cellVar_eq (k : ℕ) (t : ℝ) :
    cellVar k t = (∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), wave t x ^ 2) - cellMean k t ^ 2 := by
  set m := cellMean k t
  have hw : IntervalIntegrable (fun v => wave t ((k : ℝ) + 1 + v)) volume 0 1 :=
    intervalIntegrable_of_continuousOn_Icc (continuousOn_wave_shift k t)
  have hw2 : IntervalIntegrable (fun v => wave t ((k : ℝ) + 1 + v) ^ 2) volume 0 1 :=
    intervalIntegrable_of_continuousOn_Icc ((continuousOn_wave_shift k t).pow 2)
  have hmw : IntervalIntegrable (fun v => 2 * m * wave t ((k : ℝ) + 1 + v)) volume 0 1 :=
    hw.const_mul _
  have hexp : (fun v => unitTerm k v t ^ 2) = fun v =>
      (wave t ((k : ℝ) + 1 + v) ^ 2 - 2 * m * wave t ((k : ℝ) + 1 + v)) + m ^ 2 := by
    funext v; rw [unitTerm_eq_sub]; ring
  have i1 : ∫ v in (0 : ℝ)..1, ((wave t ((k : ℝ) + 1 + v) ^ 2 - 2 * m * wave t ((k : ℝ) + 1 + v))
      + m ^ 2) = (∫ v in (0 : ℝ)..1, wave t ((k : ℝ) + 1 + v) ^ 2)
        - (∫ v in (0 : ℝ)..1, 2 * m * wave t ((k : ℝ) + 1 + v)) + ∫ v in (0 : ℝ)..1, m ^ 2 := by
    rw [intervalIntegral.integral_add (hw2.sub hmw) intervalIntegrable_const,
      intervalIntegral.integral_sub hw2 hmw]
  have i2 : ∫ v in (0 : ℝ)..1, 2 * m * wave t ((k : ℝ) + 1 + v) = 2 * m * m := by
    rw [intervalIntegral.integral_const_mul, integral_shift k (wave t)]
    rfl
  unfold cellVar
  rw [hexp, i1, i2, integral_shift k (fun x => wave t x ^ 2), intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, one_mul]
  ring

theorem cellCov_eq (k : ℕ) (t t' : ℝ) :
    cellCov k t t' = (∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), wave t x * wave t' x)
      - cellMean k t * cellMean k t' := by
  set m := cellMean k t
  set m' := cellMean k t'
  have hw : IntervalIntegrable (fun v => wave t ((k : ℝ) + 1 + v)) volume 0 1 :=
    intervalIntegrable_of_continuousOn_Icc (continuousOn_wave_shift k t)
  have hw' : IntervalIntegrable (fun v => wave t' ((k : ℝ) + 1 + v)) volume 0 1 :=
    intervalIntegrable_of_continuousOn_Icc (continuousOn_wave_shift k t')
  have hww : IntervalIntegrable (fun v => wave t ((k : ℝ) + 1 + v) * wave t' ((k : ℝ) + 1 + v))
      volume 0 1 :=
    intervalIntegrable_of_continuousOn_Icc
      ((continuousOn_wave_shift k t).mul (continuousOn_wave_shift k t'))
  have h1 : IntervalIntegrable (fun v => m' * wave t ((k : ℝ) + 1 + v)) volume 0 1 :=
    hw.const_mul _
  have h2 : IntervalIntegrable (fun v => m * wave t' ((k : ℝ) + 1 + v)) volume 0 1 :=
    hw'.const_mul _
  have hexp : (fun v => unitTerm k v t * unitTerm k v t') = fun v =>
      ((wave t ((k : ℝ) + 1 + v) * wave t' ((k : ℝ) + 1 + v)
        - m' * wave t ((k : ℝ) + 1 + v)) - m * wave t' ((k : ℝ) + 1 + v)) + m * m' := by
    funext v; rw [unitTerm_eq_sub, unitTerm_eq_sub]; ring
  have i1 : ∫ v in (0 : ℝ)..1, (((wave t ((k : ℝ) + 1 + v) * wave t' ((k : ℝ) + 1 + v)
        - m' * wave t ((k : ℝ) + 1 + v)) - m * wave t' ((k : ℝ) + 1 + v)) + m * m')
      = (∫ v in (0 : ℝ)..1, wave t ((k : ℝ) + 1 + v) * wave t' ((k : ℝ) + 1 + v))
        - (∫ v in (0 : ℝ)..1, m' * wave t ((k : ℝ) + 1 + v))
        - (∫ v in (0 : ℝ)..1, m * wave t' ((k : ℝ) + 1 + v)) + ∫ v in (0 : ℝ)..1, m * m' := by
    rw [intervalIntegral.integral_add ((hww.sub h1).sub h2) intervalIntegrable_const,
      intervalIntegral.integral_sub (hww.sub h1) h2, intervalIntegral.integral_sub hww h1]
  have hm : (∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), wave t x) = m := rfl
  have hm' : (∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), wave t' x) = m' := rfl
  unfold cellCov
  rw [hexp, i1, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_shift k (wave t), integral_shift k (wave t'),
    integral_shift k (fun x => wave t x * wave t' x), intervalIntegral.integral_const, hm, hm']
  simp only [sub_zero, smul_eq_mul, one_mul]
  ring

/-! ### Bounds on a single cell -/

theorem abs_unitTerm_le_osc (k : ℕ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    |unitTerm k v t| ≤ 2 / Real.sqrt ((k : ℝ) + 1) := by
  rw [unitTerm_eq_cellTerm]
  have h := abs_cellTerm_le_osc (N := 1) le_rfl k hv t
  rw [cellLeft_one] at h
  simpa using h

theorem abs_unitTerm_le_smooth (k : ℕ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    |unitTerm k v t| ≤ (|t| + 1 / 2) * invPow ((k : ℝ) + 1) := by
  rw [unitTerm_eq_cellTerm]
  have h := abs_cellTerm_le_invPow (N := 1) le_rfl k hv t
  have e : ((1 + k : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [e] at h
  simpa using h

theorem cellVar_nonneg (k : ℕ) (t : ℝ) : 0 ≤ cellVar k t := by
  unfold cellVar
  exact intervalIntegral.integral_nonneg zero_le_one (fun v _ => sq_nonneg _)

theorem integral_unitTerm_sq_le {k : ℕ} {t B : ℝ}
    (hB : ∀ v ∈ Icc (0 : ℝ) 1, |unitTerm k v t| ≤ B) : cellVar k t ≤ B ^ 2 := by
  unfold cellVar
  have hi : IntervalIntegrable (fun v => unitTerm k v t ^ 2) volume 0 1 :=
    intervalIntegrable_of_continuousOn_Icc ((continuousOn_unitTerm k t).pow 2)
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one hi
    (intervalIntegrable_const (c := B ^ 2))
    (fun v hv => by
      have := hB v hv
      calc unitTerm k v t ^ 2 = |unitTerm k v t| ^ 2 := (sq_abs _).symm
        _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2)
  simpa using h

theorem abs_cellCov_le {k : ℕ} {t t' B B' : ℝ}
    (hB : ∀ v ∈ Icc (0 : ℝ) 1, |unitTerm k v t| ≤ B)
    (hB' : ∀ v ∈ Icc (0 : ℝ) 1, |unitTerm k v t'| ≤ B') : |cellCov k t t'| ≤ B * B' := by
  unfold cellCov
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := B * B')
    (f := fun v => unitTerm k v t * unitTerm k v t') (by
      intro v hv
      rw [uIoc_of_le zero_le_one] at hv
      have hv' : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2⟩
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hB v hv') (hB' v hv') (abs_nonneg _)
        (le_trans (abs_nonneg _) (hB v hv')))
  simpa [Real.norm_eq_abs] using h

theorem integral_wave_sq_cell_le (k : ℕ) (t : ℝ) :
    ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), wave t x ^ 2 ≤ 1 / ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hi : IntervalIntegrable (fun x => wave t x ^ 2) volume ((k : ℝ) + 1) ((k : ℝ) + 2) :=
    intervalIntegrable_unit_of_continuousOn ((continuousOn_wave t).pow 2) k
  have h := intervalIntegral.integral_mono_on (μ := volume)
    (by linarith : (k : ℝ) + 1 ≤ (k : ℝ) + 2) hi
    (intervalIntegrable_const (c := 1 / ((k : ℝ) + 1)))
    (fun x hx => (wave_sq_le t (lt_of_lt_of_le hk hx.1)).trans
      (one_div_le_one_div_of_le hk hx.1))
  refine h.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem cellVar_le_inv (k : ℕ) (t : ℝ) : cellVar k t ≤ 1 / ((k : ℝ) + 1) := by
  rw [cellVar_eq]
  have := integral_wave_sq_cell_le k t
  nlinarith [sq_nonneg (cellMean k t)]

theorem abs_cellMean_le (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    |cellMean k t| ≤ 4 * Real.sqrt ((k : ℝ) + 2) / |t| := by
  unfold cellMean
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  refine (abs_integral_wave_le ht hk (by linarith)).trans ?_
  apply div_le_div_of_nonneg_right _ (abs_nonneg t)
  have : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt ((k : ℝ) + 2) := Real.sqrt_le_sqrt (by linarith)
  linarith

theorem cellMean_sq_le (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    cellMean k t ^ 2 ≤ 16 * ((k : ℝ) + 2) / t ^ 2 := by
  have h := abs_cellMean_le k ht
  have hsq : cellMean k t ^ 2 ≤ (4 * Real.sqrt ((k : ℝ) + 2) / |t|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  refine hsq.trans (le_of_eq ?_)
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), sq_abs]
  ring


/-! ### The field variance and covariance -/

/-- The variance `Σ_{k<K} Var Y_k(t)` of the truncated field. -/
def fieldVar (K : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range K, cellVar k t

/-- The covariance `Σ_{k<K} Cov(Y_k(t), Y_k(t'))` of the truncated field. -/
def fieldCov (K : ℕ) (t t' : ℝ) : ℝ := ∑ k ∈ Finset.range K, cellCov k t t'

theorem waveSqPrim_one (t : ℝ) : waveSqPrim t 1 = 0 := by simp [waveSqPrim]

theorem waveSqPrim_ge (t : ℝ) (x : ℝ) : (1 / 2) * Real.log x - 1 / (4 * |t|) ≤ waveSqPrim t x := by
  unfold waveSqPrim
  have h := abs_sin_div_le t (2 * t * Real.log x)
  have := (abs_le.mp h).1
  linarith

theorem waveSqPrim_le (t : ℝ) (x : ℝ) : waveSqPrim t x ≤ (1 / 2) * Real.log x + 1 / (4 * |t|) := by
  unfold waveSqPrim
  have h := abs_sin_div_le t (2 * t * Real.log x)
  have := (abs_le.mp h).2
  linarith

theorem sum_integral_wave_sq {t : ℝ} (ht : t ≠ 0) (K : ℕ) :
    ∑ k ∈ Finset.range K, ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), wave t x ^ 2
      = waveSqPrim t ((K : ℝ) + 1) := by
  rw [sum_integral_unit_cells (f := fun x => wave t x ^ 2) ((continuousOn_wave t).pow 2) K,
    integral_wave_sq ht one_pos (by have : (0 : ℝ) ≤ K := Nat.cast_nonneg K; linarith),
    waveSqPrim_one, sub_zero]

theorem sum_integral_wave_mul {t t' : ℝ} (hd : t - t' ≠ 0) (hs : t + t' ≠ 0) (K : ℕ) :
    |∑ k ∈ Finset.range K, ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), wave t x * wave t' x|
      ≤ 1 / |t - t'| + 1 / |t + t'| := by
  rw [sum_integral_unit_cells (f := fun x => wave t x * wave t' x)
    ((continuousOn_wave t).mul (continuousOn_wave t')) K]
  exact abs_integral_wave_mul_le hd hs one_pos
    (by have : (0 : ℝ) ≤ K := Nat.cast_nonneg K; linarith)

theorem sum_range_cast_add_two_le (n : ℕ) :
    ∑ k ∈ Finset.range n, ((k : ℝ) + 2) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
  calc ∑ k ∈ Finset.range n, ((k : ℝ) + 2) ≤ ∑ _k ∈ Finset.range n, ((n : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro k hk
        have : (k : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hk
        linarith
    _ = (n : ℝ) * ((n : ℝ) + 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem sum_cellMean_sq_le {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, cellMean k t ^ 2 ≤ 16 * ((n : ℝ) * ((n : ℝ) + 1)) / t ^ 2 := by
  calc ∑ k ∈ Finset.range n, cellMean k t ^ 2
      ≤ ∑ k ∈ Finset.range n, 16 * ((k : ℝ) + 2) / t ^ 2 :=
        Finset.sum_le_sum (fun k _ => cellMean_sq_le k ht)
    _ = 16 * (∑ k ∈ Finset.range n, ((k : ℝ) + 2)) / t ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_div]
    _ ≤ 16 * ((n : ℝ) * ((n : ℝ) + 1)) / t ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg t)
        exact mul_le_mul_of_nonneg_left (sum_range_cast_add_two_le n) (by norm_num)

theorem floor_le_of_le_nat {t : ℝ} {K : ℕ} (hK : t ≤ K) : ⌊t⌋₊ ≤ K := Nat.floor_le_of_le hK

/-- **Lower bound for the field variance.** `½ log t − 19 ≤ Σ_{k<K} Var Y_k(t)` for `t ≥ 8`,
`K ≥ t`. -/
theorem fieldVar_ge {t : ℝ} (ht : 8 ≤ t) {K : ℕ} (hK : t ≤ K) :
    (1 / 2) * Real.log t - 19 ≤ fieldVar K t := by
  set K₀ := ⌊t⌋₊ with hK₀
  have ht0 : t ≠ 0 := by linarith
  have hK₀K : K₀ ≤ K := floor_le_of_le_nat hK
  have hsub : ∑ k ∈ Finset.range K₀, cellVar k t ≤ fieldVar K t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hK₀K)
      (fun k _ _ => cellVar_nonneg k t)
  have heq : ∑ k ∈ Finset.range K₀, cellVar k t
      = waveSqPrim t ((K₀ : ℝ) + 1) - ∑ k ∈ Finset.range K₀, cellMean k t ^ 2 := by
    simp only [cellVar_eq]
    rw [Finset.sum_sub_distrib, sum_integral_wave_sq ht0]
  have hfl : (K₀ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hfl2 : t < (K₀ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hprim := waveSqPrim_ge t ((K₀ : ℝ) + 1)
  have hlog : Real.log t ≤ Real.log ((K₀ : ℝ) + 1) := Real.log_le_log (by linarith) hfl2.le
  have hmean := sum_cellMean_sq_le ht0 K₀
  have hmean' : 16 * ((K₀ : ℝ) * ((K₀ : ℝ) + 1)) / t ^ 2 ≤ 18 := by
    rw [div_le_iff₀ (by positivity)]
    have hK0 : (0 : ℝ) ≤ K₀ := Nat.cast_nonneg _
    nlinarith
  have habs : |t| = t := abs_of_pos (by linarith)
  have h4 : 1 / (4 * |t|) ≤ 1 := by
    rw [habs, div_le_one (by linarith)]; linarith
  linarith

/-- The smooth-cell tail: `Σ_{K₀ ≤ k < K} ((|t|+½) invPow(k+1))² ≤ 2(|t|+½)²/K₀²`. -/
theorem sum_Ico_smooth_sq_le (t : ℝ) {K₀ K : ℕ} (hK₀ : 1 ≤ K₀) :
    ∑ k ∈ Finset.Ico K₀ K, ((|t| + 1 / 2) * invPow ((k : ℝ) + 1)) ^ 2
      ≤ 2 * (|t| + 1 / 2) ^ 2 / (K₀ : ℝ) ^ 2 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hM : 2 ≤ K₀ + 1 := by omega
  have h1 := sum_Ico_invPow_sq_le (K₀ + 1) hM (K - K₀)
  have hMr : (2 : ℝ) ≤ ((K₀ + 1 : ℕ) : ℝ) := by exact_mod_cast hM
  have h2 := invPow_mul_two_div_sqrt_le hMr
  have e : ∀ k : ℕ, ((K₀ + k : ℕ) : ℝ) + 1 = (((K₀ + 1) + k : ℕ) : ℝ) := by
    intro k; push_cast; ring
  have e2 : ((K₀ + 1 : ℕ) : ℝ) - 1 = (K₀ : ℝ) := by push_cast; ring
  calc ∑ k ∈ Finset.range (K - K₀), ((|t| + 1 / 2) * invPow ((((K₀ + k) : ℕ) : ℝ) + 1)) ^ 2
      = (|t| + 1 / 2) ^ 2 * ∑ k ∈ Finset.range (K - K₀), invPow ((((K₀ + 1) + k) : ℕ) : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_pow, e k]
    _ ≤ (|t| + 1 / 2) ^ 2 * (2 / (K₀ : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        rw [← e2]
        exact h1.trans h2
    _ = 2 * (|t| + 1 / 2) ^ 2 / (K₀ : ℝ) ^ 2 := by ring

/-- **Upper bound for the field variance.** `Σ_{k<K} Var Y_k(t) ≤ ½ log(t+1) + 4` for `t ≥ 8`,
`K ≥ t`. -/
theorem fieldVar_le {t : ℝ} (ht : 8 ≤ t) {K : ℕ} (hK : t ≤ K) :
    fieldVar K t ≤ (1 / 2) * Real.log (t + 1) + 4 := by
  set K₀ := ⌊t⌋₊ with hK₀
  have ht0 : t ≠ 0 := by linarith
  have hK₀K : K₀ ≤ K := floor_le_of_le_nat hK
  have hfl : (K₀ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hfl2 : t < (K₀ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hK₀1 : 1 ≤ K₀ := by
    have : (1 : ℝ) < (K₀ : ℝ) + 1 := by linarith
    exact_mod_cast (show (1 : ℝ) ≤ K₀ by linarith)
  unfold fieldVar
  rw [← Finset.sum_range_add_sum_Ico _ hK₀K]
  have hA : ∑ k ∈ Finset.range K₀, cellVar k t ≤ (1 / 2) * Real.log (t + 1) + 1 := by
    have hle : ∑ k ∈ Finset.range K₀, cellVar k t
        ≤ ∑ k ∈ Finset.range K₀, ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), wave t x ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      rw [cellVar_eq]
      nlinarith [sq_nonneg (cellMean k t)]
    rw [sum_integral_wave_sq ht0] at hle
    have hprim := waveSqPrim_le t ((K₀ : ℝ) + 1)
    have hlog : Real.log ((K₀ : ℝ) + 1) ≤ Real.log (t + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have habs : |t| = t := abs_of_pos (by linarith)
    have h4 : 1 / (4 * |t|) ≤ 1 := by
      rw [habs, div_le_one (by linarith)]; linarith
    linarith
  have hB : ∑ k ∈ Finset.Ico K₀ K, cellVar k t ≤ 3 := by
    have hle : ∑ k ∈ Finset.Ico K₀ K, cellVar k t
        ≤ ∑ k ∈ Finset.Ico K₀ K, ((|t| + 1 / 2) * invPow ((k : ℝ) + 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      exact integral_unitTerm_sq_le (fun v hv => abs_unitTerm_le_smooth k hv t)
    refine hle.trans ((sum_Ico_smooth_sq_le t hK₀1).trans ?_)
    have habs : |t| = t := abs_of_pos (by linarith)
    rw [habs, div_le_iff₀ (by positivity)]
    have hK0 : t - 1 ≤ (K₀ : ℝ) := by linarith
    have hK0' : (0 : ℝ) ≤ t - 1 := by linarith
    have hsq : (t - 1) ^ 2 ≤ (K₀ : ℝ) ^ 2 := pow_le_pow_left₀ hK0' hK0 2
    nlinarith
  linarith

/-- **Covariance bound.** For heights `t, t' ∈ [T, 2T]` with `|t − t'| ≥ 1`, `T ≥ 16`, `K ≥ T`:
`|Σ_{k<K} Cov(Y_k(t), Y_k(t'))| ≤ 30`. -/
theorem abs_fieldCov_le {T t t' : ℝ} (hT : 16 ≤ T) (ht : T ≤ t) (ht2 : t ≤ 2 * T) (ht' : T ≤ t')
    (ht'2 : t' ≤ 2 * T) (hsep : 1 ≤ |t - t'|) {K : ℕ} (hK : T ≤ K) :
    |fieldCov K t t'| ≤ 30 := by
  set K₀ := ⌊T⌋₊ with hK₀
  have hK₀K : K₀ ≤ K := floor_le_of_le_nat hK
  have hfl : (K₀ : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hfl2 : T < (K₀ : ℝ) + 1 := Nat.lt_floor_add_one T
  have hK₀1 : 1 ≤ K₀ := by
    exact_mod_cast (show (1 : ℝ) ≤ K₀ by linarith)
  have ht0 : t ≠ 0 := by linarith
  have ht0' : t' ≠ 0 := by linarith
  have hd : t - t' ≠ 0 := by
    intro h; rw [h, abs_zero] at hsep; linarith
  have hs : t + t' ≠ 0 := by linarith
  unfold fieldCov
  rw [← Finset.sum_range_add_sum_Ico _ hK₀K]
  have hA : |∑ k ∈ Finset.range K₀, cellCov k t t'| ≤ 19 := by
    simp only [cellCov_eq]
    rw [Finset.sum_sub_distrib]
    have h1 := sum_integral_wave_mul hd hs K₀
    have hS : 1 ≤ |t + t'| := by rw [abs_of_pos (by linarith)]; linarith
    have h1' : 1 / |t - t'| + 1 / |t + t'| ≤ 2 := by
      have a1 : 1 / |t - t'| ≤ 1 := by rw [div_le_one (by linarith)]; exact hsep
      have a2 : 1 / |t + t'| ≤ 1 := by rw [div_le_one (by linarith)]; exact hS
      linarith
    have h2 : |∑ k ∈ Finset.range K₀, cellMean k t * cellMean k t'| ≤ 17 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ k ∈ Finset.range K₀, |cellMean k t * cellMean k t'|
          ≤ 16 * ((k : ℝ) + 2) / T ^ 2 := by
        intro k _
        rw [abs_mul]
        have a := abs_cellMean_le k ht0
        have b := abs_cellMean_le k ht0'
        have hta : T ≤ |t| := by rw [abs_of_pos (by linarith)]; exact ht
        have htb : T ≤ |t'| := by rw [abs_of_pos (by linarith)]; exact ht'
        have hsq : Real.sqrt ((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 2) = (k : ℝ) + 2 :=
          Real.mul_self_sqrt (by positivity)
        calc |cellMean k t| * |cellMean k t'|
            ≤ (4 * Real.sqrt ((k : ℝ) + 2) / |t|) * (4 * Real.sqrt ((k : ℝ) + 2) / |t'|) :=
              mul_le_mul a b (abs_nonneg _) (by positivity)
          _ ≤ (4 * Real.sqrt ((k : ℝ) + 2) / T) * (4 * Real.sqrt ((k : ℝ) + 2) / T) := by
              apply mul_le_mul
              · exact div_le_div_of_nonneg_left (by positivity) (by linarith) hta
              · exact div_le_div_of_nonneg_left (by positivity) (by linarith) htb
              · positivity
              · positivity
          _ = 16 * ((k : ℝ) + 2) / T ^ 2 := by
              field_simp
              rw [show Real.sqrt ((k : ℝ) + 2) ^ 2 = (k : ℝ) + 2 from
                Real.sq_sqrt (by positivity)]
              ring
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_div, ← Finset.mul_sum]
      have hs2 := sum_range_cast_add_two_le K₀
      rw [div_le_iff₀ (by positivity)]
      have hK0 : (0 : ℝ) ≤ K₀ := Nat.cast_nonneg _
      nlinarith
    calc |(∑ k ∈ Finset.range K₀, ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), wave t x * wave t' x)
          - ∑ k ∈ Finset.range K₀, cellMean k t * cellMean k t'|
        ≤ |∑ k ∈ Finset.range K₀, ∫ x in ((k : ℝ) + 1)..((k : ℝ) + 2), wave t x * wave t' x|
          + |∑ k ∈ Finset.range K₀, cellMean k t * cellMean k t'| := abs_sub _ _
      _ ≤ 19 := by linarith
  have hB : |∑ k ∈ Finset.Ico K₀ K, cellCov k t t'| ≤ 11 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ Finset.Ico K₀ K, |cellCov k t t'|
        ≤ ((2 * T + 1 / 2) * invPow ((k : ℝ) + 1)) ^ 2 := by
      intro k _
      have hipos : 0 ≤ invPow ((k : ℝ) + 1) := invPow_nonneg (by positivity)
      have hta : |t| + 1 / 2 ≤ 2 * T + 1 / 2 := by rw [abs_of_pos (by linarith)]; linarith
      have htb : |t'| + 1 / 2 ≤ 2 * T + 1 / 2 := by rw [abs_of_pos (by linarith)]; linarith
      refine (abs_cellCov_le (B := (2 * T + 1 / 2) * invPow ((k : ℝ) + 1))
        (B' := (2 * T + 1 / 2) * invPow ((k : ℝ) + 1))
        (fun v hv => (abs_unitTerm_le_smooth k hv t).trans
          (mul_le_mul_of_nonneg_right hta hipos))
        (fun v hv => (abs_unitTerm_le_smooth k hv t').trans
          (mul_le_mul_of_nonneg_right htb hipos))).trans (le_of_eq (sq _).symm)
    refine (Finset.sum_le_sum hterm).trans ?_
    have h := sum_Ico_smooth_sq_le (2 * T) (K := K) hK₀1
    rw [abs_of_pos (by linarith)] at h
    refine h.trans ?_
    rw [div_le_iff₀ (pow_pos (by exact_mod_cast (show 0 < K₀ by omega)) 2)]
    have hK0 : T - 1 ≤ (K₀ : ℝ) := by linarith
    have hsq : (T - 1) ^ 2 ≤ (K₀ : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hK0 2
    nlinarith
  calc |∑ k ∈ Finset.range K₀, cellCov k t t' + ∑ k ∈ Finset.Ico K₀ K, cellCov k t t'|
      ≤ |∑ k ∈ Finset.range K₀, cellCov k t t'| + |∑ k ∈ Finset.Ico K₀ K, cellCov k t t'| :=
        abs_add_le _ _
    _ ≤ 30 := by linarith

end RandomCellWeil
end RHTower
