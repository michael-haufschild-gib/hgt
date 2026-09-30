import GaloisForLFunctions.RHTower.JitteredUnitCellVariance

/-!
# Unit cells: Laplace transforms of the random field

For a mean-zero `Y` on `[0, 1]` with `|Y| ≤ R` and `|λ| R ≤ 1`, the third-order Taylor bound
`|e^x − 1 − x − x²/2| ≤ (2/9)|x|³` (`|x| ≤ 1`) gives
`|∫₀¹ e^{λY} − 1 − λ² Var/2| ≤ (2/9)|λ|³ R Var` (`integral_exp_le_of_bound`,
`integral_exp_ge_of_bound`), hence the logarithmic bounds `log_integral_exp_le_large` and
`log_integral_exp_ge_large`.  Cells with `|λ| R > 1` (the first 23 unit cells for `|λ| ≤ 12/5`)
are bounded crudely by `0 ≤ log ∫ e^{λY} ≤ |λ| R`.

Under the product law the unit-cell terms are independent, so the Laplace transform of the field
`f_K(t) = Σ_{k<K} Y_k(t)` is the product of the cell transforms (`mgf_field`, `mgf_field_pair`).
With the variance and covariance of `JitteredUnitCellVariance` this gives
* `log_mgf_field_le`: `log E e^{λ f_K(t)} ≤ λ² σ²/2 + 120` for `|λ| ≤ 12/5`;
* `log_mgf_field_ge`: `log E e^{λ f_K(t)} ≥ λ² σ²/2 − 100` for `0 ≤ λ ≤ 12/5`;
* `log_mgf_field_pair_le`: `log E e^{λ(f_K(t) + f_K(t'))} ≤ λ²(σ²(t) + σ²(t') + 2Γ)/2 + 120`
  for `|λ| ≤ 6/5`.
-/

open Real MeasureTheory ProbabilityTheory Set

noncomputable section

namespace RHTower
namespace RandomCellWeil

/-! ### Taylor bounds for the exponential -/

theorem abs_exp_sub_quadratic_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ (2 / 9) * |x| ^ 3 := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
  rw [hs] at h
  refine h.trans (le_of_eq ?_)
  norm_num [Nat.factorial]
  ring

/-! ### A single mean-zero cell -/

section cell

variable {Y : ℝ → ℝ}

theorem cube_le_of_bound {x R : ℝ} (hx : |x| ≤ R) : |x| ^ 3 ≤ R * x ^ 2 := by
  have e : |x| ^ 3 = |x| * x ^ 2 := by
    rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one, sq_abs]
  rw [e]
  exact mul_le_mul_of_nonneg_right hx (sq_nonneg x)

/-- `∫₀¹ e^{λY} ≤ 1 + λ² V/2 + (2/9)|λ|³ R V`. -/
theorem integral_exp_le_of_bound (hY : ContinuousOn Y (Icc 0 1))
    (hmean : ∫ v in (0 : ℝ)..1, Y v = 0) {R l : ℝ}
    (hR : ∀ v ∈ Icc (0 : ℝ) 1, |Y v| ≤ R) (hlR : |l| * R ≤ 1) :
    ∫ v in (0 : ℝ)..1, Real.exp (l * Y v)
      ≤ 1 + l ^ 2 * (∫ v in (0 : ℝ)..1, Y v ^ 2) / 2
        + (2 / 9) * |l| ^ 3 * R * ∫ v in (0 : ℝ)..1, Y v ^ 2 := by
  have hYi : IntervalIntegrable Y volume 0 1 := hY.intervalIntegrable_of_Icc zero_le_one
  have hY2 : IntervalIntegrable (fun v => Y v ^ 2) volume 0 1 :=
    (hY.pow 2).intervalIntegrable_of_Icc zero_le_one
  have hexp : IntervalIntegrable (fun v => Real.exp (l * Y v)) volume 0 1 :=
    ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hY))).intervalIntegrable_of_Icc
      zero_le_one
  have hg : IntervalIntegrable (fun v => 1 + l * Y v + (l ^ 2 / 2 + (2 / 9) * |l| ^ 3 * R) * Y v ^ 2)
      volume 0 1 :=
    (intervalIntegrable_const.add (hYi.const_mul l)).add (hY2.const_mul _)
  have hpt : ∀ v ∈ Icc (0 : ℝ) 1, Real.exp (l * Y v)
      ≤ 1 + l * Y v + (l ^ 2 / 2 + (2 / 9) * |l| ^ 3 * R) * Y v ^ 2 := by
    intro v hv
    have hx : |l * Y v| ≤ 1 := by
      rw [abs_mul]; exact le_trans (mul_le_mul_of_nonneg_left (hR v hv) (abs_nonneg l)) hlR
    have h := abs_exp_sub_quadratic_le hx
    have hc : |l * Y v| ^ 3 ≤ |l| ^ 3 * R * Y v ^ 2 := by
      rw [abs_mul, mul_pow]
      have := cube_le_of_bound (hR v hv)
      calc |l| ^ 3 * |Y v| ^ 3 ≤ |l| ^ 3 * (R * Y v ^ 2) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = |l| ^ 3 * R * Y v ^ 2 := by ring
    have := (abs_le.mp h).2
    nlinarith
  have hmono := intervalIntegral.integral_mono_on zero_le_one hexp hg hpt
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add (hYi.const_mul l))
      (hY2.const_mul _),
    intervalIntegral.integral_add intervalIntegrable_const (hYi.const_mul l),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hmean,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, one_mul, mul_zero, add_zero]
  ring

/-- `∫₀¹ e^{λY} ≥ 1 + λ² V/2 − (2/9)|λ|³ R V`. -/
theorem integral_exp_ge_of_bound (hY : ContinuousOn Y (Icc 0 1))
    (hmean : ∫ v in (0 : ℝ)..1, Y v = 0) {R l : ℝ}
    (hR : ∀ v ∈ Icc (0 : ℝ) 1, |Y v| ≤ R) (hlR : |l| * R ≤ 1) :
    1 + l ^ 2 * (∫ v in (0 : ℝ)..1, Y v ^ 2) / 2
        - (2 / 9) * |l| ^ 3 * R * (∫ v in (0 : ℝ)..1, Y v ^ 2)
      ≤ ∫ v in (0 : ℝ)..1, Real.exp (l * Y v) := by
  have hYi : IntervalIntegrable Y volume 0 1 := hY.intervalIntegrable_of_Icc zero_le_one
  have hY2 : IntervalIntegrable (fun v => Y v ^ 2) volume 0 1 :=
    (hY.pow 2).intervalIntegrable_of_Icc zero_le_one
  have hexp : IntervalIntegrable (fun v => Real.exp (l * Y v)) volume 0 1 :=
    ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hY))).intervalIntegrable_of_Icc
      zero_le_one
  have hg : IntervalIntegrable (fun v => 1 + l * Y v + (l ^ 2 / 2 - (2 / 9) * |l| ^ 3 * R) * Y v ^ 2)
      volume 0 1 :=
    (intervalIntegrable_const.add (hYi.const_mul l)).add (hY2.const_mul _)
  have hpt : ∀ v ∈ Icc (0 : ℝ) 1,
      1 + l * Y v + (l ^ 2 / 2 - (2 / 9) * |l| ^ 3 * R) * Y v ^ 2 ≤ Real.exp (l * Y v) := by
    intro v hv
    have hx : |l * Y v| ≤ 1 := by
      rw [abs_mul]; exact le_trans (mul_le_mul_of_nonneg_left (hR v hv) (abs_nonneg l)) hlR
    have h := abs_exp_sub_quadratic_le hx
    have hc : |l * Y v| ^ 3 ≤ |l| ^ 3 * R * Y v ^ 2 := by
      rw [abs_mul, mul_pow]
      have := cube_le_of_bound (hR v hv)
      calc |l| ^ 3 * |Y v| ^ 3 ≤ |l| ^ 3 * (R * Y v ^ 2) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = |l| ^ 3 * R * Y v ^ 2 := by ring
    have := (abs_le.mp h).1
    nlinarith
  have hmono := intervalIntegral.integral_mono_on zero_le_one hg hexp hpt
  refine le_trans (le_of_eq ?_) hmono
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add (hYi.const_mul l))
      (hY2.const_mul _),
    intervalIntegral.integral_add intervalIntegrable_const (hYi.const_mul l),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hmean,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, one_mul, mul_zero, add_zero]
  ring

theorem integral_exp_ge_one (hY : ContinuousOn Y (Icc 0 1))
    (hmean : ∫ v in (0 : ℝ)..1, Y v = 0) (l : ℝ) :
    1 ≤ ∫ v in (0 : ℝ)..1, Real.exp (l * Y v) := by
  have hYi : IntervalIntegrable Y volume 0 1 := hY.intervalIntegrable_of_Icc zero_le_one
  have hexp : IntervalIntegrable (fun v => Real.exp (l * Y v)) volume 0 1 :=
    ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hY))).intervalIntegrable_of_Icc
      zero_le_one
  have hlin : IntervalIntegrable (fun v => 1 + l * Y v) volume 0 1 :=
    (intervalIntegrable_const (c := (1 : ℝ))).add (hYi.const_mul l)
  have hmono := intervalIntegral.integral_mono_on (f := fun v => 1 + l * Y v) zero_le_one
    hlin hexp (fun v _ => by have := Real.add_one_le_exp (l * Y v); linarith)
  refine le_trans (le_of_eq ?_) hmono
  rw [intervalIntegral.integral_add intervalIntegrable_const (hYi.const_mul l),
    intervalIntegral.integral_const_mul, hmean, intervalIntegral.integral_const]
  simp

theorem integral_exp_le_crude (hY : ContinuousOn Y (Icc 0 1)) {R l : ℝ}
    (hR : ∀ v ∈ Icc (0 : ℝ) 1, |Y v| ≤ R) :
    ∫ v in (0 : ℝ)..1, Real.exp (l * Y v) ≤ Real.exp (|l| * R) := by
  have hexp : IntervalIntegrable (fun v => Real.exp (l * Y v)) volume 0 1 :=
    ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hY))).intervalIntegrable_of_Icc
      zero_le_one
  have hmono := intervalIntegral.integral_mono_on zero_le_one hexp
    (intervalIntegrable_const (c := Real.exp (|l| * R)))
    (fun v hv => by
      apply Real.exp_le_exp.mpr
      calc l * Y v ≤ |l * Y v| := le_abs_self _
        _ = |l| * |Y v| := abs_mul _ _
        _ ≤ |l| * R := mul_le_mul_of_nonneg_left (hR v hv) (abs_nonneg l))
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const]
  simp

theorem log_integral_exp_nonneg (hY : ContinuousOn Y (Icc 0 1))
    (hmean : ∫ v in (0 : ℝ)..1, Y v = 0) (l : ℝ) :
    0 ≤ Real.log (∫ v in (0 : ℝ)..1, Real.exp (l * Y v)) :=
  Real.log_nonneg (integral_exp_ge_one hY hmean l)

theorem log_integral_exp_le_small (hY : ContinuousOn Y (Icc 0 1))
    (hmean : ∫ v in (0 : ℝ)..1, Y v = 0) {R l : ℝ} (hR : ∀ v ∈ Icc (0 : ℝ) 1, |Y v| ≤ R) :
    Real.log (∫ v in (0 : ℝ)..1, Real.exp (l * Y v)) ≤ |l| * R := by
  have h1 := integral_exp_ge_one hY hmean l
  have h2 := integral_exp_le_crude hY (l := l) hR
  calc Real.log (∫ v in (0 : ℝ)..1, Real.exp (l * Y v)) ≤ Real.log (Real.exp (|l| * R)) :=
        Real.log_le_log (by linarith) h2
    _ = |l| * R := Real.log_exp _

theorem log_integral_exp_le_large (hY : ContinuousOn Y (Icc 0 1))
    (hmean : ∫ v in (0 : ℝ)..1, Y v = 0) {R l : ℝ}
    (hR : ∀ v ∈ Icc (0 : ℝ) 1, |Y v| ≤ R) (hlR : |l| * R ≤ 1) :
    Real.log (∫ v in (0 : ℝ)..1, Real.exp (l * Y v))
      ≤ l ^ 2 * (∫ v in (0 : ℝ)..1, Y v ^ 2) / 2
        + (2 / 9) * |l| ^ 3 * R * ∫ v in (0 : ℝ)..1, Y v ^ 2 := by
  have h1 := integral_exp_ge_one hY hmean l
  have h2 := integral_exp_le_of_bound hY hmean hR hlR
  have := Real.log_le_sub_one_of_pos (by linarith : 0 < ∫ v in (0 : ℝ)..1, Real.exp (l * Y v))
  linarith

theorem log_integral_exp_ge_large (hY : ContinuousOn Y (Icc 0 1))
    (hmean : ∫ v in (0 : ℝ)..1, Y v = 0) {R l : ℝ}
    (hR : ∀ v ∈ Icc (0 : ℝ) 1, |Y v| ≤ R) (hlR : |l| * R ≤ 1) :
    l ^ 2 * (∫ v in (0 : ℝ)..1, Y v ^ 2) / 2
        - (2 / 9) * |l| ^ 3 * R * (∫ v in (0 : ℝ)..1, Y v ^ 2)
        - (l ^ 2 * (∫ v in (0 : ℝ)..1, Y v ^ 2)) ^ 2
      ≤ Real.log (∫ v in (0 : ℝ)..1, Real.exp (l * Y v)) := by
  set V := ∫ v in (0 : ℝ)..1, Y v ^ 2 with hV
  have hV0 : 0 ≤ V := intervalIntegral.integral_nonneg zero_le_one (fun v _ => sq_nonneg _)
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) (hR 0 ⟨le_rfl, zero_le_one⟩)
  have h2 := integral_exp_ge_of_bound hY hmean hR hlR
  rw [← hV] at h2
  have hnn : 0 ≤ |l| ^ 3 * R * V := mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg l) 3) hR0) hV0
  have hnn2 : 0 ≤ l ^ 2 * V := mul_nonneg (sq_nonneg l) hV0
  set z := l ^ 2 * V / 2 - (2 / 9) * |l| ^ 3 * R * V with hz
  have hz0 : 0 ≤ z := by
    have hl3 : |l| ^ 3 * R ≤ l ^ 2 := by
      calc |l| ^ 3 * R = |l| ^ 2 * (|l| * R) := by ring
        _ ≤ |l| ^ 2 * 1 := mul_le_mul_of_nonneg_left hlR (by positivity)
        _ = l ^ 2 := by rw [mul_one, sq_abs]
    rw [hz]
    nlinarith
  have hzle : z ≤ l ^ 2 * V := by rw [hz]; linarith
  have hlog : z - z ^ 2 ≤ Real.log (1 + z) := by
    have h := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + z)
    have : z - z ^ 2 ≤ 1 - (1 + z)⁻¹ := by
      rw [show 1 - (1 + z)⁻¹ = z / (1 + z) by field_simp; ring]
      rw [le_div_iff₀ (by linarith)]
      nlinarith [pow_nonneg hz0 3]
    linarith
  have hmono : Real.log (1 + z) ≤ Real.log (∫ v in (0 : ℝ)..1, Real.exp (l * Y v)) :=
    Real.log_le_log (by linarith) (by rw [hz]; linarith)
  have hsq : z ^ 2 ≤ (l ^ 2 * V) ^ 2 := pow_le_pow_left₀ hz0 hzle 2
  rw [hz] at hlog hsq
  linarith

end cell


/-! ### Unit-cell terms as random variables -/

theorem measurable_unitTerm (k : ℕ) (t : ℝ) : Measurable (fun v => unitTerm k v t) := by
  have : (fun v => unitTerm k v t) = fun v => cellTerm 1 k v t := by
    funext v; exact unitTerm_eq_cellTerm k v t
  rw [this]
  exact measurable_cellTerm k t

theorem integral_unitTerm_eq_zero (k : ℕ) (t : ℝ) : ∫ v in (0 : ℝ)..1, unitTerm k v t = 0 := by
  have : (fun v => unitTerm k v t) = fun v => cellTerm 1 k v t := by
    funext v; exact unitTerm_eq_cellTerm k v t
  rw [this]
  exact integral_cellTerm_eq_zero le_rfl k t

theorem integral_coord_eq (k : ℕ) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ u, g (u k) ∂cellLaw = ∫ v in (0 : ℝ)..1, g v := by
  have h := integral_map (μ := cellLaw) (φ := fun u : ℕ → ℝ => u k)
    (measurable_pi_apply k).aemeasurable (f := g) hg.aestronglyMeasurable
  rw [← h, map_eval_cellLaw k, unitLaw, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]

/-- The pair term `Y_k(t) + Y_k(t')`. -/
def pairTerm (k : ℕ) (v t t' : ℝ) : ℝ := unitTerm k v t + unitTerm k v t'

theorem iIndepFun_unitTerm (t : ℝ) :
    iIndepFun (fun k (u : ℕ → ℝ) => unitTerm k (u k) t) cellLaw :=
  iIndepFun_infinitePi (P := fun _ : ℕ => unitLaw) (X := fun k v => unitTerm k v t)
    (fun k => measurable_unitTerm k t)

theorem iIndepFun_pairTerm (t t' : ℝ) :
    iIndepFun (fun k (u : ℕ → ℝ) => pairTerm k (u k) t t') cellLaw :=
  iIndepFun_infinitePi (P := fun _ : ℕ => unitLaw) (X := fun k v => pairTerm k v t t')
    (fun k => (measurable_unitTerm k t).add (measurable_unitTerm k t'))

/-- The truncated random field `f_K(u, t) = Σ_{k<K} Y_k(u_k, t)`. -/
def field (K : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range K, unitTerm k (u k) t

theorem measurable_field (K : ℕ) (t : ℝ) : Measurable (fun u => field K u t) := by
  unfold field
  exact Finset.measurable_sum _ (fun k _ =>
    (measurable_unitTerm k t).comp (measurable_pi_apply k))

/-- The Laplace transform of the field is the product of the cell transforms. -/
theorem mgf_field (K : ℕ) (t l : ℝ) :
    mgf (fun u => field K u t) cellLaw l
      = ∏ k ∈ Finset.range K, ∫ v in (0 : ℝ)..1, Real.exp (l * unitTerm k v t) := by
  have h := (iIndepFun_unitTerm t).mgf_sum (t := l)
    (fun k => (measurable_unitTerm k t).comp (measurable_pi_apply k)) (Finset.range K)
  have hf : (∑ k ∈ Finset.range K, fun u : ℕ → ℝ => unitTerm k (u k) t)
      = fun u => field K u t := by
    funext u; simp [field, Finset.sum_apply]
  rw [hf] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro k _
  unfold mgf
  exact integral_coord_eq k (g := fun v => Real.exp (l * unitTerm k v t))
    (Real.measurable_exp.comp (measurable_const.mul (measurable_unitTerm k t)))

theorem mgf_field_pair (K : ℕ) (t t' l : ℝ) :
    mgf (fun u => field K u t + field K u t') cellLaw l
      = ∏ k ∈ Finset.range K, ∫ v in (0 : ℝ)..1, Real.exp (l * pairTerm k v t t') := by
  have h := (iIndepFun_pairTerm t t').mgf_sum (t := l)
    (fun k => ((measurable_unitTerm k t).add (measurable_unitTerm k t')).comp
      (measurable_pi_apply k)) (Finset.range K)
  have hf : (∑ k ∈ Finset.range K, fun u : ℕ → ℝ => pairTerm k (u k) t t')
      = fun u => field K u t + field K u t' := by
    funext u; simp [field, pairTerm, Finset.sum_apply, Finset.sum_add_distrib]
  rw [hf] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro k _
  unfold mgf
  exact integral_coord_eq k (g := fun v => Real.exp (l * pairTerm k v t t'))
    (by
      have := (measurable_unitTerm k t).add (measurable_unitTerm k t')
      exact Real.measurable_exp.comp (measurable_const.mul this))

/-! ### Cell data for the generic bounds -/

theorem continuousOn_pairTerm (k : ℕ) (t t' : ℝ) :
    ContinuousOn (fun v => pairTerm k v t t') (Icc 0 1) :=
  (continuousOn_unitTerm k t).add (continuousOn_unitTerm k t')

theorem integral_pairTerm_eq_zero (k : ℕ) (t t' : ℝ) :
    ∫ v in (0 : ℝ)..1, pairTerm k v t t' = 0 := by
  have h1 : IntervalIntegrable (fun v => unitTerm k v t) volume 0 1 :=
    (continuousOn_unitTerm k t).intervalIntegrable_of_Icc zero_le_one
  have h2 : IntervalIntegrable (fun v => unitTerm k v t') volume 0 1 :=
    (continuousOn_unitTerm k t').intervalIntegrable_of_Icc zero_le_one
  unfold pairTerm
  rw [intervalIntegral.integral_add h1 h2, integral_unitTerm_eq_zero, integral_unitTerm_eq_zero,
    add_zero]

theorem integral_pairTerm_sq (k : ℕ) (t t' : ℝ) :
    ∫ v in (0 : ℝ)..1, pairTerm k v t t' ^ 2
      = cellVar k t + cellVar k t' + 2 * cellCov k t t' := by
  have i11 : IntervalIntegrable (fun v => unitTerm k v t ^ 2) volume 0 1 :=
    ((continuousOn_unitTerm k t).pow 2).intervalIntegrable_of_Icc zero_le_one
  have i22 : IntervalIntegrable (fun v => unitTerm k v t' ^ 2) volume 0 1 :=
    ((continuousOn_unitTerm k t').pow 2).intervalIntegrable_of_Icc zero_le_one
  have i12 : IntervalIntegrable (fun v => 2 * (unitTerm k v t * unitTerm k v t')) volume 0 1 :=
    (((continuousOn_unitTerm k t).mul (continuousOn_unitTerm k t')).intervalIntegrable_of_Icc
      zero_le_one).const_mul 2
  have hexp : (fun v => pairTerm k v t t' ^ 2) = fun v =>
      (unitTerm k v t ^ 2 + unitTerm k v t' ^ 2) + 2 * (unitTerm k v t * unitTerm k v t') := by
    funext v; unfold pairTerm; ring
  rw [hexp, intervalIntegral.integral_add (i11.add i22) i12, intervalIntegral.integral_add i11 i22,
    intervalIntegral.integral_const_mul]
  rfl

theorem abs_pairTerm_le (k : ℕ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (t t' : ℝ) :
    |pairTerm k v t t'| ≤ 4 / Real.sqrt ((k : ℝ) + 1) := by
  unfold pairTerm
  have a := abs_unitTerm_le_osc k hv t
  have b := abs_unitTerm_le_osc k hv t'
  calc |unitTerm k v t + unitTerm k v t'| ≤ |unitTerm k v t| + |unitTerm k v t'| := abs_add_le _ _
    _ ≤ 2 / Real.sqrt ((k : ℝ) + 1) + 2 / Real.sqrt ((k : ℝ) + 1) := add_le_add a b
    _ = 4 / Real.sqrt ((k : ℝ) + 1) := by ring

theorem cellVar_pair_nonneg (k : ℕ) (t t' : ℝ) :
    0 ≤ cellVar k t + cellVar k t' + 2 * cellCov k t t' := by
  rw [← integral_pairTerm_sq]
  exact intervalIntegral.integral_nonneg zero_le_one (fun v _ => sq_nonneg _)

/-- For `k ≥ 23`, `(24/5)/√(k+1) ≤ 1`. -/
theorem large_cell_bound {k : ℕ} (hk : 23 ≤ k) : 24 / 5 / Real.sqrt ((k : ℝ) + 1) ≤ 1 := by
  have hk' : (24 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (23 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hs : 24 / 5 ≤ Real.sqrt ((k : ℝ) + 1) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  rw [div_le_one (by linarith)]
  exact hs

theorem sum_Ico_invPow_le (K : ℕ) :
    ∑ k ∈ Finset.Ico 23 K, invPow ((k : ℝ) + 1) ≤ 1 / 2 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h := sum_range_invPow_le 24 (by norm_num) (K - 23)
  have e : ∀ i : ℕ, ((23 + i : ℕ) : ℝ) + 1 = ((24 + i : ℕ) : ℝ) := by intro i; push_cast; ring
  simp only [e]
  refine h.trans ?_
  have hpos : 0 ≤ 2 / Real.sqrt (((24 + (K - 23) : ℕ) : ℝ) - 1) := by positivity
  have e23 : ((24 : ℕ) : ℝ) - 1 = 23 := by norm_num
  rw [e23]
  have h23 : 2 / Real.sqrt 23 ≤ 1 / 2 := by
    have hs : (4 : ℝ) ≤ Real.sqrt 23 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

theorem osc_mul_inv_le (k : ℕ) :
    2 / Real.sqrt ((k : ℝ) + 1) * (1 / ((k : ℝ) + 1)) = 2 * invPow ((k : ℝ) + 1) := by
  unfold invPow
  field_simp

theorem inv_sq_le_invPow (k : ℕ) : (1 / ((k : ℝ) + 1)) ^ 2 ≤ invPow ((k : ℝ) + 1) := by
  unfold invPow
  have ha : (1 : ℝ) ≤ (k : ℝ) + 1 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hs : Real.sqrt ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  rw [div_pow, one_pow]
  apply one_div_le_one_div_of_le (by positivity)
  rw [sq]
  exact mul_le_mul_of_nonneg_left hs (by linarith)

/-! ### Laplace transform of the field -/

theorem prod_integral_exp_pos (K : ℕ) (t l : ℝ) :
    0 < ∏ k ∈ Finset.range K, ∫ v in (0 : ℝ)..1, Real.exp (l * unitTerm k v t) :=
  Finset.prod_pos (fun k _ => lt_of_lt_of_le one_pos
    (integral_exp_ge_one (continuousOn_unitTerm k t) (integral_unitTerm_eq_zero k t) l))

/-- **Upper bound.** `log E e^{λ f_K(t)} ≤ λ² σ²/2 + 120` for `|λ| ≤ 12/5`, `K ≥ 23`. -/
theorem log_mgf_field_le {K : ℕ} (hK : 23 ≤ K) (t : ℝ) {l : ℝ} (hl : |l| ≤ 12 / 5) :
    Real.log (mgf (fun u => field K u t) cellLaw l) ≤ l ^ 2 * fieldVar K t / 2 + 120 := by
  rw [mgf_field, Real.log_prod (fun k _ => (lt_of_lt_of_le one_pos
    (integral_exp_ge_one (continuousOn_unitTerm k t) (integral_unitTerm_eq_zero k t) l)).ne')]
  rw [← Finset.sum_range_add_sum_Ico _ hK]
  have hsmall : ∑ k ∈ Finset.range 23,
      Real.log (∫ v in (0 : ℝ)..1, Real.exp (l * unitTerm k v t)) ≤ 23 * (2 * (12 / 5)) := by
    calc _ ≤ ∑ _k ∈ Finset.range 23, 2 * (12 / 5 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          refine (log_integral_exp_le_small (continuousOn_unitTerm k t)
            (integral_unitTerm_eq_zero k t) (R := 2) (fun v hv => ?_)).trans ?_
          · refine (abs_unitTerm_le_osc k hv t).trans ?_
            rw [div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
            have : (1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := by
              rw [Real.le_sqrt (by norm_num) (by positivity)]
              have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
              linarith
            linarith
          · nlinarith [abs_nonneg l]
      _ = 23 * (2 * (12 / 5)) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  have hlarge : ∑ k ∈ Finset.Ico 23 K,
      Real.log (∫ v in (0 : ℝ)..1, Real.exp (l * unitTerm k v t))
        ≤ ∑ k ∈ Finset.Ico 23 K, (l ^ 2 * cellVar k t / 2
          + (2 / 9) * (12 / 5) ^ 3 * (2 * invPow ((k : ℝ) + 1))) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk23 : 23 ≤ k := (Finset.mem_Ico.mp hk).1
    have hR : ∀ v ∈ Icc (0 : ℝ) 1, |unitTerm k v t| ≤ 2 / Real.sqrt ((k : ℝ) + 1) :=
      fun v hv => abs_unitTerm_le_osc k hv t
    have hlR : |l| * (2 / Real.sqrt ((k : ℝ) + 1)) ≤ 1 := by
      have := large_cell_bound hk23
      have hpos : 0 ≤ 2 / Real.sqrt ((k : ℝ) + 1) := by positivity
      calc |l| * (2 / Real.sqrt ((k : ℝ) + 1)) ≤ 12 / 5 * (2 / Real.sqrt ((k : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hl hpos
        _ = 24 / 5 / Real.sqrt ((k : ℝ) + 1) := by ring
        _ ≤ 1 := this
    have h := log_integral_exp_le_large (continuousOn_unitTerm k t)
      (integral_unitTerm_eq_zero k t) hR hlR
    have hV := cellVar_le_inv k t
    have hV0 := cellVar_nonneg k t
    change Real.log _ ≤ l ^ 2 * cellVar k t / 2 + 2 / 9 * |l| ^ 3 * (2 / Real.sqrt ((k : ℝ) + 1))
      * cellVar k t at h
    refine h.trans (add_le_add le_rfl ?_)
    have hl3 : |l| ^ 3 ≤ (12 / 5) ^ 3 := pow_le_pow_left₀ (abs_nonneg l) hl 3
    have hRV : 2 / Real.sqrt ((k : ℝ) + 1) * cellVar k t ≤ 2 * invPow ((k : ℝ) + 1) := by
      rw [← osc_mul_inv_le]
      exact mul_le_mul_of_nonneg_left hV (by positivity)
    calc 2 / 9 * |l| ^ 3 * (2 / Real.sqrt ((k : ℝ) + 1)) * cellVar k t
        = 2 / 9 * |l| ^ 3 * (2 / Real.sqrt ((k : ℝ) + 1) * cellVar k t) := by ring
      _ ≤ 2 / 9 * (12 / 5) ^ 3 * (2 * invPow ((k : ℝ) + 1)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hl3 (by norm_num)) hRV
            (mul_nonneg (by positivity) hV0) (by norm_num)
  have hsplitV : ∑ k ∈ Finset.Ico 23 K, cellVar k t ≤ fieldVar K t := by
    unfold fieldVar
    rw [← Finset.sum_range_add_sum_Ico _ hK]
    have : 0 ≤ ∑ k ∈ Finset.range 23, cellVar k t :=
      Finset.sum_nonneg (fun k _ => cellVar_nonneg k t)
    linarith
  have hinv := sum_Ico_invPow_le K
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hlarge
  have hl2 : 0 ≤ l ^ 2 := sq_nonneg l
  have hmul : l ^ 2 * ∑ k ∈ Finset.Ico 23 K, cellVar k t ≤ l ^ 2 * fieldVar K t :=
    mul_le_mul_of_nonneg_left hsplitV hl2
  nlinarith

/-- **Lower bound.** `log E e^{λ f_K(t)} ≥ λ² σ²/2 − 100` for `|λ| ≤ 12/5`, `K ≥ 23`. -/
theorem log_mgf_field_ge {K : ℕ} (hK : 23 ≤ K) (t : ℝ) {l : ℝ} (hl : |l| ≤ 12 / 5) :
    l ^ 2 * fieldVar K t / 2 - 100 ≤ Real.log (mgf (fun u => field K u t) cellLaw l) := by
  rw [mgf_field, Real.log_prod (fun k _ => (lt_of_lt_of_le one_pos
    (integral_exp_ge_one (continuousOn_unitTerm k t) (integral_unitTerm_eq_zero k t) l)).ne')]
  rw [← Finset.sum_range_add_sum_Ico _ hK]
  have hl2 : l ^ 2 ≤ (12 / 5) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg l) hl 2
  have hsmall : 0 ≤ ∑ k ∈ Finset.range 23,
      Real.log (∫ v in (0 : ℝ)..1, Real.exp (l * unitTerm k v t)) :=
    Finset.sum_nonneg (fun k _ => log_integral_exp_nonneg (continuousOn_unitTerm k t)
      (integral_unitTerm_eq_zero k t) l)
  have hsmallV : ∑ k ∈ Finset.range 23, cellVar k t ≤ 23 := by
    calc ∑ k ∈ Finset.range 23, cellVar k t ≤ ∑ _k ∈ Finset.range 23, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          refine (cellVar_le_inv k t).trans ?_
          rw [div_le_one (by positivity)]
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith
      _ = 23 := by simp
  have hlarge : ∑ k ∈ Finset.Ico 23 K, (l ^ 2 * cellVar k t / 2
        - (2 / 9) * (12 / 5) ^ 3 * (2 * invPow ((k : ℝ) + 1))
        - (12 / 5) ^ 4 * invPow ((k : ℝ) + 1))
      ≤ ∑ k ∈ Finset.Ico 23 K, Real.log (∫ v in (0 : ℝ)..1, Real.exp (l * unitTerm k v t)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk23 : 23 ≤ k := (Finset.mem_Ico.mp hk).1
    have hR : ∀ v ∈ Icc (0 : ℝ) 1, |unitTerm k v t| ≤ 2 / Real.sqrt ((k : ℝ) + 1) :=
      fun v hv => abs_unitTerm_le_osc k hv t
    have hlR : |l| * (2 / Real.sqrt ((k : ℝ) + 1)) ≤ 1 := by
      have := large_cell_bound hk23
      have hpos : 0 ≤ 2 / Real.sqrt ((k : ℝ) + 1) := by positivity
      calc |l| * (2 / Real.sqrt ((k : ℝ) + 1)) ≤ 12 / 5 * (2 / Real.sqrt ((k : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hl hpos
        _ = 24 / 5 / Real.sqrt ((k : ℝ) + 1) := by ring
        _ ≤ 1 := this
    have h := log_integral_exp_ge_large (continuousOn_unitTerm k t)
      (integral_unitTerm_eq_zero k t) hR hlR
    have hV := cellVar_le_inv k t
    have hV0 := cellVar_nonneg k t
    change l ^ 2 * cellVar k t / 2 - 2 / 9 * |l| ^ 3 * (2 / Real.sqrt ((k : ℝ) + 1))
      * cellVar k t - (l ^ 2 * cellVar k t) ^ 2 ≤ Real.log _ at h
    refine le_trans ?_ h
    have hl3 : |l| ^ 3 ≤ (12 / 5) ^ 3 := pow_le_pow_left₀ (abs_nonneg l) hl 3
    have hRV : 2 / Real.sqrt ((k : ℝ) + 1) * cellVar k t ≤ 2 * invPow ((k : ℝ) + 1) := by
      rw [← osc_mul_inv_le]
      exact mul_le_mul_of_nonneg_left hV (by positivity)
    have hc : 2 / 9 * |l| ^ 3 * (2 / Real.sqrt ((k : ℝ) + 1)) * cellVar k t
        ≤ 2 / 9 * (12 / 5) ^ 3 * (2 * invPow ((k : ℝ) + 1)) := by
      calc 2 / 9 * |l| ^ 3 * (2 / Real.sqrt ((k : ℝ) + 1)) * cellVar k t
          = 2 / 9 * |l| ^ 3 * (2 / Real.sqrt ((k : ℝ) + 1) * cellVar k t) := by ring
        _ ≤ 2 / 9 * (12 / 5) ^ 3 * (2 * invPow ((k : ℝ) + 1)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hl3 (by norm_num)) hRV
              (mul_nonneg (by positivity) hV0) (by norm_num)
    have hq : (l ^ 2 * cellVar k t) ^ 2 ≤ (12 / 5) ^ 4 * invPow ((k : ℝ) + 1) := by
      have h1 : l ^ 2 * cellVar k t ≤ (12 / 5) ^ 2 * (1 / ((k : ℝ) + 1)) :=
        mul_le_mul hl2 hV hV0 (by norm_num)
      have h2 : (l ^ 2 * cellVar k t) ^ 2 ≤ ((12 / 5) ^ 2 * (1 / ((k : ℝ) + 1))) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (sq_nonneg l) hV0) h1 2
      refine h2.trans ?_
      rw [mul_pow, show ((12 : ℝ) / 5) ^ 4 = ((12 / 5) ^ 2) ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left (inv_sq_le_invPow k) (by positivity)
    linarith
  have hsplitV : fieldVar K t = ∑ k ∈ Finset.range 23, cellVar k t
      + ∑ k ∈ Finset.Ico 23 K, cellVar k t := by
    unfold fieldVar
    rw [← Finset.sum_range_add_sum_Ico _ hK]
  have hinv := sum_Ico_invPow_le K
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hlarge
  have hinv0 : 0 ≤ ∑ k ∈ Finset.Ico 23 K, invPow ((k : ℝ) + 1) :=
    Finset.sum_nonneg (fun k _ => invPow_nonneg (by positivity))
  rw [hsplitV]
  nlinarith

theorem integral_pairTerm_sq_le (k : ℕ) (t t' : ℝ) :
    ∫ v in (0 : ℝ)..1, pairTerm k v t t' ^ 2 ≤ 16 * (1 / ((k : ℝ) + 1)) := by
  have hi : IntervalIntegrable (fun v => pairTerm k v t t' ^ 2) volume 0 1 :=
    ((continuousOn_pairTerm k t t').pow 2).intervalIntegrable_of_Icc zero_le_one
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one hi
    (intervalIntegrable_const (c := (4 / Real.sqrt ((k : ℝ) + 1)) ^ 2))
    (fun v hv => by
      have := abs_pairTerm_le k hv t t'
      calc pairTerm k v t t' ^ 2 = |pairTerm k v t t'| ^ 2 := (sq_abs _).symm
        _ ≤ (4 / Real.sqrt ((k : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2)
  refine h.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const, smul_eq_mul, div_pow, Real.sq_sqrt (by positivity)]
  ring

/-- **Pair upper bound.** `log E e^{λ(f_K(t) + f_K(t'))} ≤ λ²(σ²(t) + σ²(t') + 2Γ)/2 + 130` for
`|λ| ≤ 6/5`, `K ≥ 23`. -/
theorem log_mgf_field_pair_le {K : ℕ} (hK : 23 ≤ K) (t t' : ℝ) {l : ℝ} (hl : |l| ≤ 6 / 5) :
    Real.log (mgf (fun u => field K u t + field K u t') cellLaw l)
      ≤ l ^ 2 * (fieldVar K t + fieldVar K t' + 2 * fieldCov K t t') / 2 + 130 := by
  rw [mgf_field_pair, Real.log_prod (fun k _ => (lt_of_lt_of_le one_pos
    (integral_exp_ge_one (continuousOn_pairTerm k t t') (integral_pairTerm_eq_zero k t t') l)).ne')]
  rw [← Finset.sum_range_add_sum_Ico _ hK]
  have hsmall : ∑ k ∈ Finset.range 23,
      Real.log (∫ v in (0 : ℝ)..1, Real.exp (l * pairTerm k v t t')) ≤ 23 * (4 * (6 / 5)) := by
    calc _ ≤ ∑ _k ∈ Finset.range 23, 4 * (6 / 5 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          refine (log_integral_exp_le_small (continuousOn_pairTerm k t t')
            (integral_pairTerm_eq_zero k t t') (R := 4) (fun v hv => ?_)).trans ?_
          · refine (abs_pairTerm_le k hv t t').trans ?_
            rw [div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
            have : (1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := by
              rw [Real.le_sqrt (by norm_num) (by positivity)]
              have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
              linarith
            linarith
          · nlinarith [abs_nonneg l]
      _ = 23 * (4 * (6 / 5)) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  have hlarge : ∑ k ∈ Finset.Ico 23 K,
      Real.log (∫ v in (0 : ℝ)..1, Real.exp (l * pairTerm k v t t'))
        ≤ ∑ k ∈ Finset.Ico 23 K, (l ^ 2 * (cellVar k t + cellVar k t' + 2 * cellCov k t t') / 2
          + (2 / 9) * (6 / 5) ^ 3 * (64 * invPow ((k : ℝ) + 1))) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk23 : 23 ≤ k := (Finset.mem_Ico.mp hk).1
    have hR : ∀ v ∈ Icc (0 : ℝ) 1, |pairTerm k v t t'| ≤ 4 / Real.sqrt ((k : ℝ) + 1) :=
      fun v hv => abs_pairTerm_le k hv t t'
    have hlR : |l| * (4 / Real.sqrt ((k : ℝ) + 1)) ≤ 1 := by
      have := large_cell_bound hk23
      have hpos : 0 ≤ 4 / Real.sqrt ((k : ℝ) + 1) := by positivity
      calc |l| * (4 / Real.sqrt ((k : ℝ) + 1)) ≤ 6 / 5 * (4 / Real.sqrt ((k : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hl hpos
        _ = 24 / 5 / Real.sqrt ((k : ℝ) + 1) := by ring
        _ ≤ 1 := this
    have h := log_integral_exp_le_large (continuousOn_pairTerm k t t')
      (integral_pairTerm_eq_zero k t t') hR hlR
    have hVle := integral_pairTerm_sq_le k t t'
    have hV0 : 0 ≤ ∫ v in (0 : ℝ)..1, pairTerm k v t t' ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one (fun v _ => sq_nonneg _)
    have hl3 : |l| ^ 3 ≤ (6 / 5) ^ 3 := pow_le_pow_left₀ (abs_nonneg l) hl 3
    have hRV : 4 / Real.sqrt ((k : ℝ) + 1) * (∫ v in (0 : ℝ)..1, pairTerm k v t t' ^ 2)
        ≤ 64 * invPow ((k : ℝ) + 1) := by
      calc 4 / Real.sqrt ((k : ℝ) + 1) * (∫ v in (0 : ℝ)..1, pairTerm k v t t' ^ 2)
          ≤ 4 / Real.sqrt ((k : ℝ) + 1) * (16 * (1 / ((k : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hVle (by positivity)
        _ = 64 * invPow ((k : ℝ) + 1) := by unfold invPow; field_simp; ring
    have hc : 2 / 9 * |l| ^ 3 * (4 / Real.sqrt ((k : ℝ) + 1))
          * (∫ v in (0 : ℝ)..1, pairTerm k v t t' ^ 2)
        ≤ 2 / 9 * (6 / 5) ^ 3 * (64 * invPow ((k : ℝ) + 1)) := by
      calc 2 / 9 * |l| ^ 3 * (4 / Real.sqrt ((k : ℝ) + 1))
            * (∫ v in (0 : ℝ)..1, pairTerm k v t t' ^ 2)
          = 2 / 9 * |l| ^ 3 * (4 / Real.sqrt ((k : ℝ) + 1)
            * (∫ v in (0 : ℝ)..1, pairTerm k v t t' ^ 2)) := by ring
        _ ≤ 2 / 9 * (6 / 5) ^ 3 * (64 * invPow ((k : ℝ) + 1)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hl3 (by norm_num)) hRV
              (mul_nonneg (by positivity) hV0) (by norm_num)
    rw [integral_pairTerm_sq] at h hc
    linarith
  have hsum : fieldVar K t + fieldVar K t' + 2 * fieldCov K t t'
      = ∑ k ∈ Finset.range K, (cellVar k t + cellVar k t' + 2 * cellCov k t t') := by
    unfold fieldVar fieldCov
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hsplitV : ∑ k ∈ Finset.Ico 23 K, (cellVar k t + cellVar k t' + 2 * cellCov k t t')
      ≤ fieldVar K t + fieldVar K t' + 2 * fieldCov K t t' := by
    rw [hsum, ← Finset.sum_range_add_sum_Ico _ hK]
    have : 0 ≤ ∑ k ∈ Finset.range 23, (cellVar k t + cellVar k t' + 2 * cellCov k t t') :=
      Finset.sum_nonneg (fun k _ => cellVar_pair_nonneg k t t')
    linarith
  have hinv := sum_Ico_invPow_le K
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hlarge
  have hl2 : 0 ≤ l ^ 2 := sq_nonneg l
  have hmul := mul_le_mul_of_nonneg_left hsplitV hl2
  nlinarith

end RandomCellWeil
end RHTower
