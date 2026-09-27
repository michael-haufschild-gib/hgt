import GaloisForLFunctions.RHTower.RoutePTwoStepWildSaddleTraceClassRelocation
import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder
import GaloisForLFunctions.RHTower.XiOrderedPositiveRVMRelocation

/-!
# Adaptive wild-saddle depth and physical spectral relocation

The smooth Riemann–von Mangoldt quantile `q_n` satisfies `q_n = 2πN/u` with `u + log u = L`,
`N = n + 1/8`, `L = log(N/e)`.  The source-only iterates `v₀ = L`, `v_{k+1} = L − log v_k` stay in
`[L − log L, L]`, where the map `x ↦ L − log x` is a contraction with Lipschitz constants between
`1/L` and `2/L`.  Hence the pseudo-ordinates `t_k = 2πN/v_k` satisfy

`π N log L / L^{k+2} ≤ |t_k − q_n| ≤ 8π N log L / L² · (2/L)^k`.

Every fixed depth has physical error tending to infinity, the diagonal depth `k = n` has error
tending to zero, and the necessary and sufficient depth order is `log n / log log n`.  At depth two
the count defect is exact, `(N + 7/8) − C(t₂) = N log(v₂/v₁)/v₂ > 0`, asymptotic to
`n log log n/(log n)³`; with the unconditional `O(log T)` Riemann–von Mangoldt remainder this is
also the number of ordered Xi zero heights missed at `t_{n,2}`.
-/

open Filter Topology Asymptotics

namespace RHTower

noncomputable section

/-! ### The logarithmic saddle map on its invariant interval -/

/-- The saddle map `F_L(x) = L − log x`. -/
def wildSaddleMap (L x : ℝ) : ℝ := L - Real.log x

/-- The source iterates `v₀ = L`, `v_{k+1} = L − log v_k`. -/
def wildSaddleIterate (L : ℝ) (k : ℕ) : ℝ := (wildSaddleMap L)^[k] L

@[simp] theorem wildSaddleIterate_zero (L : ℝ) : wildSaddleIterate L 0 = L := rfl

theorem wildSaddleIterate_succ (L : ℝ) (k : ℕ) :
    wildSaddleIterate L (k + 1) = L - Real.log (wildSaddleIterate L k) := by
  simp only [wildSaddleIterate, Function.iterate_succ_apply', wildSaddleMap]

theorem half_le_sub_log {L : ℝ} (hL : 0 < L) : L / 2 ≤ L - Real.log L := by
  linarith [log_le_half_self hL]

/-- **Invariance.**  For `L ≥ 2` every iterate lies in `[L − log L, L]`. -/
theorem wildSaddleIterate_mem {L : ℝ} (hL : 2 ≤ L) (k : ℕ) :
    L - Real.log L ≤ wildSaddleIterate L k ∧ wildSaddleIterate L k ≤ L := by
  have hL0 : 0 < L := by linarith
  have ha := half_le_sub_log hL0
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  induction k with
  | zero => exact ⟨by simp; linarith, le_rfl⟩
  | succ k ih =>
    rw [wildSaddleIterate_succ]
    have hv1 : 1 ≤ wildSaddleIterate L k := by linarith [ih.1]
    have hv0 : 0 < wildSaddleIterate L k := by linarith
    refine ⟨?_, ?_⟩
    · linarith [Real.log_le_log hv0 ih.2]
    · linarith [Real.log_nonneg hv1]

/-- Two-sided Lipschitz control of the logarithm on `[L/2, L]`. -/
theorem abs_log_sub_log_le {L x y : ℝ} (hL : 0 < L) (hx : L / 2 ≤ x) (hy : L / 2 ≤ y) :
    |Real.log x - Real.log y| ≤ 2 / L * |x - y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have key : ∀ a b : ℝ, L / 2 ≤ a → a ≤ b → Real.log b - Real.log a ≤ 2 / L * (b - a) := by
    intro a b ha hab
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    have h1 : Real.log b - Real.log a ≤ b / a - 1 := by
      rw [← Real.log_div hb0.ne' ha0.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    have h2 : b / a - 1 = (b - a) / a := by field_simp
    have h3 : (b - a) / a ≤ 2 / L * (b - a) := by
      rw [div_le_iff₀ ha0]
      have : 2 / L * a ≥ 1 := by
        rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hL]; linarith
      nlinarith
    linarith
  rcases le_total x y with hxy | hxy
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hx0 hxy)),
      abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact key x y hx hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy0 hxy)),
      abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact key y x hy hxy

theorem abs_sub_div_le_abs_log_sub_log {L x y : ℝ} (hx0 : 0 < x) (hy0 : 0 < y) (hx : x ≤ L)
    (hy : y ≤ L) : |x - y| / L ≤ |Real.log x - Real.log y| := by
  have key : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ L → (b - a) / L ≤ Real.log b - Real.log a := by
    intro a b ha0 hab hbL
    have hb0 : 0 < b := ha0.trans_le hab
    have h1 : 1 - a / b ≤ Real.log b - Real.log a := by
      rw [← Real.log_div hb0.ne' ha0.ne']
      have := Real.one_sub_inv_le_log_of_pos (div_pos hb0 ha0)
      rwa [inv_div] at this
    have h2 : 1 - a / b = (b - a) / b := by field_simp
    have h3 : (b - a) / L ≤ (b - a) / b :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hb0 hbL
    linarith
  rcases le_total x y with hxy | hxy
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hx0 hxy))]
    exact key x y hx0 hxy hy
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy0 hxy))]
    exact key y x hy0 hxy hx

section FixedPoint

variable {L u : ℝ}

/-- The fixed point `u + log u = L` lies in `[L − log L, L]`. -/
theorem wildSaddle_fixedPoint_mem (hL : 4 ≤ L) (hu0 : 0 < u) (hu : u + Real.log u = L) :
    L - Real.log L ≤ u ∧ u ≤ L := by
  have hu1 : 1 ≤ u := by
    by_contra h
    have hlt : Real.log u < 0 := Real.log_neg hu0 (lt_of_not_ge h)
    linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu1
  have huL : u ≤ L := by linarith
  exact ⟨by linarith [Real.log_le_log hu0 huL], huL⟩

/-- `(log L)/2 ≤ log u ≤ log L`. -/
theorem wildSaddle_fixedPoint_log_bounds (hL : 4 ≤ L) (hu0 : 0 < u)
    (hu : u + Real.log u = L) :
    Real.log L / 2 ≤ Real.log u ∧ Real.log u ≤ Real.log L := by
  obtain ⟨hlo, hhi⟩ := wildSaddle_fixedPoint_mem hL hu0 hu
  have hL0 : 0 < L := by linarith
  refine ⟨?_, Real.log_le_log hu0 hhi⟩
  have hsq : Real.sqrt L ≤ u := by
    have h1 : Real.sqrt L ≤ L / 2 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    linarith [half_le_sub_log hL0]
  have := Real.log_le_log (Real.sqrt_pos.mpr hL0) hsq
  rw [Real.log_sqrt hL0.le] at this
  exact this

/-- **Contraction to the fixed point.**
`log u / L^k ≤ |v_k − u| ≤ (2/L)^k log u`. -/
theorem wildSaddleIterate_sub_fixedPoint_bounds (hL : 4 ≤ L) (hu0 : 0 < u)
    (hu : u + Real.log u = L) (k : ℕ) :
    Real.log u / L ^ k ≤ |wildSaddleIterate L k - u| ∧
      |wildSaddleIterate L k - u| ≤ (2 / L) ^ k * Real.log u := by
  have hL0 : 0 < L := by linarith
  obtain ⟨hulo, huhi⟩ := wildSaddle_fixedPoint_mem hL hu0 hu
  have ha := half_le_sub_log hL0
  induction k with
  | zero =>
    have : wildSaddleIterate L 0 - u = Real.log u := by simp; linarith
    rw [this, pow_zero, pow_zero, div_one, one_mul,
      abs_of_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ u))]
    exact ⟨le_rfl, le_rfl⟩
  | succ k ih =>
    obtain ⟨hvlo, hvhi⟩ := wildSaddleIterate_mem (L := L) (by linarith) k
    have hv0 : 0 < wildSaddleIterate L k := by linarith
    have hstep : wildSaddleIterate L (k + 1) - u =
        -(Real.log (wildSaddleIterate L k) - Real.log u) := by
      rw [wildSaddleIterate_succ]; linarith
    rw [hstep, abs_neg]
    refine ⟨?_, ?_⟩
    · have h1 := abs_sub_div_le_abs_log_sub_log hv0 hu0 hvhi huhi
      calc Real.log u / L ^ (k + 1) = Real.log u / L ^ k / L := by rw [pow_succ, div_div]
        _ ≤ |wildSaddleIterate L k - u| / L := div_le_div_of_nonneg_right ih.1 hL0.le
        _ ≤ _ := h1
    · have h1 := abs_log_sub_log_le hL0 (ha.trans hvlo) (ha.trans hulo)
      calc |Real.log (wildSaddleIterate L k) - Real.log u|
          ≤ 2 / L * |wildSaddleIterate L k - u| := h1
        _ ≤ 2 / L * ((2 / L) ^ k * Real.log u) :=
          mul_le_mul_of_nonneg_left ih.2 (by positivity)
        _ = (2 / L) ^ (k + 1) * Real.log u := by ring

/-- **The physical-ordinate bounds (1).**  With `t_k = 2πN/v_k` and `q = 2πN/u`,
`π N log L / L^{k+2} ≤ |t_k − q| ≤ 8π N log L / L² · (2/L)^k`. -/
theorem wildSaddle_ordinate_bounds (hL : 4 ≤ L) (hu0 : 0 < u) (hu : u + Real.log u = L)
    {N : ℝ} (hN : 0 < N) (k : ℕ) :
    Real.pi * N * Real.log L / L ^ (k + 2) ≤
        |2 * Real.pi * N / wildSaddleIterate L k - 2 * Real.pi * N / u| ∧
      |2 * Real.pi * N / wildSaddleIterate L k - 2 * Real.pi * N / u| ≤
        8 * Real.pi * N * Real.log L / L ^ 2 * (2 / L) ^ k := by
  have hL0 : 0 < L := by linarith
  obtain ⟨hulo, huhi⟩ := wildSaddle_fixedPoint_mem hL hu0 hu
  obtain ⟨hvlo, hvhi⟩ := wildSaddleIterate_mem (L := L) (by linarith) k
  have ha := half_le_sub_log hL0
  set v := wildSaddleIterate L k with hv
  have hv0 : 0 < v := by linarith
  obtain ⟨hdlo, hdhi⟩ := wildSaddleIterate_sub_fixedPoint_bounds hL hu0 hu k
  rw [← hv] at hdlo hdhi
  obtain ⟨hllo, hlhi⟩ := wildSaddle_fixedPoint_log_bounds hL hu0 hu
  have heq : |2 * Real.pi * N / v - 2 * Real.pi * N / u| = 2 * Real.pi * N * |v - u| / (u * v) := by
    rw [div_sub_div _ _ hv0.ne' hu0.ne', abs_div, abs_of_pos (mul_pos hv0 hu0)]
    rw [show 2 * Real.pi * N * u - v * (2 * Real.pi * N) = 2 * Real.pi * N * (u - v) by ring,
      abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi * N), abs_sub_comm u v, mul_comm v u]
  rw [heq]
  have huv_hi : u * v ≤ L ^ 2 := by nlinarith
  have huv_lo : L ^ 2 / 4 ≤ u * v := by nlinarith
  have huv0 : 0 < u * v := mul_pos hu0 hv0
  have hc : 0 < 2 * Real.pi * N := by positivity
  have hLk : 0 < L ^ k := pow_pos hL0 k
  refine ⟨?_, ?_⟩
  · -- lower bound
    have h1 : 2 * Real.pi * N * |v - u| / L ^ 2 ≤ 2 * Real.pi * N * |v - u| / (u * v) :=
      div_le_div_of_nonneg_left (by positivity) huv0 huv_hi
    have h2 : Real.log L / 2 / L ^ k ≤ |v - u| :=
      (div_le_div_of_nonneg_right hllo hLk.le).trans hdlo
    have h3 : 2 * Real.pi * N * (Real.log L / 2 / L ^ k) / L ^ 2 ≤
        2 * Real.pi * N * |v - u| / L ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hc.le) (by positivity)
    have h4 : Real.pi * N * Real.log L / L ^ (k + 2) =
        2 * Real.pi * N * (Real.log L / 2 / L ^ k) / L ^ 2 := by
      rw [pow_add]; field_simp
    linarith
  · -- upper bound
    have h1 : 2 * Real.pi * N * |v - u| / (u * v) ≤ 2 * Real.pi * N * |v - u| / (L ^ 2 / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) huv_lo
    have h2 : |v - u| ≤ (2 / L) ^ k * Real.log L :=
      hdhi.trans (mul_le_mul_of_nonneg_left hlhi (by positivity))
    have h3 : 2 * Real.pi * N * |v - u| / (L ^ 2 / 4) ≤
        2 * Real.pi * N * ((2 / L) ^ k * Real.log L) / (L ^ 2 / 4) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hc.le) (by positivity)
    have h4 : 2 * Real.pi * N * ((2 / L) ^ k * Real.log L) / (L ^ 2 / 4) =
        8 * Real.pi * N * Real.log L / L ^ 2 * (2 / L) ^ k := by
      field_simp; ring
    linarith

end FixedPoint

/-! ### The Riemann–von Mangoldt specialization -/

/-- The source mass `N_n = max(e³, n + 1/8)` and log phase `L_n = log(N_n/e)`. -/
abbrev wildSaddleMass (n : ℕ) : ℝ := routePTwoStepWildSaddleMass n
abbrev wildSaddleLogPhase (n : ℕ) : ℝ := routePTwoStepWildSaddleLogPhase n

/-- The adaptive pseudo-ordinate `t_{n,k} = 2πN_n / v_{k,n}`. -/
def wildSaddleOrdinate (n k : ℕ) : ℝ :=
  2 * Real.pi * wildSaddleMass n / wildSaddleIterate (wildSaddleLogPhase n) k

/-- The quantile's logarithmic coordinate `u_n = log(q_n/(2πe))`. -/
def wildSaddleQuantileCoordinate (n : ℕ) : ℝ :=
  Real.log (routeKRVMQuantile n / routeKRVMBase)

theorem wildSaddleIterate_one (n : ℕ) :
    wildSaddleIterate (wildSaddleLogPhase n) 1 = routePTwoStepWildSaddleFirstPhase n := by
  rw [wildSaddleIterate_succ, wildSaddleIterate_zero]; rfl

theorem wildSaddleIterate_two (n : ℕ) :
    wildSaddleIterate (wildSaddleLogPhase n) 2 = routePTwoStepWildSaddleSecondPhase n := by
  rw [wildSaddleIterate_succ, wildSaddleIterate_one]; rfl

theorem wildSaddleMass_eq_exp (n : ℕ) :
    wildSaddleMass n = Real.exp 1 * Real.exp (wildSaddleLogPhase n) := by
  rw [wildSaddleLogPhase, routePTwoStepWildSaddleLogPhase,
    Real.exp_log (div_pos (routePTwoStepWildSaddleMass_pos n) (Real.exp_pos 1))]
  field_simp

theorem eventually_wildSaddleMass_eq : ∀ᶠ n : ℕ in atTop, wildSaddleMass n = (n : ℝ) + 1 / 8 := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 1 / 8) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually_ge_atTop (Real.exp 3)] with n hn
  exact max_eq_right hn

theorem tendsto_wildSaddleLogPhase : Tendsto wildSaddleLogPhase atTop atTop := by
  have h : Tendsto (fun n : ℕ => wildSaddleMass n / Real.exp 1) atTop atTop := by
    refine Tendsto.atTop_div_const (Real.exp_pos 1) ?_
    refine tendsto_atTop_mono (fun n => le_max_right _ _) ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact Real.tendsto_log_atTop.comp h

theorem eventually_four_le_wildSaddleLogPhase : ∀ᶠ n : ℕ in atTop, 4 ≤ wildSaddleLogPhase n :=
  tendsto_wildSaddleLogPhase.eventually_ge_atTop 4

theorem wildSaddleQuantileCoordinate_pos (n : ℕ) : 0 < wildSaddleQuantileCoordinate n :=
  routeKRVMQuantile_logPhase_pos n

/-- **The quantile is the saddle fixed point.**  Eventually `N_n = n + 1/8`, `L_n ≥ 4`,
`u_n + log u_n = L_n` and `q_n = 2πN_n/u_n`. -/
theorem eventually_wildSaddle_quantile :
    ∀ᶠ n : ℕ in atTop, wildSaddleMass n = (n : ℝ) + 1 / 8 ∧ 4 ≤ wildSaddleLogPhase n ∧
      wildSaddleQuantileCoordinate n + Real.log (wildSaddleQuantileCoordinate n) =
        wildSaddleLogPhase n ∧
      routeKRVMQuantile n = 2 * Real.pi * wildSaddleMass n / wildSaddleQuantileCoordinate n := by
  filter_upwards [eventually_wildSaddleMass_eq, eventually_four_le_wildSaddleLogPhase]
    with n hN hL
  refine ⟨hN, hL, ?_, ?_⟩
  · have h := routeKRVMQuantile_logPhase_fixedPoint n
    simp only at h
    rw [wildSaddleQuantileCoordinate, h, wildSaddleLogPhase, routePTwoStepWildSaddleLogPhase,
      ← wildSaddleMass, hN]
  · have h := routeKRVMQuantile_reciprocal_eq_logPhase_div n
    have hq : 0 < routeKRVMQuantile n := routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)
    have hu := wildSaddleQuantileCoordinate_pos n
    rw [hN, wildSaddleQuantileCoordinate]
    rw [← wildSaddleQuantileCoordinate] at h ⊢
    have hN0 : (0 : ℝ) < n + 1 / 8 := by positivity
    rw [eq_div_iff hu.ne']
    field_simp at h
    linarith

/-- **The physical-ordinate law (1), for the actual RVM quantile.**  For all sufficiently large
`n` and every depth `k`,
`π N_n log L_n / L_n^{k+2} ≤ |t_{n,k} − q_n| ≤ 8π N_n log L_n / L_n² · (2/L_n)^k`. -/
theorem eventually_wildSaddleOrdinate_bounds :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      Real.pi * wildSaddleMass n * Real.log (wildSaddleLogPhase n) /
          wildSaddleLogPhase n ^ (k + 2) ≤ |wildSaddleOrdinate n k - routeKRVMQuantile n| ∧
        |wildSaddleOrdinate n k - routeKRVMQuantile n| ≤
          8 * Real.pi * wildSaddleMass n * Real.log (wildSaddleLogPhase n) /
            wildSaddleLogPhase n ^ 2 * (2 / wildSaddleLogPhase n) ^ k := by
  filter_upwards [eventually_wildSaddle_quantile] with n ⟨_, hL, hfix, hq⟩ k
  rw [hq, wildSaddleOrdinate]
  exact wildSaddle_ordinate_bounds hL (wildSaddleQuantileCoordinate_pos n) hfix
    (routePTwoStepWildSaddleMass_pos n) k

/-- **Every fixed depth has unbounded physical error.** -/
theorem tendsto_abs_wildSaddleOrdinate_sub_quantile_fixed (k : ℕ) :
    Tendsto (fun n => |wildSaddleOrdinate n k - routeKRVMQuantile n|) atTop atTop := by
  have hexp : Tendsto (fun n => Real.exp (wildSaddleLogPhase n) / wildSaddleLogPhase n ^ (k + 2))
      atTop atTop := (Real.tendsto_exp_div_pow_atTop (k + 2)).comp tendsto_wildSaddleLogPhase
  have hc : 0 < Real.pi * Real.exp 1 * Real.log 4 :=
    mul_pos (mul_pos Real.pi_pos (Real.exp_pos 1)) (Real.log_pos (by norm_num))
  refine tendsto_atTop_mono' atTop ?_ (hexp.const_mul_atTop hc)
  filter_upwards [eventually_wildSaddleOrdinate_bounds, eventually_four_le_wildSaddleLogPhase]
    with n hb hL
  refine le_trans ?_ (hb k).1
  have hL0 : 0 < wildSaddleLogPhase n := by linarith
  have hlog : Real.log 4 ≤ Real.log (wildSaddleLogPhase n) := Real.log_le_log (by norm_num) hL
  rw [wildSaddleMass_eq_exp]
  have hpow : 0 < wildSaddleLogPhase n ^ (k + 2) := pow_pos hL0 _
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hpow]
  have he : 0 ≤ Real.pi * Real.exp 1 * Real.exp (wildSaddleLogPhase n) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlog he]

/-- **The diagonal depth `k = n` has vanishing physical error.** -/
theorem tendsto_abs_wildSaddleOrdinate_sub_quantile_diagonal :
    Tendsto (fun n => |wildSaddleOrdinate n n - routeKRVMQuantile n|) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 8 * Real.pi * (((n : ℝ) + 1 / 8) * (1 / 2) ^ n)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) * (1 / 2) ^ n) atTop (𝓝 0) :=
      tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
    have h2 : Tendsto (fun n : ℕ => (1 / 8 : ℝ) * (1 / 2) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (1 / 8 : ℝ)
    have := (h1.add h2).const_mul (8 * Real.pi)
    simpa [add_mul] using this
  refine squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _)) ?_ hlim
  filter_upwards [eventually_wildSaddleOrdinate_bounds, eventually_wildSaddle_quantile]
    with n hb ⟨hN, hL, _, _⟩
  refine (hb n).2.trans ?_
  set L := wildSaddleLogPhase n
  have hL0 : 0 < L := by linarith
  have hlogL : Real.log L ≤ L ^ 2 := by
    have := Real.log_le_sub_one_of_pos hL0
    nlinarith
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hr : 2 / L ≤ 1 / 2 := by rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have hpow : (2 / L) ^ n ≤ (1 / 2) ^ n := pow_le_pow_left₀ (by positivity) hr n
  rw [hN]
  have hN0 : (0 : ℝ) < n + 1 / 8 := by positivity
  have h1 : Real.log L / L ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hlogL
  calc 8 * Real.pi * ((n : ℝ) + 1 / 8) * Real.log L / L ^ 2 * (2 / L) ^ n
      = 8 * Real.pi * ((n : ℝ) + 1 / 8) * (Real.log L / L ^ 2) * (2 / L) ^ n := by ring
    _ ≤ 8 * Real.pi * ((n : ℝ) + 1 / 8) * 1 * (1 / 2) ^ n := by
        gcongr
    _ = 8 * Real.pi * (((n : ℝ) + 1 / 8) * (1 / 2) ^ n) := by ring

/-! ### The depth order `log n / log log n` -/

theorem eventually_wildSaddleLogPhase_le_log :
    ∀ᶠ n : ℕ in atTop, wildSaddleLogPhase n ≤ Real.log n := by
  filter_upwards [eventually_wildSaddleMass_eq, eventually_ge_atTop 1] with n hN hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [wildSaddleLogPhase, routePTwoStepWildSaddleLogPhase, ← wildSaddleMass, hN,
    Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
  have h : (n : ℝ) + 1 / 8 ≤ Real.exp 1 * n := by
    have := Real.add_one_le_exp 1
    nlinarith
  have := Real.log_le_log (by positivity) h
  rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp] at this
  linarith

theorem eventually_log_le_wildSaddleLogPhase_add_one :
    ∀ᶠ n : ℕ in atTop, Real.log n ≤ wildSaddleLogPhase n + 1 := by
  filter_upwards [eventually_wildSaddleMass_eq, eventually_ge_atTop 1] with n hN hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [wildSaddleLogPhase, routePTwoStepWildSaddleLogPhase, ← wildSaddleMass, hN,
    Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
  have := Real.log_le_log hn0 (by linarith : (n : ℝ) ≤ n + 1 / 8)
  linarith

/-- **Bounded physical error forces depth `(1 − o(1)) log n / log log n`.** -/
theorem wildSaddle_depth_lower (k : ℕ → ℕ) {B : ℝ}
    (hB : ∀ᶠ n in atTop, |wildSaddleOrdinate n (k n) - routeKRVMQuantile n| ≤ B) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      (1 - ε) * (Real.log n / Real.log (Real.log n)) ≤ k n := by
  intro ε hε
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop,
      2 * Real.log (Real.log n) ≤ ε / 2 * Real.log n := by
    have h := Real.isLittleO_log_id_atTop.comp_tendsto hlog
    have h2 := h.def (by positivity : (0 : ℝ) < ε / 4)
    filter_upwards [h2, hlog.eventually_ge_atTop 1] with n hn hn1
    simp only [Function.comp, id, Real.norm_eq_abs] at hn
    rw [abs_of_nonneg (Real.log_nonneg hn1), abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.log n)]
      at hn
    linarith
  filter_upwards [hB, eventually_wildSaddleOrdinate_bounds, eventually_wildSaddle_quantile,
    eventually_wildSaddleLogPhase_le_log, eventually_log_le_wildSaddleLogPhase_add_one, hsmall,
    hlog.eventually_ge_atTop (2 * |Real.log B| + 2 * Real.log 4 + 4),
    hlog.eventually_ge_atTop (2 / ε * |Real.log B|)]
    with n hBn hbd ⟨hN, hL, _, _⟩ hLle hLge hsm hbig hbig2
  set L := wildSaddleLogPhase n
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogLge : Real.log 4 ≤ Real.log L := Real.log_le_log (by norm_num) hL
  have hlow := (hbd (k n)).1.trans hBn
  have hNpos : 0 < wildSaddleMass n := routePTwoStepWildSaddleMass_pos n
  have hlhs : 0 < Real.pi * wildSaddleMass n * Real.log L / L ^ (k n + 2) := by positivity
  have hB0 : 0 < B := hlhs.trans_le hlow
  -- take logarithms
  have hineq : Real.pi * wildSaddleMass n * Real.log L ≤ B * L ^ (k n + 2) := by
    rwa [div_le_iff₀ (pow_pos hL0 _)] at hlow
  have hlogs := Real.log_le_log (by positivity) hineq
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul hB0.ne' (by positivity), Real.log_pow] at hlogs
  have hmass : Real.log (wildSaddleMass n) = L + 1 := by
    rw [wildSaddleMass_eq_exp, Real.log_mul (Real.exp_pos 1).ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_exp]
    ring
  rw [hmass] at hlogs
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hll : 0 ≤ Real.log (Real.log L) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      norm_num at this ⊢
      nlinarith
    linarith)
  -- `(k + 2) log L ≥ L + 1 − log B ≥ log n − log B`
  have hk : Real.log n - Real.log B ≤ ((k n : ℝ) + 2) * Real.log L := by
    push_cast at hlogs
    linarith
  have hloglog : Real.log L ≤ Real.log (Real.log n) := Real.log_le_log hL0 hLle
  have hlln : 0 < Real.log (Real.log n) := hlogL.trans_le hloglog
  have hBabs : Real.log B ≤ |Real.log B| := le_abs_self _
  have hnum : 0 ≤ Real.log n - Real.log B := by linarith
  have hk2 : Real.log n - Real.log B ≤ ((k n : ℝ) + 2) * Real.log (Real.log n) :=
    hk.trans (mul_le_mul_of_nonneg_left hloglog (by positivity))
  have hk3 : Real.log n - Real.log B ≤
      (k n : ℝ) * Real.log (Real.log n) + 2 * Real.log (Real.log n) := by
    have : ((k n : ℝ) + 2) * Real.log (Real.log n) =
        (k n : ℝ) * Real.log (Real.log n) + 2 * Real.log (Real.log n) := by ring
    linarith
  have hB2 : Real.log B ≤ ε / 2 * Real.log n := by
    have h1 : 2 / ε * |Real.log B| ≤ Real.log n := hbig2
    have h2 : |Real.log B| ≤ ε / 2 * Real.log n := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hε] at h1
      linarith
    linarith
  rw [div_eq_mul_inv, ← mul_assoc, ← div_eq_mul_inv, div_le_iff₀ hlln]
  nlinarith

/-- **Depth `8 log n / log log n` suffices.** -/
theorem wildSaddle_depth_upper (k : ℕ → ℕ)
    (hk : ∀ᶠ n : ℕ in atTop, 8 * (Real.log n / Real.log (Real.log n)) ≤ k n) :
    Tendsto (fun n => |wildSaddleOrdinate n (k n) - routeKRVMQuantile n|) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hlim : Tendsto (fun n : ℕ => 8 * Real.pi * (((n : ℝ) + 1 / 8) / (n : ℝ) ^ 2)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1 / 8) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
      have ha : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      have hb : Tendsto (fun n : ℕ => (1 / 8 : ℝ) * (((n : ℝ))⁻¹) ^ 2) atTop (𝓝 0) := by
        simpa using (ha.pow 2).const_mul (1 / 8 : ℝ)
      have hab := ha.add hb
      rw [add_zero] at hab
      refine hab.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    simpa using h1.const_mul (8 * Real.pi)
  refine squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _)) ?_ hlim
  filter_upwards [hk, eventually_wildSaddleOrdinate_bounds, eventually_wildSaddle_quantile,
    eventually_log_le_wildSaddleLogPhase_add_one, hlog.eventually_ge_atTop 2,
    hloglog.eventually_ge_atTop (2 * Real.log 2), eventually_ge_atTop 1]
    with n hkn hbd ⟨hN, hL, _, _⟩ hLge hn2 hnn hn1
  refine (hbd (k n)).2.trans ?_
  set L := wildSaddleLogPhase n
  have hL0 : 0 < L := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlogL : Real.log L ≤ L ^ 2 := by
    have := Real.log_le_sub_one_of_pos hL0
    nlinarith
  -- `L ≥ (log n)/2`, hence `log L ≥ log log n / 2`
  have hLhalf : Real.log n / 2 ≤ L := by linarith
  have hlogLge : Real.log (Real.log n) / 2 ≤ Real.log L := by
    have h1 := Real.log_le_log (by linarith) hLhalf
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    linarith
  -- `log (L/2) ≥ log L / 2`
  have hlogL2 : Real.log L / 2 ≤ Real.log (L / 2) := by
    rw [Real.log_div hL0.ne' (by norm_num)]
    have : 2 * Real.log 2 ≤ Real.log L := by
      rw [← Real.log_rpow (by norm_num), show ((2 : ℝ) ^ (2 : ℝ)) = 4 by norm_num]
      exact Real.log_le_log (by norm_num) hL
    linarith
  have hlln : 0 < Real.log (Real.log n) := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  -- `(L/2)^k ≥ n²`
  have hkl : 2 * Real.log n ≤ (k n : ℝ) * Real.log (L / 2) := by
    have h8 : 8 * Real.log n ≤ (k n : ℝ) * Real.log (Real.log n) := by
      rwa [div_eq_mul_inv, ← mul_assoc, ← div_eq_mul_inv, div_le_iff₀ hlln] at hkn
    have hkn0 : (0 : ℝ) ≤ k n := Nat.cast_nonneg _
    nlinarith
  have hpow : (n : ℝ) ^ 2 ≤ (L / 2) ^ (k n) := by
    have h1 : Real.exp (2 * Real.log n) = (n : ℝ) ^ 2 := by
      rw [show 2 * Real.log n = (2 : ℕ) * Real.log n by norm_num, Real.exp_nat_mul,
        Real.exp_log hn0]
    have h2 : Real.exp ((k n : ℝ) * Real.log (L / 2)) = (L / 2) ^ (k n) := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
    rw [← h1, ← h2]
    exact Real.exp_le_exp.mpr hkl
  have h2L : (2 / L) ^ (k n) ≤ 1 / (n : ℝ) ^ 2 := by
    rw [show 2 / L = (L / 2)⁻¹ by field_simp, inv_pow, one_div]
    exact inv_anti₀ (by positivity) hpow
  rw [hN]
  have h1 : Real.log L / L ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hlogL
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  calc 8 * Real.pi * ((n : ℝ) + 1 / 8) * Real.log L / L ^ 2 * (2 / L) ^ (k n)
      = 8 * Real.pi * ((n : ℝ) + 1 / 8) * (Real.log L / L ^ 2) * (2 / L) ^ (k n) := by ring
    _ ≤ 8 * Real.pi * ((n : ℝ) + 1 / 8) * 1 * (1 / (n : ℝ) ^ 2) := by
        gcongr
    _ = 8 * Real.pi * (((n : ℝ) + 1 / 8) / (n : ℝ) ^ 2) := by ring

/-! ### The exact depth-two count defect -/

/-- **The count identity (2).**  `C(t₂) = N v₃/v₂ + 7/8`. -/
theorem routeKSmoothRVMCount_wildSaddleOrdinate_two (n : ℕ) :
    routeKSmoothRVMCount (wildSaddleOrdinate n 2) =
      wildSaddleMass n * wildSaddleIterate (wildSaddleLogPhase n) 3 /
        wildSaddleIterate (wildSaddleLogPhase n) 2 + 7 / 8 := by
  have hL := routePTwoStepWildSaddleLogPhase_ge_two n
  have hv2 : 0 < wildSaddleIterate (wildSaddleLogPhase n) 2 := by
    have := (wildSaddleIterate_mem hL 2).1
    have := half_le_sub_log (show 0 < wildSaddleLogPhase n by linarith)
    linarith
  have hN := routePTwoStepWildSaddleMass_pos n
  rw [routeKSmoothRVMCount, wildSaddleOrdinate, wildSaddleIterate_succ (wildSaddleLogPhase n) 2]
  have hlog : Real.log (2 * Real.pi * wildSaddleMass n /
      wildSaddleIterate (wildSaddleLogPhase n) 2 / routeKRVMBase) =
      wildSaddleLogPhase n - Real.log (wildSaddleIterate (wildSaddleLogPhase n) 2) := by
    rw [routeKRVMBase, show 2 * Real.pi * wildSaddleMass n /
        wildSaddleIterate (wildSaddleLogPhase n) 2 / (2 * Real.pi * Real.exp 1) =
        (wildSaddleMass n / Real.exp 1) / wildSaddleIterate (wildSaddleLogPhase n) 2 by
          field_simp,
      Real.log_div (by positivity) hv2.ne']
    rfl
  rw [hlog]
  field_simp

/-- **The count defect (2).**  `(N + 7/8) − C(t₂) = N log(v₂/v₁)/v₂ > 0`. -/
theorem wildSaddle_countDefect_eq (n : ℕ) :
    (wildSaddleMass n + 7 / 8) - routeKSmoothRVMCount (wildSaddleOrdinate n 2) =
      wildSaddleMass n * Real.log (wildSaddleIterate (wildSaddleLogPhase n) 2 /
        wildSaddleIterate (wildSaddleLogPhase n) 1) / wildSaddleIterate (wildSaddleLogPhase n) 2 := by
  have hL := routePTwoStepWildSaddleLogPhase_ge_two n
  have hL0 : 0 < wildSaddleLogPhase n := by linarith
  have ha := half_le_sub_log hL0
  have hv1 : 0 < wildSaddleIterate (wildSaddleLogPhase n) 1 := by
    linarith [(wildSaddleIterate_mem hL 1).1]
  have hv2 : 0 < wildSaddleIterate (wildSaddleLogPhase n) 2 := by
    linarith [(wildSaddleIterate_mem hL 2).1]
  rw [routeKSmoothRVMCount_wildSaddleOrdinate_two, Real.log_div hv2.ne' hv1.ne',
    wildSaddleIterate_succ (wildSaddleLogPhase n) 2]
  have h2 : wildSaddleIterate (wildSaddleLogPhase n) 2 =
      wildSaddleLogPhase n - Real.log (wildSaddleIterate (wildSaddleLogPhase n) 1) :=
    wildSaddleIterate_succ _ 1
  field_simp
  rw [h2]
  ring

theorem wildSaddle_countDefect_pos (n : ℕ) :
    0 < (wildSaddleMass n + 7 / 8) - routeKSmoothRVMCount (wildSaddleOrdinate n 2) := by
  rw [wildSaddle_countDefect_eq]
  have hL := routePTwoStepWildSaddleLogPhase_ge_two n
  have hL0 : 0 < wildSaddleLogPhase n := by linarith
  have ha := half_le_sub_log hL0
  have hv1 : 0 < wildSaddleIterate (wildSaddleLogPhase n) 1 := by
    linarith [(wildSaddleIterate_mem hL 1).1]
  have hv2 : 0 < wildSaddleIterate (wildSaddleLogPhase n) 2 := by
    linarith [(wildSaddleIterate_mem hL 2).1]
  have hlt : wildSaddleIterate (wildSaddleLogPhase n) 1 <
      wildSaddleIterate (wildSaddleLogPhase n) 2 := by
    rw [wildSaddleIterate_succ _ 1, wildSaddleIterate_one]
    rw [routePTwoStepWildSaddleFirstPhase]
    have hlogL : 0 < Real.log (wildSaddleLogPhase n) := Real.log_pos (by linarith)
    have hv1' : routePTwoStepWildSaddleFirstPhase n < wildSaddleLogPhase n := by
      rw [routePTwoStepWildSaddleFirstPhase]; linarith
    have := Real.log_lt_log (by rw [← wildSaddleIterate_one]; exact hv1) hv1'
    rw [routePTwoStepWildSaddleFirstPhase] at this
    linarith
  have := Real.log_pos ((one_lt_div hv1).mpr hlt)
  exact div_pos (mul_pos (routePTwoStepWildSaddleMass_pos n) this) hv2


/-! ### Asymptotics of the depth-two defect -/

theorem tendsto_log_natCast : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `N_n ∼ n`. -/
theorem isEquivalent_wildSaddleMass :
    (fun n => wildSaddleMass n) ~[atTop] (fun n : ℕ => (n : ℝ)) := by
  show (fun n => wildSaddleMass n - (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ))
  have h : (fun _ : ℕ => (1 / 8 : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) :=
    isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_wildSaddleMass_eq] with n hn
  rw [hn]; ring

/-- `L_n ∼ log n`. -/
theorem isEquivalent_wildSaddleLogPhase :
    (fun n => wildSaddleLogPhase n) ~[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
  show (fun n => wildSaddleLogPhase n - Real.log (n : ℝ)) =o[atTop] _
  have h1 : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)) :=
    isLittleO_const_left.2 (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_log_natCast))
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 ?_) h1
  filter_upwards [eventually_wildSaddleLogPhase_le_log, eventually_log_le_wildSaddleLogPhase_add_one]
    with n h1 h2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one, mul_one, abs_le]
  constructor <;> linarith

/-- `log L_n ∼ log log n`. -/
theorem isEquivalent_log_wildSaddleLogPhase :
    (fun n => Real.log (wildSaddleLogPhase n)) ~[atTop]
      (fun n : ℕ => Real.log (Real.log (n : ℝ))) :=
  isEquivalent_wildSaddleLogPhase.log tendsto_log_natCast

theorem tendsto_log_wildSaddleLogPhase_div :
    Tendsto (fun n => Real.log (wildSaddleLogPhase n) / wildSaddleLogPhase n) atTop (𝓝 0) :=
  (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_wildSaddleLogPhase

/-- Every iterate is asymptotic to the log phase: `v_{k,n} ∼ L_n`. -/
theorem isEquivalent_wildSaddleIterate (k : ℕ) :
    (fun n => wildSaddleIterate (wildSaddleLogPhase n) k) ~[atTop]
      (fun n => wildSaddleLogPhase n) := by
  show (fun n => wildSaddleIterate (wildSaddleLogPhase n) k - wildSaddleLogPhase n) =o[atTop] _
  have h : (fun n => Real.log (wildSaddleLogPhase n)) =o[atTop]
      (fun n => wildSaddleLogPhase n) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_wildSaddleLogPhase
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 ?_) h
  filter_upwards with n
  obtain ⟨h1, h2⟩ := wildSaddleIterate_mem (routePTwoStepWildSaddleLogPhase_ge_two n) k
  have hlog : 0 ≤ Real.log (wildSaddleLogPhase n) :=
    Real.log_nonneg (by linarith [routePTwoStepWildSaddleLogPhase_ge_two n])
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg hlog, abs_le]
  constructor <;> linarith

/-- `t_{n,2} ∼ 2πn/log n`. -/
theorem isEquivalent_wildSaddleOrdinate_two :
    (fun n => wildSaddleOrdinate n 2) ~[atTop]
      (fun n : ℕ => 2 * Real.pi * (n : ℝ) / Real.log (n : ℝ)) := by
  have h1 : (fun n => 2 * Real.pi * wildSaddleMass n) ~[atTop]
      (fun n : ℕ => 2 * Real.pi * (n : ℝ)) :=
    (IsEquivalent.refl (u := fun _ : ℕ => 2 * Real.pi)).mul isEquivalent_wildSaddleMass
  have h2 := (isEquivalent_wildSaddleIterate 2).trans isEquivalent_wildSaddleLogPhase
  exact h1.div h2

/-- The ratio bounds behind the defect asymptotic: `1 ≤ R ≤ (L/(L − log L))³`. -/
theorem wildSaddle_countDefect_ratio_bounds {n : ℕ} (hL : 4 ≤ wildSaddleLogPhase n) :
    1 ≤ ((wildSaddleMass n + 7 / 8) - routeKSmoothRVMCount (wildSaddleOrdinate n 2)) /
        (wildSaddleMass n * Real.log (wildSaddleLogPhase n) / wildSaddleLogPhase n ^ 3) ∧
      ((wildSaddleMass n + 7 / 8) - routeKSmoothRVMCount (wildSaddleOrdinate n 2)) /
          (wildSaddleMass n * Real.log (wildSaddleLogPhase n) / wildSaddleLogPhase n ^ 3) ≤
        (wildSaddleLogPhase n / (wildSaddleLogPhase n - Real.log (wildSaddleLogPhase n))) ^ 3 := by
  rw [wildSaddle_countDefect_eq]
  set L := wildSaddleLogPhase n with hLdef
  set N := wildSaddleMass n
  have hN : 0 < N := routePTwoStepWildSaddleMass_pos n
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  have ha := half_le_sub_log hL0
  have hv1eq : wildSaddleIterate L 1 = L - Real.log L := by
    rw [wildSaddleIterate_succ, wildSaddleIterate_zero]
  have hv2eq : wildSaddleIterate L 2 = L - Real.log (wildSaddleIterate L 1) :=
    wildSaddleIterate_succ L 1
  set v1 := wildSaddleIterate L 1
  set v2 := wildSaddleIterate L 2
  obtain ⟨h1lo, h1hi⟩ := wildSaddleIterate_mem (L := L) (by linarith) 1
  obtain ⟨h2lo, h2hi⟩ := wildSaddleIterate_mem (L := L) (by linarith) 2
  have hv10 : 0 < v1 := by linarith
  have hv20 : 0 < v2 := by linarith
  have hv12 : v1 ≤ v2 := by
    rw [hv2eq, hv1eq]
    have : Real.log (L - Real.log L) ≤ Real.log L := Real.log_le_log (by linarith) (by linarith)
    linarith
  -- `log(L/v₁)` between `log L / L` and `log L / v₁`
  have hw : v2 - v1 = Real.log (L / v1) := by
    rw [Real.log_div hL0.ne' hv10.ne', hv2eq, hv1eq]; ring
  have hwlo : Real.log L / L ≤ v2 - v1 := by
    rw [hw]
    have := Real.one_sub_inv_le_log_of_pos (div_pos hL0 hv10)
    rw [inv_div] at this
    have h : 1 - v1 / L = Real.log L / L := by
      rw [one_sub_div hL0.ne']; congr 1; rw [hv1eq]; ring
    linarith
  have hwhi : v2 - v1 ≤ Real.log L / v1 := by
    rw [hw]
    have := Real.log_le_sub_one_of_pos (div_pos hL0 hv10)
    have h : L / v1 - 1 = Real.log L / v1 := by
      rw [div_sub_one hv10.ne']; congr 1; rw [hv1eq]; ring
    linarith
  have hr0 : 0 < Real.log (v2 / v1) := by
    have hlt : v1 < v2 := by
      have : 0 < Real.log L / L := div_pos hlogL hL0
      linarith
    exact Real.log_pos ((one_lt_div hv10).mpr hlt)
  have hden : 0 < N * Real.log L / L ^ 3 := by positivity
  have hratio : N * Real.log (v2 / v1) / v2 / (N * Real.log L / L ^ 3) =
      L ^ 3 * Real.log (v2 / v1) / (v2 * Real.log L) := by
    field_simp
  rw [hratio]
  constructor
  · -- `log(v₂/v₁) ≥ (v₂ − v₁)/v₂ ≥ log L/(L v₂)`
    have hlog1 : (v2 - v1) / v2 ≤ Real.log (v2 / v1) := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos hv20 hv10)
      rw [inv_div] at this
      have h : 1 - v1 / v2 = (v2 - v1) / v2 := by field_simp
      linarith
    have hlog2 : Real.log L / (L * v2) ≤ Real.log (v2 / v1) := by
      refine le_trans ?_ hlog1
      rw [div_mul_eq_div_div]
      exact div_le_div_of_nonneg_right hwlo hv20.le
    rw [le_div_iff₀ (by positivity), one_mul]
    have hL2 : v2 * Real.log L ≤ L ^ 3 * (Real.log L / (L * v2)) := by
      rw [show L ^ 3 * (Real.log L / (L * v2)) = L ^ 2 * Real.log L / v2 by
        field_simp]
      rw [le_div_iff₀ hv20]
      have : v2 * v2 ≤ L ^ 2 := by nlinarith
      nlinarith
    exact hL2.trans (mul_le_mul_of_nonneg_left hlog2 (by positivity))
  · -- `log(v₂/v₁) ≤ (v₂ − v₁)/v₁ ≤ log L / v₁²`
    have hlog1 : Real.log (v2 / v1) ≤ (v2 - v1) / v1 := by
      have := Real.log_le_sub_one_of_pos (div_pos hv20 hv10)
      have h : v2 / v1 - 1 = (v2 - v1) / v1 := by field_simp
      linarith
    have hlog2 : Real.log (v2 / v1) ≤ Real.log L / v1 ^ 2 := by
      refine hlog1.trans ?_
      rw [pow_two, ← div_div]
      exact div_le_div_of_nonneg_right hwhi hv10.le
    rw [div_le_iff₀ (by positivity), ← hv1eq]
    calc L ^ 3 * Real.log (v2 / v1) ≤ L ^ 3 * (Real.log L / v1 ^ 2) :=
          mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ = (L / v1) ^ 3 * (v1 * Real.log L) := by field_simp
      _ ≤ (L / v1) ^ 3 * (v2 * Real.log L) := by
          gcongr

/-- **The defect asymptotic.**  `(N + 7/8) − C(t₂) ∼ N log L / L³`. -/
theorem isEquivalent_wildSaddle_countDefect :
    (fun n => (wildSaddleMass n + 7 / 8) - routeKSmoothRVMCount (wildSaddleOrdinate n 2)) ~[atTop]
      (fun n => wildSaddleMass n * Real.log (wildSaddleLogPhase n) / wildSaddleLogPhase n ^ 3) := by
  refine isEquivalent_of_tendsto_one ?_
  have hup : Tendsto (fun n => (wildSaddleLogPhase n /
      (wildSaddleLogPhase n - Real.log (wildSaddleLogPhase n))) ^ 3) atTop (𝓝 1) := by
    have h : Tendsto (fun n => (1 - Real.log (wildSaddleLogPhase n) / wildSaddleLogPhase n)⁻¹)
        atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_log_wildSaddleLogPhase_div
      rw [sub_zero] at this
      simpa using this.inv₀ one_ne_zero
    have h3 := h.pow 3
    rw [one_pow] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_four_le_wildSaddleLogPhase] with n hL
    have hL0 : 0 < wildSaddleLogPhase n := by linarith
    have hpos : 0 < wildSaddleLogPhase n - Real.log (wildSaddleLogPhase n) := by
      linarith [half_le_sub_log hL0]
    congr 1
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_four_le_wildSaddleLogPhase] with n hL
    exact (wildSaddle_countDefect_ratio_bounds hL).1
  · filter_upwards [eventually_four_le_wildSaddleLogPhase] with n hL
    exact (wildSaddle_countDefect_ratio_bounds hL).2

/-- **The defect asymptotic, in the rank variable.**
`(N + 7/8) − C(t_{n,2}) ∼ n log log n / (log n)³`. -/
theorem isEquivalent_wildSaddle_countDefect_rank :
    (fun n => (wildSaddleMass n + 7 / 8) - routeKSmoothRVMCount (wildSaddleOrdinate n 2)) ~[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ^ 3) :=
  isEquivalent_wildSaddle_countDefect.trans
    ((isEquivalent_wildSaddleMass.mul isEquivalent_log_wildSaddleLogPhase).div
      (isEquivalent_wildSaddleLogPhase.pow 3))

/-- **The depth-two physical gap has order `n log log n/(log n)⁴`.** -/
theorem isTheta_wildSaddleOrdinate_two_sub_quantile :
    (fun n => |wildSaddleOrdinate n 2 - routeKRVMQuantile n|) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ^ 4) := by
  have hequiv : (fun n => wildSaddleMass n * Real.log (wildSaddleLogPhase n) /
      wildSaddleLogPhase n ^ 4) ~[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ^ 4) :=
    (isEquivalent_wildSaddleMass.mul isEquivalent_log_wildSaddleLogPhase).div
      (isEquivalent_wildSaddleLogPhase.pow 4)
  refine IsTheta.trans_isEquivalent ⟨IsBigO.of_bound (32 * Real.pi) ?_,
    IsBigO.of_bound (1 / Real.pi) ?_⟩ hequiv
  · filter_upwards [eventually_wildSaddleOrdinate_bounds, eventually_four_le_wildSaddleLogPhase]
      with n hb hL
    have hL0 : 0 < wildSaddleLogPhase n := by linarith
    have hpos : 0 ≤ wildSaddleMass n * Real.log (wildSaddleLogPhase n) / wildSaddleLogPhase n ^ 4 :=
      div_nonneg (mul_nonneg (routePTwoStepWildSaddleMass_pos n).le
        (Real.log_nonneg (by linarith))) (by positivity)
    simp only [Real.norm_eq_abs, abs_abs]
    rw [abs_of_nonneg hpos]
    refine (hb 2).2.trans (le_of_eq ?_)
    field_simp
    ring
  · filter_upwards [eventually_wildSaddleOrdinate_bounds, eventually_four_le_wildSaddleLogPhase]
      with n hb hL
    have hL0 : 0 < wildSaddleLogPhase n := by linarith
    have hpos : 0 ≤ wildSaddleMass n * Real.log (wildSaddleLogPhase n) / wildSaddleLogPhase n ^ 4 :=
      div_nonneg (mul_nonneg (routePTwoStepWildSaddleMass_pos n).le
        (Real.log_nonneg (by linarith))) (by positivity)
    simp only [Real.norm_eq_abs, abs_abs]
    rw [abs_of_nonneg hpos]
    have h := (hb 2).1
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ Real.pi_pos]
    calc wildSaddleMass n * Real.log (wildSaddleLogPhase n) / wildSaddleLogPhase n ^ 4 * Real.pi
        = Real.pi * wildSaddleMass n * Real.log (wildSaddleLogPhase n) /
            wildSaddleLogPhase n ^ (2 + 2) := by ring
      _ ≤ _ := h

/-! ### Comparison with the ordered Xi ordinates -/

/-- **No fixed depth has eventual rankwise occurrence.**  For every fixed `k`,
`|t_{n,k} − γ_n| → ∞`, where `γ_n` is the `n`th ordered positive Xi ordinate. -/
theorem tendsto_abs_wildSaddleOrdinate_sub_xiOrdinate_fixed (k : ℕ) :
    Tendsto (fun n => |wildSaddleOrdinate n k - xiOrderedPositiveOrdinate n|) atTop atTop := by
  obtain ⟨D, _, hD⟩ := exists_eventually_abs_xiOrderedPositiveOrdinate_sub_routeKRVMQuantile_le
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_right _ (-D) (tendsto_abs_wildSaddleOrdinate_sub_quantile_fixed k))
  filter_upwards [hD] with n hn
  have := abs_sub_abs_le_abs_sub (wildSaddleOrdinate n k - routeKRVMQuantile n)
    (xiOrderedPositiveOrdinate n - routeKRVMQuantile n)
  rw [show wildSaddleOrdinate n k - routeKRVMQuantile n -
      (xiOrderedPositiveOrdinate n - routeKRVMQuantile n) =
      wildSaddleOrdinate n k - xiOrderedPositiveOrdinate n by ring] at this
  linarith

/-- **The adaptive depth lands within the RVM–Xi constant.**  There is `D` with
`|t_{n,n} − γ_n| ≤ D + ε` eventually, for every `ε > 0`. -/
theorem exists_eventually_abs_wildSaddleOrdinate_diagonal_sub_xiOrdinate_le :
    ∃ D : ℝ, 0 < D ∧ ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      |wildSaddleOrdinate n n - xiOrderedPositiveOrdinate n| ≤ D + ε := by
  obtain ⟨D, hD0, hD⟩ := exists_eventually_abs_xiOrderedPositiveOrdinate_sub_routeKRVMQuantile_le
  refine ⟨D, hD0, fun ε hε => ?_⟩
  filter_upwards [hD, (tendsto_order.1 tendsto_abs_wildSaddleOrdinate_sub_quantile_diagonal).2
    ε hε] with n hn hε'
  have := abs_sub_le (wildSaddleOrdinate n n) (routeKRVMQuantile n) (xiOrderedPositiveOrdinate n)
  rw [abs_sub_comm (routeKRVMQuantile n)] at this
  linarith

/-! ### The missed ordered heights at depth two -/

theorem tendsto_wildSaddleOrdinate_two : Tendsto (fun n => wildSaddleOrdinate n 2) atTop atTop := by
  have h : Tendsto (fun n => Real.exp (wildSaddleLogPhase n) / wildSaddleLogPhase n ^ 1)
      atTop atTop := (Real.tendsto_exp_div_pow_atTop 1).comp tendsto_wildSaddleLogPhase
  have hc : 0 < 2 * Real.pi * Real.exp 1 := by positivity
  refine tendsto_atTop_mono' atTop ?_ (h.const_mul_atTop hc)
  filter_upwards [eventually_four_le_wildSaddleLogPhase] with n hL
  have hL0 : 0 < wildSaddleLogPhase n := by linarith
  obtain ⟨h2lo, h2hi⟩ := wildSaddleIterate_mem (L := wildSaddleLogPhase n) (by linarith) 2
  have hv2 : 0 < wildSaddleIterate (wildSaddleLogPhase n) 2 := by
    linarith [half_le_sub_log hL0]
  rw [wildSaddleOrdinate, wildSaddleMass_eq_exp, pow_one]
  rw [mul_div_assoc', div_le_div_iff₀ hL0 hv2]
  have : 0 ≤ 2 * Real.pi * (Real.exp 1 * Real.exp (wildSaddleLogPhase n)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2hi this]

theorem isLittleO_log_rank_countScale :
    (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ^ 3) := by
  have hpow : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ 4 / (n : ℝ)) atTop (𝓝 0) :=
    ((Real.isLittleO_pow_log_id_atTop (n := 4)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_log_natCast
  rw [isLittleO_iff_tendsto']
  · refine squeeze_zero' ?_ ?_ hpow
    · filter_upwards [hll.eventually_ge_atTop 1, tendsto_log_natCast.eventually_ge_atTop 1]
        with n h1 h2
      have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      positivity
    · filter_upwards [hll.eventually_ge_atTop 1, tendsto_log_natCast.eventually_ge_atTop 1,
        eventually_ge_atTop 1] with n h1 h2 h3
      have hn : (0 : ℝ) < n := by exact_mod_cast h3
      rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hn]
      have hl0 : 0 < Real.log (n : ℝ) := by linarith
      have : Real.log (n : ℝ) * Real.log (n : ℝ) ^ 3 * n ≤
          Real.log (n : ℝ) ^ 4 * ((n : ℝ) * Real.log (Real.log (n : ℝ))) := by
        have h4 : Real.log (n : ℝ) * Real.log (n : ℝ) ^ 3 = Real.log (n : ℝ) ^ 4 := by ring
        rw [h4]
        have : (0 : ℝ) ≤ Real.log (n : ℝ) ^ 4 * n := by positivity
        nlinarith
      linarith
  · filter_upwards [tendsto_log_natCast.eventually_ge_atTop 1,
      (Real.tendsto_log_atTop.comp tendsto_log_natCast).eventually_ge_atTop 1,
      eventually_ge_atTop 1] with n h1 h2 h3 h0
    have hn : (0 : ℝ) < n := by exact_mod_cast h3
    have h2 : 1 ≤ Real.log (Real.log (n : ℝ)) := h2
    exfalso
    have : 0 < (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ^ 3 := by
      have : 0 < Real.log (Real.log (n : ℝ)) := by linarith
      have : 0 < Real.log (n : ℝ) := by linarith
      positivity
    exact this.ne' h0

/-- **The missed ordered zero heights at the depth-two pseudo-ordinate.**  Without assuming RH,
`(n + 1) − N_ξ(t_{n,2}) ∼ n log log n / (log n)³`. -/
theorem isEquivalent_wildSaddle_missedZeroCount :
    (fun n : ℕ => ((n : ℝ) + 1) - (xiZeroCount (wildSaddleOrdinate n 2) : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ^ 3) := by
  obtain ⟨C, hC, T₀, hT₀, hrem⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  set g := fun n : ℕ => (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ^ 3
  have he : (fun n : ℕ => routeKSmoothRVMCount (wildSaddleOrdinate n 2) -
      (xiZeroCount (wildSaddleOrdinate n 2) : ℝ)) =o[atTop] g := by
    refine IsBigO.trans_isLittleO (IsBigO.of_bound (2 * C) ?_) isLittleO_log_rank_countScale
    filter_upwards [tendsto_wildSaddleOrdinate_two.eventually_ge_atTop T₀,
      eventually_four_le_wildSaddleLogPhase, eventually_wildSaddleMass_eq,
      eventually_ge_atTop 8] with n ht hL hN hn
    have hrn := hrem _ ht
    rw [abs_sub_comm] at hrn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
    have hL0 : 0 < wildSaddleLogPhase n := by linarith
    obtain ⟨h2lo, h2hi⟩ := wildSaddleIterate_mem (L := wildSaddleLogPhase n) (by linarith) 2
    have hv2 : wildSaddleLogPhase n / 2 ≤ wildSaddleIterate (wildSaddleLogPhase n) 2 := by
      linarith [half_le_sub_log hL0]
    have htpos : 0 < wildSaddleOrdinate n 2 := by linarith
    -- `t ≤ n²`
    have htle : wildSaddleOrdinate n 2 ≤ (n : ℝ) ^ 2 := by
      rw [wildSaddleOrdinate, hN, div_le_iff₀ (by linarith)]
      have hpi := Real.pi_lt_four
      have h1 : 2 * Real.pi * ((n : ℝ) + 1 / 8) ≤ (n : ℝ) ^ 2 * 2 := by nlinarith
      nlinarith
    have hlogt : Real.log (wildSaddleOrdinate n 2) ≤ 2 * Real.log (n : ℝ) := by
      have := Real.log_le_log htpos htle
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith))]
    calc |routeKSmoothRVMCount (wildSaddleOrdinate n 2) - (xiZeroCount (wildSaddleOrdinate n 2) : ℝ)|
        ≤ C * Real.log (wildSaddleOrdinate n 2) := hrn
      _ ≤ C * (2 * Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hlogt hC.le
      _ = 2 * C * Real.log (n : ℝ) := by ring
  have hsum := isEquivalent_wildSaddle_countDefect_rank.add_isLittleO he
  refine hsum.congr_left ?_
  filter_upwards [eventually_wildSaddleMass_eq] with n hN
  simp only [Pi.add_apply]
  rw [hN]
  ring

end

end RHTower
