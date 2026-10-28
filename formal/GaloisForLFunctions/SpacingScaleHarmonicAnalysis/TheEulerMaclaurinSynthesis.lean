import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSecondOrderSynthesis
import GaloisForLFunctions.RHTower.DQPTEulerMaclaurin

/-!
# The Euler–Maclaurin synthesis

The atoms `log n` are the image of the integers under `log`. Weighting the atom `log n` by
`F(log n − c)/n` turns the synthesis `Σ_n F(log n − c)/n · ψ(r + c − log n)` into the sum over the
integers of `s ↦ s⁻¹ H(log s)` with `H(t) = F(t − c) ψ(r + c − t)`, whose integral is `(F ∗ ψ)(r)`.
Euler–Maclaurin summation to order `p` bounds the error by `∫ |(d/ds)^p [s⁻¹ H(log s)]|`, and the
substitution `s = e^t` turns this into `n₀^{−p}` times the `L¹` norm of `p` derivatives of `H`:
the error is `O((k/n₀)^p)` for atoms of width `1/k` starting at `n₀`.

* **The logarithmic tower** (`logTower`, `hasDerivAt_logTowerS`):
  `(d/ds)^j [s⁻¹ H(log s)] = s^{−(j+1)} T_j(log s)` with `T_0 = H`, `T_{j+1} = T_j′ − (j+1) T_j`.
* **Euler–Maclaurin on the log-lattice** (`abs_sum_logTowerS_sub_integral_le`): for a smooth `H`
  vanishing off `[α, β]`, `0 < α`, `β < log(1 + N)`,
  `|Σ_{n ≤ N+1} n⁻¹ H(log n) − ∫ H| ≤ (|B_p|/p!) e^{−pα} ‖T_p‖₁`, `p = 2m + 2`.
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower RHTower.DQPT
open scoped Real ContDiff

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

/-! ### The logarithmic tower -/

/-- `T_0 = H`, `T_{j+1} = T_j′ − (j + 1) T_j`: the `j`-th derivative of `s ↦ s⁻¹ H(log s)` is
`s^{−(j+1)} T_j(log s)`. -/
def logTower (H : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => H
  | j + 1 => fun t => deriv (logTower H j) t - (j + 1) * logTower H j t

/-- `s ↦ s^{−(j+1)} T_j(log s)`. -/
def logTowerS (H : ℝ → ℝ) (j : ℕ) (s : ℝ) : ℝ := s⁻¹ ^ (j + 1) * logTower H j (Real.log s)

variable {H : ℝ → ℝ}

theorem logTower_succ (j : ℕ) (t : ℝ) :
    logTower H (j + 1) t = deriv (logTower H j) t - (j + 1) * logTower H j t := rfl

theorem contDiff_logTower (hH : ContDiff ℝ ∞ H) (j : ℕ) : ContDiff ℝ ∞ (logTower H j) := by
  induction j with
  | zero => exact hH
  | succ j ih =>
    exact (contDiff_infty_iff_deriv.mp ih).2.sub (contDiff_const.mul ih)

/-- The tower vanishes wherever `H` vanishes near the point: off `[α, β]`. -/
theorem logTower_eq_zero {α β : ℝ} (hH : ∀ t, t ∉ Icc α β → H t = 0) (j : ℕ) :
    ∀ t, t ∉ Icc α β → logTower H j t = 0 := by
  induction j with
  | zero => exact hH
  | succ j ih =>
    intro t ht
    have hev : logTower H j =ᶠ[𝓝 t] fun _ => 0 :=
      Filter.eventually_of_mem (isClosed_Icc.isOpen_compl.mem_nhds ht) fun s hs => ih s hs
    rw [logTower_succ, hev.deriv_eq, deriv_const, ih t ht]
    ring

/-- **The logarithmic tower is a derivative tower**:
`(s^{−(j+1)} T_j(log s))′ = s^{−(j+2)} T_{j+1}(log s)`. -/
theorem hasDerivAt_logTowerS (hH : ContDiff ℝ ∞ H) (j : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (logTowerS H j) (logTowerS H (j + 1) s) s := by
  have hT : HasDerivAt (logTower H j) (deriv (logTower H j) (Real.log s)) (Real.log s) :=
    ((contDiff_logTower hH j).differentiable (by simp) _).hasDerivAt
  have h2 := hT.comp s (Real.hasDerivAt_log hs.ne')
  have h3 := (hasDerivAt_inv hs.ne').pow (j + 1)
  have hf : logTowerS H j = (fun y : ℝ => y⁻¹) ^ (j + 1) * (logTower H j ∘ Real.log) := by
    funext y; simp only [logTowerS, Pi.mul_apply, Pi.pow_apply, Function.comp]
  rw [hf]
  refine (h3.mul h2).congr_deriv ?_
  simp only [logTowerS, logTower_succ, Nat.add_sub_cancel, Pi.pow_apply, Function.comp]
  rw [← inv_pow]
  push_cast
  ring

theorem dqptDerivTower_logTowerS (hH : ContDiff ℝ ∞ H) {a b : ℝ} (ha : 0 < a) :
    DqptDerivTower (logTowerS H) (Icc a b) :=
  fun j _ hx => hasDerivAt_logTowerS hH j (lt_of_lt_of_le ha hx.1)

/-! ### Change of variables `s = e^t` -/

theorem continuous_logTower (hH : ContDiff ℝ ∞ H) (j : ℕ) : Continuous (logTower H j) :=
  (contDiff_logTower hH j).continuous

/-- `∫_a^b s⁻¹ G(log s) ds = ∫_{log a}^{log b} G`. -/
theorem integral_inv_mul_comp_log {G : ℝ → ℝ} (hG : Continuous G) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) : ∫ s in a..b, s⁻¹ * G (Real.log s) = ∫ t in Real.log a..Real.log b, G t := by
  have hpos : ∀ x ∈ uIcc a b, 0 < x := fun x hx => by
    rw [uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
  have h := intervalIntegral.integral_comp_mul_deriv (f := Real.log) (f' := fun x => x⁻¹) (g := G)
    (fun x hx => Real.hasDerivAt_log (hpos x hx).ne')
    (continuousOn_inv₀.mono fun x hx => (hpos x hx).ne') hG
  rw [← h]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [Function.comp]
  ring

/-! ### Euler–Maclaurin on the log-lattice -/

/-- The Euler–Maclaurin cell integral of order `2m + 2` is at most
`(|B_{2m+2}|/(2m+2)!) ∫_t^{t+1} |F_{2m+2}|`. -/
theorem abs_dqptEMJ_le {F : ℕ → ℝ → ℝ} {t : ℝ} (m : ℕ)
    (hF : ContinuousOn (F (2 * m + 2)) (Icc t (t + 1))) :
    |dqptEMJ F (2 * m + 2) t| ≤ |((bernoulli (2 * m + 2) : ℚ) : ℝ)| /
      ((2 * m + 2).factorial : ℝ) * ∫ x in t..t + 1, |F (2 * m + 2) x| := by
  unfold dqptEMJ
  have htt : t ≤ t + 1 := by linarith
  have hu : uIcc t (t + 1) = Icc t (t + 1) := uIcc_of_le htt
  have hb : ∀ x ∈ Icc t (t + 1),
      |bernoulliFun (2 * m + 2) (x - t)| ≤ |((bernoulli (2 * m + 2) : ℚ) : ℝ)| := by
    intro x hx
    have := dqpt_abs_bernoulliFun_le (k := m + 1) (by omega)
      (x := x - t) ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rwa [show 2 * (m + 1) = 2 * m + 2 by ring] at this
  have hfac : (0 : ℝ) < ((2 * m + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hcB : ContinuousOn (fun x => bernoulliFun (2 * m + 2) (x - t)) (Icc t (t + 1)) :=
    ((continuous_bernoulliFun (2 * m + 2)).comp (continuous_id.sub continuous_const)).continuousOn
  have i1 : IntervalIntegrable (fun x => |bernoulliFun (2 * m + 2) (x - t) /
      ((2 * m + 2).factorial : ℝ) * F (2 * m + 2) x|) volume t (t + 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hu]
    exact ((hcB.div_const _).mul hF).abs
  have i2 : IntervalIntegrable (fun x => |((bernoulli (2 * m + 2) : ℚ) : ℝ)| /
      ((2 * m + 2).factorial : ℝ) * |F (2 * m + 2) x|) volume t (t + 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hu]
    exact continuousOn_const.mul hF.abs
  calc |∫ x in t..t + 1, bernoulliFun (2 * m + 2) (x - t) / ((2 * m + 2).factorial : ℝ) *
        F (2 * m + 2) x|
      ≤ ∫ x in t..t + 1, |bernoulliFun (2 * m + 2) (x - t) / ((2 * m + 2).factorial : ℝ) *
          F (2 * m + 2) x| := intervalIntegral.abs_integral_le_integral_abs htt
    _ ≤ ∫ x in t..t + 1, |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
          |F (2 * m + 2) x| := by
        refine intervalIntegral.integral_mono_on htt i1 i2 fun x hx => ?_
        rw [abs_mul, abs_div, abs_of_pos hfac]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hb x hx) hfac.le)
          (abs_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem continuousOn_logTowerS (hH : ContDiff ℝ ∞ H) (j : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (logTowerS H j) (Icc a b) := fun _ hs =>
  (hasDerivAt_logTowerS hH j (lt_of_lt_of_le ha hs.1)).continuousAt.continuousWithinAt

/-- On `[1, 1 + N]`, `|s^{−(p+1)} T_p(log s)| ≤ e^{−pα} s⁻¹ |T_p(log s)|` when `T_p` vanishes
below `α ≥ 0`. -/
theorem abs_logTowerS_le {α β : ℝ} (hH : ∀ t, t ∉ Icc α β → H t = 0) (p : ℕ)
    {s : ℝ} (hs : 1 ≤ s) :
    |logTowerS H p s| ≤ Real.exp (-α) ^ p * (s⁻¹ * |logTower H p (Real.log s)|) := by
  have hs0 : 0 < s := by linarith
  unfold logTowerS
  by_cases hmem : Real.log s ∈ Icc α β
  · have hes : Real.exp α ≤ s := by
      rw [← Real.exp_log hs0]; exact Real.exp_le_exp.mpr hmem.1
    have hinv : s⁻¹ ≤ Real.exp (-α) := by
      rw [Real.exp_neg]; exact inv_anti₀ (Real.exp_pos α) hes
    have hpow : s⁻¹ ^ p ≤ Real.exp (-α) ^ p := pow_le_pow_left₀ (by positivity) hinv p
    rw [abs_mul, abs_of_nonneg (by positivity), pow_succ]
    have := mul_le_mul_of_nonneg_right hpow
      (mul_nonneg (inv_nonneg.mpr hs0.le) (abs_nonneg (logTower H p (Real.log s))))
    linarith
  · rw [logTower_eq_zero hH p _ hmem]
    simp

/-- **Euler–Maclaurin on the log-lattice**: for a smooth `H` vanishing off `[α, β]` with `0 < α`
and `β < log(1 + N)`,
`|Σ_{n ≤ N} (1 + n)⁻¹ H(log(1 + n)) − ∫ H| ≤ (|B_p|/p!) e^{−pα} ‖T_p‖₁`, `p = 2m + 2`. -/
theorem abs_sum_logTowerS_sub_integral_le (hH : ContDiff ℝ ∞ H) {α β : ℝ} (hα : 0 < α)
    (hHsupp : ∀ t, t ∉ Icc α β → H t = 0) {N : ℕ} (hβ : β < Real.log (1 + N)) (m : ℕ) :
    |(∑ n ∈ Finset.range (N + 1), logTowerS H 0 (1 + n)) - ∫ t, H t| ≤
      |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
        (Real.exp (-α) ^ (2 * m + 2) * ∫ t, |logTower H (2 * m + 2) t|) := by
  set p := 2 * m + 2
  set C := |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ)
  have hC : 0 ≤ C := by positivity
  have hN1 : (1 : ℝ) ≤ 1 + N := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hlogN : 0 ≤ Real.log (1 + N) := Real.log_nonneg hN1
  have em := dqpt_euler_maclaurin (F := logTowerS H) (a := 1) m N
    (dqptDerivTower_logTowerS hH one_pos)
  -- the boundary terms vanish
  have h0 : ∀ j, logTowerS H j 1 = 0 := fun j => by
    unfold logTowerS
    rw [Real.log_one, logTower_eq_zero hHsupp j 0 fun h => by linarith [h.1], mul_zero]
  have hNe : ∀ j, logTowerS H j (1 + N) = 0 := fun j => by
    unfold logTowerS
    rw [logTower_eq_zero hHsupp j _ fun h => by linarith [h.2], mul_zero]
  simp only [h0, hNe, sub_self, mul_zero, Finset.sum_const_zero, add_zero, zero_div] at em
  -- the main term is `∫ H`
  have hHc : Continuous H := hH.continuous
  have hint : ∫ s in (1 : ℝ)..1 + N, logTowerS H 0 s = ∫ t, H t := by
    have e1 : ∫ s in (1 : ℝ)..1 + N, logTowerS H 0 s =
        ∫ s in (1 : ℝ)..1 + N, s⁻¹ * H (Real.log s) := by
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [logTowerS, zero_add, pow_one, logTower]
    rw [e1, integral_inv_mul_comp_log hHc one_pos hN1, Real.log_one,
      intervalIntegral.integral_of_le hlogN, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => hHsupp t fun h => ht ?_
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [hint] at em
  rw [em, show ∀ x y : ℝ, x - y - x = -y by intros; ring, abs_neg]
  -- the remainder
  have hcont : ContinuousOn (logTowerS H p) (Icc 1 (1 + N)) := continuousOn_logTowerS hH p one_pos
  have hcells : ∀ n ∈ Finset.range N, |dqptEMJ (logTowerS H) p (1 + n)| ≤
      C * ∫ x in (1 + n : ℝ)..1 + n + 1, |logTowerS H p x| := by
    intro n hn
    refine abs_dqptEMJ_le m (hcont.mono fun x hx => ⟨?_, ?_⟩)
    · have := Nat.cast_nonneg (α := ℝ) n; linarith [hx.1]
    · have : (n : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hn
      linarith [hx.2]
  have hsum : ∑ n ∈ Finset.range N, ∫ x in (1 + n : ℝ)..1 + n + 1, |logTowerS H p x| =
      ∫ x in (1 : ℝ)..1 + N, |logTowerS H p x| := by
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (a := fun n : ℕ => (1 + n : ℝ))
      (f := fun x => |logTowerS H p x|) (n := N) fun k hk => by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le (by push_cast; linarith)]
        refine (hcont.mono fun x hx => ⟨?_, ?_⟩).abs
        · have := Nat.cast_nonneg (α := ℝ) k; linarith [hx.1]
        · have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
          linarith [hx.2]
    simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one] at this
    rw [← this]
    exact Finset.sum_congr rfl fun n _ => by rw [add_assoc]
  -- the tower integral
  have hTc : Continuous (logTower H p) := continuous_logTower hH p
  have hTsupp := logTower_eq_zero hHsupp p
  have hTint : Integrable fun t => |logTower H p t| :=
    (hTc.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc
      fun t ht => hTsupp t ht)).abs
  have htower : ∫ x in (1 : ℝ)..1 + N, |logTowerS H p x| ≤
      Real.exp (-α) ^ p * ∫ t, |logTower H p t| := by
    have i1 : IntervalIntegrable (fun x => |logTowerS H p x|) volume 1 (1 + N) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hN1]; exact hcont.abs
    have i2 : IntervalIntegrable (fun x => Real.exp (-α) ^ p * (x⁻¹ * |logTower H p (Real.log x)|))
        volume 1 (1 + N) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hN1]
      refine continuousOn_const.mul ((continuousOn_inv₀.mono fun x hx => ?_).mul
        (hTc.abs.comp_continuousOn (Real.continuousOn_log.mono fun x hx => ?_)))
      · exact (lt_of_lt_of_le one_pos hx.1).ne'
      · exact (lt_of_lt_of_le one_pos hx.1).ne'
    calc ∫ x in (1 : ℝ)..1 + N, |logTowerS H p x|
        ≤ ∫ x in (1 : ℝ)..1 + N, Real.exp (-α) ^ p * (x⁻¹ * |logTower H p (Real.log x)|) :=
          intervalIntegral.integral_mono_on hN1 i1 i2 fun x hx =>
            abs_logTowerS_le hHsupp p hx.1
      _ = Real.exp (-α) ^ p * ∫ t in (0 : ℝ)..Real.log (1 + N), |logTower H p t| := by
          rw [intervalIntegral.integral_const_mul,
            integral_inv_mul_comp_log (G := fun t => |logTower H p t|) hTc.abs one_pos hN1,
            Real.log_one]
      _ ≤ Real.exp (-α) ^ p * ∫ t, |logTower H p t| := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [intervalIntegral.integral_of_le hlogN]
          exact setIntegral_le_integral hTint (Eventually.of_forall fun t => abs_nonneg _)
  calc |∑ n ∈ Finset.range N, dqptEMJ (logTowerS H) p (1 + n)|
      ≤ ∑ n ∈ Finset.range N, |dqptEMJ (logTowerS H) p (1 + n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, C * ∫ x in (1 + n : ℝ)..1 + n + 1, |logTowerS H p x| :=
        Finset.sum_le_sum hcells
    _ = C * ∫ x in (1 : ℝ)..1 + N, |logTowerS H p x| := by rw [← Finset.mul_sum, hsum]
    _ ≤ C * (Real.exp (-α) ^ p * ∫ t, |logTower H p t|) := mul_le_mul_of_nonneg_left htower hC

/-! ### `L¹` bounds of the tower -/

section TowerBounds

theorem natCast_le_infty (j : ℕ) : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top

theorem contDiffAt_of_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (t : ℝ) :
    ContDiffAt ℝ j f t :=
  (hf.of_le (natCast_le_infty j)).contDiffAt

/-- Iterated derivatives vanish where the function vanishes near the point. -/
theorem iteratedDeriv_eq_zero_of_vanish {f : ℝ → ℝ} {α β : ℝ} (hf : ∀ t, t ∉ Icc α β → f t = 0)
    (j : ℕ) {t : ℝ} (ht : t ∉ Icc α β) : iteratedDeriv j f t = 0 := by
  have hev : f =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (isClosed_Icc.isOpen_compl.mem_nhds ht) fun s hs => hf s hs
  rw [hev.iteratedDeriv_eq]
  simp

theorem integrable_iteratedDeriv_of_vanish {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hfs : ∀ t, t ∉ Icc α β → f t = 0) (j : ℕ) : Integrable (iteratedDeriv j f) :=
  (hf.continuous_iteratedDeriv j (natCast_le_infty j)).integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc fun _ ht => iteratedDeriv_eq_zero_of_vanish hfs j ht)

theorem iteratedDeriv_logTower_succ (hH : ContDiff ℝ ∞ H) (p j : ℕ) (t : ℝ) :
    iteratedDeriv j (logTower H (p + 1)) t =
      iteratedDeriv (j + 1) (logTower H p) t - (p + 1) * iteratedDeriv j (logTower H p) t := by
  have hT := contDiff_logTower hH p
  have hD : ContDiff ℝ ∞ (deriv (logTower H p)) := (contDiff_infty_iff_deriv.mp hT).2
  have e : logTower H (p + 1) = deriv (logTower H p) - fun t => ((p : ℝ) + 1) * logTower H p t := by
    funext t; rw [logTower_succ]; rfl
  rw [e, iteratedDeriv_sub (contDiffAt_of_smooth hD j t)
    ((contDiff_const.mul hT).contDiffAt.of_le (natCast_le_infty j)),
    iteratedDeriv_const_mul _ (contDiffAt_of_smooth hT j t), iteratedDeriv_succ']

/-- **The tower in `L¹`**: `‖T_p^{(j)}‖₁ ≤ (p+1)! Σ_{i ≤ p} ‖H^{(j+i)}‖₁`. -/
theorem integral_abs_iteratedDeriv_logTower_le (hH : ContDiff ℝ ∞ H) {α β : ℝ}
    (hHs : ∀ t, t ∉ Icc α β → H t = 0) (p : ℕ) : ∀ j : ℕ,
    ∫ t, |iteratedDeriv j (logTower H p) t| ≤
      ((p + 1).factorial : ℝ) * ∑ i ∈ Finset.range (p + 1), ∫ t, |iteratedDeriv (j + i) H t| := by
  induction p with
  | zero => intro j; simp [logTower]
  | succ p ih =>
    intro j
    set I : ℕ → ℝ := fun i => ∫ t, |iteratedDeriv i H t|
    have hI : ∀ i, 0 ≤ I i := fun i => integral_nonneg fun t => abs_nonneg _
    have hTs := logTower_eq_zero hHs p
    have hTsm := contDiff_logTower hH p
    have i1 := (integrable_iteratedDeriv_of_vanish hTsm hTs (j + 1)).abs
    have i2 := ((integrable_iteratedDeriv_of_vanish hTsm hTs j).abs).const_mul ((p : ℝ) + 1)
    have hpt : ∀ t, |iteratedDeriv j (logTower H (p + 1)) t| ≤
        |iteratedDeriv (j + 1) (logTower H p) t| +
          ((p : ℝ) + 1) * |iteratedDeriv j (logTower H p) t| := by
      intro t
      rw [iteratedDeriv_logTower_succ hH p j t]
      have h := abs_sub (iteratedDeriv (j + 1) (logTower H p) t)
        (((p : ℝ) + 1) * iteratedDeriv j (logTower H p) t)
      rwa [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) + 1)] at h
    have hstep : ∫ t, |iteratedDeriv j (logTower H (p + 1)) t| ≤
        (∫ t, |iteratedDeriv (j + 1) (logTower H p) t|) +
          ((p : ℝ) + 1) * ∫ t, |iteratedDeriv j (logTower H p) t| := by
      rw [← integral_const_mul, ← integral_add i1 i2]
      exact integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _) (i1.add i2)
        (Eventually.of_forall hpt)
    have h1 := ih (j + 1)
    have h2 := ih j
    -- reindex the two sums into one of length `p + 2`
    have s1 : ∑ i ∈ Finset.range (p + 1), I (j + 1 + i) ≤
        ∑ i ∈ Finset.range (p + 1 + 1), I (j + i) := by
      rw [Finset.sum_range_succ' (fun i => I (j + i)) (p + 1)]
      have : ∑ i ∈ Finset.range (p + 1), I (j + 1 + i) =
          ∑ i ∈ Finset.range (p + 1), I (j + (i + 1)) :=
        Finset.sum_congr rfl fun i _ => by rw [add_assoc, add_comm 1 i]
      rw [this]; linarith [hI (j + 0)]
    have s2 : ∑ i ∈ Finset.range (p + 1), I (j + i) ≤
        ∑ i ∈ Finset.range (p + 1 + 1), I (j + i) := by
      rw [Finset.sum_range_succ (fun i => I (j + i)) (p + 1)]; linarith [hI (j + (p + 1))]
    have hfac : ((p + 1 + 1).factorial : ℝ) = ((p : ℝ) + 2) * ((p + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hf0 : (0 : ℝ) ≤ ((p + 1).factorial : ℝ) := by positivity
    have hS0 : 0 ≤ ∑ i ∈ Finset.range (p + 1 + 1), I (j + i) := Finset.sum_nonneg fun i _ => hI _
    simp only [I] at s1 s2 hS0
    rw [hfac]
    calc ∫ t, |iteratedDeriv j (logTower H (p + 1)) t|
        ≤ (∫ t, |iteratedDeriv (j + 1) (logTower H p) t|) +
          ((p : ℝ) + 1) * ∫ t, |iteratedDeriv j (logTower H p) t| := hstep
      _ ≤ ((p + 1).factorial : ℝ) *
            (∑ i ∈ Finset.range (p + 1 + 1), ∫ t, |iteratedDeriv (j + i) H t|) +
          ((p : ℝ) + 1) * (((p + 1).factorial : ℝ) *
            ∑ i ∈ Finset.range (p + 1 + 1), ∫ t, |iteratedDeriv (j + i) H t|) := by
          refine add_le_add (h1.trans (mul_le_mul_of_nonneg_left s1 hf0))
            (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left s2 hf0))
              (by positivity))
      _ = _ := by ring

end TowerBounds

/-! ### The Leibniz bound -/

section Leibniz

/-- `Σ_{l ≤ i} C(i, l) M_l P_{i−l}`: the Leibniz bound on `‖(F(· − c) G(a − ·))^{(i)}‖₁` from
`|F^{(l)}| ≤ M_l` and `‖G^{(q)}‖₁ ≤ P_q`. -/
def leibnizBound (M P : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * M l * P (i - l)

theorem hasCompactSupport_iteratedDeriv {f : ℝ → ℝ} (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- **The Leibniz bound**: `‖(F(· − c) G(a − ·))^{(i)}‖₁ ≤ Σ_{l ≤ i} C(i, l) M_l ‖G^{(i−l)}‖₁`. -/
theorem integral_abs_iteratedDeriv_mul_le {F G : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) {M : ℕ → ℝ}
    (hM : ∀ l t, |iteratedDeriv l F t| ≤ M l) (c a : ℝ) (i : ℕ) :
    ∫ t, |iteratedDeriv i (fun t => F (t - c) * G (a - t)) t| ≤
      leibnizBound M (fun q => ∫ s, |iteratedDeriv q G s|) i := by
  have hF' : ContDiff ℝ ∞ fun t => F (t - c) := hF.comp (contDiff_id.sub contDiff_const)
  have hG' : ContDiff ℝ ∞ fun t => G (a - t) := hG.comp (contDiff_const.sub contDiff_id)
  have hGi : ∀ q, Integrable fun t => |iteratedDeriv q G (a - t)| := fun q =>
    (((hG.continuous_iteratedDeriv q (natCast_le_infty q)).integrable_of_hasCompactSupport
      (hasCompactSupport_iteratedDeriv hGc q)).comp_sub_left a).abs
  have hpt : ∀ t, |iteratedDeriv i (fun t => F (t - c) * G (a - t)) t| ≤
      ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * M l * |iteratedDeriv (i - l) G (a - t)| := by
    intro t
    have e : (fun t => F (t - c) * G (a - t)) = (fun t => F (t - c)) * fun t => G (a - t) := rfl
    rw [e, iteratedDeriv_mul (contDiffAt_of_smooth hF' i t) (contDiffAt_of_smooth hG' i t)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [iteratedDeriv_comp_sub_const, iteratedDeriv_comp_const_sub]
    simp only [smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM l (t - c)) (by positivity))
      (abs_nonneg _)
  have hint : Integrable fun t => ∑ l ∈ Finset.range (i + 1),
      (i.choose l : ℝ) * M l * |iteratedDeriv (i - l) G (a - t)| :=
    integrable_finsetSum _ fun l _ => (hGi (i - l)).const_mul _
  calc ∫ t, |iteratedDeriv i (fun t => F (t - c) * G (a - t)) t|
      ≤ ∫ t, ∑ l ∈ Finset.range (i + 1),
          (i.choose l : ℝ) * M l * |iteratedDeriv (i - l) G (a - t)| :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = leibnizBound M (fun q => ∫ s, |iteratedDeriv q G s|) i := by
        rw [integral_finsetSum _ fun l _ => (hGi (i - l)).const_mul _]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [integral_const_mul, integral_sub_left_eq_self (fun s => |iteratedDeriv (i - l) G s|)]

end Leibniz

/-! ### The Euler–Maclaurin synthesis -/

section Synthesis

open ArithmeticElectrostatics

variable {F G : ℝ → ℝ} {M : ℕ → ℝ} {R c : ℝ}

/-- The Euler–Maclaurin weights `x_n = F(log n − c)/n`. -/
def emWeights (F : ℝ → ℝ) (c : ℝ) (n : ℕ) : ℝ := (n : ℝ)⁻¹ * F (Real.log n - c)

theorem atomicTest_emWeights (F G : ℝ → ℝ) (c : ℝ) (N : ℕ) (u : ℝ) :
    atomicTest (N + 1) (emWeights F c) G u = ∑ n ∈ Finset.range (N + 1),
      (1 + n : ℝ)⁻¹ * F (Real.log (1 + n) - c) * G (u - Real.log (1 + n)) := by
  unfold atomicTest emWeights
  rw [show Finset.Icc 1 (N + 1) = Finset.Ico 1 (N + 1 + 1) by ext; simp,
    Finset.sum_Ico_eq_sum_range, show N + 1 + 1 - 1 = N + 1 by omega]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  ring

/-- The constant `(|B_p|/p!) (p+1)! Σ_{i ≤ p} Λ_i` of the order-`p` synthesis, `p = 2m + 2`. -/
def emConst (M A : ℕ → ℝ) (m : ℕ) : ℝ :=
  |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
    (((2 * m + 2 + 1).factorial : ℝ) * ∑ i ∈ Finset.range (2 * m + 2 + 1), leibnizBound M A i)

/-- **The Euler–Maclaurin synthesis error**: for `F` smooth, vanishing off `[−R, R]`, with
`|F^{(l)}| ≤ M_l`, and `G` smooth with compact support, if `0 < c − R` and `c + R < log(1 + N)`,
`|Σ_n F(log n − c)/n · G(r + c − log n) − ∫ F(v) G(r − v) dv| ≤
(|B_p|/p!) e^{−p(c−R)} (p+1)! Σ_{i ≤ p} Σ_{l ≤ i} C(i,l) M_l ‖G^{(i−l)}‖₁`. -/
theorem abs_emSynth_sub_conv_le (hF : ContDiff ℝ ∞ F) (hFs : ∀ t, t ∉ Icc (-R) R → F t = 0)
    (hM : ∀ l t, |iteratedDeriv l F t| ≤ M l) (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
    (hc : 0 < c - R) {N : ℕ} (hN : c + R < Real.log (1 + N)) (m : ℕ) (r : ℝ) :
    |atomicTest (N + 1) (emWeights F c) G (r + c) - ∫ v, F v * G (r - v)| ≤
      |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
        (Real.exp (-(c - R)) ^ (2 * m + 2) * (((2 * m + 2 + 1).factorial : ℝ) *
          ∑ i ∈ Finset.range (2 * m + 2 + 1),
            leibnizBound M (fun q => ∫ s, |iteratedDeriv q G s|) i)) := by
  set H : ℝ → ℝ := fun t => F (t - c) * G (r + c - t)
  have hH : ContDiff ℝ ∞ H :=
    (hF.comp (contDiff_id.sub contDiff_const)).mul (hG.comp (contDiff_const.sub contDiff_id))
  have hHs : ∀ t, t ∉ Icc (c - R) (c + R) → H t = 0 := fun t ht => by
    have : t - c ∉ Icc (-R) R := fun h => ht ⟨by linarith [h.1], by linarith [h.2]⟩
    simp only [H, hFs _ this, zero_mul]
  have hEM := abs_sum_logTowerS_sub_integral_le hH hc hHs hN m
  have hsum : atomicTest (N + 1) (emWeights F c) G (r + c) =
      ∑ n ∈ Finset.range (N + 1), logTowerS H 0 (1 + n) := by
    rw [atomicTest_emWeights]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [logTowerS, logTower, zero_add, pow_one, H]
    ring
  have hint : ∫ t, H t = ∫ v, F v * G (r - v) := by
    rw [← integral_add_right_eq_self H c]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [H]
    ring_nf
  have htower := integral_abs_iteratedDeriv_logTower_le hH hHs (2 * m + 2) 0
  simp only [iteratedDeriv_zero, zero_add] at htower
  have hleib : ∀ i, ∫ t, |iteratedDeriv i H t| ≤
      leibnizBound M (fun q => ∫ s, |iteratedDeriv q G s|) i := fun i =>
    integral_abs_iteratedDeriv_mul_le hF hG hGc hM c (r + c) i
  rw [hsum, ← hint]
  refine hEM.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (htower.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hleib i)
      (by positivity))) (by positivity)) (by positivity))

/-- `‖(φ_k)^{(q)}‖₁ = k^q ‖φ^{(q)}‖₁` for the dilate `φ_k = k φ(k·)`. -/
theorem integral_abs_iteratedDeriv_dilate {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {k : ℝ} (hk : 0 < k)
    (q : ℕ) : ∫ s, |iteratedDeriv q (dilate k φ) s| = k ^ q * ∫ s, |iteratedDeriv q φ s| := by
  have hφk : ContDiff ℝ ∞ fun s => φ (k * s) := hφ.comp (contDiff_const.mul contDiff_id)
  have e : iteratedDeriv q (dilate k φ) = dilate k fun s => k ^ q * iteratedDeriv q φ s := by
    funext s
    have h1 := iteratedDeriv_const_mul (n := q) (x := s) k (contDiffAt_of_smooth hφk q s)
    rw [iteratedDeriv_comp_const_mul (hφ.of_le (natCast_le_infty q)) k] at h1
    exact h1
  rw [e, integral_abs_dilate hk]
  simp_rw [abs_mul, abs_pow, abs_of_pos hk]
  exact integral_const_mul _ _

theorem leibnizBound_pow_le {M A : ℕ → ℝ} (hM : ∀ l, 0 ≤ M l) (hA : ∀ q, 0 ≤ A q) {k : ℝ}
    (hk : 1 ≤ k) (i : ℕ) :
    leibnizBound M (fun q => k ^ q * A q) i ≤ k ^ i * leibnizBound M A i := by
  unfold leibnizBound
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  have hkl : k ^ (i - l) ≤ k ^ i := pow_le_pow_right₀ hk (Nat.sub_le i l)
  have h0 : 0 ≤ (i.choose l : ℝ) * M l * A (i - l) := by
    have := hM l; have := hA (i - l); positivity
  calc (i.choose l : ℝ) * M l * (k ^ (i - l) * A (i - l))
      = k ^ (i - l) * ((i.choose l : ℝ) * M l * A (i - l)) := by ring
    _ ≤ k ^ i * ((i.choose l : ℝ) * M l * A (i - l)) := mul_le_mul_of_nonneg_right hkl h0

theorem leibnizBound_nonneg {M A : ℕ → ℝ} (hM : ∀ l, 0 ≤ M l) (hA : ∀ q, 0 ≤ A q) (i : ℕ) :
    0 ≤ leibnizBound M A i :=
  Finset.sum_nonneg fun l _ => by have := hM l; have := hA (i - l); positivity

theorem emConst_nonneg {M A : ℕ → ℝ} (hM : ∀ l, 0 ≤ M l) (hA : ∀ q, 0 ≤ A q) (m : ℕ) :
    0 ≤ emConst M A m := by
  unfold emConst
  have := Finset.sum_nonneg fun i (_ : i ∈ Finset.range (2 * m + 2 + 1)) =>
    leibnizBound_nonneg hM hA i
  positivity

/-- **The synthesis error at order `p = 2m + 2`**: with `c = log n₀ + R`, `n₀ ≥ 2`, atoms of width
`1/k`, `k ≥ 1`, the Euler–Maclaurin synthesis is within `emConst · (k/n₀)^p` of `F ∗ φ_k`. -/
theorem abs_emSynth_dilate_sub_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hF : ContDiff ℝ ∞ F) (hFs : ∀ t, t ∉ Icc (-R) R → F t = 0)
    (hM : ∀ l t, |iteratedDeriv l F t| ≤ M l) (hM0 : ∀ l, 0 ≤ M l) {n₀ N : ℕ} (hn₀ : 2 ≤ n₀)
    (hN : Real.log n₀ + 2 * R < Real.log (1 + N)) {k : ℝ} (hk : 1 ≤ k) (m : ℕ) (r : ℝ) :
    |atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (dilate k φ) (r + (Real.log n₀ + R)) -
        ∫ v, F v * dilate k φ (r - v)| ≤
      emConst M (fun q => ∫ s, |iteratedDeriv q φ s|) m * (k / n₀) ^ (2 * m + 2) := by
  have hk0 : 0 < k := by linarith
  have hn0 : (1 : ℝ) < n₀ := by exact_mod_cast hn₀
  have hψ : ContDiff ℝ ∞ (dilate k φ) :=
    contDiff_const.mul (hφ.comp (contDiff_const.mul contDiff_id))
  have hψc : HasCompactSupport (dilate k φ) := by
    have : dilate k φ = fun s => k * φ (k * s) := rfl
    rw [this]
    exact (hφc.comp_smul hk0.ne').mul_left
  set A : ℕ → ℝ := fun q => ∫ s, |iteratedDeriv q φ s|
  have hA : ∀ q, 0 ≤ A q := fun q => integral_nonneg fun s => abs_nonneg _
  have h := abs_emSynth_sub_conv_le hF hFs hM hψ hψc (c := Real.log n₀ + R)
    (by rw [add_sub_cancel_right]; exact Real.log_pos hn0) (by linarith) m r
  simp_rw [integral_abs_iteratedDeriv_dilate hφ hk0] at h
  rw [add_sub_cancel_right, Real.exp_neg, Real.exp_log (by linarith)] at h
  refine h.trans (le_of_eq_of_le rfl ?_)
  set p := 2 * m + 2
  have hsum : ∑ i ∈ Finset.range (p + 1), leibnizBound M (fun q => k ^ q * A q) i ≤
      k ^ p * ∑ i ∈ Finset.range (p + 1), leibnizBound M A i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => (leibnizBound_pow_le hM0 hA hk i).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hk (Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hi))) (leibnizBound_nonneg hM0 hA i)
  have hB : 0 ≤ |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) := by positivity
  calc |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
        ((n₀ : ℝ)⁻¹ ^ p * (((p + 1).factorial : ℝ) *
          ∑ i ∈ Finset.range (p + 1), leibnizBound M (fun q => k ^ q * A q) i))
      ≤ |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
        ((n₀ : ℝ)⁻¹ ^ p * (((p + 1).factorial : ℝ) *
          (k ^ p * ∑ i ∈ Finset.range (p + 1), leibnizBound M A i))) := by
        gcongr
    _ = emConst M A m * (k / n₀) ^ p := by
        unfold emConst
        rw [div_pow, div_eq_mul_inv (k ^ p), ← inv_pow]
        ring

/-- The derivative of a translated atomic test is the atomic test of the derivative. -/
theorem hasDerivAt_atomicTest {g : ℝ → ℝ} (hg : Differentiable ℝ g) (N : ℕ) (x : ℕ → ℝ)
    (c r : ℝ) :
    HasDerivAt (fun r => atomicTest N x g (r + c)) (atomicTest N x (deriv g) (r + c)) r := by
  unfold atomicTest
  refine HasDerivAt.fun_sum fun n _ => ?_
  have := ((hg (r + c - Real.log n)).hasDerivAt.comp r
    (((hasDerivAt_id r).add_const c).sub_const (Real.log n))).const_mul (x n)
  simpa using this

/-- **The Lipschitz bound of the synthesis**: `|S′| ≤ k (M₀ ‖φ′‖₁ + emConst′ (k/n₀)²)`. -/
theorem abs_emSynth_deriv_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hF : ContDiff ℝ ∞ F) (hFs : ∀ t, t ∉ Icc (-R) R → F t = 0)
    (hM : ∀ l t, |iteratedDeriv l F t| ≤ M l) (hM0 : ∀ l, 0 ≤ M l) {n₀ N : ℕ} (hn₀ : 2 ≤ n₀)
    (hN : Real.log n₀ + 2 * R < Real.log (1 + N)) {k : ℝ} (hk : 1 ≤ k) (r : ℝ) :
    |atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (deriv (dilate k φ))
        (r + (Real.log n₀ + R))| ≤
      k * (M 0 * (∫ s, |deriv φ s|) +
        emConst M (fun q => ∫ s, |iteratedDeriv (q + 1) φ s|) 0 * (k / n₀) ^ 2) := by
  have hk0 : 0 < k := by linarith
  have hn0 : (1 : ℝ) < n₀ := by exact_mod_cast hn₀
  have hψ : ContDiff ℝ ∞ (dilate k φ) :=
    contDiff_const.mul (hφ.comp (contDiff_const.mul contDiff_id))
  have hψc : HasCompactSupport (dilate k φ) := by
    have : dilate k φ = fun s => k * φ (k * s) := rfl
    rw [this]
    exact (hφc.comp_smul hk0.ne').mul_left
  have hψ' : ContDiff ℝ ∞ (deriv (dilate k φ)) := (contDiff_infty_iff_deriv.mp hψ).2
  set A' : ℕ → ℝ := fun q => ∫ s, |iteratedDeriv (q + 1) φ s|
  have hA' : ∀ q, 0 ≤ A' q := fun q => integral_nonneg fun s => abs_nonneg _
  have h := abs_emSynth_sub_conv_le hF hFs hM hψ' hψc.deriv (c := Real.log n₀ + R)
    (by rw [add_sub_cancel_right]; exact Real.log_pos hn0) (by linarith) 0 r
  have hP : ∀ q, ∫ s, |iteratedDeriv q (deriv (dilate k φ)) s| = k * (k ^ q * A' q) := fun q => by
    rw [← iteratedDeriv_succ', integral_abs_iteratedDeriv_dilate hφ hk0, pow_succ]
    simp only [A']; ring
  simp_rw [hP] at h
  rw [add_sub_cancel_right, Real.exp_neg, Real.exp_log (by linarith)] at h
  have hsum : ∑ i ∈ Finset.range (2 * 0 + 2 + 1), leibnizBound M (fun q => k * (k ^ q * A' q)) i ≤
      k * (k ^ 2 * ∑ i ∈ Finset.range (2 * 0 + 2 + 1), leibnizBound M A' i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have e : leibnizBound M (fun q => k * (k ^ q * A' q)) i =
        k * leibnizBound M (fun q => k ^ q * A' q) i := by
      unfold leibnizBound; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ((leibnizBound_pow_le hM0 hA' hk i).trans ?_) hk0.le
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hk (Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hi))) (leibnizBound_nonneg hM0 hA' i)
  -- the convolution term
  have hconv : |∫ v, F v * deriv (dilate k φ) (r - v)| ≤ M 0 * (k * ∫ s, |deriv φ s|) := by
    have hFM : ∀ t, |F t| ≤ M 0 := fun t => by simpa using hM 0 t
    have h1 := abs_integral_mul_le_sup_mul hFM
      (hψ'.continuous.integrable_of_hasCompactSupport hψc.deriv) r
    have h2 := hP 0
    simp only [iteratedDeriv_zero, pow_zero, one_mul, A', zero_add, iteratedDeriv_one] at h2
    rwa [h2] at h1
  have hB : 0 ≤ |((bernoulli (2 * 0 + 2) : ℚ) : ℝ)| / ((2 * 0 + 2).factorial : ℝ) := by positivity
  have hEM : |atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (deriv (dilate k φ))
      (r + (Real.log n₀ + R)) - ∫ v, F v * deriv (dilate k φ) (r - v)| ≤
      k * (emConst M A' 0 * (k / n₀) ^ 2) := by
    refine h.trans ?_
    calc |((bernoulli (2 * 0 + 2) : ℚ) : ℝ)| / ((2 * 0 + 2).factorial : ℝ) *
          ((n₀ : ℝ)⁻¹ ^ (2 * 0 + 2) * (((2 * 0 + 2 + 1).factorial : ℝ) *
            ∑ i ∈ Finset.range (2 * 0 + 2 + 1), leibnizBound M (fun q => k * (k ^ q * A' q)) i))
        ≤ |((bernoulli (2 * 0 + 2) : ℚ) : ℝ)| / ((2 * 0 + 2).factorial : ℝ) *
          ((n₀ : ℝ)⁻¹ ^ (2 * 0 + 2) * (((2 * 0 + 2 + 1).factorial : ℝ) *
            (k * (k ^ 2 * ∑ i ∈ Finset.range (2 * 0 + 2 + 1), leibnizBound M A' i)))) := by
          gcongr
      _ = k * (emConst M A' 0 * (k / n₀) ^ 2) := by
          unfold emConst
          rw [div_pow, div_eq_mul_inv (k ^ 2), ← inv_pow]
          ring
  have := abs_sub_abs_le_abs_sub (atomicTest (N + 1) (emWeights F (Real.log n₀ + R))
    (deriv (dilate k φ)) (r + (Real.log n₀ + R))) (∫ v, F v * deriv (dilate k φ) (r - v))
  nlinarith

end Synthesis

/-! ### The motion of Weil's form -/

section Perturbation

open ArithmeticElectrostatics

/-- **The norms of a small perturbation**: a `C²` test `D` supported in `[−R′, R′]` with `|D| ≤ e`
and Lipschitz constant `L_D` has `‖D‖₂ ≤ √(2R′) e`, `‖D‖₂² ≤ 2R′e²`, `‖D‖₁ ≤ 2R′e` and Lévy energy
`≤ synthLevy R′ e L_D k` for every `k ≥ 1`. -/
theorem perturbation_norms {D : ℝ → ℝ} {R' e LD k : ℝ} (hD : ContDiff ℝ 2 D)
    (hDR : SupportedIn R' D) (hR' : 0 ≤ R') (he : ∀ u, |D u| ≤ e)
    (hLD : ∀ u v, |D u - D v| ≤ LD * |u - v|) (hk : 1 ≤ k) :
    HasCompactSupport D ∧ Real.sqrt (∫ u, D u ^ 2) ≤ Real.sqrt (2 * R') * e ∧
      ∫ u, D u ^ 2 ≤ 2 * R' * e ^ 2 ∧ levyEnergy D ≤ synthLevy R' e LD k ∧
      0 ≤ ∫ u, |D u| ∧ ∫ u, |D u| ≤ 2 * R' * e := by
  have hk0 : 0 < k := by linarith
  have hDc : HasCompactSupport D := hasCompactSupport_of_vanishes hDR
  have he0 : 0 ≤ e := (abs_nonneg _).trans (he 0)
  have hN1 := integral_abs_le_of_bound hD.continuous hDc he hDR hR'
  have hN2 : ∫ u, D u ^ 2 ≤ 2 * R' * e ^ 2 := by
    have := integral_sq_le_of_bound hD.continuous hDc he
    nlinarith
  have hLD0 : 0 ≤ LD := by
    have := hLD 1 0
    simp only [sub_zero, abs_one, mul_one] at this
    linarith [abs_nonneg (D 1 - D 0)]
  have hLev : levyEnergy D ≤ synthLevy R' e LD k := by
    have h := levyEnergy_le_lipschitz hD hDc hLD (δ := 1 / k) (one_div_pos.mpr hk0)
      (by rw [div_le_one hk0]; exact hk)
    rw [one_div_one_div] at h
    have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk
    have hC1 := levyLipConstant_nonneg
    have hb1 : Real.exp (1 / 2) * LD * (1 / k) * (∫ u, |D u|) ≤
        Real.exp (1 / 2) * LD * (1 / k) * (2 * R' * e) :=
      mul_le_mul_of_nonneg_left hN1
        (mul_nonneg (mul_nonneg (Real.exp_pos _).le hLD0) (one_div_pos.mpr hk0).le)
    have hb2 : (2 * Real.log k + levyLipConstant) * (∫ u, D u ^ 2) ≤
        (2 * Real.log k + levyLipConstant) * (2 * R' * e ^ 2) :=
      mul_le_mul_of_nonneg_left hN2 (by linarith)
    unfold synthLevy
    linarith
  have hsqD : Real.sqrt (∫ u, D u ^ 2) ≤ Real.sqrt (2 * R') * e := by
    rw [← Real.sqrt_sq he0, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  exact ⟨hDc, hsqD, hN2, hLev, integral_nonneg fun u => abs_nonneg _, hN1⟩

/-- **A small perturbation moves Weil's form by `weilErr`**: a `C²` perturbation `D` supported in
`[−R′, R′]` with `|D| ≤ e` and Lipschitz constant `L_D` moves `weilQuad F` by at most
`weilErr F R′ e (synthLevy R′ e L_D k)` for every `k ≥ 1`. -/
theorem weilQuad_add_le_of_lip {F D : ℝ → ℝ} {R' e LD k : ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hFR : SupportedIn R' F) (hD : ContDiff ℝ 2 D)
    (hDR : SupportedIn R' D) (hR' : 0 ≤ R') (he : ∀ u, |D u| ≤ e)
    (hLD : ∀ u v, |D u - D v| ≤ LD * |u - v|) (hk : 1 ≤ k) :
    weilQuad (fun u => F u + D u) ≤ weilQuad F + weilErr F R' e (synthLevy R' e LD k) := by
  obtain ⟨hDc, hsqD, hN2, hLev, hN0, hN1⟩ := perturbation_norms hD hDR hR' he hLD hk
  exact (weilQuad_add_le hF hFc hD hDc hFR hDR).trans (add_le_add le_rfl
    (weilErr_mono (F := F) hsqD hN2 hLev hN0 hN1))

end Perturbation

/-! ### The Euler–Maclaurin synthesis bound -/

section SynthesisBound

open ArithmeticElectrostatics

variable {φ F : ℝ → ℝ} {M : ℕ → ℝ} {R : ℝ}

/-- The supremum error `emConst (k/n₀)^{2m+2} + M₁ ‖φ‖₁/k` of the order-`(2m+2)` synthesis. -/
def emErr (M A : ℕ → ℝ) (m : ℕ) (k : ℝ) (n₀ : ℕ) : ℝ :=
  emConst M A m * (k / n₀) ^ (2 * m + 2) + M 1 * (1 / k) * A 0

/-- The Lipschitz constant `k (M₀ ‖φ′‖₁ + emConst′ (k/n₀)²) + M₁` of its error. -/
def emLip (M A : ℕ → ℝ) (k : ℝ) (n₀ : ℕ) : ℝ :=
  k * (M 0 * A 1 + emConst M (fun q => A (q + 1)) 0 * (k / n₀) ^ 2) + M 1

theorem log_lt_log_block {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (R : ℝ) :
    Real.log n₀ + 2 * R < Real.log ((n₀ * blockSize R : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  have hB : 1 + Real.exp (2 * R) ≤ blockSize R := Nat.le_ceil _
  have hB0 : (0 : ℝ) < blockSize R := by linarith [Real.exp_pos (2 * R)]
  push_cast
  rw [Real.log_mul hn.ne' hB0.ne']
  have : 2 * R < Real.log (blockSize R) := by
    rw [← Real.log_exp (2 * R)]
    exact Real.log_lt_log (Real.exp_pos _) (by linarith)
  linarith

/-- **The Euler–Maclaurin synthesis as a perturbation, for a given quadrature error**: if the
weights `F(log n − c)/n` reproduce `F ∗ φ_k` within `e₁`, the atomic test of level `n₀ B` is the
translate by `c = log n₀ + R` of `F + D` with `D` a `C²` test supported in `[−(R+1), R+1]`,
`|D| ≤ e₁ + M₁ ‖φ‖₁/k`, and Lipschitz constant `emLip`. -/
theorem exists_emSynthesis_of (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hF : ContDiff ℝ ∞ F) (hFR : SupportedIn R F)
    (hM : ∀ l t, |iteratedDeriv l F t| ≤ M l) (hM0 : ∀ l, 0 ≤ M l)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {k e₁ : ℝ} (hk : 1 ≤ k)
    (h1' : ∀ r, |atomicTest (n₀ * blockSize R) (emWeights F (Real.log n₀ + R)) (dilate k φ)
      (r + (Real.log n₀ + R)) - ∫ v, F v * dilate k φ (r - v)| ≤ e₁) :
    ∃ (x : ℕ → ℝ) (D : ℝ → ℝ),
      atomicTest (n₀ * blockSize R) x (dilate k φ) =
        (fun u => F (u - (Real.log n₀ + R)) + D (u - (Real.log n₀ + R))) ∧
      ContDiff ℝ 2 D ∧ SupportedIn (R + 1) D ∧
      (∀ u, |D u| ≤ e₁ + M 1 * (1 / k) * ∫ s, |φ s|) ∧
      ∀ u v, |D u - D v| ≤ emLip M (fun q => ∫ s, |iteratedDeriv q φ s|) k n₀ * |u - v| := by
  have hk0 : 0 < k := by linarith
  have hn₀1 : 1 ≤ n₀ := by omega
  have hB : 1 ≤ n₀ * blockSize R := by
    have : 1 ≤ blockSize R := by
      have h := Nat.le_ceil (1 + Real.exp (2 * R))
      have : (1 : ℝ) ≤ blockSize R := by
        have := Real.exp_pos (2 * R); simp only [blockSize] at h ⊢; linarith
      exact_mod_cast this
    nlinarith
  obtain ⟨N, hNB⟩ : ∃ N : ℕ, n₀ * blockSize R = N + 1 := ⟨n₀ * blockSize R - 1, by omega⟩
  have hN : Real.log n₀ + 2 * R < Real.log (1 + N) := by
    have := log_lt_log_block hn₀1 R
    rw [hNB] at this
    push_cast at this
    rwa [add_comm (N : ℝ) 1] at this
  have hφc : HasCompactSupport φ := hasCompactSupport_of_vanishes hφ1
  have hψ : ContDiff ℝ ∞ (dilate k φ) :=
    contDiff_const.mul (hφ.comp (contDiff_const.mul contDiff_id))
  have hFs : ∀ t, t ∉ Icc (-R) R → F t = 0 := fun t ht => hFR t (by
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
    · exact lt_of_lt_of_le ht (le_abs_self t))
  have hF1 : ∀ t, HasDerivAt F (deriv F t) t := fun t =>
    (hF.differentiable (by simp) t).hasDerivAt
  have hFL : ∀ u v, |F u - F v| ≤ M 1 * |u - v| :=
    abs_sub_le_of_hasDerivAt hF1 fun t => by simpa using hM 1 t
  -- the two halves of the supremum error, and the Lipschitz bound of the synthesis
  have h1 : ∀ r, |atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (dilate k φ)
      (r + (Real.log n₀ + R)) - ∫ v, F v * dilate k φ (r - v)| ≤ e₁ := fun r => by
    rw [← hNB]; exact h1' r
  have h2 : ∀ r, |(∫ v, F v * dilate k φ (r - v)) - F r| ≤ M 1 * (1 / k) * ∫ s, |φ s| := by
    intro r
    have := abs_integral_mul_sub_le hF.continuous hψ.continuous
      (hasCompactSupport_of_vanishes fun s hs => dilate_vanishes hφ1 hk0 hs)
      (by rw [integral_dilate hk0, hφint]) (fun s hs => dilate_vanishes hφ1 hk0 hs) hFL r
    rwa [integral_abs_dilate hk0] at this
  have hS : ∀ u v, |atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (dilate k φ)
      (u + (Real.log n₀ + R)) - atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (dilate k φ)
      (v + (Real.log n₀ + R))| ≤ k * (M 0 * (∫ s, |deriv φ s|) +
        emConst M (fun q => ∫ s, |iteratedDeriv (q + 1) φ s|) 0 * (k / n₀) ^ 2) * |u - v| :=
    abs_sub_le_of_hasDerivAt (fun r => hasDerivAt_atomicTest
      (hψ.differentiable (by simp)) (N + 1) (emWeights F (Real.log n₀ + R)) _ r)
      fun r => abs_emSynth_deriv_le hφ hφc hF hFs hM hM0 hn₀ hN hk r
  have hA1 : (fun q => ∫ s, |iteratedDeriv q φ s|) 1 = ∫ s, |deriv φ s| := by simp
  set S : ℝ → ℝ := fun r => atomicTest (N + 1) (emWeights F (Real.log n₀ + R)) (dilate k φ)
    (r + (Real.log n₀ + R))
  set D : ℝ → ℝ := fun r => S r - F r
  have hsup : ∀ r, |D r| ≤ e₁ + M 1 * (1 / k) * ∫ s, |φ s| := by
    intro r
    calc |D r| = |(S r - ∫ v, F v * dilate k φ (r - v)) +
          ((∫ v, F v * dilate k φ (r - v)) - F r)| := by simp only [D]; ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith [h1 r, h2 r])
  have hlip : ∀ u v, |D u - D v| ≤ emLip M (fun q => ∫ s, |iteratedDeriv q φ s|) k n₀ *
      |u - v| := by
    intro u v
    have e : D u - D v = (S u - S v) - (F u - F v) := by simp only [D]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have := add_le_add (hS u v) (hFL u v)
    unfold emLip
    rw [hA1]
    linarith
  -- the support
  have hDsupp : SupportedIn (R + 1) D := by
    intro r hr
    have hS0 : S r = 0 := by
      simp only [S, atomicTest]
      refine Finset.sum_eq_zero fun n _ => ?_
      by_cases hn : |Real.log n - (Real.log n₀ + R)| ≤ R
      · have hk1 : 1 / k ≤ 1 := by rw [div_le_one hk0]; exact hk
        rw [dilate_vanishes hφ1 hk0 (by
          have := abs_sub_abs_le_abs_sub r (Real.log n - (Real.log n₀ + R))
          rw [show r + (Real.log n₀ + R) - Real.log n = r - (Real.log n - (Real.log n₀ + R)) by
            ring]
          linarith), mul_zero]
      · push Not at hn
        rw [emWeights, hFR _ hn, mul_zero, zero_mul]
    simp only [D, hS0, hFR r (by linarith), sub_zero]
  have hD2 : ContDiff ℝ 2 D :=
    ((contDiff_atomicTest (hψ.of_le (natCast_le_infty 2)) (N + 1)
      (emWeights F (Real.log n₀ + R))).comp (contDiff_id.add contDiff_const)).sub
      (hF.of_le (natCast_le_infty 2))
  refine ⟨emWeights F (Real.log n₀ + R), D, ?_, hD2, hDsupp, hsup, hlip⟩
  funext u
  simp only [D, S, hNB, sub_add_cancel]
  ring


/-- **The Euler–Maclaurin synthesis as a perturbation**: for a smooth profile `φ` and a smooth test
`F` supported in `[−R, R]` with `|F^{(l)}| ≤ M_l`, the atomic test of level `n₀ B`, `n₀ ≥ 2`, with
the weights `F(log n − c)/n` and width `1/k` is the translate by `c = log n₀ + R` of `F + D`, where
`D` is a `C²` test supported in `[−(R+1), R+1]` with `|D| ≤ emErr` and Lipschitz constant `emLip`:
the error is of order `(k/n₀)^{2m+2}` for every `m`. -/
theorem exists_emSynthesis (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hF : ContDiff ℝ ∞ F) (hFR : SupportedIn R F)
    (hM : ∀ l t, |iteratedDeriv l F t| ≤ M l) (hM0 : ∀ l, 0 ≤ M l)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {k : ℝ} (hk : 1 ≤ k) (m : ℕ) :
    ∃ (x : ℕ → ℝ) (D : ℝ → ℝ),
      atomicTest (n₀ * blockSize R) x (dilate k φ) =
        (fun u => F (u - (Real.log n₀ + R)) + D (u - (Real.log n₀ + R))) ∧
      ContDiff ℝ 2 D ∧ SupportedIn (R + 1) D ∧
      (∀ u, |D u| ≤ emErr M (fun q => ∫ s, |iteratedDeriv q φ s|) m k n₀) ∧
      ∀ u v, |D u - D v| ≤ emLip M (fun q => ∫ s, |iteratedDeriv q φ s|) k n₀ * |u - v| := by
  have hn₀1 : 1 ≤ n₀ := by omega
  have hB : 1 ≤ n₀ * blockSize R := by
    have : 1 ≤ blockSize R := by
      have h := Nat.le_ceil (1 + Real.exp (2 * R))
      have : (1 : ℝ) ≤ blockSize R := by
        have := Real.exp_pos (2 * R); simp only [blockSize] at h ⊢; linarith
      exact_mod_cast this
    nlinarith
  obtain ⟨N, hNB⟩ : ∃ N : ℕ, n₀ * blockSize R = N + 1 := ⟨n₀ * blockSize R - 1, by omega⟩
  have hN : Real.log n₀ + 2 * R < Real.log (1 + N) := by
    have := log_lt_log_block hn₀1 R
    rw [hNB] at this
    push_cast at this
    rwa [add_comm (N : ℝ) 1] at this
  have hFs : ∀ t, t ∉ Icc (-R) R → F t = 0 := fun t ht => hFR t (by
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
    · exact lt_of_lt_of_le ht (le_abs_self t))
  obtain ⟨x, D, hx, hD2, hDR, hsup, hlip⟩ := exists_emSynthesis_of hφ hφ1 hφint hF hFR hM hM0 hn₀ hk
    (e₁ := emConst M (fun q => ∫ s, |iteratedDeriv q φ s|) m * (k / n₀) ^ (2 * m + 2))
    fun r => by
      rw [hNB]
      exact abs_emSynth_dilate_sub_le hφ (hasCompactSupport_of_vanishes hφ1) hF hFs hM hM0 hn₀ hN
        hk m r
  refine ⟨x, D, hx, hD2, hDR, fun u => (hsup u).trans (le_of_eq ?_), hlip⟩
  unfold emErr
  simp

/-- **The Euler–Maclaurin synthesis bound**: the atoms of level `n₀ B` synthesize `F` up to a
motion `weilErr F (R+1) e (synthLevy (R+1) e L k)` of Weil's form, `e = emErr`, `L = emLip`. -/
theorem exists_atomicTest_weilQuad_le_em (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) (hR : 0 ≤ R)
    (hFR : SupportedIn R F) (hM : ∀ l t, |iteratedDeriv l F t| ≤ M l) (hM0 : ∀ l, 0 ≤ M l)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {k : ℝ} (hk : 1 ≤ k) (m : ℕ) :
    ∃ x : ℕ → ℝ, weilQuad (atomicTest (n₀ * blockSize R) x (dilate k φ)) ≤ weilQuad F +
      weilErr F (R + 1) (emErr M (fun q => ∫ s, |iteratedDeriv q φ s|) m k n₀)
        (synthLevy (R + 1) (emErr M (fun q => ∫ s, |iteratedDeriv q φ s|) m k n₀)
          (emLip M (fun q => ∫ s, |iteratedDeriv q φ s|) k n₀) k) := by
  obtain ⟨x, D, hx, hD2, hDR, hsup, hlip⟩ :=
    exists_emSynthesis hφ hφ1 hφint hF hFR hM hM0 hn₀ hk m
  refine ⟨x, ?_⟩
  rw [hx, weilQuad_comp_sub (fun u => F u + D u)]
  exact weilQuad_add_le_of_lip (hF.of_le (natCast_le_infty 2)) hFc
    (fun u hu => hFR u (by linarith)) hD2 hDR (by linarith) hsup hlip hk

end SynthesisBound

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
