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

/-- **The logarithmic tower is a derivative tower**: `(s^{−(j+1)} T_j(log s))′ = s^{−(j+2)} T_{j+1}(log s)`. -/
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
        |iteratedDeriv (j + 1) (logTower H p) t| + ((p : ℝ) + 1) * |iteratedDeriv j (logTower H p) t| := by
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
    have s1 : ∑ i ∈ Finset.range (p + 1), I (j + 1 + i) ≤ ∑ i ∈ Finset.range (p + 1 + 1), I (j + i) := by
      rw [Finset.sum_range_succ' (fun i => I (j + i)) (p + 1)]
      have : ∑ i ∈ Finset.range (p + 1), I (j + 1 + i) = ∑ i ∈ Finset.range (p + 1), I (j + (i + 1)) :=
        Finset.sum_congr rfl fun i _ => by rw [add_assoc, add_comm 1 i]
      rw [this]; linarith [hI (j + 0)]
    have s2 : ∑ i ∈ Finset.range (p + 1), I (j + i) ≤ ∑ i ∈ Finset.range (p + 1 + 1), I (j + i) := by
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
            (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left s2 hf0)) (by positivity))
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
    integrable_finset_sum _ fun l _ => (hGi (i - l)).const_mul _
  calc ∫ t, |iteratedDeriv i (fun t => F (t - c) * G (a - t)) t|
      ≤ ∫ t, ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * M l * |iteratedDeriv (i - l) G (a - t)| :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = leibnizBound M (fun q => ∫ s, |iteratedDeriv q G s|) i := by
        rw [integral_finset_sum _ fun l _ => (hGi (i - l)).const_mul _]
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

end Synthesis

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
