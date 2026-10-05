import GaloisForLFunctions.RHTower.LiEvenCrossActualClockMarking
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockHistoryBarrier
import GaloisForLFunctions.RHTower.LiClockThetaForcingRatioShape
import GaloisForLFunctions.RHTower.LiClockThetaResolventSignChange
import GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentRecurrence
import GaloisForLFunctions.HTGeometry.VolterraFlatGrowth

/-!
# The complete causal history of the integrated clock

With the actual kernel `K = B'` put `V_1 = K`, `V_{m+1} = V_m ⋆ K`, `W_m(T) = ∫_0^T V_m`,
`h_0 = tK`, `h_{n+1} = h_n ⋆ K`, `N_n(T) = ∫_0^T h_n(t)/t dt`, `T_K f = f ⋆ K` and
`D(T) = ∫_0^T P(t)/t dt`.  In Lean `V m`, `W m` carry the index `m + 1` of `V_{m+1}`, `W_{m+1}`.

* (simplex symmetry) `(n+1) h_n = t V_{n+1}`, `N_n = W_{n+1}/(n+1)`, `N_0 = B - 1`,
  `W_{m+1} = W_m ⋆ K`;
* `V_m > 0` on `t > 0`, `V_{m+1}' = K' ⋆ V_m ≥ 0`, each `V_m` nondecreasing, each `W_m` strictly
  increasing from `W_m(0) = 0`;
* (factorial bounds) if `K(s) ≤ Ls` and `|P(s)| ≤ Cs²` on `[0,T]`, then
  `0 ≤ h_n(t) ≤ 2L^{n+1} t^{2n+2}/(2n+2)!`, `0 ≤ N_n(T) ≤ L^{n+1}T^{2n+2}/((n+1)(2n+2)!)` and
  `|T_K^m P(t)| ≤ 2C L^m t^{2m+2}/(2m+2)!`;
* (source envelope) the odd Taylor coefficients `k_r` of `K` obey
  `k_{r+1} ≤ (32r+49) k_r/(1212(r+1)(r+2)(2r+3)²) ≤ (49/21816) k_r/(r+1)`, so
  `bs ≤ K(s) ≤ bs e^{as²}` with `b = K'(0) = ν₁/2`, `a = 49/21816`; the optimal rate
  `c_T = sup_{0<s≤T} log(K(s)/(bs))/s²` lies in `[0, a]`;
* (simplex bounds) `b^m T^{2m}/(2m)! ≤ W_m(T) ≤ e^{c_T T²} b^m T^{2m}/(2m)!`, hence
  `N_{n+1}/N_n ≤ (n+1)/(n+2) · e^{c_T T²} b T²/((2n+4)(2n+3)) → 0` as `n → ∞` at fixed `T`;
* (complete expansion) `P = Σ_{n≤m} (-1)^n h_n + (-1)^{m+1} T_K^{m+1} P` on `t ≥ 0`,
  `T_K^m P → 0` uniformly on `[0,T]`, and `D(T) = Σ_n (-1)^n N_n(T)` absolutely;
* (adaptive brackets) if `e^{c_T T²} b T²/((2m+4)(2m+3)) ≤ 1/2`, the partial sums `S_m, S_{m+1}`
  bracket `D(T)` with `|D(T) - S_m(T)| ≤ N_{m+1}(T)`; such `m` exist at every clock, and the first
  descent index `d(T) = min{n : N_{n+1}(T) ≤ N_n(T)}` exists for `T > 0`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "P" => liEvenCrossActualClockPrimitive
local notation "K" => liClockThetaKernel
local notation "K'" => liClockThetaKernelDeriv
local notation "b₀" => liClockThetaKernelDeriv 0
local notation "D" => liEvenCrossActualClockLogHistory

/-! ## Definitions -/

/-- `V_{m+1} = K^{⋆(m+1)}`. -/
def liClockHistoryKernelPower : ℕ → ℝ → ℝ
  | 0 => liClockThetaKernel
  | m + 1 => volterraConv (liClockHistoryKernelPower m) liClockThetaKernel

/-- The derivative `V_1' = K'`, `V_{m+2}' = K' ⋆ V_{m+1}`. -/
def liClockHistoryKernelPowerDeriv : ℕ → ℝ → ℝ
  | 0 => liClockThetaKernelDeriv
  | m + 1 => volterraConv liClockThetaKernelDeriv (liClockHistoryKernelPower m)

/-- `W_{m+1}(T) = ∫_0^T V_{m+1}`. -/
def liClockHistoryCumulative (m : ℕ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, liClockHistoryKernelPower m t

/-- `h_0 = tK`, `h_{n+1} = h_n ⋆ K`. -/
def liClockHistoryRow : ℕ → ℝ → ℝ
  | 0 => fun t => t * liClockThetaKernel t
  | n + 1 => volterraConv (liClockHistoryRow n) liClockThetaKernel

/-- `N_n(T) = ∫_0^T h_n(t)/t dt`. -/
def liClockHistoryIntegratedRow (n : ℕ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, liClockHistoryRow n t / t

/-- `T_K^m P`, `T_K f = f ⋆ K`. -/
def liClockHistoryRemainder (m : ℕ) : ℝ → ℝ :=
  (fun f => volterraConv f liClockThetaKernel)^[m] liEvenCrossActualClockPrimitive

/-- The partial history sum `S_m = Σ_{n ≤ m} (-1)^n N_n`. -/
def liClockHistoryPartialSum (m : ℕ) (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), (-1 : ℝ) ^ n * liClockHistoryIntegratedRow n T

/-- The odd Taylor coefficient `k_r = c_{r+1}/(2r+1)!` of `K = Σ k_r t^{2r+1}`. -/
def liClockThetaKernelTaylorCoeff (r : ℕ) : ℝ :=
  liClockThetaGeneratorCoeff (r + 1) / ((2 * r + 1).factorial : ℝ)

/-- The optimal envelope rate `c_T = sup_{0<s≤T} log(K(s)/(bs))/s²`. -/
def liClockHistoryEnvelopeRate (T : ℝ) : ℝ :=
  sSup ((fun s => Real.log (liClockThetaKernel s / (liClockThetaKernelDeriv 0 * s)) / s ^ 2) ''
    Ioc 0 T)

/-- The first descent index `d(T) = min{n : N_{n+1}(T) ≤ N_n(T)}` (`0` if there is none). -/
def liClockHistoryDescentIndex (T : ℝ) : ℕ := by
  classical
  exact if hd : ∃ n, liClockHistoryIntegratedRow (n + 1) T ≤ liClockHistoryIntegratedRow n T
    then Nat.find hd else 0

local notation "V" => liClockHistoryKernelPower
local notation "V'" => liClockHistoryKernelPowerDeriv
local notation "W" => liClockHistoryCumulative
local notation "ℎ" => liClockHistoryRow
local notation "N" => liClockHistoryIntegratedRow
local notation "R" => liClockHistoryRemainder
local notation "S" => liClockHistoryPartialSum
local notation "k" => liClockThetaKernelTaylorCoeff
local notation "cT" => liClockHistoryEnvelopeRate

/-! ## Continuity and the simplex symmetry -/

theorem continuous_liClockHistoryKernelPower (m : ℕ) : Continuous (V m) := by
  induction m with
  | zero => exact continuous_liClockThetaKernel
  | succ m ih => exact continuous_volterraConv ih continuous_liClockThetaKernel

theorem continuous_liClockHistoryRow (n : ℕ) : Continuous (ℎ n) := by
  induction n with
  | zero => exact continuous_id.mul continuous_liClockThetaKernel
  | succ n ih => exact continuous_volterraConv ih continuous_liClockThetaKernel

theorem liClockHistoryRemainder_zero : R 0 = P := rfl

theorem liClockHistoryRemainder_succ (m : ℕ) : R (m + 1) = volterraConv (R m) K := by
  rw [liClockHistoryRemainder, Function.iterate_succ_apply']
  rfl

theorem continuous_liClockHistoryRemainder (m : ℕ) : Continuous (R m) := by
  induction m with
  | zero => exact continuous_liEvenCrossActualClockPrimitive
  | succ m ih =>
    rw [liClockHistoryRemainder_succ]
    exact continuous_volterraConv ih continuous_liClockThetaKernel

theorem liClockHistoryKernelPower_apply_zero (m : ℕ) : V m 0 = 0 := by
  cases m with
  | zero => exact liClockThetaKernel_zero
  | succ m => exact volterraConv_apply_zero _ _

/-- `h_{n+1} = h_0 ⋆ V_{n+1}`. -/
theorem liClockHistoryRow_succ_eq (n : ℕ) : ℎ (n + 1) = volterraConv (ℎ 0) (V n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext t
    show volterraConv (ℎ (n + 1)) K t = volterraConv (ℎ 0) (volterraConv (V n) K) t
    rw [ih, volterraConv_assoc (continuous_liClockHistoryRow 0)
      (continuous_liClockHistoryKernelPower n) continuous_liClockThetaKernel]

/-- **Simplex symmetry.**  `(n+1) h_n(t) = t V_{n+1}(t)`. -/
theorem liClockHistoryRow_eq (n : ℕ) (t : ℝ) : (n + 1) * ℎ n t = t * V n t := by
  induction n generalizing t with
  | zero => simp [liClockHistoryRow, liClockHistoryKernelPower]
  | succ n ih =>
    have hV := continuous_liClockHistoryKernelPower n
    have hK := continuous_liClockThetaKernel
    show ((n + 1 : ℕ) + 1 : ℝ) * ℎ (n + 1) t = t * volterraConv (V n) K t
    rw [mul_volterraConv hV hK t]
    have e1 : (fun s => s * V n s) = fun s => (n + 1) * ℎ n s := funext fun s => (ih s).symm
    rw [e1, volterraConv_smul_left]
    have e2 : volterraConv (V n) (fun s => s * K s) t = ℎ (n + 1) t := by
      rw [liClockHistoryRow_succ_eq, volterraConv_comm]; rfl
    have e3 : volterraConv (ℎ n) K t = ℎ (n + 1) t := rfl
    rw [e2, e3]
    push_cast
    ring

/-- `h_n(t)/t = V_{n+1}(t)/(n+1)` at every clock (both sides vanish at the origin). -/
theorem liClockHistoryRow_div_eq (n : ℕ) (t : ℝ) : ℎ n t / t = V n t / (n + 1) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [liClockHistoryKernelPower_apply_zero]
  · have := liClockHistoryRow_eq n t
    field_simp
    linarith

theorem continuous_liClockHistoryRow_div (n : ℕ) : Continuous fun t => ℎ n t / t := by
  have e : (fun t => ℎ n t / t) = fun t => V n t / (n + 1) := funext (liClockHistoryRow_div_eq n)
  rw [e]
  exact (continuous_liClockHistoryKernelPower n).div_const _

/-- `N_n = W_{n+1}/(n+1)`. -/
theorem liClockHistoryIntegratedRow_eq (n : ℕ) (T : ℝ) : N n T = W n T / (n + 1) := by
  unfold liClockHistoryIntegratedRow liClockHistoryCumulative
  rw [← intervalIntegral.integral_div]
  exact intervalIntegral.integral_congr fun t _ => liClockHistoryRow_div_eq n t

/-! ## Positivity, monotonicity and the derivative law -/

theorem continuous_liClockHistoryKernelPowerDeriv (m : ℕ) : Continuous (V' m) := by
  cases m with
  | zero => exact continuous_liClockThetaKernelDeriv
  | succ m =>
    exact continuous_volterraConv continuous_liClockThetaKernelDeriv
      (continuous_liClockHistoryKernelPower m)

/-- `V_1' = K'` and `V_{m+2}' = K' ⋆ V_{m+1}`; the boundary term `V_{m+1}(t) K(0)` vanishes. -/
theorem hasDerivAt_liClockHistoryKernelPower (m : ℕ) (t : ℝ) :
    HasDerivAt (V m) (V' m t) t := by
  cases m with
  | zero => exact hasDerivAt_liClockThetaKernel t
  | succ m =>
    exact hasDerivAt_volterraConv_of_apply_zero hasDerivAt_liClockThetaKernel
      continuous_liClockThetaKernelDeriv (continuous_liClockHistoryKernelPower m)
      liClockThetaKernel_zero t

theorem liClockHistoryKernelPower_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < V m t := by
  induction m generalizing t with
  | zero => exact liClockThetaKernel_pos ht
  | succ m ih =>
    exact volterraConv_pos_of_pos (continuous_liClockHistoryKernelPower m)
      continuous_liClockThetaKernel (fun s hs => ih hs) (fun s hs => liClockThetaKernel_pos hs) ht

theorem liClockHistoryKernelPower_nonneg (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ V m t := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [liClockHistoryKernelPower_apply_zero]
  · exact (liClockHistoryKernelPower_pos m ht).le

theorem liClockHistoryKernelPowerDeriv_nonneg (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ V' m t := by
  cases m with
  | zero => exact liClockThetaKernelDeriv_nonneg t
  | succ m =>
    exact volterraConv_nonneg_of_nonneg ht (fun s _ => liClockThetaKernelDeriv_nonneg s)
      (fun s hs => liClockHistoryKernelPower_nonneg m hs.1)

/-- Every `V_m` is nondecreasing on the positive ray. -/
theorem monotoneOn_liClockHistoryKernelPower (m : ℕ) : MonotoneOn (V m) (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (continuous_liClockHistoryKernelPower m).continuousOn
    (fun x _ => (hasDerivAt_liClockHistoryKernelPower m x).differentiableAt.differentiableWithinAt) ?_
  rw [interior_Ici]
  intro x hx
  rw [(hasDerivAt_liClockHistoryKernelPower m x).deriv]
  exact liClockHistoryKernelPowerDeriv_nonneg m (le_of_lt hx)

theorem liClockHistoryCumulative_eq_volterraConv (m : ℕ) :
    W m = volterraConv (fun _ => 1) (V m) :=
  funext fun T => (volterraConv_one_left (V m) T).symm

/-- `W_{m+1} = W_m ⋆ K`. -/
theorem liClockHistoryCumulative_succ (m : ℕ) : W (m + 1) = volterraConv (W m) K := by
  rw [liClockHistoryCumulative_eq_volterraConv, liClockHistoryCumulative_eq_volterraConv]
  funext T
  exact (volterraConv_assoc continuous_const (continuous_liClockHistoryKernelPower m)
    continuous_liClockThetaKernel T).symm

theorem hasDerivAt_liClockHistoryCumulative (m : ℕ) (t : ℝ) : HasDerivAt (W m) (V m t) t :=
  ((continuous_liClockHistoryKernelPower m).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem liClockHistoryCumulative_apply_zero (m : ℕ) : W m 0 = 0 := by
  simp [liClockHistoryCumulative]

theorem continuous_liClockHistoryCumulative (m : ℕ) : Continuous (W m) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_liClockHistoryCumulative m t).continuousAt

/-- Every `W_m` is strictly increasing on the positive ray. -/
theorem strictMonoOn_liClockHistoryCumulative (m : ℕ) : StrictMonoOn (W m) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (continuous_liClockHistoryCumulative m).continuousOn ?_
  rw [interior_Ici]
  intro x hx
  rw [(hasDerivAt_liClockHistoryCumulative m x).deriv]
  exact liClockHistoryKernelPower_pos m hx

theorem liClockHistoryCumulative_pos (m : ℕ) {T : ℝ} (hT : 0 < T) : 0 < W m T := by
  have := strictMonoOn_liClockHistoryCumulative m (self_mem_Ici : (0 : ℝ) ∈ Ici 0)
    (show T ∈ Ici 0 from hT.le) hT
  rwa [liClockHistoryCumulative_apply_zero] at this

theorem liClockHistoryCumulative_nonneg (m : ℕ) {T : ℝ} (hT : 0 ≤ T) : 0 ≤ W m T := by
  rcases hT.eq_or_lt with rfl | hT
  · rw [liClockHistoryCumulative_apply_zero]
  · exact (liClockHistoryCumulative_pos m hT).le

theorem liClockHistoryIntegratedRow_pos (n : ℕ) {T : ℝ} (hT : 0 < T) : 0 < N n T := by
  rw [liClockHistoryIntegratedRow_eq]
  exact div_pos (liClockHistoryCumulative_pos n hT) (by positivity)

theorem liClockHistoryIntegratedRow_nonneg (n : ℕ) {T : ℝ} (hT : 0 ≤ T) : 0 ≤ N n T := by
  rw [liClockHistoryIntegratedRow_eq]
  exact div_nonneg (liClockHistoryCumulative_nonneg n hT) (by positivity)

/-- `N_0 = B - 1`. -/
theorem liClockHistoryIntegratedRow_zero (T : ℝ) :
    N 0 T = liEvenCrossActualClockBorelKernel T - 1 := by
  rw [liClockHistoryIntegratedRow_eq]
  have e : W 0 T = ∫ t in (0 : ℝ)..T, K t := rfl
  rw [e, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_liEvenCrossActualClockBorelKernel_eq s)
    (continuous_liClockThetaKernel.intervalIntegrable _ _)]
  simp

/-! ## Factorial bounds on a compact clock interval -/

private theorem volterraConv_const_pow (A B : ℝ) (j l : ℕ) (t : ℝ) :
    volterraConv (fun s => A * (s ^ j / (j.factorial : ℝ)))
      (fun s => B * (s ^ l / (l.factorial : ℝ))) t =
      A * B * (t ^ (j + l + 1) / ((j + l + 1).factorial : ℝ)) := by
  rw [volterraConv_smul_left, volterraConv_smul_right, volterraConv_pow_div_factorial]
  ring

private theorem kernel_le_one {L T t : ℝ} (hK : ∀ s ∈ Icc 0 T, K s ≤ L * s) (ht : t ≤ T) :
    ∀ s ∈ Icc 0 t, 0 ≤ K s ∧ K s ≤ L * (s ^ 1 / ((1 : ℕ).factorial : ℝ)) := fun s hs =>
  ⟨liClockThetaKernel_nonneg hs.1, by simpa using hK s ⟨hs.1, hs.2.trans ht⟩⟩

/-- `0 ≤ h_n(t) ≤ 2L^{n+1} t^{2n+2}/(2n+2)!` on `[0,T]` when `K(s) ≤ Ls` there. -/
theorem liClockHistoryRow_le {L T : ℝ} (hK : ∀ s ∈ Icc 0 T, K s ≤ L * s) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    0 ≤ ℎ n t ∧ ℎ n t ≤ 2 * L ^ (n + 1) * t ^ (2 * n + 2) / ((2 * n + 2).factorial : ℝ) := by
  induction n generalizing t with
  | zero =>
    refine ⟨mul_nonneg ht.1 (liClockThetaKernel_nonneg ht.1), ?_⟩
    show t * K t ≤ _
    have h1 := hK t ht
    have h2 : (2 * 0 + 2).factorial = 2 := rfl
    rw [h2]
    push_cast
    nlinarith [ht.1]
  | succ n ih =>
    have hcmp := volterraConv_le_of_nonneg (continuous_liClockHistoryRow n)
      (f₂ := fun s => (2 * L ^ (n + 1)) * (s ^ (2 * n + 2) / ((2 * n + 2).factorial : ℝ)))
      (by fun_prop) continuous_liClockThetaKernel
      (g₂ := fun s => L * (s ^ 1 / ((1 : ℕ).factorial : ℝ))) (by fun_prop) ht.1
      (fun s hs => by
        have := ih ⟨hs.1, hs.2.trans ht.2⟩
        rw [mul_div_assoc] at this
        exact this)
      (kernel_le_one hK ht.2)
    rw [volterraConv_const_pow] at hcmp
    refine ⟨volterraConv_nonneg_of_nonneg ht.1 (fun s hs => (ih ⟨hs.1, hs.2.trans ht.2⟩).1)
      (fun s hs => liClockThetaKernel_nonneg hs.1), hcmp.trans_eq ?_⟩
    rw [show 2 * n + 2 + 1 + 1 = 2 * (n + 1) + 2 by ring]
    ring

/-- `0 ≤ N_n(T) ≤ L^{n+1} T^{2n+2}/((n+1)(2n+2)!)` when `K(s) ≤ Ls` on `[0,T]`. -/
theorem liClockHistoryIntegratedRow_le {L T : ℝ} (hK : ∀ s ∈ Icc 0 T, K s ≤ L * s) (hT : 0 ≤ T)
    (n : ℕ) :
    N n T ≤ L ^ (n + 1) * T ^ (2 * n + 2) / ((n + 1) * ((2 * n + 2).factorial : ℝ)) := by
  unfold liClockHistoryIntegratedRow
  have hle := intervalIntegral.integral_mono_on (μ := volume) hT
    ((continuous_liClockHistoryRow_div n).intervalIntegrable 0 T)
    ((by fun_prop : Continuous fun t : ℝ =>
      2 * L ^ (n + 1) / ((2 * n + 2).factorial : ℝ) * t ^ (2 * n + 1)).intervalIntegrable 0 T)
    fun t ht => by
      rcases ht.1.eq_or_lt with h0 | h0
      · subst h0; simp
      · rw [div_le_iff₀ h0]
        refine (liClockHistoryRow_le hK n ht).2.trans_eq ?_
        ring
  refine hle.trans_eq ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring]
  simp only [ne_eq, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, not_false_eq_true,
    zero_pow, sub_zero]
  push_cast
  field_simp
  ring

/-- `|T_K^m P(t)| ≤ 2C L^m t^{2m+2}/(2m+2)!` on `[0,T]` when `K(s) ≤ Ls` and `|P(s)| ≤ Cs²`. -/
theorem abs_liClockHistoryRemainder_le {L C T : ℝ} (hK : ∀ s ∈ Icc 0 T, K s ≤ L * s)
    (hP : ∀ s ∈ Icc 0 T, |P s| ≤ C * s ^ 2) (m : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    |R m t| ≤ 2 * C * L ^ m * t ^ (2 * m + 2) / ((2 * m + 2).factorial : ℝ) := by
  induction m generalizing t with
  | zero =>
    have h1 := hP t ht
    have h2 : (2 * 0 + 2).factorial = 2 := rfl
    rw [liClockHistoryRemainder_zero, h2]
    push_cast
    linarith
  | succ m ih =>
    rw [liClockHistoryRemainder_succ]
    have hR := continuous_liClockHistoryRemainder m
    have h1 : |volterraConv (R m) K t| ≤ volterraConv (fun s => |R m s|) K t := by
      unfold volterraConv
      refine (intervalIntegral.abs_integral_le_integral_abs ht.1).trans_eq ?_
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht.1] at hs
      simp only [abs_mul, abs_of_nonneg (liClockThetaKernel_nonneg hs.1)]
    have h2 := volterraConv_le_of_nonneg hR.abs
      (f₂ := fun s => (2 * C * L ^ m) * (s ^ (2 * m + 2) / ((2 * m + 2).factorial : ℝ)))
      (by fun_prop) continuous_liClockThetaKernel
      (g₂ := fun s => L * (s ^ 1 / ((1 : ℕ).factorial : ℝ))) (by fun_prop) ht.1
      (fun s hs => ⟨abs_nonneg _, by
        have := ih ⟨hs.1, hs.2.trans ht.2⟩
        rw [mul_div_assoc] at this
        exact this⟩)
      (kernel_le_one hK ht.2)
    rw [volterraConv_const_pow] at h2
    refine (h1.trans h2).trans_eq ?_
    rw [show 2 * m + 2 + 1 + 1 = 2 * (m + 1) + 2 by ring]
    ring

/-! ## The source envelope of the kernel -/

theorem liClockThetaKernelDeriv_zero_pos : 0 < b₀ := by
  rw [liClockThetaKernelDeriv_zero]
  exact half_pos (thetaCuspNormalizedEvenMoment_pos 1)

theorem liClockThetaKernelTaylorCoeff_pos (r : ℕ) : 0 < k r :=
  div_pos (liClockThetaGeneratorCoeff_pos _) (by positivity)

theorem liClockThetaKernelTaylorCoeff_zero : k 0 = b₀ := by
  simp [liClockThetaKernelTaylorCoeff, liClockThetaGeneratorCoeff_one, liClockThetaKernelDeriv_zero]

theorem hasSum_liClockThetaKernelTaylorCoeff (s : ℝ) :
    HasSum (fun r => k r * s ^ (2 * r + 1)) (K s) := by
  have e : (fun r => k r * s ^ (2 * r + 1)) = fun j =>
      liClockThetaGeneratorCoeff (j + 1) * s ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) :=
    funext fun r => by unfold liClockThetaKernelTaylorCoeff; ring
  rw [e]
  exact (summable_oddFactorialSeries_term (by norm_num)
    geometricCoeffBound_liClockThetaKernelCoeff s).hasSum

/-- **Score fence on the kernel coefficients.**
`k_{r+1} ≤ (32r+49) k_r/(1212(r+1)(r+2)(2r+3)²)`. -/
theorem liClockThetaKernelTaylorCoeff_succ_le (r : ℕ) :
    k (r + 1) ≤ (32 * r + 49) / (1212 * (r + 1) * (r + 2) * (2 * r + 3) ^ 2) * k r := by
  unfold liClockThetaKernelTaylorCoeff liClockThetaGeneratorCoeff
  have hfence := thetaCuspNormalizedEvenMoment_succ_le_score (r + 1)
  have e1 : ((2 * (r + 1 + 1)).factorial : ℝ) =
      (2 * r + 4) * (2 * r + 3) * ((2 * (r + 1)).factorial : ℝ) := by
    rw [show 2 * (r + 1 + 1) = (2 * (r + 1) + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast; ring
  have e2 : ((2 * (r + 1) + 1).factorial : ℝ) =
      (2 * r + 3) * (2 * r + 2) * ((2 * r + 1).factorial : ℝ) := by
    rw [show 2 * (r + 1) + 1 = (2 * r + 1 + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [e1, e2]
  set F1 := ((2 * (r + 1)).factorial : ℝ)
  set F2 := ((2 * r + 1).factorial : ℝ)
  set ν₁ := thetaCuspNormalizedEvenMoment (r + 1)
  set ν₂ := thetaCuspNormalizedEvenMoment (r + 1 + 1)
  have hF1 : 0 < F1 := by positivity
  have hF2 : 0 < F2 := by positivity
  have hQ : 0 < (2 * (r : ℝ) + 4) * (2 * r + 3) ^ 2 * (2 * r + 2) * F1 * F2 := by positivity
  have lhs : ν₂ / ((2 * r + 4) * (2 * r + 3) * F1) / ((2 * r + 3) * (2 * r + 2) * F2) =
      ν₂ / ((2 * (r : ℝ) + 4) * (2 * r + 3) ^ 2 * (2 * r + 2) * F1 * F2) := by
    rw [div_div]; congr 1; ring
  have rhs : (32 * r + 49) / (1212 * (r + 1) * (r + 2) * (2 * r + 3) ^ 2) * (ν₁ / F1 / F2) =
      (ν₁ * (32 * r + 49) / 303) / ((2 * (r : ℝ) + 4) * (2 * r + 3) ^ 2 * (2 * r + 2) * F1 * F2) := by
    field_simp
    ring
  rw [lhs, rhs]
  apply div_le_div_of_nonneg_right _ hQ.le
  push_cast at hfence
  linarith

/-- `k_{r+1} ≤ (49/21816) k_r/(r+1)`, from `49(r+2)(2r+3)² - 18(32r+49) = 196r³+980r²+1041r`. -/
theorem liClockThetaKernelTaylorCoeff_succ_le_div (r : ℕ) :
    k (r + 1) ≤ 49 / 21816 / (r + 1) * k r := by
  refine (liClockThetaKernelTaylorCoeff_succ_le r).trans
    (mul_le_mul_of_nonneg_right ?_ (liClockThetaKernelTaylorCoeff_pos r).le)
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  have hpoly : 18 * (32 * (r : ℝ) + 49) ≤ 49 * ((r + 2) * (2 * r + 3) ^ 2) := by
    nlinarith [mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg hr hr]
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hpoly (by positivity : (0 : ℝ) ≤ 1212 * (r + 1))]

/-- `k_r ≤ b a^r/r!` with `a = 49/21816`. -/
theorem liClockThetaKernelTaylorCoeff_le (r : ℕ) :
    k r ≤ b₀ * (49 / 21816) ^ r / (r.factorial : ℝ) := by
  induction r with
  | zero => simp [liClockThetaKernelTaylorCoeff_zero]
  | succ r ih =>
    refine (liClockThetaKernelTaylorCoeff_succ_le_div r).trans ?_
    calc 49 / 21816 / ((r : ℝ) + 1) * k r
        ≤ 49 / 21816 / ((r : ℝ) + 1) * (b₀ * (49 / 21816) ^ r / (r.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = b₀ * (49 / 21816) ^ (r + 1) / ((r + 1).factorial : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; field_simp; ring

/-- **Source envelope.**  `K(s) ≤ bs e^{as²}` for `s ≥ 0`, `a = 49/21816`. -/
theorem liClockThetaKernel_le_mul_exp {s : ℝ} (hs : 0 ≤ s) :
    K s ≤ b₀ * s * Real.exp (49 / 21816 * s ^ 2) := by
  have hexp : HasSum (fun r : ℕ => b₀ * s * ((49 / 21816 * s ^ 2) ^ r / (r.factorial : ℝ)))
      (b₀ * s * Real.exp (49 / 21816 * s ^ 2)) := by
    have h : HasSum (fun r : ℕ => (49 / 21816 * s ^ 2) ^ r / (r.factorial : ℝ))
        (Real.exp (49 / 21816 * s ^ 2)) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
    exact h.mul_left _
  refine hasSum_le (fun r => ?_) (hasSum_liClockThetaKernelTaylorCoeff s) hexp
  have h1 := mul_le_mul_of_nonneg_right (liClockThetaKernelTaylorCoeff_le r)
    (pow_nonneg hs (2 * r + 1))
  refine h1.trans_eq ?_
  rw [mul_pow, ← pow_mul, pow_succ]
  ring

/-- `bs ≤ K(s)` for `s ≥ 0`. -/
theorem mul_le_liClockThetaKernel {s : ℝ} (hs : 0 ≤ s) : b₀ * s ≤ K s := by
  have h := le_hasSum (hasSum_liClockThetaKernelTaylorCoeff s) 0 fun j _ =>
    mul_nonneg (liClockThetaKernelTaylorCoeff_pos j).le (pow_nonneg hs _)
  simpa [liClockThetaKernelTaylorCoeff_zero] using h

/-- `K(s) ≤ (b e^{aT²}) s` on `[0,T]`. -/
theorem liClockThetaKernel_le_mul_of_mem {T s : ℝ} (hs : s ∈ Icc 0 T) :
    K s ≤ b₀ * Real.exp (49 / 21816 * T ^ 2) * s := by
  refine (liClockThetaKernel_le_mul_exp hs.1).trans ?_
  have : Real.exp (49 / 21816 * s ^ 2) ≤ Real.exp (49 / 21816 * T ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [hs.1, hs.2])
  have hb := liClockThetaKernelDeriv_zero_pos
  nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hb.le hs.1)]

/-- `|P(s)| ≤ (A/2) e^{βT} s²` on `[0,T]`, `A = Σ_q |w_q|²`. -/
theorem abs_liEvenCrossActualClockPrimitive_le_sq_of_mem {T s : ℝ} (hs : s ∈ Icc 0 T) :
    |P s| ≤ xiShiftAbsoluteMass 0 / 2 * Real.exp (liEvenCrossActualClockMaxGrowthRate * T) *
      s ^ 2 := by
  refine (abs_liEvenCrossActualClockPrimitive_le_max hs.1).trans ?_
  have hA := xiShiftAbsoluteMass_nonneg 0
  have hβ := liEvenCrossActualClockMaxGrowthRate_nonneg
  have : Real.exp (liEvenCrossActualClockMaxGrowthRate * s) ≤
      Real.exp (liEvenCrossActualClockMaxGrowthRate * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hβ)
  have h2 : 0 ≤ xiShiftAbsoluteMass 0 * s ^ 2 / 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this h2]

/-- The optimal rate: `0 ≤ c_T ≤ a` and `K(s) ≤ bs e^{c_T s²}` on `[0,T]`. -/
theorem liClockHistoryEnvelopeRate_spec {T : ℝ} (hT : 0 < T) :
    0 ≤ cT T ∧ cT T ≤ 49 / 21816 ∧ ∀ s ∈ Icc 0 T, K s ≤ b₀ * s * Real.exp (cT T * s ^ 2) := by
  have hb := liClockThetaKernelDeriv_zero_pos
  set φ := fun s : ℝ => Real.log (K s / (b₀ * s)) / s ^ 2 with hφ
  have hrange : ∀ s ∈ Ioc (0 : ℝ) T, 0 ≤ φ s ∧ φ s ≤ 49 / 21816 := fun s hs => by
    have hs0 := hs.1
    have hbs : 0 < b₀ * s := mul_pos hb hs0
    have h1 : 1 ≤ K s / (b₀ * s) := by
      rw [le_div_iff₀ hbs, one_mul]; exact mul_le_liClockThetaKernel hs0.le
    have h2 : K s / (b₀ * s) ≤ Real.exp (49 / 21816 * s ^ 2) := by
      rw [div_le_iff₀ hbs]
      have := liClockThetaKernel_le_mul_exp hs0.le
      linarith
    have hl0 : 0 ≤ Real.log (K s / (b₀ * s)) := Real.log_nonneg h1
    have hl1 : Real.log (K s / (b₀ * s)) ≤ 49 / 21816 * s ^ 2 := by
      rw [Real.log_le_iff_le_exp (by linarith)]; exact h2
    exact ⟨div_nonneg hl0 (by positivity), by rw [div_le_iff₀ (by positivity)]; exact hl1⟩
  have hne : (φ '' Ioc 0 T).Nonempty := ⟨φ T, mem_image_of_mem φ ⟨hT, le_rfl⟩⟩
  have hbdd : BddAbove (φ '' Ioc 0 T) :=
    ⟨49 / 21816, forall_mem_image.2 fun s hs => (hrange s hs).2⟩
  have hc0 : 0 ≤ cT T :=
    (hrange T ⟨hT, le_rfl⟩).1.trans (le_csSup hbdd (mem_image_of_mem φ ⟨hT, le_rfl⟩))
  refine ⟨hc0, csSup_le hne (forall_mem_image.2 fun s hs => (hrange s hs).2), fun s hs => ?_⟩
  rcases hs.1.eq_or_lt with h0 | h0
  · subst h0; simp [liClockThetaKernel_zero]
  · have hle : φ s ≤ cT T := le_csSup hbdd (mem_image_of_mem φ ⟨h0, hs.2⟩)
    have hbs : 0 < b₀ * s := mul_pos hb h0
    have hKs : 0 < K s / (b₀ * s) := div_pos (liClockThetaKernel_pos h0) hbs
    simp only [hφ] at hle
    rw [div_le_iff₀ (by positivity), Real.log_le_iff_le_exp hKs, div_le_iff₀ hbs] at hle
    linarith

/-! ## Simplex bounds and the vanishing order ratio -/

private theorem monomial_nonneg (c : ℝ) (hc : 0 ≤ c) (j : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ c * (s ^ j / (j.factorial : ℝ)) :=
  mul_nonneg hc (div_nonneg (pow_nonneg hs j) (by positivity))

/-- `b^{n+1} t^{2n+1}/(2n+1)! ≤ V_{n+1}(t)` for `t ≥ 0`. -/
theorem liClockHistoryKernelPower_ge (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    b₀ ^ (n + 1) * (t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) ≤ V n t := by
  have hb := liClockThetaKernelDeriv_zero_pos
  induction n generalizing t with
  | zero =>
    have := mul_le_liClockThetaKernel ht
    show _ ≤ K t
    simpa using this
  | succ n ih =>
    have h := volterraConv_le_of_nonneg
      (f₁ := fun s => b₀ ^ (n + 1) * (s ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)))
      (g₁ := fun s => b₀ * (s ^ 1 / ((1 : ℕ).factorial : ℝ))) (by fun_prop)
      (continuous_liClockHistoryKernelPower n) (by fun_prop) continuous_liClockThetaKernel ht
      (fun s hs => ⟨monomial_nonneg _ (pow_nonneg hb.le _) _ hs.1, ih hs.1⟩)
      (fun s hs => ⟨monomial_nonneg _ hb.le _ hs.1, by simpa using mul_le_liClockThetaKernel hs.1⟩)
    rw [volterraConv_const_pow] at h
    refine le_of_eq_of_le ?_ h
    rw [show 2 * n + 1 + 1 + 1 = 2 * (n + 1) + 1 by ring]
    ring

/-- `V_{n+1}(t) ≤ e^{ct²} b^{n+1} t^{2n+1}/(2n+1)!` on `[0,T]` when `K(s) ≤ bs e^{cs²}` there. -/
theorem liClockHistoryKernelPower_le_exp {c T : ℝ} (hc : 0 ≤ c)
    (hK : ∀ s ∈ Icc 0 T, K s ≤ b₀ * s * Real.exp (c * s ^ 2)) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    V n t ≤ Real.exp (c * t ^ 2) * (b₀ ^ (n + 1) * (t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))) := by
  have hb := liClockThetaKernelDeriv_zero_pos
  induction n generalizing t with
  | zero =>
    have := hK t ht
    simp only [zero_add, pow_one, mul_zero, Nat.factorial_one, Nat.cast_one, div_one]
    show K t ≤ _
    linarith
  | succ n ih =>
    show volterraConv (V n) K t ≤ _
    set A : ℝ → ℝ := fun s => b₀ ^ (n + 1) * (s ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))
    set G : ℝ → ℝ := fun s => b₀ * (s ^ 1 / ((1 : ℕ).factorial : ℝ))
    have hAc : Continuous A := by fun_prop
    have hGc : Continuous G := by fun_prop
    have hVc := continuous_liClockHistoryKernelPower n
    have hKc := continuous_liClockThetaKernel
    have h1 : volterraConv (V n) K t ≤
        ∫ s in (0 : ℝ)..t, Real.exp (c * t ^ 2) * (A (t - s) * G s) := by
      unfold volterraConv
      refine intervalIntegral.integral_mono_on ht.1
        ((by fun_prop : Continuous fun s => V n (t - s) * K s).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun s => Real.exp (c * t ^ 2) * (A (t - s) * G s)).intervalIntegrable
          _ _) fun s hs => ?_
      have hts : t - s ∈ Icc 0 T := ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
      have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
      have e1 := ih hts
      have e2 := hK s hsT
      have hexp : Real.exp (c * (t - s) ^ 2) * Real.exp (c * s ^ 2) ≤ Real.exp (c * t ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith [mul_nonneg hc (mul_nonneg hs.1 (sub_nonneg.2 hs.2))]
      have hK0 := liClockThetaKernel_nonneg hs.1
      have hA0 : 0 ≤ A (t - s) := monomial_nonneg _ (pow_nonneg hb.le _) _ hts.1
      have hG : G s = b₀ * s := by simp [G]
      calc V n (t - s) * K s
          ≤ (Real.exp (c * (t - s) ^ 2) * A (t - s)) * (b₀ * s * Real.exp (c * s ^ 2)) :=
            mul_le_mul e1 e2 hK0 (mul_nonneg (Real.exp_pos _).le hA0)
        _ = (Real.exp (c * (t - s) ^ 2) * Real.exp (c * s ^ 2)) * (A (t - s) * (b₀ * s)) := by ring
        _ ≤ Real.exp (c * t ^ 2) * (A (t - s) * (b₀ * s)) :=
            mul_le_mul_of_nonneg_right hexp (mul_nonneg hA0 (mul_nonneg hb.le hs.1))
        _ = Real.exp (c * t ^ 2) * (A (t - s) * G s) := by rw [hG]
    rw [intervalIntegral.integral_const_mul] at h1
    have h2 : ∫ s in (0 : ℝ)..t, A (t - s) * G s = volterraConv A G t := rfl
    rw [h2, volterraConv_const_pow] at h1
    refine h1.trans_eq ?_
    rw [show 2 * n + 1 + 1 + 1 = 2 * (n + 1) + 1 by ring]
    ring

private theorem integral_monomial (c : ℝ) (n : ℕ) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, c * (t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) =
      c * (T ^ (2 * n + 2) / ((2 * n + 2).factorial : ℝ)) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div, integral_pow]
  have e : ((2 * n + 2).factorial : ℝ) = (2 * n + 2) * ((2 * n + 1).factorial : ℝ) := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  rw [e, show 2 * n + 1 + 1 = 2 * n + 2 by ring]
  simp only [ne_eq, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, not_false_eq_true,
    zero_pow, sub_zero]
  push_cast
  field_simp
  ring

/-- **Simplex lower bound.**  `b^{n+1} T^{2n+2}/(2n+2)! ≤ W_{n+1}(T)` for `T ≥ 0`. -/
theorem liClockHistoryCumulative_ge (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    b₀ ^ (n + 1) * (T ^ (2 * n + 2) / ((2 * n + 2).factorial : ℝ)) ≤ W n T := by
  unfold liClockHistoryCumulative
  rw [← integral_monomial]
  exact intervalIntegral.integral_mono_on hT
    ((by fun_prop : Continuous fun t : ℝ =>
      b₀ ^ (n + 1) * (t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))).intervalIntegrable _ _)
    ((continuous_liClockHistoryKernelPower n).intervalIntegrable 0 T)
    fun t ht => liClockHistoryKernelPower_ge n ht.1

/-- **Simplex upper bound.**  `W_{n+1}(T) ≤ e^{cT²} b^{n+1} T^{2n+2}/(2n+2)!` when
`K(s) ≤ bs e^{cs²}` on `[0,T]`. -/
theorem liClockHistoryCumulative_le_exp {c T : ℝ} (hc : 0 ≤ c) (hT : 0 ≤ T)
    (hK : ∀ s ∈ Icc 0 T, K s ≤ b₀ * s * Real.exp (c * s ^ 2)) (n : ℕ) :
    W n T ≤ Real.exp (c * T ^ 2) * (b₀ ^ (n + 1) * (T ^ (2 * n + 2) / ((2 * n + 2).factorial : ℝ))) := by
  have hb := liClockThetaKernelDeriv_zero_pos
  unfold liClockHistoryCumulative
  rw [← integral_monomial, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on hT
    ((continuous_liClockHistoryKernelPower n).intervalIntegrable 0 T)
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (c * T ^ 2) *
      (b₀ ^ (n + 1) * (t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)))).intervalIntegrable _ _)
    fun t ht => (liClockHistoryKernelPower_le_exp hc hK n ht).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ ht.1 ht.2 2) hc)) (monomial_nonneg _ (pow_nonneg hb.le _) _ ht.1))

/-- **Order-ratio bound.**
`N_{n+1}(T) ≤ (n+1)/(n+2) · e^{cT²} b T²/((2n+4)(2n+3)) · N_n(T)`. -/
theorem liClockHistoryIntegratedRow_succ_le {c T : ℝ} (hc : 0 ≤ c) (hT : 0 ≤ T)
    (hK : ∀ s ∈ Icc 0 T, K s ≤ b₀ * s * Real.exp (c * s ^ 2)) (n : ℕ) :
    N (n + 1) T ≤ (n + 1) / (n + 2) *
      (Real.exp (c * T ^ 2) * b₀ * T ^ 2 / ((2 * n + 4) * (2 * n + 3))) * N n T := by
  have hb := liClockThetaKernelDeriv_zero_pos
  rw [liClockHistoryIntegratedRow_eq, liClockHistoryIntegratedRow_eq]
  have hup := liClockHistoryCumulative_le_exp hc hT hK (n + 1)
  have hlow := liClockHistoryCumulative_ge n hT
  have e : ((2 * (n + 1) + 2).factorial : ℝ) =
      (2 * n + 4) * (2 * n + 3) * ((2 * n + 2).factorial : ℝ) := by
    rw [show 2 * (n + 1) + 2 = (2 * n + 2 + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [e] at hup
  set F := ((2 * n + 2).factorial : ℝ)
  have hF : 0 < F := by positivity
  have hcoef : 0 ≤ (n + 1 : ℝ) / (n + 2) *
      (Real.exp (c * T ^ 2) * b₀ * T ^ 2 / ((2 * n + 4) * (2 * n + 3))) := by positivity
  push_cast
  calc W (n + 1) T / ((n : ℝ) + 1 + 1)
      ≤ Real.exp (c * T ^ 2) * (b₀ ^ (n + 1 + 1) *
          (T ^ (2 * (n + 1) + 2) / ((2 * n + 4) * (2 * n + 3) * F))) / ((n : ℝ) + 1 + 1) :=
        div_le_div_of_nonneg_right hup (by positivity)
    _ = (n + 1 : ℝ) / (n + 2) *
          (Real.exp (c * T ^ 2) * b₀ * T ^ 2 / ((2 * n + 4) * (2 * n + 3))) *
          (b₀ ^ (n + 1) * (T ^ (2 * n + 2) / F) / ((n : ℝ) + 1)) := by
        field_simp
        ring
    _ ≤ (n + 1 : ℝ) / (n + 2) *
          (Real.exp (c * T ^ 2) * b₀ * T ^ 2 / ((2 * n + 4) * (2 * n + 3))) *
          (W n T / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlow (by positivity)) hcoef

/-- At a fixed clock the consecutive history ratio vanishes with order. -/
theorem tendsto_liClockHistoryIntegratedRow_ratio_zero {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => N (n + 1) T / N n T) atTop (𝓝 0) := by
  obtain ⟨hc0, -, hK⟩ := liClockHistoryEnvelopeRate_spec hT
  have hb := liClockThetaKernelDeriv_zero_pos
  set M := Real.exp (cT T * T ^ 2) * b₀ * T ^ 2
  have hM : 0 ≤ M := by positivity
  have hlim : Tendsto (fun n : ℕ => M * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul M
  refine squeeze_zero (fun n => div_nonneg (liClockHistoryIntegratedRow_pos _ hT).le
    (liClockHistoryIntegratedRow_pos _ hT).le) (fun n => ?_) hlim
  have hNn := liClockHistoryIntegratedRow_pos n hT
  rw [div_le_iff₀ hNn]
  refine (liClockHistoryIntegratedRow_succ_le hc0 hT.le hK n).trans ?_
  apply mul_le_mul_of_nonneg_right _ hNn.le
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have h1 : (n + 1 : ℝ) / (n + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have h2 : M / ((2 * n + 4) * (2 * n + 3)) ≤ M * (1 / ((n : ℝ) + 1)) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left hM (by positivity) (by nlinarith)
  calc (n + 1 : ℝ) / (n + 2) * (M / ((2 * n + 4) * (2 * n + 3)))
      ≤ 1 * (M / ((2 * n + 4) * (2 * n + 3))) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ M * (1 / ((n : ℝ) + 1)) := by rw [one_mul]; exact h2

/-- The first descent index exists at every positive clock. -/
theorem exists_liClockHistoryIntegratedRow_succ_le {T : ℝ} (hT : 0 < T) :
    ∃ n, N (n + 1) T ≤ N n T := by
  obtain ⟨n, hn⟩ := ((tendsto_liClockHistoryIntegratedRow_ratio_zero hT).eventually
    (gt_mem_nhds one_pos)).exists
  exact ⟨n, (div_le_one (liClockHistoryIntegratedRow_pos n hT)).1 hn.le⟩

theorem liClockHistoryDescentIndex_spec {T : ℝ} (hT : 0 < T) :
    N (liClockHistoryDescentIndex T + 1) T ≤ N (liClockHistoryDescentIndex T) T ∧
      ∀ n < liClockHistoryDescentIndex T, N n T < N (n + 1) T := by
  classical
  have hex := exists_liClockHistoryIntegratedRow_succ_le hT
  have e : liClockHistoryDescentIndex T = Nat.find hex := by
    unfold liClockHistoryDescentIndex
    rw [dif_pos hex]
  rw [e]
  exact ⟨Nat.find_spec hex, fun n hn => lt_of_not_ge (Nat.find_min hex hn)⟩

/-! ## The complete history expansion -/

private theorem volterraConv_kernel_congr {f g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hfg : ∀ s ∈ Icc 0 t, f s = g s) : volterraConv f K t = volterraConv g K t := by
  unfold volterraConv
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  rw [hfg (t - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩]

/-- `T_K^k P = h_k - T_K^{k+1} P` on `t ≥ 0`, from `P + P ⋆ K = tK`. -/
theorem liClockHistoryRemainder_eq_sub (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    R j t = ℎ j t - R (j + 1) t := by
  induction j generalizing t with
  | zero =>
    rw [liClockHistoryRemainder_succ, liClockHistoryRemainder_zero]
    have := liEvenCrossActualClockPrimitive_add_volterraConv ht
    show P t = t * K t - volterraConv P K t
    linarith
  | succ j ih =>
    have hh := continuous_liClockHistoryRow j
    have hr := continuous_liClockHistoryRemainder (j + 1)
    have hK := continuous_liClockThetaKernel
    have e1 : R (j + 1) t = volterraConv (fun s => ℎ j s - R (j + 1) s) K t := by
      conv_lhs => rw [liClockHistoryRemainder_succ]
      exact volterraConv_kernel_congr ht fun s hs => ih hs.1
    have e2 : volterraConv (fun s => ℎ j s - R (j + 1) s) K t = ℎ (j + 1) t - R (j + 1 + 1) t := by
      rw [liClockHistoryRemainder_succ (j + 1)]
      show _ = volterraConv (ℎ j) K t - volterraConv (R (j + 1)) K t
      unfold volterraConv
      rw [← intervalIntegral.integral_sub
        ((by fun_prop : Continuous fun s => ℎ j (t - s) * K s).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun s => R (j + 1) (t - s) * K s).intervalIntegrable _ _)]
      refine intervalIntegral.integral_congr fun s _ => ?_
      ring
    rw [e1, e2]

/-- **Complete causal expansion.**  `P = Σ_{n≤m} (-1)^n h_n + (-1)^{m+1} T_K^{m+1} P` on `t ≥ 0`. -/
theorem liEvenCrossActualClockPrimitive_eq_history (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    P t = ∑ n ∈ Finset.range (m + 1), (-1 : ℝ) ^ n * ℎ n t + (-1) ^ (m + 1) * R (m + 1) t := by
  induction m with
  | zero =>
    have := liClockHistoryRemainder_eq_sub 0 ht
    rw [liClockHistoryRemainder_zero] at this
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, pow_one]
    linarith
  | succ m ih =>
    rw [Finset.sum_range_succ _ (m + 1), ih, liClockHistoryRemainder_eq_sub (m + 1) ht]
    ring

private theorem exists_compact_constants (T : ℝ) :
    ∃ L C : ℝ, 0 ≤ L ∧ 0 ≤ C ∧ (∀ s ∈ Icc 0 T, K s ≤ L * s) ∧
      ∀ s ∈ Icc 0 T, |P s| ≤ C * s ^ 2 :=
  ⟨_, _, by have := liClockThetaKernelDeriv_zero_pos; positivity,
    by have := xiShiftAbsoluteMass_nonneg 0; positivity,
    fun _ hs => liClockThetaKernel_le_mul_of_mem hs,
    fun _ hs => abs_liEvenCrossActualClockPrimitive_le_sq_of_mem hs⟩

/-- The history remainder tends to zero uniformly on every compact clock interval. -/
theorem tendstoUniformlyOn_liClockHistoryRemainder (T : ℝ) :
    TendstoUniformlyOn (fun m => R m) (fun _ => 0) atTop (Icc 0 T) := by
  obtain ⟨L, C, hL, hC, hK, hP⟩ := exists_compact_constants T
  set T' := max T 0
  have hlim : Tendsto (fun m : ℕ => 2 * C * T' ^ 2 * ((L * T' ^ 2) ^ m / (m.factorial : ℝ)))
      atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (L * T' ^ 2)).const_mul (2 * C * T' ^ 2)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.1 hlim) ε hε] with m hm t ht
  rw [Real.dist_eq, abs_lt, sub_zero] at hm
  rw [dist_zero_left, Real.norm_eq_abs]
  have hT' : t ≤ T' := ht.2.trans (le_max_left _ _)
  have h0T' : 0 ≤ T' := le_max_right _ _
  have hfac : (m.factorial : ℝ) ≤ ((2 * m + 2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have htp : t ^ (2 * m + 2) ≤ T' ^ 2 * (T' ^ 2) ^ m := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_left₀ ht.1 hT' _ |>.trans_eq (by ring)
  calc |R m t| ≤ 2 * C * L ^ m * t ^ (2 * m + 2) / ((2 * m + 2).factorial : ℝ) :=
        abs_liClockHistoryRemainder_le hK hP m ht
    _ ≤ 2 * C * L ^ m * (T' ^ 2 * (T' ^ 2) ^ m) / ((2 * m + 2).factorial : ℝ) := by
        gcongr
    _ ≤ 2 * C * L ^ m * (T' ^ 2 * (T' ^ 2) ^ m) / (m.factorial : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
    _ = 2 * C * T' ^ 2 * ((L * T' ^ 2) ^ m / (m.factorial : ℝ)) := by rw [mul_pow]; ring
    _ < ε := hm.2

/-- Absolute summability of the history rows at a fixed clock. -/
theorem summable_liClockHistoryIntegratedRow {T : ℝ} (hT : 0 ≤ T) :
    Summable fun n => N n T := by
  obtain ⟨L, -, hL, -, hK, -⟩ := exists_compact_constants T
  have hsum : Summable fun n : ℕ => (L * T ^ 2) ^ (n + 1) / ((n + 1).factorial : ℝ) :=
    (summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial (L * T ^ 2))
  refine Summable.of_nonneg_of_le (fun n => liClockHistoryIntegratedRow_nonneg n hT)
    (fun n => (liClockHistoryIntegratedRow_le hK hT n).trans ?_) hsum
  have hfac : ((n + 1).factorial : ℝ) ≤ (n + 1) * ((2 * n + 2).factorial : ℝ) := by
    have : ((n + 1).factorial : ℝ) ≤ ((2 * n + 2).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    nlinarith [(by positivity : (0 : ℝ) ≤ ((2 * n + 2).factorial : ℝ)),
      (n.cast_nonneg : (0 : ℝ) ≤ n)]
  have e : (L * T ^ 2) ^ (n + 1) = L ^ (n + 1) * T ^ (2 * n + 2) := by
    rw [mul_pow, ← pow_mul]; ring
  rw [e]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac

/-- **Complete causal-log history.**  `D(T) = Σ_n (-1)^n N_n(T)` for every `T ≥ 0`. -/
theorem hasSum_liClockHistoryIntegratedRow {T : ℝ} (hT : 0 ≤ T) :
    HasSum (fun n => (-1 : ℝ) ^ n * N n T) (D T) := by
  obtain ⟨L, C, hL, hC, hK, hP⟩ := exists_compact_constants T
  have hsum : Summable fun n => (-1 : ℝ) ^ n * N n T :=
    Summable.of_norm_bounded (summable_liClockHistoryIntegratedRow hT) fun n => by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (liClockHistoryIntegratedRow_nonneg n hT)]
  rw [hsum.hasSum_iff_tendsto_nat, ← tendsto_add_atTop_iff_nat 1]
  have herr : ∀ m : ℕ, |D T - ∑ n ∈ Finset.range (m + 1), (-1 : ℝ) ^ n * N n T| ≤
      2 * C * L ^ (m + 1) * T ^ (2 * (m + 1) + 2) / ((2 * (m + 1) + 2).factorial : ℝ) := by
    intro m
    have hcont : Continuous fun t =>
        liEvenCrossActualClockLogHistoryDensity t -
          ∑ n ∈ Finset.range (m + 1), (-1 : ℝ) ^ n * (ℎ n t / t) := by
      have := continuous_liEvenCrossActualClockLogHistoryDensity
      have hr := continuous_liClockHistoryRow_div
      fun_prop
    have e : D T - ∑ n ∈ Finset.range (m + 1), (-1 : ℝ) ^ n * N n T =
        ∫ t in (0 : ℝ)..T, (liEvenCrossActualClockLogHistoryDensity t -
          ∑ n ∈ Finset.range (m + 1), (-1 : ℝ) ^ n * (ℎ n t / t)) := by
      rw [intervalIntegral.integral_sub
        (continuous_liEvenCrossActualClockLogHistoryDensity.intervalIntegrable _ _)
        ((by have hr := continuous_liClockHistoryRow_div; fun_prop :
          Continuous fun t => ∑ n ∈ Finset.range (m + 1), (-1 : ℝ) ^ n * (ℎ n t / t)).intervalIntegrable
            _ _),
        intervalIntegral.integral_finsetSum fun n _ =>
          ((continuous_liClockHistoryRow_div n).const_mul _).intervalIntegrable _ _]
      simp only [intervalIntegral.integral_const_mul]
      rfl
    rw [e, ← Real.norm_eq_abs]
    have hb2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
      (C := 2 * C * L ^ (m + 1) * T ^ (2 * (m + 1) + 1) / ((2 * (m + 1) + 2).factorial : ℝ))
      (f := fun t => liEvenCrossActualClockLogHistoryDensity t -
          ∑ n ∈ Finset.range (m + 1), (-1 : ℝ) ^ n * (ℎ n t / t)) fun t ht => by
        rw [uIoc_of_le hT] at ht
        have ht0 : 0 < t := ht.1
        have htT : t ∈ Icc 0 T := ⟨ht0.le, ht.2⟩
        have hexp := liEvenCrossActualClockPrimitive_eq_history m ht0.le
        have hval : liEvenCrossActualClockLogHistoryDensity t -
            ∑ n ∈ Finset.range (m + 1), (-1 : ℝ) ^ n * (ℎ n t / t) =
            (-1) ^ (m + 1) * R (m + 1) t / t := by
          unfold liEvenCrossActualClockLogHistoryDensity
          rw [hexp, add_div, Finset.sum_div]
          simp only [mul_div_assoc]
          ring
        rw [hval, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_pos ht0, div_le_iff₀ ht0]
        refine (abs_liClockHistoryRemainder_le hK hP (m + 1) htT).trans ?_
        have htp : t ^ (2 * (m + 1) + 2) ≤ T ^ (2 * (m + 1) + 1) * t := by
          rw [show 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 by ring, pow_succ]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0.le ht.2 _) ht0.le
        calc 2 * C * L ^ (m + 1) * t ^ (2 * (m + 1) + 2) / ((2 * (m + 1) + 2).factorial : ℝ)
            ≤ 2 * C * L ^ (m + 1) * (T ^ (2 * (m + 1) + 1) * t) /
                ((2 * (m + 1) + 2).factorial : ℝ) := by gcongr
          _ = _ := by ring
    refine hb2.trans_eq ?_
    rw [sub_zero, abs_of_nonneg hT]
    ring
  have hlim : Tendsto (fun m : ℕ => 2 * C * T ^ 2 * ((L * T ^ 2) ^ (m + 1) / ((m + 1).factorial : ℝ)))
      atTop (𝓝 0) := by
    have := ((FloorSemiring.tendsto_pow_div_factorial_atTop (L * T ^ 2)).comp
      (tendsto_add_atTop_nat 1)).const_mul (2 * C * T ^ 2)
    simpa using this
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun m => ?_) hlim
  rw [Real.dist_eq, abs_sub_comm]
  refine (herr m).trans ?_
  have hfac : ((m + 1).factorial : ℝ) ≤ ((2 * (m + 1) + 2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have e : 2 * C * L ^ (m + 1) * T ^ (2 * (m + 1) + 2) = 2 * C * T ^ 2 * (L * T ^ 2) ^ (m + 1) := by
    rw [mul_pow, ← pow_mul]; ring
  rw [e, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity) hfac)
    (by positivity)

/-- `D(T) = Σ_n (-1)^n N_n(T)`. -/
theorem liEvenCrossActualClockLogHistory_eq_tsum {T : ℝ} (hT : 0 ≤ T) :
    D T = ∑' n, (-1 : ℝ) ^ n * N n T :=
  (hasSum_liClockHistoryIntegratedRow hT).tsum_eq.symm

/-! ## Adaptive alternating brackets -/

theorem liClockHistoryPartialSum_succ (m : ℕ) (T : ℝ) :
    S (m + 1) T = S m T + (-1) ^ (m + 1) * N (m + 1) T := by
  unfold liClockHistoryPartialSum
  rw [Finset.sum_range_succ]

/-- **Adaptive brackets.**  If `e^{c_T T²} b T²/((2m+4)(2m+3)) ≤ 1/2`, then every later row ratio is
at most `1/2`, `S_m` and `S_{m+1}` bracket `D(T)`, and `|D(T) - S_m(T)| ≤ N_{m+1}(T)`. -/
theorem liClockHistory_brackets {T : ℝ} (hT : 0 < T) {m : ℕ}
    (hm : Real.exp (cT T * T ^ 2) * b₀ * T ^ 2 / ((2 * m + 4) * (2 * m + 3)) ≤ 1 / 2) :
    (∀ n, m ≤ n → N (n + 1) T ≤ N n T / 2) ∧
    (Even m → S (m + 1) T ≤ D T ∧ D T ≤ S m T) ∧
    (Odd m → S m T ≤ D T ∧ D T ≤ S (m + 1) T) ∧
    |D T - S m T| ≤ N (m + 1) T := by
  obtain ⟨hc0, -, hK⟩ := liClockHistoryEnvelopeRate_spec hT
  have hb := liClockThetaKernelDeriv_zero_pos
  have hdec : ∀ n, m ≤ n → N (n + 1) T ≤ N n T / 2 := fun n hn => by
    refine (liClockHistoryIntegratedRow_succ_le hc0 hT.le hK n).trans ?_
    have hNn := liClockHistoryIntegratedRow_nonneg n hT.le
    have hnm : (m : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : (n + 1 : ℝ) / (n + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h2 : Real.exp (cT T * T ^ 2) * b₀ * T ^ 2 / ((2 * n + 4) * (2 * n + 3)) ≤ 1 / 2 :=
      (div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)).trans hm
    have h3 : (n + 1 : ℝ) / (n + 2) *
        (Real.exp (cT T * T ^ 2) * b₀ * T ^ 2 / ((2 * n + 4) * (2 * n + 3))) ≤ 1 / 2 :=
      (mul_le_of_le_one_left (by positivity) h1).trans h2
    nlinarith [mul_le_mul_of_nonneg_right h3 hNn]
  set r : ℕ → ℝ := fun i => N (m + 1 + i) T
  have hanti : Antitone r := antitone_nat_of_succ_le fun i => by
    have := hdec (m + 1 + i) (by omega)
    have h0 := liClockHistoryIntegratedRow_nonneg (m + 1 + i) hT.le
    simp only [r]
    rw [show m + 1 + (i + 1) = m + 1 + i + 1 by ring]
    linarith
  have hsum := (hasSum_liClockHistoryIntegratedRow hT.le).summable
  have hsplit := hsum.sum_add_tsum_nat_add (m + 1)
  rw [← liEvenCrossActualClockLogHistory_eq_tsum hT.le] at hsplit
  have htail : ∑' i, (-1 : ℝ) ^ (i + (m + 1)) * N (i + (m + 1)) T =
      (-1) ^ (m + 1) * ∑' i, (-1 : ℝ) ^ i * r i := by
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    simp only [r]
    rw [show m + 1 + i = i + (m + 1) by ring, pow_add]
    ring
  have hrN : Summable r := by
    have := (summable_nat_add_iff (m + 1)).2 (summable_liClockHistoryIntegratedRow hT.le)
    refine this.congr fun i => ?_
    simp only [r]
    rw [show i + (m + 1) = m + 1 + i by ring]
  have hrs : Summable fun i => (-1 : ℝ) ^ i * r i :=
    Summable.of_norm_bounded hrN fun i => by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (liClockHistoryIntegratedRow_nonneg _ hT.le)]
  set l := ∑' i, (-1 : ℝ) ^ i * r i
  have hl := hrs.tendsto_sum_tsum_nat
  have hl0 : 0 ≤ l := by simpa using hanti.alternating_series_le_tendsto hl 0
  have hl1 : l ≤ N (m + 1) T := by
    have := hanti.tendsto_le_alternating_series hl 0
    simpa [r] using this
  have hD : D T = S m T + (-1) ^ (m + 1) * l := by
    rw [← hsplit, htail]
    rfl
  refine ⟨hdec, fun he => ?_, fun ho => ?_, ?_⟩
  · have hpow : (-1 : ℝ) ^ (m + 1) = -1 := by rw [pow_succ, he.neg_one_pow]; ring
    rw [liClockHistoryPartialSum_succ, hD, hpow]
    constructor <;> linarith
  · have hpow : (-1 : ℝ) ^ (m + 1) = 1 := by rw [pow_succ, ho.neg_one_pow]; ring
    rw [liClockHistoryPartialSum_succ, hD, hpow]
    constructor <;> linarith
  · rw [hD, add_sub_cancel_left, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg hl0]
    exact hl1

/-- The explicit sufficient bracket condition `e^{aT²} b T²/((2m+4)(2m+3)) ≤ 1/2`,
`a = 49/21816`. -/
theorem liClockHistory_brackets_of_explicit {T : ℝ} (hT : 0 < T) {m : ℕ}
    (hm : Real.exp (49 / 21816 * T ^ 2) * b₀ * T ^ 2 / ((2 * m + 4) * (2 * m + 3)) ≤ 1 / 2) :
    (∀ n, m ≤ n → N (n + 1) T ≤ N n T / 2) ∧
    (Even m → S (m + 1) T ≤ D T ∧ D T ≤ S m T) ∧
    (Odd m → S m T ≤ D T ∧ D T ≤ S (m + 1) T) ∧
    |D T - S m T| ≤ N (m + 1) T := by
  obtain ⟨-, hca, -⟩ := liClockHistoryEnvelopeRate_spec hT
  have hb := liClockThetaKernelDeriv_zero_pos
  refine liClockHistory_brackets hT (le_trans ?_ hm)
  have : Real.exp (cT T * T ^ 2) ≤ Real.exp (49 / 21816 * T ^ 2) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hca (by positivity))
  gcongr

/-- Certified adaptive brackets exist at every positive clock. -/
theorem exists_liClockHistory_bracket_order (T : ℝ) :
    ∃ m : ℕ, Real.exp (49 / 21816 * T ^ 2) * b₀ * T ^ 2 / ((2 * m + 4) * (2 * m + 3)) ≤ 1 / 2 := by
  have hb := liClockThetaKernelDeriv_zero_pos
  set M := Real.exp (49 / 21816 * T ^ 2) * b₀ * T ^ 2
  obtain ⟨m, hm⟩ := exists_nat_ge (2 * M)
  refine ⟨m, ?_⟩
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end RHTower
