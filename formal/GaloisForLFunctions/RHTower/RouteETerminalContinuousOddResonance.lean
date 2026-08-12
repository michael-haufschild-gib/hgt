import GaloisForLFunctions.RHTower.RouteETerminalPrimeStieltjesTransport
import GaloisForLFunctions.RHTower.RouteECriticalTerminalVarianceMinimax
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Route E continuous terminal odd-resonance localization

This module solves global coercive part of terminal-band minimax.  It proves exact flat integral,
quantitative quadratic floor near zero frequency, absolute floor outside unit window, and resulting
`O(1/L)` localization of every bounded normalized-energy history.
-/

namespace RHTower

open Filter Topology Set MeasureTheory intervalIntegral

noncomputable section

/-- Continuous logarithmic terminal-frame energy. -/
noncomputable def routeETerminalContinuousEnergy (a L t : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1,
    routeETerminalWeight a v * routeETerminalPhaseEnergy t (Real.exp (L - v))

/-- Flat terminal frame, before exponential position tilt. -/
noncomputable def routeETerminalFlatEnergy (L t : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1, routeETerminalPhaseEnergy t (Real.exp (L - v))

theorem routeETerminalPhaseEnergy_exp (L t v : ℝ) :
    routeETerminalPhaseEnergy t (Real.exp (L - v)) =
      2 + 2 * Real.cos (t * (L - v)) := by
  rw [routeETerminalPhaseEnergy, Real.log_exp]

theorem continuous_routeETerminalContinuousIntegrand (a L t : ℝ) :
    Continuous (fun v : ℝ =>
      routeETerminalWeight a v * routeETerminalPhaseEnergy t (Real.exp (L - v))) := by
  rw [show (fun v : ℝ =>
      routeETerminalWeight a v * routeETerminalPhaseEnergy t (Real.exp (L - v))) =
      fun v : ℝ => Real.exp (-a * v) * (2 + 2 * Real.cos (t * (L - v))) by
        funext v
        rw [routeETerminalWeight, routeETerminalPhaseEnergy_exp]]
  fun_prop

theorem routeETerminalContinuousEnergy_nonneg (a L t : ℝ) :
    0 ≤ routeETerminalContinuousEnergy a L t := by
  rw [routeETerminalContinuousEnergy]
  apply intervalIntegral.integral_nonneg zero_le_one
  intro v _
  exact mul_nonneg (routeETerminalWeight_pos a v).le
    (routeETerminalPhaseEnergy_nonneg t (Real.exp (L - v)))

theorem integral_cos_terminal {L t : ℝ} (ht : t ≠ 0) :
    (∫ v in (0 : ℝ)..1, Real.cos (t * (L - v))) =
      (Real.sin (t * L) - Real.sin (t * (L - 1))) / t := by
  have hderiv : ∀ v : ℝ,
      HasDerivAt (fun x : ℝ => Real.sin (t * (L - x)) / (-t))
        (Real.cos (t * (L - v))) v := by
    intro v
    have harg : HasDerivAt (fun x : ℝ => t * (L - x)) (-t) v := by
      have h := ((hasDerivAt_const v L).sub (hasDerivAt_id v)).const_mul t
      simpa only [Pi.sub_apply, id_eq, sub_zero, zero_sub, mul_neg, mul_one] using h
    have hsin := harg.sin
    have hne : -t ≠ 0 := neg_ne_zero.mpr ht
    apply (hsin.div_const (-t)).congr_deriv
    field_simp [hne]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hderiv v)
    ((Real.continuous_cos.comp (continuous_const.mul
      (continuous_const.sub continuous_id))).intervalIntegrable 0 1)]
  field_simp
  ring

theorem sin_sub_terminal_factorization (L t : ℝ) :
    Real.sin (t * L) - Real.sin (t * (L - 1)) =
      2 * Real.sin (t / 2) * Real.cos (t * (L - 1 / 2)) := by
  rw [Real.sin_sub_sin]
  ring_nf

/-- Exact unweighted integral `(21)`. -/
theorem routeETerminalFlatEnergy_eq {L t : ℝ} (ht : t ≠ 0) :
    routeETerminalFlatEnergy L t =
      2 + 4 * (Real.sin (t / 2) / t) * Real.cos (t * (L - 1 / 2)) := by
  rw [routeETerminalFlatEnergy]
  have hsplit : (∫ v in (0 : ℝ)..1,
      routeETerminalPhaseEnergy t (Real.exp (L - v))) =
      ∫ v in (0 : ℝ)..1, (2 + 2 * Real.cos (t * (L - v))) := by
    apply intervalIntegral.integral_congr
    intro v _
    exact routeETerminalPhaseEnergy_exp L t v
  rw [hsplit]
  have hcos : IntervalIntegrable (fun v : ℝ =>
      2 * Real.cos (t * (L - v))) volume 0 1 := by
    exact (by fun_prop : Continuous (fun v : ℝ =>
      2 * Real.cos (t * (L - v)))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add intervalIntegrable_const hcos,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_cos_terminal ht, sin_sub_terminal_factorization]
  ring

theorem routeETerminalFlatEnergy_eq_sinc {L t : ℝ} (ht : t ≠ 0) :
    routeETerminalFlatEnergy L t =
      2 + 2 * Real.sinc (t / 2) * Real.cos (t * (L - 1 / 2)) := by
  rw [routeETerminalFlatEnergy_eq ht, Real.sinc_of_ne_zero (by positivity)]
  ring

/-- Positive sinc gap controlling worst common phase at fixed nonzero frequency magnitude. -/
def routeETerminalSincGap (s : ℝ) : ℝ :=
  2 - 4 * |Real.sin (s / 2)| / s

theorem routeETerminalSincGap_pos {s : ℝ} (hs : 0 < s) :
    0 < routeETerminalSincGap s := by
  have hstrict := Real.abs_sin_lt_abs (show s / 2 ≠ 0 by positivity)
  rw [abs_of_pos (by positivity : 0 < s / 2)] at hstrict
  rw [routeETerminalSincGap]
  have hs0 : 0 < s := hs
  apply sub_pos.mpr
  rw [div_lt_iff₀ hs0]
  nlinarith

/-- Sharp-enough local Taylor defect from the paper: on the unit frequency window, sinc loses
at least `s²/28`, hence the flat phase frame loses at least `s²/14`. -/
theorem routeETerminalSincGap_ge_sq_div_fourteen
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    s ^ 2 / 14 ≤ routeETerminalSincGap s := by
  let x : ℝ := s / 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hxhalf : x ≤ 1 / 2 := by dsimp [x]; linarith
  have hxabs : |x| ≤ 1 := by
    rw [abs_of_pos hx]
    linarith
  have hTaylor := (abs_le.mp (Real.sin_bound hxabs)).2
  rw [abs_of_pos hx] at hTaylor
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
  have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx.le 3
  have hx5 : x ^ 5 / 100 ≤ x ^ 3 / 42 := by
    have hmul := mul_le_mul_of_nonneg_left hx2 hx3
    rw [show x ^ 3 * x ^ 2 = x ^ 5 by ring] at hmul
    nlinarith
  have hsin : Real.sin x ≤ x - x ^ 3 / 7 := by
    nlinarith
  have hxpi : x ≤ Real.pi :=
    hxhalf.trans (by linarith [Real.two_le_pi])
  have hsin0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.le hxpi
  rw [routeETerminalSincGap, show s / 2 = x by rfl,
    abs_of_nonneg hsin0]
  have hsx : s = 2 * x := by dsimp [x]; ring
  rw [hsx]
  field_simp
  nlinarith

theorem continuousOn_routeETerminalSincGap_Icc (A B : ℝ) (hA : 0 < A) :
    ContinuousOn routeETerminalSincGap (Icc A B) := by
  intro s hs
  have hs0 : s ≠ 0 := ne_of_gt (hA.trans_le hs.1)
  unfold routeETerminalSincGap
  fun_prop

/-- Absolute global frequency gap. Compactness handles intermediate frequencies; the elementary
`|sin| ≤ 1` tail prevents any escape at infinity. -/
theorem exists_routeETerminalSincGap_uniform_of_one_le :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 1 ≤ s → δ ≤ routeETerminalSincGap s := by
  have hne : (Icc (1 : ℝ) 4).Nonempty := nonempty_Icc.mpr (by norm_num)
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne
    (continuousOn_routeETerminalSincGap_Icc 1 4 zero_lt_one)
  let δ : ℝ := min (routeETerminalSincGap s₀) 1
  have hs₀pos : 0 < routeETerminalSincGap s₀ :=
    routeETerminalSincGap_pos (zero_lt_one.trans_le hs₀.1)
  have hδpos : 0 < δ := lt_min hs₀pos zero_lt_one
  refine ⟨δ, hδpos, ?_⟩
  intro s hs
  by_cases hs4 : s ≤ 4
  · exact (min_le_left _ _).trans (hmin ⟨hs, hs4⟩)
  · have hspos : 0 < s := zero_lt_one.trans_le hs
    have hsin : |Real.sin (s / 2)| ≤ 1 := Real.abs_sin_le_one _
    have hratio : 4 * |Real.sin (s / 2)| / s ≤ 1 := by
      rw [div_le_one hspos]
      nlinarith
    exact (min_le_right _ _).trans (by
      rw [routeETerminalSincGap]
      linarith)

theorem routeETerminalFlatEnergy_ge_sincGap {L t : ℝ} (ht : t ≠ 0) :
    routeETerminalSincGap |t| ≤ routeETerminalFlatEnergy L t := by
  rw [routeETerminalFlatEnergy_eq ht, routeETerminalSincGap]
  have ht0 : 0 < |t| := abs_pos.mpr ht
  have hcos := abs_le.mp (Real.abs_cos_le_one (t * (L - 1 / 2)))
  have hcoeff :
      |4 * (Real.sin (t / 2) / t)| = 4 * |Real.sin (|t| / 2)| / |t| := by
    have hsinAbs : |Real.sin (t / 2)| = |Real.sin (|t| / 2)| := by
      by_cases htpos : 0 ≤ t
      · rw [abs_of_nonneg htpos]
      · have htneg : t ≤ 0 := le_of_not_ge htpos
        rw [abs_of_nonpos htneg]
        rw [show -t / 2 = -(t / 2) by ring, Real.sin_neg, abs_neg]
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), hsinAbs]
    ring
  have hprod :
      -(4 * |Real.sin (|t| / 2)| / |t|) ≤
        4 * (Real.sin (t / 2) / t) * Real.cos (t * (L - 1 / 2)) := by
    rw [← hcoeff]
    let q : ℝ := 4 * (Real.sin (t / 2) / t)
    let z : ℝ := Real.cos (t * (L - 1 / 2))
    change -|q| ≤ q * z
    have habsprod : |q * z| ≤ |q| := by
      have hz : |z| ≤ 1 := by
        dsimp [z]
        exact Real.abs_cos_le_one _
      rw [abs_mul]
      have hq0 : 0 ≤ |q| := abs_nonneg _
      exact mul_le_of_le_one_right hq0 hz
    linarith [neg_abs_le (q * z)]
  linarith

/-- Discarding exponential terminal tilt costs at most the universal factor `exp (-1)`. -/
theorem routeETerminalContinuousEnergy_ge_exp_neg_one_mul_flat
    {a L t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp (-1) * routeETerminalFlatEnergy L t ≤
      routeETerminalContinuousEnergy a L t := by
  rw [routeETerminalFlatEnergy, routeETerminalContinuousEnergy,
    ← intervalIntegral.integral_const_mul]
  have hflat : IntervalIntegrable (fun v : ℝ =>
      routeETerminalPhaseEnergy t (Real.exp (L - v))) volume 0 1 := by
    rw [show (fun v : ℝ =>
        routeETerminalPhaseEnergy t (Real.exp (L - v))) =
        fun v : ℝ => 2 + 2 * Real.cos (t * (L - v)) by
      funext v
      exact routeETerminalPhaseEnergy_exp L t v]
    exact (by fun_prop : Continuous (fun v : ℝ =>
      2 + 2 * Real.cos (t * (L - v)))).intervalIntegrable 0 1
  have htilted : IntervalIntegrable (fun v : ℝ =>
      routeETerminalWeight a v *
        routeETerminalPhaseEnergy t (Real.exp (L - v))) volume 0 1 :=
    (continuous_routeETerminalContinuousIntegrand a L t).intervalIntegrable 0 1
  refine intervalIntegral.integral_mono_on zero_le_one
    (hflat.const_mul (Real.exp (-1))) htilted ?_
  intro v hv
  have hav : a * v ≤ 1 := by nlinarith [hv.1, hv.2]
  have hweight : Real.exp (-1) ≤ routeETerminalWeight a v := by
    rw [routeETerminalWeight]
    exact Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul_of_nonneg_right hweight
    (routeETerminalPhaseEnergy_nonneg t (Real.exp (L - v)))

/-- Local weighted coercivity `(22)`, uniform over all critical tilts `0 ≤ a ≤ 1`. -/
theorem routeETerminalContinuousEnergy_ge_local_sq
    {a L t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ht0 : t ≠ 0) (ht1 : |t| ≤ 1) :
    Real.exp (-1) * (t ^ 2 / 14) ≤
      routeETerminalContinuousEnergy a L t := by
  have htpos : 0 < |t| := abs_pos.mpr ht0
  have hgap := routeETerminalSincGap_ge_sq_div_fourteen htpos ht1
  have hflat := routeETerminalFlatEnergy_ge_sincGap (L := L) ht0
  have htilt := routeETerminalContinuousEnergy_ge_exp_neg_one_mul_flat
    (L := L) (t := t) ha0 ha1
  have hexp : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have htSq : |t| ^ 2 = t ^ 2 := sq_abs t
  rw [htSq] at hgap
  exact (mul_le_mul_of_nonneg_left (hgap.trans hflat) hexp).trans htilt

/-- Global weighted coercivity `(23)`, with an absolute positive constant independent of tilt and
terminal position. -/
theorem exists_routeETerminalContinuousEnergy_uniform_of_one_le_abs :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a L t : ℝ,
      0 ≤ a → a ≤ 1 → 1 ≤ |t| →
        δ ≤ routeETerminalContinuousEnergy a L t := by
  obtain ⟨δ₀, hδ₀, hgap⟩ := exists_routeETerminalSincGap_uniform_of_one_le
  refine ⟨Real.exp (-1) * δ₀, mul_pos (Real.exp_pos _) hδ₀, ?_⟩
  intro a L t ha0 ha1 ht
  have ht0 : t ≠ 0 := abs_pos.mp (zero_lt_one.trans_le ht)
  have hflat := (hgap |t| ht).trans
    (routeETerminalFlatEnergy_ge_sincGap (L := L) ht0)
  exact (mul_le_mul_of_nonneg_left hflat (Real.exp_pos _).le).trans
    (routeETerminalContinuousEnergy_ge_exp_neg_one_mul_flat
      (L := L) (t := t) ha0 ha1)

/-- Quantitative global localization `(24)`. A bounded `L²` energy cannot use the nonlocal
frequency region; once there, local sinc coercivity bounds `L|t|` absolutely. -/
theorem exists_routeETerminal_boundedEnergy_localization_constant :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a L t C : ℝ,
      0 ≤ a → a ≤ 1 → 1 ≤ L → 0 ≤ C →
      L ^ 2 * routeETerminalContinuousEnergy a L t ≤ C →
      C < L ^ 2 * δ →
      (L * |t|) ^ 2 ≤ 14 * Real.exp 1 * C := by
  obtain ⟨δ, hδ, hglobal⟩ :=
    exists_routeETerminalContinuousEnergy_uniform_of_one_le_abs
  refine ⟨δ, hδ, ?_⟩
  intro a L t C ha0 ha1 hL hC henergy hthreshold
  have hLabs : 0 ≤ L ^ 2 := sq_nonneg L
  have ht1 : |t| < 1 := by
    by_contra hnot
    have hfar : 1 ≤ |t| := le_of_not_gt hnot
    have hframe := hglobal a L t ha0 ha1 hfar
    have hmul := mul_le_mul_of_nonneg_left hframe hLabs
    linarith
  by_cases ht0 : t = 0
  · have hRHS : 0 ≤ 14 * Real.exp 1 * C := by positivity
    simpa [ht0] using hRHS
  · have hlocal := routeETerminalContinuousEnergy_ge_local_sq
      (L := L) ha0 ha1 ht0 ht1.le
    have hscaled := mul_le_mul_of_nonneg_left hlocal hLabs
    have hbasic : L ^ 2 * (Real.exp (-1) * (t ^ 2 / 14)) ≤ C :=
      hscaled.trans henergy
    have hexp : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hscaledBasic := mul_le_mul_of_nonneg_left hbasic
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 14) (Real.exp_pos 1).le)
    calc
      (L * |t|) ^ 2 = L ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]
      _ = 14 * Real.exp 1 *
          (L ^ 2 * (Real.exp (-1) * (t ^ 2 / 14))) := by
        symm
        calc
          14 * Real.exp 1 *
              (L ^ 2 * (Real.exp (-1) * (t ^ 2 / 14))) =
              (Real.exp 1 * Real.exp (-1)) * (L ^ 2 * t ^ 2) := by ring
          _ = L ^ 2 * t ^ 2 := by rw [mul_comm (Real.exp 1), hexp, one_mul]
      _ ≤ 14 * Real.exp 1 * C := hscaledBasic

/-- Odd-resonance classifier for every cofinal history already localized to `t → 0`: if its
weighted terminal energy vanishes while `tL → u`, then `u` is an odd multiple of `pi`.
This is exact escape-mode statement `(25)`. -/
theorem routeETerminal_oddResonance_of_vanishingEnergy
    {Z : Type*} {l : Filter Z} [l.NeBot]
    {a L t : Z → ℝ} {u : ℝ}
    (ha0 : ∀ᶠ z in l, 0 ≤ a z)
    (ha1 : ∀ᶠ z in l, a z ≤ 1)
    (ht0 : ∀ᶠ z in l, t z ≠ 0)
    (htend : Tendsto t l (𝓝 0))
    (hphase : Tendsto (fun z => t z * L z) l (𝓝 u))
    (henergy : Tendsto (fun z => routeETerminalContinuousEnergy (a z) (L z) (t z))
      l (𝓝 0)) :
    ∃ k : ℤ, Real.pi + k * (2 * Real.pi) = u := by
  have hsinc : Tendsto (fun z => Real.sinc (t z / 2)) l (𝓝 1) := by
    change Tendsto (Real.sinc ∘ fun z => t z / 2) l (𝓝 1)
    convert Real.continuous_sinc.continuousAt.tendsto.comp
      (htend.div_const 2) using 1 <;> norm_num
  have hshift : Tendsto (fun z => t z * (L z - 1 / 2)) l (𝓝 u) := by
    have hhalf : Tendsto (fun z => t z / 2) l (𝓝 0) := by
      simpa using htend.div_const 2
    convert hphase.sub hhalf using 1 <;> ring
  have hcos : Tendsto (fun z => Real.cos (t z * (L z - 1 / 2))) l
      (𝓝 (Real.cos u)) := Real.continuous_cos.continuousAt.tendsto.comp hshift
  have hflatFormula : ∀ᶠ z in l,
      routeETerminalFlatEnergy (L z) (t z) =
        2 + 2 * Real.sinc (t z / 2) * Real.cos (t z * (L z - 1 / 2)) := by
    filter_upwards [ht0] with z hz
    exact routeETerminalFlatEnergy_eq_sinc hz
  have hflatLimit : Tendsto (fun z => routeETerminalFlatEnergy (L z) (t z)) l
      (𝓝 (2 + 2 * Real.cos u)) := by
    have htwo : Tendsto (fun _ : Z => (2 : ℝ)) l (𝓝 2) := tendsto_const_nhds
    have hraw := htwo.add ((htwo.mul hsinc).mul hcos)
    have heq : ∀ᶠ z in l,
        (2 + 2 * Real.sinc (t z / 2) * Real.cos (t z * (L z - 1 / 2))) =
          routeETerminalFlatEnergy (L z) (t z) := by
      filter_upwards [hflatFormula] with z hz
      exact hz.symm
    convert hraw.congr' heq using 1 <;> ring
  have hflatZero : Tendsto (fun z => routeETerminalFlatEnergy (L z) (t z)) l
      (𝓝 0) := by
    have hnonneg : ∀ᶠ z in l, 0 ≤ routeETerminalFlatEnergy (L z) (t z) := by
      filter_upwards with z
      rw [routeETerminalFlatEnergy]
      exact intervalIntegral.integral_nonneg zero_le_one fun v _ =>
        routeETerminalPhaseEnergy_nonneg (t z) (Real.exp (L z - v))
    have hupper : ∀ᶠ z in l,
        routeETerminalFlatEnergy (L z) (t z) ≤
          Real.exp 1 * routeETerminalContinuousEnergy (a z) (L z) (t z) := by
      filter_upwards [ha0, ha1] with z hza0 hza1
      have htilt := routeETerminalContinuousEnergy_ge_exp_neg_one_mul_flat
        (L := L z) (t := t z) hza0 hza1
      have hexp : Real.exp (-1) * Real.exp 1 = 1 := by
        rw [← Real.exp_add]
        norm_num
      have hm := mul_le_mul_of_nonneg_left htilt (Real.exp_pos 1).le
      calc
        routeETerminalFlatEnergy (L z) (t z) =
            Real.exp 1 * (Real.exp (-1) *
              routeETerminalFlatEnergy (L z) (t z)) := by
          rw [← mul_assoc, mul_comm (Real.exp 1), hexp, one_mul]
        _ ≤ Real.exp 1 *
            routeETerminalContinuousEnergy (a z) (L z) (t z) := hm
    refine squeeze_zero' hnonneg hupper ?_
    simpa using henergy.const_mul (Real.exp 1)
  have hlimitEq : 2 + 2 * Real.cos u = 0 :=
    tendsto_nhds_unique hflatLimit hflatZero
  apply Real.cos_eq_neg_one_iff.mp
  linarith

theorem routeETerminalPhaseEnergy_eq_two_mul_one_sub_cos
    (u₀ e : ℝ) (hodd : Real.cos u₀ = -1) (hsin : Real.sin u₀ = 0) :
    2 + 2 * Real.cos (u₀ + e) = 2 * (1 - Real.cos e) := by
  rw [Real.cos_add, hodd, hsin]
  ring

/-- First odd resonance is literally odd: both trigonometric identities needed by second-order
expansion are proved without selecting a branch of a square root. -/
theorem routeETerminal_pi_is_odd_phase :
    Real.cos Real.pi = -1 ∧ Real.sin Real.pi = 0 := by
  simp

/-- Pointwise second-order phase law. This replaces informal uniform small-angle notation by an
exact filter theorem obtained from the second derivative of cosine. -/
theorem tendsto_terminalPhaseEnergy_scaled
    {Z : Type*} {l : Filter Z}
    {e scale : Z → ℝ} {q u₀ : ℝ}
    (hodd : Real.cos u₀ = -1) (hsin : Real.sin u₀ = 0)
    (he : Tendsto e l (𝓝 0))
    (hscaled : Tendsto (fun z => scale z * e z) l (𝓝 q)) :
    Tendsto (fun z => scale z ^ 2 * (2 + 2 * Real.cos (u₀ + e z))) l
      (𝓝 (q ^ 2)) := by
  have hcosRatio : Tendsto (fun x : ℝ =>
      if x = 0 then (1 : ℝ) else 2 * (1 - Real.cos x) / x ^ 2)
      (𝓝 0) (𝓝 1) := by
    have hratioEq : (fun x : ℝ =>
        if x = 0 then (1 : ℝ) else 2 * (1 - Real.cos x) / x ^ 2) =
        fun x : ℝ => Real.sinc (x / 2) ^ 2 := by
      funext x
      by_cases hx : x = 0
      · simp [hx]
      · have hx2 : x / 2 ≠ 0 := div_ne_zero hx (by norm_num)
        rw [if_neg hx, Real.sinc_of_ne_zero hx2]
        field_simp
        have hs := Real.sin_sq_eq_half_sub (x / 2)
        rw [show 2 * (x / 2) = x by ring] at hs
        nlinarith
    rw [hratioEq]
    convert ((Real.continuous_sinc.comp (continuous_id.div_const 2)).tendsto 0).pow 2 using 1 <;>
      norm_num
  have hratioComp : Tendsto (fun z =>
      if e z = 0 then (1 : ℝ) else 2 * (1 - Real.cos (e z)) / e z ^ 2)
      l (𝓝 1) := hcosRatio.comp he
  have hfactor : ∀ z : Z,
      scale z ^ 2 * (2 + 2 * Real.cos (u₀ + e z)) =
        (scale z * e z) ^ 2 *
          (if e z = 0 then 1 else 2 * (1 - Real.cos (e z)) / e z ^ 2) := by
    intro z
    rw [routeETerminalPhaseEnergy_eq_two_mul_one_sub_cos u₀ (e z) hodd hsin]
    by_cases hz : e z = 0
    · simp [hz]
    · simp only [hz, if_false]
      field_simp
  have hprod := hscaled.pow 2 |>.mul hratioComp
  convert hprod using 1
  · funext z
    exact hfactor z
  · try ring

/-- Complete second-order history law `(26)`--`(28)`. Once a history is localized to an odd
terminal phase `u₀` and its centered correction has limit `b`, its normalized energy converges to
the exact weighted quadratic. No informal Taylor remainder or subsequence argument remains. -/
theorem tendsto_routeETerminalContinuousEnergy_of_secondOrderHistory
    (a u₀ b : ℝ) (t : ℝ → ℝ)
    (hodd : Real.cos u₀ = -1) (hsin : Real.sin u₀ = 0)
    (hphase : Tendsto (fun L => t L * L) atTop (𝓝 u₀))
    (hcorrection : Tendsto (fun L => L * (t L * L - u₀)) atTop (𝓝 b)) :
    Tendsto (fun L => L ^ 2 * routeETerminalContinuousEnergy a L (t L))
      atTop (𝓝 (routeETerminalQuadratic a u₀ b)) := by
  let e : ℝ → ℝ → ℝ := fun L v => t L * (L - v) - u₀
  let scaled : ℝ → ℝ → ℝ := fun L v => L * e L v
  have hscaled (v : ℝ) : Tendsto (fun L => scaled L v) atTop
      (𝓝 (b - u₀ * v)) := by
    have hEq : (fun L => scaled L v) =
        (fun L => L * (t L * L - u₀) - (t L * L) * v) := by
      funext L
      dsimp [scaled, e]
      ring
    rw [hEq]
    exact hcorrection.sub (hphase.mul_const v)
  have hLinv : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have he0 (v : ℝ) : Tendsto (fun L => e L v) atTop (𝓝 0) := by
    have hEq : ∀ᶠ L : ℝ in atTop,
        e L v = scaled L v * L⁻¹ := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with L hL
      dsimp [scaled]
      field_simp
    have hEq' : (fun L => scaled L v * L⁻¹) =ᶠ[atTop]
        (fun L => e L v) := by
      filter_upwards [hEq] with L hL
      exact hL.symm
    convert ((hscaled v).mul hLinv).congr' hEq' using 1 <;> ring
  have hpoint (v : ℝ) : Tendsto (fun L =>
      L ^ 2 * (routeETerminalWeight a v *
        routeETerminalPhaseEnergy (t L) (Real.exp (L - v)))) atTop
      (𝓝 (routeETerminalWeight a v * (b - u₀ * v) ^ 2)) := by
    have hphaseScaled := tendsto_terminalPhaseEnergy_scaled hodd hsin
      (he0 v) (hscaled v)
    have hweightLimit : Tendsto (fun _ : ℝ => routeETerminalWeight a v) atTop
        (𝓝 (routeETerminalWeight a v)) := tendsto_const_nhds
    have hmul := hweightLimit.mul hphaseScaled
    have hEq : (fun L => routeETerminalWeight a v *
        (L ^ 2 * (2 + 2 * Real.cos (u₀ + e L v)))) =
        (fun L => L ^ 2 * (routeETerminalWeight a v *
          routeETerminalPhaseEnergy (t L) (Real.exp (L - v)))) := by
      funext L
      rw [routeETerminalPhaseEnergy_exp]
      rw [show t L * (L - v) = u₀ + e L v by dsimp [e]; ring]
      ring
    convert hmul.congr' (Filter.Eventually.of_forall fun L => congrFun hEq L) using 1 <;> ring
  let B : ℝ := |b| + |u₀| + 2
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hcorrAbs : ∀ᶠ L : ℝ in atTop,
      |L * (t L * L - u₀)| < |b| + 1 := by
    have habs : Tendsto (fun L => |L * (t L * L - u₀)|) atTop (𝓝 |b|) :=
      (continuous_abs.tendsto b).comp hcorrection
    exact (tendsto_order.1 habs).2 (|b| + 1) (by linarith)
  have hphaseAbs : ∀ᶠ L : ℝ in atTop,
      |t L * L| < |u₀| + 1 := by
    have habs : Tendsto (fun L => |t L * L|) atTop (𝓝 |u₀|) :=
      (continuous_abs.tendsto u₀).comp hphase
    exact (tendsto_order.1 habs).2 (|u₀| + 1) (by linarith)
  have hbound : ∀ᶠ L : ℝ in atTop, ∀ᵐ v : ℝ,
      v ∈ uIoc (0 : ℝ) 1 →
      ‖L ^ 2 * (routeETerminalWeight a v *
        routeETerminalPhaseEnergy (t L) (Real.exp (L - v)))‖ ≤
        routeETerminalWeight a v * B ^ 2 := by
    filter_upwards [hcorrAbs, hphaseAbs] with L hcorr hphaseL
    filter_upwards with v hv
    rw [uIoc_of_le zero_le_one] at hv
    have hvabs : |v| ≤ 1 := by rw [abs_of_nonneg hv.1.le]; exact hv.2
    have hscaledBound : |scaled L v| ≤ B := by
      have hEq : scaled L v = L * (t L * L - u₀) - (t L * L) * v := by
        dsimp [scaled, e]
        ring
      rw [hEq]
      calc
        |L * (t L * L - u₀) - (t L * L) * v| ≤
            |L * (t L * L - u₀)| + |(t L * L) * v| := abs_sub _ _
        _ = |L * (t L * L - u₀)| + |t L * L| * |v| := by simp only [abs_mul]
        _ ≤ (|b| + 1) + (|u₀| + 1) * 1 := by
          exact add_le_add hcorr.le
            (mul_le_mul hphaseL.le hvabs (abs_nonneg _) (by positivity))
        _ = B := by dsimp [B]; ring
    have hrewrite : routeETerminalPhaseEnergy (t L) (Real.exp (L - v)) =
        2 * (1 - Real.cos (e L v)) := by
      rw [routeETerminalPhaseEnergy_exp]
      rw [show t L * (L - v) = u₀ + e L v by dsimp [e]; ring]
      exact routeETerminalPhaseEnergy_eq_two_mul_one_sub_cos u₀ (e L v) hodd hsin
    rw [hrewrite, Real.norm_eq_abs]
    have hphaseNonneg : 0 ≤ 2 * (1 - Real.cos (e L v)) := by
      nlinarith [Real.cos_le_one (e L v)]
    have hnonneg : 0 ≤ L ^ 2 *
        (routeETerminalWeight a v * (2 * (1 - Real.cos (e L v)))) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg (routeETerminalWeight_pos a v).le hphaseNonneg)
    rw [abs_of_nonneg hnonneg]
    have hphaseLe : 2 * (1 - Real.cos (e L v)) ≤ (e L v) ^ 2 := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := e L v)]
    have hsq : (scaled L v) ^ 2 ≤ B ^ 2 := by
      apply (sq_le_sq).2
      rwa [abs_of_pos hBpos]
    calc
      L ^ 2 * (routeETerminalWeight a v * (2 * (1 - Real.cos (e L v)))) ≤
          L ^ 2 * (routeETerminalWeight a v * (e L v) ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hphaseLe (routeETerminalWeight_pos a v).le)
          (sq_nonneg _)
      _ = routeETerminalWeight a v * (scaled L v) ^ 2 := by
        dsimp [scaled]
        ring
      _ ≤ routeETerminalWeight a v * B ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (routeETerminalWeight_pos a v).le
  have hboundInt : IntervalIntegrable (fun v : ℝ =>
      routeETerminalWeight a v * B ^ 2) volume 0 1 :=
    ((continuous_routeETerminalWeight a).mul continuous_const).intervalIntegrable 0 1
  have hmeas (L : ℝ) : AEStronglyMeasurable (fun v : ℝ =>
      L ^ 2 * (routeETerminalWeight a v *
        routeETerminalPhaseEnergy (t L) (Real.exp (L - v))))
      (volume.restrict (uIoc (0 : ℝ) 1)) :=
    ((continuous_const.mul
      (continuous_routeETerminalContinuousIntegrand a L (t L))).aestronglyMeasurable).mono_measure
        Measure.restrict_le_self
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun v : ℝ => routeETerminalWeight a v * B ^ 2)
    (l := (atTop : Filter ℝ))
    (F := fun L v => L ^ 2 * (routeETerminalWeight a v *
      routeETerminalPhaseEnergy (t L) (Real.exp (L - v))))
    (f := fun v => routeETerminalWeight a v * (b - u₀ * v) ^ 2)
    (Eventually.of_forall hmeas) hbound hboundInt
    (Eventually.of_forall fun v _ => hpoint v)
  have hleft : ∀ L : ℝ,
      (∫ v in (0 : ℝ)..1, L ^ 2 * (routeETerminalWeight a v *
        routeETerminalPhaseEnergy (t L) (Real.exp (L - v)))) =
      L ^ 2 * routeETerminalContinuousEnergy a L (t L) := by
    intro L
    rw [routeETerminalContinuousEnergy, intervalIntegral.integral_const_mul]
  simpa only [hleft, routeETerminalQuadratic] using hDCT

/-- Sharp lower law for every convergent second-order odd-resonant history. -/
theorem routeETerminal_secondOrderHistory_limit_ge_variance
    (a u₀ b : ℝ) (t : ℝ → ℝ)
    (hodd : Real.cos u₀ = -1) (hsin : Real.sin u₀ = 0)
    (hphase : Tendsto (fun L => t L * L) atTop (𝓝 u₀))
    (hcorrection : Tendsto (fun L => L * (t L * L - u₀)) atTop (𝓝 b)) :
    Tendsto (fun L => L ^ 2 * routeETerminalContinuousEnergy a L (t L))
        atTop (𝓝 (routeETerminalQuadratic a u₀ b)) ∧
      u₀ ^ 2 * routeETerminalVariance a ≤ routeETerminalQuadratic a u₀ b := by
  exact ⟨tendsto_routeETerminalContinuousEnergy_of_secondOrderHistory
    a u₀ b t hodd hsin hphase hcorrection,
    routeETerminalVariance_minimax_lower a u₀ b⟩

/-- Exact sharp trial history `(30)`--`(32)`: centered first odd resonance reaches precisely
`pi²` times unnormalized weighted terminal-position variance. -/
theorem tendsto_routeETerminalContinuousEnergy_centeredFirstOdd
    (a : ℝ) :
    Tendsto (fun L : ℝ => L ^ 2 * routeETerminalContinuousEnergy a L
      (Real.pi / L + Real.pi * routeETerminalMean a / L ^ 2))
      atTop (𝓝 (Real.pi ^ 2 * routeETerminalVariance a)) := by
  let t : ℝ → ℝ := fun L =>
    Real.pi / L + Real.pi * routeETerminalMean a / L ^ 2
  let e : ℝ → ℝ → ℝ := fun L v => t L * (L - v) - Real.pi
  have hLinv : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hLinv2 : Tendsto (fun L : ℝ => (L ^ 2)⁻¹) atTop (𝓝 0) := by
    simpa [inv_pow] using hLinv.pow 2
  have ht0 : Tendsto t atTop (𝓝 0) := by
    dsimp [t]
    simpa [div_eq_mul_inv] using
      (hLinv.const_mul Real.pi).add
        (hLinv2.const_mul (Real.pi * routeETerminalMean a))
  have hscaled (v : ℝ) :
      Tendsto (fun L => L * e L v) atTop
        (𝓝 (Real.pi * (routeETerminalMean a - v))) := by
    have hEq : ∀ᶠ L : ℝ in atTop,
        L * e L v = Real.pi * (routeETerminalMean a - v) -
          Real.pi * routeETerminalMean a * v / L := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with L hL
      dsimp [e, t]
      field_simp
      ring
    have htail : Tendsto (fun L : ℝ =>
        Real.pi * routeETerminalMean a * v / L) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        hLinv.const_mul (Real.pi * routeETerminalMean a * v)
    have hEq' : (fun L => Real.pi * (routeETerminalMean a - v) -
        Real.pi * routeETerminalMean a * v / L) =ᶠ[atTop]
        (fun L => L * e L v) := by
      filter_upwards [hEq] with L hL
      exact hL.symm
    have hconst : Tendsto (fun _ : ℝ =>
        Real.pi * (routeETerminalMean a - v)) atTop
        (𝓝 (Real.pi * (routeETerminalMean a - v))) := tendsto_const_nhds
    simpa only [sub_zero] using (hconst.sub htail).congr' hEq'
  have hpoint (v : ℝ) : Tendsto (fun L =>
      L ^ 2 * (routeETerminalWeight a v *
        routeETerminalPhaseEnergy (t L) (Real.exp (L - v)))) atTop
      (𝓝 (routeETerminalWeight a v *
        (Real.pi * (routeETerminalMean a - v)) ^ 2)) := by
    have he0 : Tendsto (fun L => e L v) atTop (𝓝 0) := by
      have hEq : ∀ᶠ L : ℝ in atTop,
          e L v = (L * e L v) * L⁻¹ := by
        filter_upwards [eventually_ne_atTop (0 : ℝ)] with L hL
        field_simp
      have hprod := (hscaled v).mul hLinv
      have hEq' : (fun L => (L * e L v) * L⁻¹) =ᶠ[atTop]
          (fun L => e L v) := by
        filter_upwards [hEq] with L hL
        exact hL.symm
      convert hprod.congr' hEq' using 1 <;> ring
    have hphaseScaled := tendsto_terminalPhaseEnergy_scaled
      routeETerminal_pi_is_odd_phase.1 routeETerminal_pi_is_odd_phase.2
      he0 (hscaled v)
    have hweightLimit : Tendsto (fun _ : ℝ => routeETerminalWeight a v) atTop
        (𝓝 (routeETerminalWeight a v)) := tendsto_const_nhds
    have hmul := hweightLimit.mul hphaseScaled
    have hEq : (fun L => routeETerminalWeight a v *
        (L ^ 2 * (2 + 2 * Real.cos (Real.pi + e L v)))) =
        (fun L => L ^ 2 * (routeETerminalWeight a v *
          routeETerminalPhaseEnergy (t L) (Real.exp (L - v)))) := by
      funext L
      rw [routeETerminalPhaseEnergy_exp]
      rw [show t L * (L - v) = Real.pi + e L v by dsimp [e]; ring]
      ring
    convert hmul.congr' (Filter.Eventually.of_forall fun L => congrFun hEq L) using 1 <;> ring
  have hbound : ∀ᶠ L : ℝ in atTop, ∀ v ∈ uIoc (0 : ℝ) 1,
      ‖L ^ 2 * (routeETerminalWeight a v *
        routeETerminalPhaseEnergy (t L) (Real.exp (L - v)))‖ ≤
        routeETerminalWeight a v *
          (2 * Real.pi * (1 + |routeETerminalMean a|)) ^ 2 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
    intro v hv
    rw [uIoc_of_le zero_le_one] at hv
    have hv01 : 0 ≤ v ∧ v ≤ 1 := ⟨hv.1.le, hv.2⟩
    have hphaseChord := routeETerminalPhaseEnergy_nonneg (t L) (Real.exp (L - v))
    rw [routeETerminalPhaseEnergy_exp]
    have hrewrite : 2 + 2 * Real.cos (t L * (L - v)) =
        2 * (1 - Real.cos (e L v)) := by
      rw [show t L * (L - v) = Real.pi + e L v by dsimp [e]; ring]
      exact routeETerminalPhaseEnergy_eq_two_mul_one_sub_cos _ _
        routeETerminal_pi_is_odd_phase.1 routeETerminal_pi_is_odd_phase.2
    rw [hrewrite]
    have hcosLower := Real.one_sub_sq_div_two_le_cos (x := e L v)
    have hphaseLe : 2 * (1 - Real.cos (e L v)) ≤ (e L v) ^ 2 := by linarith
    have hscaledPhase : |L * e L v| ≤
        2 * Real.pi * (1 + |routeETerminalMean a|) := by
      have hLpos : 0 < L := by linarith
      have hvabs : |v| ≤ 1 := by rw [abs_of_nonneg hv01.1]; exact hv01.2
      have hmean := abs_nonneg (routeETerminalMean a)
      have hEq : L * e L v = Real.pi * (routeETerminalMean a - v) -
          Real.pi * routeETerminalMean a * v / L := by
        dsimp [e, t]
        field_simp
        ring
      rw [hEq]
      have hfirst : |Real.pi * (routeETerminalMean a - v)| ≤
          Real.pi * (|routeETerminalMean a| + 1) := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        exact mul_le_mul_of_nonneg_left
          ((abs_sub _ _).trans (add_le_add le_rfl hvabs)) Real.pi_pos.le
      have hsecond : |Real.pi * routeETerminalMean a * v / L| ≤
          Real.pi * |routeETerminalMean a| := by
        rw [abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
          abs_of_pos hLpos]
        have hnum : Real.pi * |routeETerminalMean a| * |v| ≤
            Real.pi * |routeETerminalMean a| := by
          exact mul_le_of_le_one_right
            (mul_nonneg Real.pi_pos.le hmean) hvabs
        exact (div_le_iff₀ hLpos).2
          (hnum.trans (le_mul_of_one_le_right
            (mul_nonneg Real.pi_pos.le hmean) (by linarith)))
      calc
        |Real.pi * (routeETerminalMean a - v) -
            Real.pi * routeETerminalMean a * v / L| ≤
            |Real.pi * (routeETerminalMean a - v)| +
              |Real.pi * routeETerminalMean a * v / L| := abs_sub _ _
        _ ≤ Real.pi * (|routeETerminalMean a| + 1) +
            Real.pi * |routeETerminalMean a| := add_le_add hfirst hsecond
        _ ≤ 2 * Real.pi * (1 + |routeETerminalMean a|) := by
          nlinarith [Real.pi_pos]
    rw [Real.norm_eq_abs]
    have hnonneg : 0 ≤ L ^ 2 * (routeETerminalWeight a v *
        (2 * (1 - Real.cos (e L v)))) := by
      exact mul_nonneg (sq_nonneg _) (mul_nonneg
        (routeETerminalWeight_pos a v).le (by nlinarith [Real.cos_le_one (e L v)]))
    rw [abs_of_nonneg hnonneg]
    have hweight := (routeETerminalWeight_pos a v).le
    calc
      L ^ 2 * (routeETerminalWeight a v * (2 * (1 - Real.cos (e L v))))
          ≤ L ^ 2 * (routeETerminalWeight a v * (e L v) ^ 2) := by gcongr
      _ = routeETerminalWeight a v * (L * e L v) ^ 2 := by ring
      _ ≤ routeETerminalWeight a v *
          (2 * Real.pi * (1 + |routeETerminalMean a|)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hweight
        apply (sq_le_sq).2
        rw [abs_of_nonneg (mul_nonneg
          (mul_nonneg (by norm_num) Real.pi_pos.le) (by positivity))]
        exact hscaledPhase
  have hboundInt : IntervalIntegrable (fun v : ℝ =>
      routeETerminalWeight a v *
        (2 * Real.pi * (1 + |routeETerminalMean a|)) ^ 2) volume 0 1 := by
    exact ((continuous_routeETerminalWeight a).mul continuous_const).intervalIntegrable 0 1
  have hmeas (L : ℝ) : AEStronglyMeasurable (fun v : ℝ =>
      L ^ 2 * (routeETerminalWeight a v *
        routeETerminalPhaseEnergy (t L) (Real.exp (L - v))))
      (volume.restrict (uIoc (0 : ℝ) 1)) :=
    ((continuous_const.mul
      (continuous_routeETerminalContinuousIntegrand a L (t L))).aestronglyMeasurable).mono_measure
        Measure.restrict_le_self
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun v : ℝ => routeETerminalWeight a v *
      (2 * Real.pi * (1 + |routeETerminalMean a|)) ^ 2)
    (l := (atTop : Filter ℝ))
    (F := fun L v => L ^ 2 * (routeETerminalWeight a v *
      routeETerminalPhaseEnergy (t L) (Real.exp (L - v))))
    (f := fun v => routeETerminalWeight a v *
      (Real.pi * (routeETerminalMean a - v)) ^ 2)
    (Eventually.of_forall hmeas)
    (hbound.mono fun _ hL => Filter.Eventually.of_forall fun v => hL v)
    hboundInt (Eventually.of_forall fun v _ => hpoint v)
  have hleft : ∀ L : ℝ,
      (∫ v in (0 : ℝ)..1, L ^ 2 * (routeETerminalWeight a v *
        routeETerminalPhaseEnergy (t L) (Real.exp (L - v)))) =
      L ^ 2 * routeETerminalContinuousEnergy a L (t L) := by
    intro L
    rw [routeETerminalContinuousEnergy, intervalIntegral.integral_const_mul]
  have hright : (∫ v in (0 : ℝ)..1,
      routeETerminalWeight a v *
        (Real.pi * (routeETerminalMean a - v)) ^ 2) =
      Real.pi ^ 2 * routeETerminalVariance a := by
    rw [routeETerminalVariance, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    ring
  simpa only [hleft, hright, t] using hDCT

end

end RHTower
