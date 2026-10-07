import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseRegularization
import GaloisForLFunctions.RHTower.WeilConeSpectralCounting
import GaloisForLFunctions.RHTower.VanDerCorputIBP
import GaloisForLFunctions.HTGeometry.ShortBumpMellinSmoothedSums

/-!
# Cancellation of the actual source phase away from the boundary

Full positivity forces the normalized phase mean at width `η` to be at most
`18 / (η² log Y)` on a sufficiently high dyadic block. Fixed positive widths
therefore cannot be used as settled boundary phases. All constants and the
height threshold come from the original source; no atomicity is assumed.
-/

open Complex Set Filter MeasureTheory Topology Metric
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower.WeilWorkSettledPhase
open WeilSpectral WeilHerglotz

private theorem halfPlane_open : IsOpen {s : ℂ | 1 / 2 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- A local Caratheodory bound for the original continuation. -/
theorem norm_deriv_weilContinuation_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {η : ℝ} (hη : 0 < η) (t : ℝ) :
    ‖deriv (weilContinuation hW) (tracePoint η t)‖ ≤
      4 * (weilContinuation hW (tracePoint η t)).re / η := by
  let s := tracePoint η t
  have hs : 1 / 2 < s.re := by simp [s, tracePoint]; linarith
  have hpos := re_weilContinuation_nonneg hW hs
  have hsub : ball s η ⊆ {w : ℂ | 1 / 2 < w.re} := by
    intro w hw
    have hn := Complex.abs_re_le_norm (w - s)
    have hd := mem_ball_iff_norm.mp hw
    simp only [Complex.sub_re] at hn
    have hsr : s.re = 1 / 2 + η := by simp [s, tracePoint]
    change 1 / 2 < w.re
    linarith [neg_abs_le (w.re - s.re)]
  apply norm_deriv_le_of_lip' (by positivity)
  filter_upwards [Metric.ball_mem_nhds s (show 0 < η / 2 by positivity)] with w hw
  have hd : ‖w - s‖ < η / 2 := mem_ball_iff_norm.mp hw
  have hwb : w ∈ ball s η := mem_ball_iff_norm.mpr (by linarith)
  have h := norm_sub_le_of_re_nonneg_on_ball
    ((differentiableOn_weilContinuation hW).mono hsub)
    (fun z hz => re_weilContinuation_nonneg hW (hsub hz)) hwb
  have hc : 2 / (η - ‖w - s‖) ≤ 4 / η := by
    apply (div_le_div_iff₀ (by linarith) hη).mpr
    linarith
  calc
    ‖weilContinuation hW w - weilContinuation hW s‖ ≤
        (2 / (η - ‖w - s‖)) * ‖w - s‖ * (weilContinuation hW s).re := by
          convert h using 1; ring
    _ ≤ (4 / η) * ‖w - s‖ * (weilContinuation hW s).re := by gcongr
    _ = (4 * (weilContinuation hW s).re / η) * ‖w - s‖ := by ring

/-- The full positive Poisson measure transports the right-line lower bound. -/
theorem mul_re_weilContinuation_two_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (t : ℝ) :
    (2 * η / 3) * (weilContinuation hW ((2 : ℂ) + t * I)).re ≤
      (weilContinuation hW (tracePoint η t)).re := by
  have hs : 1 / 2 < 1 / 2 + η := by linarith
  apply (ENNReal.ofReal_le_ofReal_iff (re_weilContinuation_nonneg hW
    (s := tracePoint η t) (by simp [tracePoint]; linarith))).mp
  rw [ENNReal.ofReal_mul (by positivity)]
  have htwo := ofReal_re_weilContinuation_eq hW 2 t (by norm_num)
  norm_num only [Complex.ofReal_ofNat] at htwo
  rw [htwo]
  change _ ≤ ENNReal.ofReal (weilContinuation hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).re
  rw [ofReal_re_weilContinuation_eq hW (1 / 2 + η) t hs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro r
  dsimp only
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hden : 0 < η ^ 2 + (r - t) ^ 2 := by positivity
  convert (div_le_div_of_nonneg_left hη.le hden
    (show η ^ 2 + (r - t) ^ 2 ≤ (3 / 2 : ℝ) ^ 2 + (r - t) ^ 2 by nlinarith)) using 1 <;>
    first | rfl | ring

private theorem exists_right_line_lower {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ Y₀ : ℝ, 4 ≤ Y₀ ∧ ∀ t : ℝ, Y₀ ≤ t →
      Real.log t / 4 ≤ (weilContinuation hW ((2 : ℂ) + t * I)).re := by
  let M : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)
  let C : ℝ := (Real.log 2 + Real.log Real.pi) / 2 + 1 + M
  refine ⟨max 4 (Real.exp (4 * C)), le_max_left _ _, ?_⟩
  intro t ht
  have ht4 : 4 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have hlog : 4 * C ≤ Real.log t := by
    rw [← Real.log_exp (4 * C)]
    exact Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans ht)
  have hd := abs_re_digamma_one_sub_log_le (t := t / 2) (by linarith)
  have he : 8 / (t / 2) ^ (2 : ℕ) ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < (t / 2) ^ (2 : ℕ))).mpr
    nlinarith
  have hD : (LSeries (lamC lam) ((2 : ℂ) + t * I)).re ≤ M := by
    have h := norm_producerA_two_le hW t
    rw [producerA_eq_LSeries hW (by simp)] at h
    exact (Complex.re_le_norm _).trans h
  rw [re_weilContinuation_two_add hW]
  rw [Real.log_div ht0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hd
  have h1 : 0 ≤ 2 / (4 + t ^ 2) := by positivity
  have h2 : 0 ≤ 1 / (1 + t ^ 2) := by positivity
  dsimp [C] at hlog
  linarith [(abs_le.mp hd).1]

private theorem hasDerivAt_tracePoint_height (η t : ℝ) :
    HasDerivAt (tracePoint η) I t := by
  change HasDerivAt (fun y : ℝ => (((1 / 2 + η : ℝ) : ℂ)) + y * I) I t
  simpa only [Complex.ofReal_one, one_mul, id_eq] using!
    ((hasDerivAt_id t).ofReal_comp.mul_const I).const_add (((1 / 2 + η : ℝ) : ℂ))

private theorem source_rate_deriv {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {η : ℝ} (hη : 0 < η) (t : ℝ) :
    HasDerivAt (fun y => 2 * (weilContinuation hW (tracePoint η y)).re)
      (2 * (deriv (weilContinuation hW) (tracePoint η t) * I).re) t := by
  have hd := (differentiableOn_weilContinuation hW).differentiableAt
    (halfPlane_open.mem_nhds (show 1 / 2 < (tracePoint η t).re by
      simp [tracePoint]; linarith))
  have h := hd.hasDerivAt.comp t (hasDerivAt_tracePoint_height η t)
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h).const_mul 2

private theorem source_phase_deriv {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {η : ℝ} (hη : 0 < η) (t : ℝ) :
    HasDerivAt (fun y => 2 * (sourcePrimitive hW (tracePoint η y)).im)
      (2 * (weilContinuation hW (tracePoint η t)).re) t := by
  have h := (hasDerivAt_sourcePrimitive hW (s := tracePoint η t)
    (by simp [tracePoint]; linarith)).comp t (hasDerivAt_tracePoint_height η t)
  have hi := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h).const_mul 2
  simpa using hi

/-- Uniform source phase cancellation before the singular boundary layer. -/
theorem exists_integral_regularizedPhase_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ Y₀ : ℝ, 4 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y → ∀ η : ℝ, 0 < η → η ≤ 1 →
      ‖∫ t in Y..(2 * Y), regularizedPhase hW η t‖ ≤
        18 * Y / (η ^ 2 * Real.log Y) := by
  obtain ⟨Y₀, hY₀, hlower⟩ := exists_right_line_lower hW
  refine ⟨Y₀, hY₀, ?_⟩
  intro Y hY η hη hη1
  have hY4 : 4 ≤ Y := hY₀.trans hY
  have hYpos : 0 < Y := by linarith
  have hlog : 0 < Real.log Y := Real.log_pos (by linarith)
  let φ : ℝ → ℝ := fun t => 2 * (sourcePrimitive hW (tracePoint η t)).im
  let v : ℝ → ℝ := fun t => 2 * (weilContinuation hW (tracePoint η t)).re
  let v' : ℝ → ℝ := fun t => 2 * (deriv (weilContinuation hW) (tracePoint η t) * I).re
  let L : ℝ := η * Real.log Y / 3
  have hL : 0 < L := by dsimp [L]; positivity
  have hv (t : ℝ) : HasDerivAt v (v' t) t := source_rate_deriv hW hη t
  have hφ (t : ℝ) : HasDerivAt φ (v t) t := source_phase_deriv hW hη t
  have hvc : Continuous v := continuous_iff_continuousAt.mpr fun t => (hv t).continuousAt
  have hpc : Continuous v' := by
    have hc := ((differentiableOn_weilContinuation hW).deriv halfPlane_open).continuousOn
    have hcomp : Continuous (fun t => deriv (weilContinuation hW) (tracePoint η t)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (hc.continuousAt (halfPlane_open.mem_nhds
        (show 1 / 2 < (tracePoint η t).re by simp [tracePoint]; linarith))).comp
          (hasDerivAt_tracePoint_height η t).continuousAt
    exact (Complex.continuous_re.comp (hcomp.mul continuous_const)).const_mul 2
  have hvL : ∀ t ∈ uIcc Y (2 * Y), L ≤ v t := by
    intro t ht
    rw [uIcc_of_le (by linarith : Y ≤ 2 * Y)] at ht
    have hright := hlower t (hY.trans ht.1)
    have hshift := mul_re_weilContinuation_two_le hW hη hη1 t
    have hlogt := Real.log_le_log hYpos ht.1
    have hmul := mul_le_mul_of_nonneg_left hright (show 0 ≤ 2 * η / 3 by positivity)
    have hm := mul_le_mul_of_nonneg_left hlogt hη.le
    dsimp [L, v]
    nlinarith
  have hvpos : ∀ t ∈ uIcc Y (2 * Y), 0 < v t := fun t ht => hL.trans_le (hvL t ht)
  have hvabs (t : ℝ) : |v' t| ≤ 4 * v t / η := by
    have h := norm_deriv_weilContinuation_le hW hη t
    have hre := Complex.abs_re_le_norm (deriv (weilContinuation hW) (tracePoint η t) * I)
    rw [norm_mul, Complex.norm_I, mul_one] at hre
    dsimp [v', v]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      2 * |(deriv (weilContinuation hW) (tracePoint η t) * I).re| ≤
          2 * (4 * (weilContinuation hW (tracePoint η t)).re / η) := by linarith
      _ = _ := by ring
  let B : ℝ → ℂ := fun t => -I * (v t : ℂ)⁻¹
  let B' : ℝ → ℂ := fun t => I * (v' t : ℂ) / (v t : ℂ) ^ 2
  have hn : ∀ t ∈ uIcc Y (2 * Y), (v t : ℂ) ≠ 0 := fun t ht =>
    Complex.ofReal_ne_zero.mpr (hvpos t ht).ne'
  have hB : ∀ t ∈ uIcc Y (2 * Y), HasDerivAt B (B' t) t := by
    intro t ht
    exact (((hv t).ofReal_comp.inv (hn t ht)).const_mul (-I)).congr_deriv (by
      dsimp [B']; ring)
  have hBc : ContinuousOn B' (uIcc Y (2 * Y)) := by
    exact (continuousOn_const.mul (Complex.continuous_ofReal.comp hpc).continuousOn).div
      ((Complex.continuous_ofReal.comp hvc).pow 2).continuousOn
      (fun t ht => pow_ne_zero 2 (hn t ht))
  have hrel : ∀ t ∈ uIcc Y (2 * Y), B t * (I * (v t : ℂ)) = 1 := by
    intro t ht
    dsimp [B]
    field_simp [hn t ht]
    simp [Complex.I_sq]
  have hBb : ∀ t ∈ uIcc Y (2 * Y), ‖B t‖ ≤ 1 / L := by
    intro t ht
    have he : ‖B t‖ = 1 / v t := by
      simp [B, Complex.norm_real, abs_of_pos (hvpos t ht), one_div]
    rw [he]
    exact one_div_le_one_div_of_le hL (hvL t ht)
  have hB'b : ∀ t ∈ uIcc Y (2 * Y), ‖B' t‖ ≤ 4 / (η * L) := by
    intro t ht
    have htpos := hvpos t ht
    have he : ‖B' t‖ = |v' t| / v t ^ 2 := by
      simp [B', norm_pow, Complex.norm_real, abs_of_pos htpos]
    rw [he]
    calc
      |v' t| / v t ^ 2 ≤ (4 * v t / η) / v t ^ 2 :=
        div_le_div_of_nonneg_right (hvabs t) (sq_nonneg _)
      _ = 4 / (η * v t) := by field_simp
      _ ≤ 4 / (η * L) := div_le_div_of_nonneg_left (by norm_num)
        (mul_pos hη hL) (mul_le_mul_of_nonneg_left (hvL t ht) hη.le)
  have hi : (∫ t in Y..(2 * Y), ‖B' t‖) ≤ Y * (4 / (η * L)) := by
    have hm : (∫ t in Y..(2 * Y), ‖B' t‖) ≤ ∫ _ in Y..(2 * Y), 4 / (η * L) :=
      intervalIntegral.integral_mono_on (show Y ≤ 2 * Y by linarith)
      hBc.norm.intervalIntegrable (continuous_const.intervalIntegrable Y (2 * Y))
      (fun t ht => hB'b t ((uIcc_of_le (by linarith : Y ≤ 2 * Y)).symm ▸ ht))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, show 2 * Y - Y = Y by ring] using hm
  have hmain := norm_integral_cexp_le_of_antiderivative (show Y ≤ 2 * Y by linarith)
    (fun t _ => hφ t) hB hBc (A := fun _ => 1) continuousOn_const hrel
  have heq : (fun t => (1 : ℂ) * cexp (I * (φ t : ℂ))) = regularizedPhase hW η := by
    funext t
    simp only [one_mul, φ, regularizedPhase, mul_comm I]
  rw [heq] at hmain
  have hbb := hBb (2 * Y) right_mem_uIcc
  have hba := hBb Y left_mem_uIcc
  have hbound : ‖∫ t in Y..(2 * Y), regularizedPhase hW η t‖ ≤
      2 / L + Y * (4 / (η * L)) := by
    calc
      _ ≤ ‖B (2 * Y)‖ + ‖B Y‖ + ∫ t in Y..(2 * Y), ‖B' t‖ := hmain
      _ ≤ 1 / L + 1 / L + Y * (4 / (η * L)) := add_le_add (add_le_add hbb hba) hi
      _ = _ := by ring
  apply hbound.trans
  dsimp [L]
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hη) hlog)).mpr
  field_simp
  nlinarith

end RHTower.WeilWorkSettledPhase
