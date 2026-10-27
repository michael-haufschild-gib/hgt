import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.CriticalDiscsAndTheTerminalLens
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiTerminalRegularField
import GaloisForLFunctions.HTGeometry.PoissonBoundaryPositivity

/-!
# Harnack on the Carathéodory region

Right of the critical line and strictly outside every critical disc, `ξ` has no zero and every
reflected pair is positive, so `u = Re ξ′/ξ` is a nonnegative harmonic function there. Harnack's
inequality then compares its values across any disc inside the region.

* **Carathéodory Harnack** (`harnack_re_logDeriv_xi`). If the disc `B(c, R)` lies right of the
  critical line and strictly outside every critical disc, then for `s ∈ B(c, R)`
  `(R − |s − c|)/(R + |s − c|) · u(c) ≤ u(s) ≤ (R + |s − c|)/(R − |s − c|) · u(c)`.
* **Discs on the outward ray** (`terminalRayBall_subset`). For a terminal `p = ½ + a + iγ_p` and
  `0 < h < ½ − a`, the disc of radius `ρ h`, `ρ = a/(2(a + T))`, `T = √(¼ − a²)`, about `p + h` lies
  strictly outside every critical disc.
* **The outward floor spreads** (`exists_terminal_floor_spreads`). ACP's floor
  `u(p + h) ≥ m/h + m/(2a + h) + c a log(|γ_p| + 4)` holds, up to the factor `1/3`, on the whole disc
  of radius `ρh/2` about `p + h`.

This is the harmonic-measure tool on the terminal geometry: positivity of the pair field transports
two-sided bounds for `Re ξ′/ξ` through the zero-free lens.
-/

noncomputable section

open RHTower Metric InnerProductSpace

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open ArithmeticCorrespondencePositivity

/-- `s` lies strictly outside every critical disc (its closure included). -/
def StrictlyOutsideDiscs (s : ℂ) : Prop :=
  ∀ q : XiZeroCopy, ((q.1 : ℂ).re - 1 / 2) ^ 2 < (s.re - 1 / 2) ^ 2 + (s.im - (q.1 : ℂ).im) ^ 2

theorem xi_ne_zero_of_strictlyOutsideDiscs {s : ℂ} (hs : StrictlyOutsideDiscs s) : xi s ≠ 0 := by
  intro hz
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hz
  have h := hs q
  rw [hq, sub_self] at h
  norm_num at h

theorem not_inCriticalDisc_of_strictlyOutsideDiscs {s : ℂ} (hs : StrictlyOutsideDiscs s)
    (q : XiZeroCopy) : ¬ InCriticalDisc q s := by
  unfold InCriticalDisc
  exact not_lt.mpr (hs q).le

/-- `ξ′/ξ` is analytic off the zeros of `ξ`. -/
theorem analyticAt_logDeriv_xi {s : ℂ} (hxi : xi s ≠ 0) : AnalyticAt ℂ (logDeriv xi) s := by
  have hξ : AnalyticAt ℂ xi s := xi_differentiable.analyticAt s
  have h := hξ.deriv.div hξ hxi
  have heq : logDeriv xi = fun z => deriv xi z / xi z := funext fun z => logDeriv_apply xi z
  rw [heq]
  exact h

/-- **Carathéodory Harnack.** On a disc right of the critical line and strictly outside every
critical disc, `Re ξ′/ξ` satisfies Harnack's inequality. -/
theorem harnack_re_logDeriv_xi {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : ∀ s ∈ ball c R, 1 / 2 < s.re ∧ StrictlyOutsideDiscs s) {s : ℂ} (hs : s ∈ ball c R) :
    (R - ‖s - c‖) / (R + ‖s - c‖) * (logDeriv xi c).re ≤ (logDeriv xi s).re ∧
      (logDeriv xi s).re ≤ (R + ‖s - c‖) / (R - ‖s - c‖) * (logDeriv xi c).re := by
  set φ : ℂ → ℂ := fun z => c + (R : ℂ) * z
  set u : ℂ → ℝ := fun z => (logDeriv xi (φ z)).re
  have hφ : ∀ z ∈ ball (0 : ℂ) 1, φ z ∈ ball c R := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    rw [mem_ball, dist_eq_norm, show φ z - c = (R : ℂ) * z by simp [φ], norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    nlinarith
  have hu : HarmonicOnNhd u (ball 0 1) := by
    intro z hz
    have hxi := xi_ne_zero_of_strictlyOutsideDiscs (hball _ (hφ z hz)).2
    have han : AnalyticAt ℂ (fun w => logDeriv xi (φ w)) z :=
      (analyticAt_logDeriv_xi hxi).comp (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
    exact han.harmonicAt_re
  have hnn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z := by
    intro z hz
    obtain ⟨hre, hout⟩ := hball _ (hφ z hz)
    exact re_logDeriv_xi_nonneg_of_outside_discs hre (xi_ne_zero_of_strictlyOutsideDiscs hout)
      (not_inCriticalDisc_of_strictlyOutsideDiscs hout)
  set w : ℂ := (s - c) / R
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hw : ‖w‖ = ‖s - c‖ / R := by
    simp only [w, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hsc : ‖s - c‖ < R := by rw [mem_ball, dist_eq_norm] at hs; exact hs
  have hwball : w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hw, div_lt_one hR]; exact hsc
  obtain ⟨h1, h2⟩ := HTGeometry.harnack hu hnn hwball
  have hu0 : u 0 = (logDeriv xi c).re := by simp [u, φ]
  have huw : u w = (logDeriv xi s).re := by
    simp only [u, φ, w]
    congr 2
    field_simp
    ring
  rw [hu0, huw, hw] at h1 h2
  have e1 : (1 - ‖s - c‖ / R) / (1 + ‖s - c‖ / R) = (R - ‖s - c‖) / (R + ‖s - c‖) := by
    field_simp
  have e2 : (1 + ‖s - c‖ / R) / (1 - ‖s - c‖ / R) = (R + ‖s - c‖) / (R - ‖s - c‖) := by
    have : R - ‖s - c‖ ≠ 0 := by linarith
    field_simp
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨h1, h2⟩

/-! ### Discs on the outward ray of a terminal -/

/-- The relative radius `ρ = a/(2(a + T))` of the ray discs of a terminal of depth `a`. -/
def rayRadius (a : ℝ) : ℝ := a / (2 * (a + lensWidth a))

/-- **Discs on the outward ray.** For a right terminal `p` of depth `a` and `0 < h < ½ − a`, the
disc of radius `ρ h` about `p + h` lies right of the critical line and strictly outside every
critical disc. -/
theorem terminalRayBall_subset {p : XiZeroCopy} (hp : IsTerminal p) (hright : 1 / 2 < (p.1 : ℂ).re)
    {h : ℝ} (hh : 0 < h) (hh' : h < 1 / 2 - xiZeroDepth p) :
    ∀ s ∈ ball ((p.1 : ℂ) + h) (rayRadius (xiZeroDepth p) * h),
      1 / 2 < s.re ∧ StrictlyOutsideDiscs s := by
  intro s hs
  set a := xiZeroDepth p
  set T := lensWidth a
  have ha : a = (p.1 : ℂ).re - 1 / 2 := by
    simp only [a, xiZeroDepth]; rw [abs_of_pos (by linarith)]
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha2 : a ≤ 1 / 2 := (xiZeroDepth_bounds p).2
  have ha2' : a ^ 2 ≤ 1 / 4 := by nlinarith [mul_le_mul ha2 ha2 ha0.le (by norm_num : (0:ℝ) ≤ 1 / 2)]
  have hTsq : T ^ 2 = 1 / 4 - a ^ 2 := by
    rw [show T = Real.sqrt (1 / 4 - a ^ 2) from rfl, Real.sq_sqrt (by linarith)]
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hTa : 1 / 2 - a ≤ T := by nlinarith
  have hρdef : rayRadius a = a / (2 * (a + T)) := rfl
  set ρ := rayRadius a
  have haT : 0 < a + T := by linarith
  have hρ : ρ * (a + T) = a / 2 := by
    rw [hρdef]
    field_simp
  have hρ0 : 0 < ρ := by rw [hρdef]; positivity
  have hρ1 : ρ ≤ 1 / 2 := by
    rw [hρdef, div_le_iff₀ (by positivity)]
    linarith
  -- Coordinates of `s` relative to `p + h`.
  set x := s.re - 1 / 2
  set d := s.im - xiZeroHeight p
  have hdist : ‖s - ((p.1 : ℂ) + h)‖ < ρ * h := by
    rw [mem_ball, dist_eq_norm] at hs; exact hs
  have hxre : |x - (a + h)| < ρ * h := by
    have := (Complex.abs_re_le_norm (s - ((p.1 : ℂ) + h))).trans_lt hdist
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at this
    rw [show x - (a + h) = s.re - ((p.1 : ℂ).re + h) by simp only [x]; rw [ha]; ring]
    exact this
  have hdim : |d| < ρ * h := by
    have := (Complex.abs_im_le_norm (s - ((p.1 : ℂ) + h))).trans_lt hdist
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, add_zero] at this
    exact this
  have hxlow : a + (1 - ρ) * h < x := by
    have := (abs_lt.mp hxre).1; linarith
  have hx0 : 0 < x := by nlinarith
  have hxdef : x = s.re - 1 / 2 := rfl
  refine ⟨by linarith, fun r => ?_⟩
  -- The strict lens inequality `x² − a² + d² > 2T|d|`.
  have hρh : ρ * h ≤ 1 / 2 * h := mul_le_mul_of_nonneg_right hρ1 hh.le
  have hkey : 2 * T * |d| < x ^ 2 - a ^ 2 + d ^ 2 := by
    have h1 : 0 < x - a - (1 - ρ) * h := by linarith
    have h2 : 0 < x + a := by linarith
    have h3 : 0 < (1 - ρ) * h := mul_pos (by linarith) hh
    have h4 : 0 < x - a := by linarith
    have hxa : 2 * a * ((1 - ρ) * h) < x ^ 2 - a ^ 2 := by
      nlinarith [mul_pos h1 h2, mul_pos h3 h4]
    have hTd : 2 * T * |d| ≤ 2 * T * (ρ * h) :=
      mul_le_mul_of_nonneg_left hdim.le (by positivity)
    have hTρ : T * ρ ≤ a * (1 - ρ) := by nlinarith [hρ]
    have hcmp : 2 * T * (ρ * h) ≤ 2 * a * ((1 - ρ) * h) := by
      have := mul_le_mul_of_nonneg_right hTρ (by positivity : (0 : ℝ) ≤ 2 * h)
      calc 2 * T * (ρ * h) = T * ρ * (2 * h) := by ring
        _ ≤ a * (1 - ρ) * (2 * h) := this
        _ = 2 * a * ((1 - ρ) * h) := by ring
    linarith [sq_nonneg d]
  set t := xiZeroHeight r - xiZeroHeight p
  set b := (r.1 : ℂ).re - 1 / 2
  have hcone : b ^ 2 ≤ a ^ 2 + t ^ 2 := by
    have hc := hp r
    have hb' : xiZeroDepth r ^ 2 = b ^ 2 := by simp only [xiZeroDepth, b, sq_abs]
    rw [hb'] at hc
    exact hc
  have hb : b ^ 2 ≤ 1 / 4 := by
    have h' := xiZeroDepth_bounds r
    have : |b| ≤ 1 / 2 := h'.2
    nlinarith [abs_nonneg b, sq_abs b]
  have hsd : s.im - (r.1 : ℂ).im = d - t := by simp only [d, t, xiZeroHeight]; ring
  change b ^ 2 < (s.re - 1 / 2) ^ 2 + (s.im - (r.1 : ℂ).im) ^ 2
  rw [hsd]
  change b ^ 2 < x ^ 2 + (d - t) ^ 2
  have hexp : (d - t) ^ 2 = d ^ 2 - 2 * (d * t) + t ^ 2 := by ring
  rcases le_or_gt |t| T with htT | htT
  · have hdt : d * t ≤ |d| * T := by
      calc d * t ≤ |d * t| := le_abs_self _
        _ = |d| * |t| := abs_mul d t
        _ ≤ |d| * T := mul_le_mul_of_nonneg_left htT (abs_nonneg d)
    have : 2 * (d * t) ≤ 2 * T * |d| := by linarith
    linarith
  · have hdT : |d| < T := by linarith
    have h3 : (T - |d|) ^ 2 ≤ (d - t) ^ 2 := by
      have h4 := abs_sub_abs_le_abs_sub t d
      have h5 : |t - d| = |d - t| := abs_sub_comm t d
      have h6 : T - |d| ≤ |d - t| := by linarith
      have h7 := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ T - |d|) h6 2
      rwa [sq_abs] at h7
    have e : (T - |d|) ^ 2 = T ^ 2 - 2 * T * |d| + d ^ 2 := by rw [sub_sq, sq_abs]
    linarith

/-- **The outward floor spreads.** On the disc of radius `ρh/2` about each point `p + h` of the
outward ray of a terminal, `Re ξ′/ξ` is at least a third of ACP's floor. -/
theorem exists_terminal_floor_spreads :
    ∃ c : ℝ, 0 < c ∧ ∀ p : XiZeroCopy, 1 / 2 < (p.1 : ℂ).re → IsTerminal p →
      ∀ h : ℝ, 0 < h → h < 1 / 2 - xiZeroDepth p →
        ∀ s : ℂ, ‖s - ((p.1 : ℂ) + h)‖ ≤ rayRadius (xiZeroDepth p) * h / 2 →
          (((xiZeroCopyFiber p.1).card : ℝ) / h +
            ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p + h) +
            c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4)) / 3 ≤ (logDeriv xi s).re := by
  obtain ⟨c, hc, hfloor⟩ := exists_xiTerminal_transverseField_and_ray_lower
  refine ⟨c, hc, fun p hright hp h hh hh' s hs => ?_⟩
  set R := rayRadius (xiZeroDepth p) * h
  have ha0 : 0 < xiZeroDepth p := by
    simp only [xiZeroDepth]; rw [abs_of_pos (by linarith)]; linarith
  have hR : 0 < R := mul_pos (div_pos ha0 (by
    have := Real.sqrt_nonneg (1 / 4 - xiZeroDepth p ^ 2)
    simp only [lensWidth]; positivity)) hh
  have hsball : s ∈ ball ((p.1 : ℂ) + h) R := by
    rw [mem_ball, dist_eq_norm]; linarith
  obtain ⟨hlow, -⟩ := harnack_re_logDeriv_xi hR (terminalRayBall_subset hp hright hh hh') hsball
  have hray := (hfloor p hright hp).2 h hh hh'
  set F := ((xiZeroCopyFiber p.1).card : ℝ) / h +
    ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p + h) +
    c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4)
  have hF : 0 ≤ F := by
    have hlog : 0 ≤ Real.log (|xiZeroHeight p| + 4) :=
      Real.log_nonneg (by linarith [abs_nonneg (xiZeroHeight p)])
    simp only [F]; positivity
  set r := ‖s - ((p.1 : ℂ) + h)‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hfac : 1 / 3 ≤ (R - r) / (R + r) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hu : 0 ≤ (logDeriv xi ((p.1 : ℂ) + h)).re := hF.trans hray
  calc F / 3 = 1 / 3 * F := by ring
    _ ≤ 1 / 3 * (logDeriv xi ((p.1 : ℂ) + h)).re := by linarith
    _ ≤ (R - r) / (R + r) * (logDeriv xi ((p.1 : ℂ) + h)).re :=
        mul_le_mul_of_nonneg_right hfac hu
    _ ≤ (logDeriv xi s).re := hlow

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
