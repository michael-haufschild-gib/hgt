import GaloisForLFunctions.HTGeometry.BarnesSingleZetaShiftEquation

/-!
# The difference equation of the one-dimensional Barnes gamma

The exponential bracket is holomorphic on `Re s > -1`: its head integrand is `O(t)` at the origin
because `1 - e^(-xt) <= xt`, and its tail decays exponentially.  Regularizing the pole at `s = 0`
against the simple zero of `1/Gamma` gives a function analytic there, which agrees with
`x^(-s)` where the Euler integral converges.  Both are analytic on the convex half-plane
`Re s > -1`, so the identity theorem extends the agreement, and the derivative at the origin is
`-log x`.

Feeding this into the shift equation of the continued one-dimensional zeta gives the classical
difference equation

```text
log Gamma_1(omega; x + omega) = log Gamma_1(omega; x) + log x.
```
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem isBigO_indicator_expSub_zero {x : ℝ} (hx : 0 < x) :
    Set.indicator (Ioc (0 : ℝ) 1)
        (fun t : ℝ => Complex.exp (-((x : ℂ) * (t : ℂ))) - 1)
      =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-(-1 : ℝ)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨x, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [neg_neg, Real.rpow_one, Real.norm_eq_abs, abs_of_pos ht0]
  by_cases hin : t ∈ Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hin]
    exact norm_exp_neg_sub_one_le hx ht0
  · rw [Set.indicator_of_notMem hin, norm_zero]
    positivity

theorem differentiableAt_expSubHead {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ
      (fun w : ℂ => ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) *
        (Complex.exp (-((x : ℂ) * (t : ℂ))) - 1)) s := by
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun t ht => ht.1
  have hfun : (fun w : ℂ => ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) *
        (Complex.exp (-((x : ℂ) * (t : ℂ))) - 1))
      = mellin (Set.indicator (Ioc (0 : ℝ) 1)
          (fun t : ℝ => Complex.exp (-((x : ℂ) * (t : ℂ))) - 1)) := by
    funext w
    rw [mellin_indicator_of_subset measurableSet_Ioc hsub _ w]
  rw [hfun]
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := -1) ?_ ?_
    (by linarith) (isBigO_indicator_expSub_zero hx) hs
  · refine locallyIntegrableOn_of_integrableOn_Ioi
      (integrableOn_indicator_of_integrableOn measurableSet_Ioc hsub ?_)
    have hcont : ContinuousOn
        (fun t : ℝ => Complex.exp (-((x : ℂ) * (t : ℂ))) - 1) (Icc 0 1) :=
      ((Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).neg)).sub continuous_const).continuousOn
    exact (hcont.integrableOn_compact isCompact_Icc).mono_set (fun _ ht => ⟨ht.1.le, ht.2⟩)
  · refine isBigO_indicator_of_eventuallyZero ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact fun hmem => absurd hmem.2 (not_le.mpr ht)

theorem differentiableAt_expTail {x : ℝ} (hx : 0 < x) (s : ℂ) :
    DifferentiableAt ℂ
      (fun w : ℂ => ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) *
        Complex.exp (-((x : ℂ) * (t : ℂ)))) s := by
  have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (by norm_num)
  have hfun : (fun w : ℂ => ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) *
        Complex.exp (-((x : ℂ) * (t : ℂ))))
      = mellin (Set.indicator (Ioi (1 : ℝ))
          (fun t : ℝ => Complex.exp (-((x : ℂ) * (t : ℂ))))) := by
    funext w
    rw [mellin_indicator_of_subset measurableSet_Ioi hsub _ w]
  have htop : Set.indicator (Ioi (1 : ℝ))
      (fun t : ℝ => Complex.exp (-((x : ℂ) * (t : ℂ))))
      =O[atTop] fun t : ℝ => Real.exp (-x * t) := by
    refine Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [Set.indicator_of_mem (mem_Ioi.mpr ht), Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), one_mul, Complex.norm_exp]
    have : (-((x : ℂ) * (t : ℂ))).re = -x * t := by simp
    rw [this]
  rw [hfun]
  refine mellin_differentiableAt_of_isBigO_rpow_exp (b := s.re - 1) hx ?_ htop ?_ (by linarith)
  · exact locallyIntegrableOn_of_integrableOn_Ioi
      (integrableOn_indicator_of_integrableOn measurableSet_Ioi hsub
        (by simpa using integrableOn_cpow_mul_exp_Ioi_one hx 1))
  · refine isBigO_indicator_of_eventuallyZero ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact fun hmem => absurd (mem_Ioi.mp hmem) (not_lt.mpr ht.2.le)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem analyticAt_analyticSlope_of_ne {f : ℂ → ℂ} {c z : ℂ} (hf : AnalyticAt ℂ f z)
    (hz : z ≠ c) : AnalyticAt ℂ (analyticSlope f c) z := by
  have heq : analyticSlope f c =ᶠ[𝓝 z] fun w => (f w - f c) / (w - c) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hz)] with w hw
    exact analyticSlope_of_ne (by simpa using hw)
  refine AnalyticAt.congr ?_ heq.symm
  exact (hf.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz)

theorem analyticAt_analyticSlope_all {f : ℂ → ℂ} {c z : ℂ} (hf : ∀ w, AnalyticAt ℂ f w) :
    AnalyticAt ℂ (analyticSlope f c) z := by
  rcases eq_or_ne z c with rfl | hz
  · exact analyticAt_analyticSlope (hf z)
  · exact analyticAt_analyticSlope_of_ne (hf z) hz

/-- The regularization of the exponential bracket at the origin. -/
def expShiftRegZero (x : ℝ) (s : ℂ) : ℂ :=
  ((∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) *
      (Complex.exp (-((x : ℂ) * (t : ℂ))) - 1))
    + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * Complex.exp (-((x : ℂ) * (t : ℂ))))
      * (Complex.Gamma s)⁻¹
    + analyticSlope (fun w : ℂ => (Complex.Gamma w)⁻¹) 0 s

theorem expShiftRegZero_eq {x : ℝ} {s : ℂ} (hs : s ≠ 0) :
    expShiftRegZero x s = expShiftBracket x s * (Complex.Gamma s)⁻¹ := by
  have hG0 : (Complex.Gamma (0 : ℂ))⁻¹ = 0 := by rw [Complex.Gamma_zero, inv_zero]
  have hslope := sub_eq_mul_analyticSlope (fun w : ℂ => (Complex.Gamma w)⁻¹) 0 s
  simp only [hG0, sub_zero] at hslope
  rw [expShiftRegZero, expShiftBracket]
  set Qs : ℂ := (Complex.Gamma s)⁻¹ with hQs
  set σ : ℂ := analyticSlope (fun w : ℂ => (Complex.Gamma w)⁻¹) 0 s with hσ
  have hQ : Qs = s * σ := by rw [hQs, hσ]; linear_combination hslope
  have key : 1 / s * Qs = σ := by
    rw [hQ]
    field_simp
  linear_combination -key

theorem analyticAt_expShiftRegZero {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : -1 < s.re) :
    AnalyticAt ℂ (expShiftRegZero x) s := by
  have hQent : ∀ w : ℂ, AnalyticAt ℂ (fun v : ℂ => (Complex.Gamma v)⁻¹) w := fun w =>
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ) w
      (Set.mem_univ w)
  have hopen : IsOpen {w : ℂ | -1 < w.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hpieces : AnalyticAt ℂ
      (fun w : ℂ => (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (w - 1) *
          (Complex.exp (-((x : ℂ) * (t : ℂ))) - 1))
        + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * Complex.exp (-((x : ℂ) * (t : ℂ)))) s := by
    refine DifferentiableOn.analyticAt (s := {w : ℂ | -1 < w.re}) ?_ (hopen.mem_nhds hs)
    intro w hw
    exact ((differentiableAt_expSubHead hx hw).add
      (differentiableAt_expTail hx w)).differentiableWithinAt
  exact (hpieces.mul (hQent s)).add (analyticAt_analyticSlope_all hQent)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 800000 in
/-- **The regularized exponential bracket is the power.**  Both sides are analytic on the convex
half-plane `Re s > -1` and agree where the Euler integral converges. -/
theorem expShiftRegZero_eq_cpow {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : -1 < s.re) :
    expShiftRegZero x s = (x : ℂ) ^ (-s) := by
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  set U : Set ℂ := {w : ℂ | -1 < w.re} with hU
  have hUopen : IsOpen U := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt (-1 : ℝ)).isPreconnected
  have hf : AnalyticOnNhd ℂ (expShiftRegZero x) U :=
    fun w hw => analyticAt_expShiftRegZero hx hw
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => (x : ℂ) ^ (-w)) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUopen
    intro w _
    exact ((differentiableAt_id.neg).const_cpow (Or.inl hxne)).differentiableWithinAt
  have hone : (1 : ℂ) ∈ U := by simp [hU]
  have hright : IsOpen {w : ℂ | 0 < w.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hev : expShiftRegZero x =ᶠ[𝓝 (1 : ℂ)] fun w => (x : ℂ) ^ (-w) := by
    filter_upwards [hright.mem_nhds (by simp)] with w hw
    have hwre : 0 < w.re := hw
    have hwne : w ≠ 0 := by
      intro hcon
      rw [hcon] at hwre
      simp at hwre
    have hG : Complex.Gamma w ≠ 0 :=
      Complex.Gamma_ne_zero (_root_.HTGeometry.ne_neg_natCast_of_re_pos hwre)
    rw [expShiftRegZero_eq hwne, expShiftBracket_eq_Gamma_mul hx hwre]
    field_simp
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUconn hone hev hs

theorem hasDerivAt_cpow_neg_zero {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun s : ℂ => (x : ℂ) ^ (-s)) (-((Real.log x : ℝ) : ℂ)) 0 := by
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hlog : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hx.le]
  have hfun : (fun s : ℂ => (x : ℂ) ^ (-s))
      = fun s : ℂ => Complex.exp (Complex.log (x : ℂ) * (-s)) := by
    funext s
    rw [Complex.cpow_def_of_ne_zero hxne]
  have hlin : HasDerivAt (fun s : ℂ => Complex.log (x : ℂ) * (-s))
      (-Complex.log (x : ℂ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).neg).const_mul (Complex.log (x : ℂ))
  have h := hlin.cexp
  rw [hfun]
  simpa [hlog] using h

/-- **The derivative of the exponential bracket at the origin is minus the logarithm.** -/
theorem deriv_expShiftRegZero_zero {x : ℝ} (hx : 0 < x) :
    deriv (expShiftRegZero x) 0 = -((Real.log x : ℝ) : ℂ) := by
  have hev : expShiftRegZero x =ᶠ[𝓝 (0 : ℂ)] fun s : ℂ => (x : ℂ) ^ (-s) := by
    have hopen : IsOpen {w : ℂ | -1 < w.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
    filter_upwards [hopen.mem_nhds (by norm_num)] with w hw
    exact expShiftRegZero_eq_cpow hx hw
  rw [hev.deriv_eq]
  exact (hasDerivAt_cpow_neg_zero hx).deriv

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 800000 in
theorem barnesSingleRegZero_shift_eventually {o x : ℝ} (ho : 0 < o) (hx : 0 < x) :
    (fun s : ℂ => barnesSingleZetaRegZero o x s)
      =ᶠ[𝓝 (0 : ℂ)] fun s : ℂ => barnesSingleZetaRegZero o (x + o) s + expShiftRegZero x s := by
  have hx1 : 0 < x + o := by linarith
  have hopen : IsOpen {w : ℂ | -1 < w.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hmem : {w : ℂ | -1 < w.re} ∈ 𝓝 (0 : ℂ) := hopen.mem_nhds (by norm_num)
  have hpunct : (fun s : ℂ => barnesSingleZetaRegZero o x s)
      =ᶠ[𝓝[≠] (0 : ℂ)] fun s : ℂ => barnesSingleZetaRegZero o (x + o) s
        + expShiftRegZero x s := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hmem] with s hs hs'
    have hsne : s ≠ 0 := hs
    rw [barnesSingleZetaRegZero_eq hsne, barnesSingleZetaRegZero_eq hsne,
      expShiftRegZero_eq hsne, barnesSingleZetaDeep, barnesSingleZetaDeep,
      barnesSingleZetaBracket_shift ho hx hs']
    ring
  have hL : ContinuousAt (fun s : ℂ => barnesSingleZetaRegZero o x s) 0 :=
    (analyticAt_barnesSingleZetaRegZero ho hx).continuousAt
  have hR : ContinuousAt (fun s : ℂ => barnesSingleZetaRegZero o (x + o) s
      + expShiftRegZero x s) 0 :=
    ((analyticAt_barnesSingleZetaRegZero ho hx1).add
      (analyticAt_expShiftRegZero hx (by norm_num))).continuousAt
  have hval : barnesSingleZetaRegZero o x 0
      = barnesSingleZetaRegZero o (x + o) 0 + expShiftRegZero x 0 := by
    have t1 : Filter.Tendsto (fun s : ℂ => barnesSingleZetaRegZero o x s) (𝓝[≠] (0 : ℂ))
        (𝓝 (barnesSingleZetaRegZero o x 0)) := hL.continuousWithinAt.tendsto
    have t2 : Filter.Tendsto (fun s : ℂ => barnesSingleZetaRegZero o x s) (𝓝[≠] (0 : ℂ))
        (𝓝 (barnesSingleZetaRegZero o (x + o) 0 + expShiftRegZero x 0)) :=
      (hR.continuousWithinAt.tendsto).congr' hpunct.symm
    exact tendsto_nhds_unique t1 t2
  rw [Filter.EventuallyEq, ← nhdsNE_sup_pure (0 : ℂ), Filter.eventually_sup]
  exact ⟨hpunct, by simpa using hval⟩

/-- **The difference equation of the one-dimensional Barnes gamma.**  Shifting the argument by the
period adds the logarithm: the classical `log Gamma(x + omega) - log Gamma(x) = log x`. -/
theorem logBarnesSingleGamma_shift {o x : ℝ} (ho : 0 < o) (hx : 0 < x) :
    logBarnesSingleGamma o (x + o) = logBarnesSingleGamma o x + ((Real.log x : ℝ) : ℂ) := by
  have hx1 : 0 < x + o := by linarith
  have hdiffS : DifferentiableAt ℂ (barnesSingleZetaRegZero o (x + o)) 0 :=
    (analyticAt_barnesSingleZetaRegZero ho hx1).differentiableAt
  have hdiffE : DifferentiableAt ℂ (expShiftRegZero x) 0 :=
    (analyticAt_expShiftRegZero hx (by norm_num)).differentiableAt
  have hderiv := (barnesSingleRegZero_shift_eventually ho hx).deriv_eq
  have hsum : deriv (fun s : ℂ => barnesSingleZetaRegZero o (x + o) s + expShiftRegZero x s) 0
      = deriv (barnesSingleZetaRegZero o (x + o)) 0 + deriv (expShiftRegZero x) 0 :=
    (hdiffS.hasDerivAt.add hdiffE.hasDerivAt).deriv
  rw [logBarnesSingleGamma, logBarnesSingleGamma]
  have hkey : deriv (barnesSingleZetaRegZero o x) 0
      = deriv (barnesSingleZetaRegZero o (x + o)) 0 + deriv (expShiftRegZero x) 0 := by
    rw [hderiv, hsum]
  rw [deriv_expShiftRegZero_zero hx] at hkey
  linear_combination -hkey

end

end GaloisForLFunctions.HTGeometry
