import GaloisForLFunctions.RHTower.ThetaCuspImaginaryArcCharge
import GaloisForLFunctions.RHTower.ThetaCuspGlobalReflectedRiccati
import GaloisForLFunctions.HTGeometry.VivantiPringsheim
import GaloisForLFunctions.HTGeometry.LogDerivativeResidue
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Both signs occur cofinally among the even logarithmic theta-source jets

The literal source has a nonzero imaginary zero inside its analytic strip.
Its Euler logarithmic derivative therefore has a finite Taylor radius strictly
inside that strip, while remaining analytic on the real axis. Local meromorphic
continuation and Vivanti--Pringsheim exclude either eventual coefficient sign.
This obstructs extending fourth-log negativity to an all-even curvature cone;
it does not decide arbitrary-rank theta tail-kernel positivity.
-/

open Complex Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace RHTower.ThetaLogJet

private theorem meromorphic_germ_propagation
    {f g : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hU : IsPreconnected U) (hu : u ∈ U)
    (hseed : f =ᶠ[𝓝[≠] u] g) :
    ∀ z ∈ U, f =ᶠ[𝓝[≠] z] g := by
  have hsub : MeromorphicOn (f - g) U := hf.sub hg
  have htopu : meromorphicOrderAt (f - g) u = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hseed] with z hz using sub_eq_zero.mpr hz
  let S : Set U := {x | meromorphicOrderAt (f - g) x = ⊤}
  have hSclopen : IsClopen S := hsub.isClopen_setOf_meromorphicOrderAt_eq_top
  letI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  have hSne : S ≠ ∅ := by
    intro hS
    have huS : (⟨u, hu⟩ : U) ∈ S := htopu
    rw [hS] at huS
    exact huS
  have hSuniv : S = Set.univ := (isClopen_iff.mp hSclopen).resolve_left hSne
  intro z hz
  have htopz : meromorphicOrderAt (f - g) z = ⊤ := by
    have hzS : (⟨z, hz⟩ : U) ∈ S := by rw [hSuniv]; trivial
    exact hzS
  rw [eventuallyEq_iff_sub]
  exact meromorphicOrderAt_eq_top_iff.mp htopz

private theorem germ_eq_sum {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0) :
    f =ᶠ[𝓝 0] p.sum := by
  filter_upwards [hp.eventually_hasSum] with z hz
  simpa only [zero_add, FormalMultilinearSeries.sum] using hz.tsum_eq.symm


private theorem continuesAcross {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0)
    {B : ℝ} (hf : MeromorphicOn f (Metric.ball 0 B)) {R : ℝ} (hR : 0 < R)
    (hrad : p.radius = ENNReal.ofReal R) (hRB : R ≤ B) (hreal : AnalyticAt ℂ f (R : ℂ)) :
    GaloisForLFunctions.HTGeometry.ContinuesAcross p.sum (Metric.ball 0 R) (R : ℂ) := by
  have hsum : AnalyticOnNhd ℂ p.sum (Metric.ball 0 R) := by
    have h := (p.hasFPowerSeriesOnBall hp.radius_pos).analyticOnNhd
    simpa [hrad] using h
  have heq := meromorphic_germ_propagation
    (U := Metric.ball 0 R) (u := 0) (fun z hz => hf z (Metric.ball_subset_ball hRB hz))
    hsum.meromorphicOn (convex_ball (0 : ℂ) R).isPreconnected
    (Metric.mem_ball_self hR)
    ((germ_eq_sum hp).filter_mono nhdsWithin_le_nhds)
  refine ⟨f, hreal, ?_⟩
  filter_upwards [hreal.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hzball
  have hstrong : f =ᶠ[𝓝 z] p.sum :=
    (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hz.continuousAt
      (hsum z hzball).continuousAt).1 (heq z hzball)
  exact hstrong.eq_of_nhds

private theorem nonnegative_impossible {f : ℂ → ℂ} {a : ℕ → ℝ}
    (hp : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ
      (fun n => (a n : ℂ))) 0)
    {B : ℝ} (hf : MeromorphicOn f (Metric.ball 0 B)) (hreal : ∀ R : ℝ, 0 ≤ R → AnalyticAt ℂ f (R : ℂ))
    (hbound : (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius < ENNReal.ofReal B)
    (ha : ∀ n, 0 ≤ a n) : False := by
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  have hfinite : p.radius ≠ ⊤ := ne_top_of_lt hbound
  let R := p.radius.toReal
  have hR : 0 < R := ENNReal.toReal_pos hp.radius_pos.ne' hfinite
  have hrad : p.radius = ENNReal.ofReal R := (ENNReal.ofReal_toReal hfinite).symm
  have hRB : R ≤ B := by
    apply le_of_lt
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hR.le).mp
    rwa [← hrad]
  have hconv : ∀ s : ℝ, 0 ≤ s → s < R → Summable (fun n => a n * s ^ n) := by
    intro s hs hsR
    let sNN : ℝ≥0 := ⟨s, hs⟩
    have hsrad : (sNN : ℝ≥0∞) < p.radius := by
      rw [hrad, ENNReal.coe_nnreal_eq]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg sNN.coe_nonneg |>.mpr hsR
    refine (p.summable_norm_mul_pow (r := sNN) hsrad).congr fun n => ?_
    change ‖p n‖ * (sNN : ℝ) ^ n = a n * s ^ n
    have hn : ‖p n‖ = a n := by
      change ‖FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ)) n‖ = a n
      rw [FormalMultilinearSeries.ofScalars_norm, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (ha n)]
    rw [hn]
    rfl
  have hdiv : ∀ s : ℝ, R < s → ¬ Summable (fun n => a n * s ^ n) := by
    intro s hs hsum
    have hs0 : 0 ≤ s := (hR.trans hs).le
    have hle : ENNReal.ofReal s ≤ p.radius := by
      rw [ENNReal.ofReal_eq_coe_nnreal hs0]
      apply p.le_radius_of_summable_norm
      simpa [p, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs,
        abs_of_nonneg (ha _)] using hsum
    rw [hrad] at hle
    have : s ≤ R := (ENNReal.ofReal_le_ofReal_iff hR.le).mp hle
    exact (not_le_of_gt hs) this
  have hcontin := continuesAcross hp hf hR hrad hRB (hreal R hR.le)
  have hsumid : p.sum = GaloisForLFunctions.HTGeometry.realSeriesSum a := by
    funext z
    simp [p, FormalMultilinearSeries.sum,
      GaloisForLFunctions.HTGeometry.realSeriesSum, smul_eq_mul, mul_comm]
  rw [hsumid] at hcontin
  exact GaloisForLFunctions.HTGeometry.not_continuesAcross_of_nonneg
    ha hR hconv hdiv hcontin


private theorem not_eventually_nonnegative {f : ℂ → ℂ} {a : ℕ → ℝ}
    (hp : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ
      (fun n => (a n : ℂ))) 0)
    {B : ℝ} (hf : MeromorphicOn f (Metric.ball 0 B)) (hreal : ∀ R : ℝ, 0 ≤ R → AnalyticAt ℂ f (R : ℂ))
    (hbound : (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius < ENNReal.ofReal B) :
    ¬ ∀ᶠ n in atTop, 0 ≤ a n := by
  classical
  intro hnonneg
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnonneg
  let c : ℕ → ℝ := fun n => if n < N then a n else 0
  let b : ℕ → ℝ := fun n => a n - c n
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  let q := FormalMultilinearSeries.ofScalars ℂ (fun n => (c n : ℂ))
  let r := FormalMultilinearSeries.ofScalars ℂ (fun n => (b n : ℂ))
  have hqtop : q.radius = ⊤ := by
    apply q.radius_eq_top_of_eventually_eq_zero
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [q, c, Nat.not_lt.mpr hn]
  have hr : r = p - q := by
    ext n
    simp [r, p, q, b, FormalMultilinearSeries.ofScalars]
  have hrad : r.radius = p.radius := by
    apply le_antisymm
    · have h := (p - q).min_radius_le_radius_add q
      simpa [hqtop, hr, sub_add_cancel] using h
    · have h := p.min_radius_le_radius_add (-q)
      simpa [hqtop, hr, sub_eq_add_neg] using h
  have hqp : HasFPowerSeriesOnBall q.sum q 0 q.radius :=
    q.hasFPowerSeriesOnBall (by rw [hqtop]; simp)
  have hqsum : AnalyticOnNhd ℂ q.sum Set.univ := by
    simpa [hqtop] using hqp.analyticOnNhd
  have hsubp : HasFPowerSeriesAt (f - q.sum) r 0 := by
    rw [hr]
    exact hp.sub hqp.hasFPowerSeriesAt
  have hb : ∀ n, 0 ≤ b n := by
    intro n
    by_cases hn : n < N
    · simp [b, c, hn]
    · simpa [b, c, hn] using hN n (Nat.le_of_not_gt hn)
  apply nonnegative_impossible hsubp (hf.sub (fun z _ => (hqsum z (Set.mem_univ z)).meromorphicAt))
      (fun R hR => (hreal R hR).sub (hqsum (R : ℂ) (Set.mem_univ _))) ?_ hb
  change r.radius < ENNReal.ofReal B
  rw [hrad]
  exact hbound


private theorem not_eventually_nonpositive {f : ℂ → ℂ} {a : ℕ → ℝ}
    (hp : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ
      (fun n => (a n : ℂ))) 0)
    {B : ℝ} (hf : MeromorphicOn f (Metric.ball 0 B)) (hreal : ∀ R : ℝ, 0 ≤ R → AnalyticAt ℂ f (R : ℂ))
    (hbound : (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius < ENNReal.ofReal B) :
    ¬ ∀ᶠ n in atTop, a n ≤ 0 := by
  have hneg : (FormalMultilinearSeries.ofScalars ℂ (fun n => ((-a n : ℝ) : ℂ))) =
      -(FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))) := by
    ext n
    simp [FormalMultilinearSeries.ofScalars]
  have hpneg : HasFPowerSeriesAt (-f)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => ((-a n : ℝ) : ℂ))) 0 := by
    rw [hneg]
    exact hp.neg
  have hboundneg : (FormalMultilinearSeries.ofScalars ℂ
      (fun n => ((-a n : ℝ) : ℂ))).radius < ENNReal.ofReal B := by
    rw [hneg, FormalMultilinearSeries.radius_neg]
    exact hbound
  intro hnonpos
  apply not_eventually_nonnegative hpneg hf.neg
    (fun R hR => (hreal R hR).neg) hboundneg
  simpa only [neg_nonneg] using hnonpos

private theorem cofinal_negative_even {a : ℕ → ℝ}
    (hne : ¬ ∀ᶠ n in atTop, 0 ≤ a n) (hodd : ∀ k, a (2 * k + 1) = 0)
    (N : ℕ) : ∃ k, N ≤ k ∧ a (2 * k) < 0 := by
  have hex : ∃ n, 2 * N ≤ n ∧ a n < 0 := by
    by_contra h
    push Not at h
    apply hne
    exact eventually_atTop.2 ⟨2 * N, h⟩
  obtain ⟨n, hn, ha⟩ := hex
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · rw [hk] at hn ha
    exact ⟨k, by omega, ha⟩
  · rw [hk, hodd] at ha
    exact (lt_irrefl 0 ha).elim

private theorem cofinal_positive_even {a : ℕ → ℝ}
    (hne : ¬ ∀ᶠ n in atTop, a n ≤ 0) (hodd : ∀ k, a (2 * k + 1) = 0)
    (N : ℕ) : ∃ k, N ≤ k ∧ 0 < a (2 * k) := by
  have hex : ∃ n, 2 * N ≤ n ∧ 0 < a n := by
    by_contra h
    push Not at h
    apply hne
    exact eventually_atTop.2 ⟨2 * N, h⟩
  obtain ⟨n, hn, ha⟩ := hex
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · rw [hk] at hn ha
    exact ⟨k, by omega, ha⟩
  · rw [hk, hodd] at ha
    exact (lt_irrefl 0 ha).elim


private theorem radius_lt_of_residue {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0)
    {B : ℝ} (hB : 0 < B) (hf : MeromorphicOn f (Metric.ball 0 B))
    {z c : ℂ} (hz : z ∈ Metric.ball 0 B) (hc : c ≠ 0)
    (hres : Tendsto (fun w => (w - z) * f w) (𝓝[≠] z) (𝓝 c)) :
    p.radius < ENNReal.ofReal B := by
  by_contra h
  have hle : ENNReal.ofReal B ≤ p.radius := le_of_not_gt h
  have hsum : AnalyticOnNhd ℂ p.sum (Metric.ball 0 B) := by
    apply (p.hasFPowerSeriesOnBall hp.radius_pos).analyticOnNhd.mono
    intro w hw
    exact (edist_lt_ofReal.mpr hw).trans_le hle
  have heq := meromorphic_germ_propagation hf hsum.meromorphicOn
    (convex_ball (0 : ℂ) B).isPreconnected (Metric.mem_ball_self hB)
    ((germ_eq_sum hp).filter_mono nhdsWithin_le_nhds)
  have hzero : Tendsto (fun w => (w - z) * p.sum w) (𝓝[≠] z) (𝓝 0) := by
    simpa using ((tendsto_id.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℂ => z) (𝓝 z) (𝓝 z))).mul
      (hsum z hz).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hzero' : Tendsto (fun w => (w - z) * f w) (𝓝[≠] z) (𝓝 0) := by
    apply hzero.congr'
    filter_upwards [heq z hz] with w hw
    rw [hw]
  exact hc (tendsto_nhds_unique hres hzero')

/-- The Euler logarithmic derivative of the literal complex theta source. -/
def eulerLog (z : ℂ) : ℂ := z * logDeriv thetaCuspStripSource z

private theorem real_mem (x : ℝ) : (x : ℂ) ∈ thetaCuspStrip := by
  simp [thetaCuspStrip, Real.pi_pos]

private theorem source_real_ne (x : ℝ) : thetaCuspStripSource (x : ℂ) ≠ 0 := by
  rw [thetaCuspStripSource_ofReal]
  exact_mod_cast (thetaCuspFullSource_pos_all x).ne'

private theorem analytic_real (x : ℝ) : AnalyticAt ℂ eulerLog (x : ℂ) := by
  have ha := analyticOnNhd_thetaCuspStripSource _ (real_mem x)
  exact analyticAt_id.mul (ha.deriv.div ha (source_real_ne x))

private theorem meromorphic_strip : MeromorphicOn eulerLog thetaCuspStrip := by
  intro z hz
  exact analyticAt_id.meromorphicAt.mul
    (analyticOnNhd_thetaCuspStripSource.meromorphicOn.logDeriv z hz)

private theorem ball_subset_strip :
    Metric.ball (0 : ℂ) ThetaImaginaryArc.arcEnd ⊆ thetaCuspStrip := by
  intro z hz
  exact (Complex.abs_im_le_norm z).trans_lt
    (by simpa [Metric.mem_ball, dist_zero_right, ThetaImaginaryArc.arcEnd] using hz)

private theorem eulerLog_real (x : ℝ) :
    eulerLog (x : ℂ) = (x * iteratedDeriv 1 thetaCuspLogSource x : ℝ) := by
  have hc := (analyticOnNhd_thetaCuspStripSource _ (real_mem x)).differentiableAt.hasDerivAt.comp_ofReal
  have hr := (hasDerivAt_thetaCuspFullSource_iterate_zero x).ofReal_comp
  have hd : deriv thetaCuspStripSource (x : ℂ) =
      ((iteratedDeriv 1 thetaCuspFullSource x : ℝ) : ℂ) := by
    apply HasDerivAt.unique _ hr
    simpa only [thetaCuspStripSource_ofReal] using hc
  have hl := (hasDerivAt_thetaCuspLogSource x).deriv
  simp only [← iteratedDeriv_one] at hl
  simp only [eulerLog, logDeriv_apply, hd, thetaCuspStripSource_ofReal, hl,
    Complex.ofReal_mul, Complex.ofReal_div]

private theorem real_jet (n : ℕ) (x : ℝ) :
    iteratedDeriv n eulerLog (x : ℂ) =
      (x * iteratedDeriv (n + 1) thetaCuspLogSource x +
        (n : ℝ) * iteratedDeriv n thetaCuspLogSource x : ℝ) := by
  induction n generalizing x with
  | zero => simpa only [iteratedDeriv_zero, Nat.cast_zero, zero_mul, add_zero] using eulerLog_real x
  | succ n ih =>
    have ha : AnalyticAt ℂ (iteratedDeriv n eulerLog) (x : ℂ) := by
      simpa only [iteratedDeriv_eq_iterate] using (analytic_real x).iterated_deriv n
    have hc := ha.differentiableAt.hasDerivAt.comp_ofReal
    have hr : HasDerivAt
        (fun y : ℝ => y * iteratedDeriv (n + 1) thetaCuspLogSource y +
          (n : ℝ) * iteratedDeriv n thetaCuspLogSource y)
        (1 * iteratedDeriv (n + 1) thetaCuspLogSource x +
          x * iteratedDeriv (n + 1 + 1) thetaCuspLogSource x +
          (n : ℝ) * iteratedDeriv (n + 1) thetaCuspLogSource x) x :=
      ((hasDerivAt_id x).mul
        (hasDerivAt_iteratedDeriv_thetaCuspLogSource (n + 1) x)).add
        ((hasDerivAt_iteratedDeriv_thetaCuspLogSource n x).const_mul (n : ℝ))
    have hr' : HasDerivAt
        (fun y : ℝ => y * iteratedDeriv (n + 1) thetaCuspLogSource y +
          (n : ℝ) * iteratedDeriv n thetaCuspLogSource y)
        (x * iteratedDeriv (n + 1 + 1) thetaCuspLogSource x +
          ((n + 1 : ℕ) : ℝ) * iteratedDeriv (n + 1) thetaCuspLogSource x) x := by
      exact hr.congr_deriv (by push_cast; ring)
    have hc' : HasDerivAt
        (fun y : ℝ => ((y * iteratedDeriv (n + 1) thetaCuspLogSource y +
          (n : ℝ) * iteratedDeriv n thetaCuspLogSource y : ℝ) : ℂ))
        (deriv (iteratedDeriv n eulerLog) (x : ℂ)) x := by
      simpa only [ih] using hc
    simpa only [iteratedDeriv_succ] using hc'.unique hr'.ofReal_comp

/-- Real canonical Taylor coefficients of the Euler logarithmic source. -/
def coeff (n : ℕ) : ℝ :=
  (n : ℝ) * iteratedDeriv n thetaCuspLogSource 0 / (n.factorial : ℝ)

private theorem powerSeries : HasFPowerSeriesAt eulerLog
    (FormalMultilinearSeries.ofScalars ℂ (fun n => (coeff n : ℂ))) 0 := by
  have hc : ∀ n, (coeff n : ℂ) = iteratedDeriv n eulerLog 0 / (n.factorial : ℂ) := by
    intro n
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by rfl, real_jet]
    simp [coeff]
  simpa only [hc, Complex.ofReal_zero] using (analytic_real 0).hasFPowerSeriesAt

private theorem coeff_odd (k : ℕ) : coeff (2 * k + 1) = 0 := by
  have ho : Odd (2 * k + 1) := ⟨k, by omega⟩
  simp [coeff, iteratedDeriv_thetaCuspLogSource_zero_of_odd ho]

/-- An actual imaginary source zero places the Euler-log Taylor radius inside the strip. -/
theorem radius_lt_strip :
    (FormalMultilinearSeries.ofScalars ℂ (fun n => (coeff n : ℂ))).radius <
      ENNReal.ofReal ThetaImaginaryArc.arcEnd := by
  obtain ⟨t, ht, htB, hzero⟩ := ThetaImaginaryArc.exists_imaginary_source_zero
  let z : ℂ := (t : ℂ) * I
  have hzstrip : z ∈ thetaCuspStrip := ThetaImaginaryArc.axis_mem_strip ht.le htB
  have haz := analyticOnNhd_thetaCuspStripSource z hzstrip
  have hfinite : analyticOrderAt thetaCuspStripSource z ≠ ⊤ := by
    apply analyticOnNhd_thetaCuspStripSource.analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_thetaCuspStrip (real_mem 0) hzstrip
    rw [(analyticOnNhd_thetaCuspStripSource _ (real_mem 0)).analyticOrderAt_eq_zero.mpr
      (source_real_ne 0)]
    simp
  let n := (analyticOrderAt thetaCuspStripSource z).toNat
  have hn : analyticOrderAt thetaCuspStripSource z = (n : ℕ∞) :=
    (ENat.coe_toNat_eq_self.mpr hfinite).symm
  have hn0 : n ≠ 0 := by
    intro h
    have horder := haz.analyticOrderAt_ne_zero.mpr hzero
    apply horder
    simpa [h] using hn
  have hz0 : z ≠ 0 := mul_ne_zero (by exact_mod_cast ht.ne') I_ne_zero
  have hres := GaloisForLFunctions.HTGeometry.tendsto_sub_mul_logDeriv_of_analyticOrderAt haz hn
  have hres' : Tendsto (fun w => (w - z) * eulerLog w) (𝓝[≠] z) (𝓝 (z * (n : ℂ))) := by
    have h := (tendsto_id.mono_left nhdsWithin_le_nhds).mul hres
    convert h using 1
    funext w
    dsimp [eulerLog]
    ring
  apply radius_lt_of_residue powerSeries ThetaImaginaryArc.arcEnd_pos
    (fun z hz => meromorphic_strip z (ball_subset_strip hz)) (z := z) ?_
    (mul_ne_zero hz0 (by exact_mod_cast hn0)) hres'
  simpa [z, Metric.mem_ball, dist_zero_right, norm_mul, abs_of_pos ht] using htB

/-- The actual Euler-log coefficients have negative entries arbitrarily far out. -/
theorem coeff_cofinal_negative_even (N : ℕ) :
    ∃ m, N ≤ m ∧ coeff (2 * m) < 0 := by
  exact cofinal_negative_even (not_eventually_nonnegative powerSeries
    (fun z hz => meromorphic_strip z (ball_subset_strip hz)) (fun x _ => analytic_real x)
    radius_lt_strip) coeff_odd N

/-- The actual Euler-log coefficients have positive entries arbitrarily far out. -/
theorem coeff_cofinal_positive_even (N : ℕ) :
    ∃ m, N ≤ m ∧ 0 < coeff (2 * m) := by
  exact cofinal_positive_even (not_eventually_nonpositive powerSeries
    (fun z hz => meromorphic_strip z (ball_subset_strip hz)) (fun x _ => analytic_real x)
    radius_lt_strip) coeff_odd N

/-- Even logarithmic center jets of the literal theta source are cofinally negative. -/
theorem logJet_cofinal_negative (N : ℕ) :
    ∃ m, N ≤ m ∧ iteratedDeriv (2 * m) thetaCuspLogSource 0 < 0 := by
  obtain ⟨m, hm, hneg⟩ := coeff_cofinal_negative_even N
  refine ⟨m, hm, ?_⟩
  by_contra h
  have hnonneg : 0 ≤ coeff (2 * m) := by
    unfold coeff
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_of_not_gt h))
      (Nat.cast_nonneg _)
  exact (not_lt_of_ge hnonneg) hneg

/-- Even logarithmic center jets of the literal theta source are cofinally positive. -/
theorem logJet_cofinal_positive (N : ℕ) :
    ∃ m, N ≤ m ∧ 0 < iteratedDeriv (2 * m) thetaCuspLogSource 0 := by
  obtain ⟨m, hm, hpos⟩ := coeff_cofinal_positive_even N
  refine ⟨m, hm, ?_⟩
  by_contra h
  have hnonpos : coeff (2 * m) ≤ 0 := by
    unfold coeff
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_gt h))
      (Nat.cast_nonneg _)
  exact (not_lt_of_ge hnonpos) hpos

end RHTower.ThetaLogJet
