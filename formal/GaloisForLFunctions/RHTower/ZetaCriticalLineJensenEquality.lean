import GaloisForLFunctions.HTGeometry.ShiftedCircleLogKernel
import GaloisForLFunctions.HTGeometry.LogDerivPoissonJensen
import GaloisForLFunctions.RHTower.ZetaCriticalLineJensenInequality


/-!
# The Balazard–Saias–Yor equality

With `G(w) = (s − 1) ζ(s)` at `s = 1/(1 − w)` (`zetaDisc`), the circle averages of `log |G|`
converge, as the radius tends to `1`, to the boundary average

`(1/2π) ∫ log |ζ(½ + it)| dt/(¼ + t²)`

(`tendsto_circleAverage_log_norm_zetaDisc`).  By Jensen's formula the circle average at radius `r`
is the zero sum `Σ_{|u| < r} m_u log(r/|u|)` (`tendsto_jensenSum_zetaDisc`), so the integral equals
the multiplicity-weighted sum of `log(|ρ|/|ρ − 1|)` over the zeros of `ζ` with `Re ρ > ½`.

The convergence is proved for any `Φ` holomorphic off `1` with `log |Φ(w)| ≤ A − 2 log |1 − w|` and
`|Φ| ≥ c > 0` on `[½, 1)` (`tendsto_integral_log_norm_circleMap_nhdsLT_one`):

* `log⁺ |Φ|` converges by dominated convergence;
* on the sector `|arg w| ≤ η`, `log⁻ |Φ|` has average at most `4η(A − log c + 2 log(1/η))` uniformly
  in the radius (`circleAverage_indicator_posLog_inv_le`): the Poisson–Jensen inequality
  (`log_norm_le_circleAverage_poisson`) at the real point `r − η`, whose Poisson kernel is
  `≥ 1/(4η)` on the sector, excludes any concentration of `log⁻` at `w = 1`;
* off the sector, divisor extraction on a closed disc that contains the arc but not `1` gives the
  integrable majorant `C + Σ_u d_u (log 2 + log(1 + |u|) − log |sin(θ − arg u)|)`
  (`tendsto_integral_compl_sector_log_norm`).
-/

open Complex Metric MeasureTheory Set Filter Topology MeromorphicOn
open GaloisForLFunctions.HTGeometry.PoissonJensen
open scoped Real

namespace RHTower

noncomputable section

/-! ## The Poisson–Jensen inequality -/

/-- **The Poisson–Jensen inequality.**  If `f` is analytic on the closed disc of radius `R` and
`f(w) ≠ 0` at an interior point `w`, then `log |f(w)|` is at most the Poisson average of
`log |f|` over the boundary circle. -/
theorem log_norm_le_circleAverage_poisson {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) (hfw : f w ≠ 0) :
    Real.log ‖f w‖ ≤
      Real.circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • (fun z => Real.log ‖f z‖))
        0 R := by
  classical
  have habs : |R| = R := abs_of_pos hR
  set CB := closedBall (0 : ℂ) |R| with hCB
  have hf' : AnalyticOnNhd ℂ f CB := by rw [hCB, habs]; exact hf
  have hwCB : w ∈ CB := by rw [hCB, habs]; exact ball_subset_closedBall hw
  have hordw : analyticOrderAt f w ≠ ⊤ := by
    rw [(hf' w hwCB).analyticOrderAt_eq_zero.mpr hfw]; exact ENat.zero_ne_top
  have h₂f : ∀ u : (CB : Set ℂ), meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    rw [(hf' u u.2).meromorphicOrderAt_eq]
    have := AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hf'
      (convex_closedBall _ _).isPreconnected hwCB u.2 hordw
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp this
    rw [← hm]; simp
  obtain ⟨g, hg, hg0, hlog, hformula⟩ := poissonJensen hR hf'.meromorphicOn h₂f hw
  rw [hformula]
  set D := divisor f CB with hD
  have hDfin : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 |R|)
  have hDnn : ∀ u, 0 ≤ D u := fun u => AnalyticOnNhd.divisor_nonneg hf' u
  -- the divisor avoids `w`
  have hDw : D w = 0 := by
    rw [hD, AnalyticOnNhd.divisor_apply hf' hwCB, (hf' w hwCB).analyticOrderAt_eq_zero.mpr hfw]
    rfl
  -- the pointwise factorization at `w`
  set T := hDfin.toFinset with hT
  have hsum : (∑ᶠ u, fun x : ℂ => (D u : ℝ) * Real.log ‖x - u‖) =
      fun x => ∑ u ∈ T, (D u : ℝ) * Real.log ‖x - u‖ := by
    rw [finsum_eq_sum_of_support_subset (s := T)]
    · funext x; simp [Finset.sum_apply]
    · intro u hu
      simp only [Function.mem_support] at hu
      simp only [hT, Set.Finite.coe_toFinset, Function.mem_support]
      intro hzero
      apply hu
      funext x; simp [hzero]
  rw [hsum] at hlog
  have hTw : ∀ u ∈ T, u ≠ w := by
    intro u hu huw
    rw [hT, Set.Finite.mem_toFinset, Function.mem_support, huw] at hu
    exact hu hDw
  have hcontS : ContinuousAt (fun x => ∑ u ∈ T, (D u : ℝ) * Real.log ‖x - u‖ +
      Real.log ‖g x‖) w := by
    refine ContinuousAt.add (tendsto_finsetSum T fun u hu => ?_) ?_
    · refine continuousAt_const.mul (ContinuousAt.log
        ((continuousAt_id.sub continuousAt_const).norm) ?_)
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hTw u hu).symm)
    · exact ContinuousAt.log ((hg w hwCB).continuousAt.norm) (norm_ne_zero_iff.mpr (hg0 ⟨w, hwCB⟩))
  have hcontF : ContinuousAt (fun x => Real.log ‖f x‖) w :=
    ContinuousAt.log ((hf' w hwCB).continuousAt.norm) (norm_ne_zero_iff.mpr hfw)
  have hevt : (fun x => Real.log ‖f x‖) =ᶠ[𝓝[≠] w]
      (fun x => ∑ u ∈ T, (D u : ℝ) * Real.log ‖x - u‖ + Real.log ‖g x‖) := by
    have h1 := (mem_codiscreteWithin.mp hlog) w hwCB
    rw [disjoint_principal_right] at h1
    have h2 : CB ∈ 𝓝[≠] w := mem_nhdsWithin_of_mem_nhds (by
      rw [hCB, habs]; exact closedBall_mem_nhds_of_mem hw)
    filter_upwards [h1, h2] with x hx1 hx2
    by_contra hne
    exact hx1 ⟨hx2, hne⟩
  have hval : Real.log ‖f w‖ = ∑ u ∈ T, (D u : ℝ) * Real.log ‖w - u‖ + Real.log ‖g w‖ :=
    tendsto_nhds_unique (hcontF.tendsto.mono_left nhdsWithin_le_nhds)
      ((hcontS.tendsto.mono_left nhdsWithin_le_nhds).congr' hevt.symm)
  rw [hval, add_le_add_iff_right]
  have hfin2 : ∑ᶠ u, (D u : ℝ) * Real.log ‖innerLogKernel 0 u R w‖ =
      ∑ u ∈ T, (D u : ℝ) * Real.log ‖innerLogKernel 0 u R w‖ := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [hT, Set.Finite.coe_toFinset, Function.mem_support]
    intro hzero; apply hu; simp [hzero]
  rw [hfin2]
  refine Finset.sum_le_sum fun u hu => ?_
  have huCB : u ∈ CB := by
    have : u ∈ Function.support D := by simpa [hT] using hu
    exact D.supportWithinDomain this
  have hu' : ‖u‖ ≤ R := by rw [hCB, habs, mem_closedBall, dist_zero_right] at huCB; exact huCB
  have hw' : ‖w‖ < R := by rw [mem_ball, dist_zero_right] at hw; exact hw
  refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast hDnn u)
  exact Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr (hTw u hu).symm))
    (GaloisForLFunctions.HTGeometry.norm_sub_le_norm_innerLogKernel hR
      (mem_closedBall_iff_norm.mpr (by rwa [sub_zero])) (mem_closedBall_iff_norm.mpr (by
        rw [sub_zero]; exact hw'.le)))

/-! ## No concentration at the boundary point `1` -/

/-- The sector `|arg z| ≤ η` around the positive axis. -/
def rightArc (η : ℝ) : Set ℂ := {z : ℂ | ‖z‖ * Real.cos η ≤ z.re}

theorem isClosed_rightArc (η : ℝ) : IsClosed (rightArc η) :=
  isClosed_le (continuous_norm.mul continuous_const) Complex.continuous_re

theorem circleIntegrable_indicator_of_isClosed {f : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) {S : Set ℂ} (hS : IsClosed S) :
    CircleIntegrable (S.indicator f) c R := by
  have hmeas : MeasurableSet (circleMap c R ⁻¹' S) :=
    (hS.preimage (continuous_circleMap c R)).measurableSet
  have heq : (fun θ => S.indicator f (circleMap c R θ)) =
      (circleMap c R ⁻¹' S).indicator (fun θ => f (circleMap c R θ)) := by
    funext θ
    rfl
  unfold CircleIntegrable at hf ⊢
  rw [heq]
  exact ⟨hf.1.indicator hmeas, hf.2.indicator hmeas⟩

/-- The Poisson kernel at a real point `x ∈ (0, r)` on the circle of radius `r`. -/
theorem re_herglotzRieszKernel_real_eq {x r : ℝ} {z : ℂ} (hz : ‖z‖ = r) :
    (herglotzRieszKernel 0 (x : ℂ) z).re = (r ^ 2 - x ^ 2) / ‖z - x‖ ^ 2 := by
  have h := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := (x : ℂ))) z
  simp only [Function.comp_apply] at h
  rw [← h, poissonKernel_def]
  simp [hz, Complex.norm_real, sq_abs]

theorem one_div_four_mul_le_re_herglotzRieszKernel {x r η : ℝ} (hη : 0 < η) (hxr : x = r - η)
    (hr1 : r ≤ 1) (hrx : 1 ≤ r + x) {z : ℂ} (hz : ‖z‖ = r) (harc : z ∈ rightArc η) :
    1 / (4 * η) ≤ (herglotzRieszKernel 0 (x : ℂ) z).re := by
  rw [re_herglotzRieszKernel_real_eq hz]
  have hr0 : 0 < r := by linarith
  -- `|z - r| ≤ η` on the sector
  have hzr : ‖z - r‖ ^ 2 ≤ η ^ 2 := by
    have hre : r * Real.cos η ≤ z.re := by
      have h := harc
      simp only [rightArc, Set.mem_setOf_eq, hz] at h
      exact h
    have hnorm : ‖z - r‖ ^ 2 = 2 * r ^ 2 - 2 * r * z.re := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hz2 : z.re * z.re + z.im * z.im = r ^ 2 := by
        rw [← Complex.normSq_apply, ← Complex.sq_norm, hz]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
      nlinarith
    rw [hnorm]
    have hcos : 1 - η ^ 2 / 2 ≤ Real.cos η := Real.one_sub_sq_div_two_le_cos
    have h1 := mul_le_mul_of_nonneg_left hre (by positivity : (0 : ℝ) ≤ 2 * r)
    have h2 := mul_le_mul_of_nonneg_left hcos (by positivity : (0 : ℝ) ≤ r ^ 2)
    have h3 : r ^ 2 * η ^ 2 ≤ η ^ 2 := by
      have : r ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg η]
    nlinarith
  have hzx : ‖z - x‖ ≤ 2 * η := by
    have h1 : ‖z - r‖ ≤ η := by
      have := Real.sqrt_le_sqrt hzr
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hη.le] at this
    calc ‖z - x‖ = ‖(z - r) + ((r : ℂ) - x)‖ := by ring_nf
      _ ≤ ‖z - r‖ + ‖(r : ℂ) - x‖ := norm_add_le _ _
      _ ≤ η + η := by
          gcongr
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hxr]
          simp [abs_of_pos hη]
      _ = 2 * η := by ring
  have hzx0 : 0 < ‖z - x‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have : ‖z‖ = |x| := by rw [sub_eq_zero.mp h, Complex.norm_real, Real.norm_eq_abs]
    rw [hz] at this
    have hx : x < r := by linarith
    rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hnum : r ^ 2 - x ^ 2 = η * (r + x) := by rw [hxr]; ring
  rw [hnum, le_div_iff₀ (by positivity)]
  have hsq : ‖z - x‖ ^ 2 ≤ 4 * η ^ 2 := by nlinarith
  calc 1 / (4 * η) * ‖z - ↑x‖ ^ 2 ≤ 1 / (4 * η) * (4 * η ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = η := by field_simp
    _ ≤ η * (r + x) := le_mul_of_one_le_right hη.le hrx

theorem circleAverage_poisson_const {x r : ℝ} (hx : (x : ℂ) ∈ ball (0 : ℂ) r) (a : ℝ) :
    Real.circleAverage ((Complex.re ∘ herglotzRieszKernel 0 (x : ℂ)) • fun _ => a) 0 r = a :=
  InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul
    InnerProductSpace.harmonicContOnCl_const hx

theorem circleAverage_poisson_log_norm_one_sub {x r : ℝ} (hr1 : r < 1)
    (hx : (x : ℂ) ∈ ball (0 : ℂ) r) :
    Real.circleAverage ((Complex.re ∘ herglotzRieszKernel 0 (x : ℂ)) •
      fun z => Real.log ‖1 - z‖) 0 r = Real.log ‖1 - (x : ℂ)‖ := by
  refine InnerProductSpace.HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul
    (fun z hz => ?_) hx
  refine AnalyticAt.harmonicAt_log_norm (by fun_prop) (sub_ne_zero.mpr fun h => ?_)
  rw [mem_closedBall, dist_zero_right, ← h, norm_one] at hz
  linarith

/-- **No concentration of `log⁻` at `w = 1`.**  Let `Φ` be holomorphic off `1` with
`log⁺ |Φ(w)| ≤ A − 2 log |1 − w|` on the closed disc and `|Φ(x)| ≥ c > 0` for `x ∈ [½, 1)`.  Then
for `½ + η ≤ r < 1` the average of `log⁻ |Φ|` over the sector `|arg z| ≤ η` of the circle of radius
`r` is at most `4η(A − log c + 2 log(1/η))`.  Poisson–Jensen at the real point `r − η`, whose
Poisson kernel is `≥ 1/(4η)` on the sector. -/
theorem circleAverage_indicator_posLog_inv_le {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ {1}ᶜ)
    {A : ℝ} (hup : ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 → Real.posLog ‖Φ w‖ ≤ A - 2 * Real.log ‖1 - w‖)
    {c x₀ : ℝ} (hc : 0 < c) (hx₀ : 1 / 2 ≤ x₀) (hlow : ∀ x : ℝ, x₀ ≤ x → x < 1 → c ≤ ‖Φ x‖)
    {η r : ℝ} (hη : 0 < η) (hr : x₀ + η ≤ r) (hr1 : r < 1) :
    Real.circleAverage ((rightArc η).indicator fun z => Real.posLog ‖Φ z‖⁻¹) 0 r ≤
      4 * η * (A - Real.log c + 2 * Real.log (1 / η)) := by
  set x : ℝ := r - η with hxdef
  have hx1 : 1 / 2 ≤ x := by rw [hxdef]; linarith
  have hxr : x < r := by rw [hxdef]; linarith
  have hr0 : 0 < r := by linarith
  have habs : |r| = r := abs_of_pos hr0
  have hxball : (x : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact hxr
  have hΦx : c ≤ ‖Φ x‖ := hlow x (by rw [hxdef]; linarith) (by linarith)
  have hΦx0 : Φ x ≠ 0 := fun h => by rw [h, norm_zero] at hΦx; linarith
  have hne1 : ∀ z : ℂ, ‖z‖ ≤ r → z ≠ 1 := fun z hz h => by
    rw [h, norm_one] at hz; linarith
  have hanal : AnalyticOnNhd ℂ Φ (closedBall 0 r) := fun z hz =>
    hΦ.analyticAt (isOpen_compl_singleton.mem_nhds (hne1 z (by
      rwa [mem_closedBall, dist_zero_right] at hz)))
  have hPJ := log_norm_le_circleAverage_poisson hr0 hanal hxball hΦx0
  set P : ℂ → ℝ := Complex.re ∘ herglotzRieszKernel 0 (x : ℂ) with hP
  set Neg : ℂ → ℝ := (rightArc η).indicator fun z => Real.posLog ‖Φ z‖⁻¹ with hNeg
  set U : ℂ → ℝ := fun z => A - 2 * Real.log ‖1 - z‖ with hU
  -- the pointwise bound on the circle
  have hpt : ∀ z ∈ sphere (0 : ℂ) |r|,
      (P • fun z => Real.log ‖Φ z‖) z ≤ (P • U - (1 / (4 * η)) • Neg) z := by
    intro z hz
    rw [habs, mem_sphere_iff_norm, sub_zero] at hz
    have hP0 : 0 ≤ P z := by
      simp only [hP, Function.comp_apply]
      rw [re_herglotzRieszKernel_real_eq hz]
      exact div_nonneg (by nlinarith) (sq_nonneg _)
    have hlog := (Real.posLog_sub_posLog_inv (x := ‖Φ z‖)).symm
    have hplus := hup z (by rw [hz]; exact hr1.le) (hne1 z hz.le)
    have hneg0 : 0 ≤ Real.posLog ‖Φ z‖⁻¹ := Real.posLog_nonneg
    have hPneg : (1 / (4 * η)) * Neg z ≤ P z * Real.posLog ‖Φ z‖⁻¹ := by
      simp only [hNeg, Set.indicator]
      split_ifs with harc
      · exact mul_le_mul_of_nonneg_right (one_div_four_mul_le_re_herglotzRieszKernel hη hxdef
          hr1.le (by rw [hxdef]; linarith) hz harc) hneg0
      · rw [mul_zero]; exact mul_nonneg hP0 hneg0
    show P z * Real.log ‖Φ z‖ ≤ P z * U z - (1 / (4 * η)) * Neg z
    rw [hlog]
    have h1 := mul_le_mul_of_nonneg_left hplus hP0
    have hUz : U z = A - 2 * Real.log ‖1 - z‖ := rfl
    rw [hUz]
    have e : P z * (Real.posLog ‖Φ z‖ - Real.posLog ‖Φ z‖⁻¹) =
        P z * Real.posLog ‖Φ z‖ - P z * Real.posLog ‖Φ z‖⁻¹ := by ring
    rw [e]
    linarith [h1, hPneg]
  -- integrability
  have hmer : MeromorphicOn Φ (sphere (0 : ℂ) |r|) := fun z hz =>
    (hanal z (sphere_subset_closedBall (by rwa [habs] at hz))).meromorphicAt
  have hPcont : ContinuousOn P (sphere (0 : ℂ) |r|) := continuousOn_re_herglotzRieszKernel hxball
  have hint1 : CircleIntegrable (P • fun z => Real.log ‖Φ z‖) 0 r :=
    hmer.circleIntegrable_log_norm.smul_of_continuousOn hPcont
  have hUcont : ContinuousOn U (sphere (0 : ℂ) |r|) := by
    refine continuousOn_const.sub (continuousOn_const.mul (ContinuousOn.log
      (continuousOn_const.sub continuousOn_id).norm fun z hz => ?_))
    rw [habs, mem_sphere_iff_norm, sub_zero] at hz
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hne1 z hz.le).symm)
  have hint2 : CircleIntegrable (P • U) 0 r := (hPcont.smul hUcont).circleIntegrable'
  have hint3 : CircleIntegrable Neg 0 r := by
    have hinv : MeromorphicOn (fun z => (Φ z)⁻¹) (sphere (0 : ℂ) |r|) := hmer.inv
    have h := hinv.circleIntegrable_posLog_norm
    simp only [norm_inv] at h
    exact circleIntegrable_indicator_of_isClosed h (isClosed_rightArc η)
  have hint3' := CircleIntegrable.const_smul (a := (1 / (4 * η) : ℝ)) hint3
  have hmono := Real.circleAverage_mono hint1 (hint2.sub hint3') hpt
  rw [Real.circleAverage_sub hint2 hint3', Real.circleAverage_smul] at hmono
  -- the Poisson average of `U`
  have hUavg : Real.circleAverage (P • U) 0 r = A - 2 * Real.log ‖1 - (x : ℂ)‖ := by
    have hsplit : P • U = (P • fun _ => A) - (2 : ℝ) • (P • fun z => Real.log ‖1 - z‖) := by
      funext z
      show P z * U z = P z * A - (2 : ℝ) * (P z * Real.log ‖1 - z‖)
      simp only [hU]
      ring
    have hc1 : CircleIntegrable (P • fun _ : ℂ => A) 0 r :=
      (hPcont.smul continuousOn_const).circleIntegrable'
    have hc2 : CircleIntegrable (P • fun z : ℂ => Real.log ‖1 - z‖) 0 r := by
      refine (hPcont.smul ((continuousOn_const.sub continuousOn_id).norm.log fun z hz => ?_))
        |>.circleIntegrable'
      rw [habs, mem_sphere_iff_norm, sub_zero] at hz
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hne1 z hz.le).symm)
    rw [hsplit, Real.circleAverage_sub hc1 (CircleIntegrable.const_smul (a := (2 : ℝ)) hc2),
      Real.circleAverage_smul,
      circleAverage_poisson_const hxball, circleAverage_poisson_log_norm_one_sub hr1 hxball,
      smul_eq_mul]
  have key : Real.log ‖Φ x‖ ≤
      A - 2 * Real.log ‖1 - (x : ℂ)‖ - 1 / (4 * η) * Real.circleAverage Neg 0 r := by
    calc Real.log ‖Φ x‖ ≤ _ := hPJ
      _ ≤ _ := hmono
      _ = _ := by rw [hUavg, smul_eq_mul]
  -- the arithmetic
  have h1x : η ≤ ‖1 - (x : ℂ)‖ := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    rw [hxdef]; linarith
  have hlogη : -(2 * Real.log ‖1 - (x : ℂ)‖) ≤ 2 * Real.log (1 / η) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log hη h1x
    linarith
  have hlogc : Real.log c ≤ Real.log ‖Φ x‖ := Real.log_le_log hc hΦx
  have hfin : 1 / (4 * η) * Real.circleAverage Neg 0 r ≤
      A - Real.log c + 2 * Real.log (1 / η) := by linarith [key, hlogc, hlogη]
  have h4 : 0 < 4 * η := by positivity
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ h4] at hfin
  linarith

/-! ## Convergence away from `w = 1` -/

theorem norm_circleMap_sub_ge_mul_abs_sin (u : ℂ) (r θ : ℝ) (hr : 0 ≤ r) :
    r * |Real.sin (θ - Complex.arg u)| ≤ ‖circleMap 0 r θ - u‖ := by
  set α := Complex.arg u
  have hu : (‖u‖ : ℂ) * Complex.exp (α * Complex.I) = u := Complex.norm_mul_exp_arg_mul_I u
  have hrot : ‖circleMap 0 r θ - u‖ =
      ‖Complex.exp (-(α * Complex.I)) * (circleMap 0 r θ - u)‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp
  have e1 : Complex.exp (-(α * Complex.I)) * circleMap 0 r θ =
      (r : ℂ) * Complex.exp (((θ - α : ℝ) : ℂ) * Complex.I) := by
    rw [circleMap, zero_add, mul_left_comm, ← Complex.exp_add]; push_cast; ring_nf
  have e2 : Complex.exp (-(α * Complex.I)) * u = (‖u‖ : ℂ) := by
    conv_lhs => rw [← hu]
    rw [mul_left_comm, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  rw [hrot, mul_sub, e1, e2]
  refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.mul_im, Complex.ofReal_re,
    Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re, zero_mul, add_zero]
  rw [abs_mul, abs_of_nonneg hr]

theorem abs_log_norm_circleMap_sub_le (u : ℂ) {r θ : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1)
    (hs : Real.sin (θ - Complex.arg u) ≠ 0) :
    |Real.log ‖circleMap 0 r θ - u‖| ≤
      Real.log 2 + Real.log (1 + ‖u‖) - Real.log (Real.sin (θ - Complex.arg u)) := by
  set σ := Real.sin (θ - Complex.arg u)
  have hσ0 : 0 < |σ| := abs_pos.mpr hs
  have hσ1 : |σ| ≤ 1 := Real.abs_sin_le_one _
  have hlogσ : Real.log σ ≤ 0 := by
    rw [← Real.log_abs]; exact Real.log_nonpos (abs_nonneg _) hσ1
  have hlower := norm_circleMap_sub_ge_mul_abs_sin u r θ (by linarith)
  have hhalf : |σ| / 2 ≤ r * |σ| := by
    have := mul_le_mul_of_nonneg_right hr (abs_nonneg σ); linarith
  have hpos : 0 < ‖circleMap 0 r θ - u‖ :=
    lt_of_lt_of_le (by positivity) (hhalf.trans hlower)
  have hupper : ‖circleMap 0 r θ - u‖ ≤ 1 + ‖u‖ := by
    calc ‖circleMap 0 r θ - u‖ ≤ ‖circleMap 0 r θ‖ + ‖u‖ := norm_sub_le _ _
      _ ≤ 1 + ‖u‖ := by
          rw [norm_circleMap_zero, abs_of_nonneg (by linarith)]; linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogu : 0 ≤ Real.log (1 + ‖u‖) := Real.log_nonneg (by linarith [norm_nonneg u])
  rw [abs_le]
  constructor
  · -- lower bound: `|z − u| ≥ |σ|/2`
    have h1 : |σ| / 2 ≤ ‖circleMap 0 r θ - u‖ := hhalf.trans hlower
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div hσ0.ne' (by norm_num), Real.log_abs] at h2
    linarith
  · have := Real.log_le_log hpos hupper
    linarith

theorem countable_setOf_sin_sub_eq_zero (α : ℝ) :
    {θ : ℝ | Real.sin (θ - α) = 0}.Countable := by
  refine (Set.countable_range fun n : ℤ => (n : ℝ) * Real.pi + α).mono fun θ hθ => ?_
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hθ
  exact ⟨n, by simp only; linarith⟩

theorem countable_zeros_of_differentiableOn {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ {1}ᶜ)
    (h0 : Φ 0 ≠ 0) : ({z : ℂ | Φ z = 0} ∩ {1}ᶜ).Countable := by
  have han : AnalyticOnNhd ℂ Φ {1}ᶜ := fun z hz =>
    hΦ.analyticAt (isOpen_compl_singleton.mem_nhds hz)
  have hconn : IsConnected ({1}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have hcod := han.preimage_zero_mem_codiscreteWithin h0 (by simp) hconn
  have hdisc := isDiscrete_of_codiscreteWithin (U := {1}ᶜ) (s := Φ ⁻¹' {0}) (by simpa using hcod)
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc

/-- The angles of the sector `|arg z| ≤ η`. -/
def sectorAngles (η : ℝ) : Set ℝ := {θ : ℝ | Real.cos η ≤ Real.cos θ}

theorem measurableSet_sectorAngles (η : ℝ) : MeasurableSet (sectorAngles η) :=
  measurableSet_le measurable_const Real.measurable_cos

theorem circleMap_mem_rightArc_iff {η r θ : ℝ} (hr : 0 < r) :
    circleMap 0 r θ ∈ rightArc η ↔ θ ∈ sectorAngles η := by
  have hre : (circleMap 0 r θ).re = r * Real.cos θ := by
    simp [circleMap, Complex.exp_ofReal_mul_I_re]
  simp only [rightArc, sectorAngles, Set.mem_setOf_eq, norm_circleMap_zero, abs_of_pos hr, hre]
  constructor
  · intro h; exact le_of_mul_le_mul_left (by linarith) hr
  · intro h; exact mul_le_mul_of_nonneg_left h hr.le

theorem norm_circleMap_add_one_le {η r θ : ℝ} (hη : 0 < η) (hη2 : η ≤ π / 2) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hθ : θ ∉ sectorAngles η) :
    ‖circleMap 0 r θ - (-1)‖ ≤ 2 * Real.cos (η / 2) := by
  have hpi := Real.pi_pos
  have hcosη : 0 ≤ Real.cos η :=
    Real.cos_nonneg_of_mem_Icc (Set.mem_Icc.mpr ⟨by linarith, hη2⟩)
  have hθ' : Real.cos θ < Real.cos η := by simpa [sectorAngles] using hθ
  have hcos2 : 0 ≤ Real.cos (η / 2) :=
    Real.cos_nonneg_of_mem_Icc (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
  have hsq : ‖circleMap 0 r θ - (-1)‖ ^ 2 = r ^ 2 + 2 * r * Real.cos θ + 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [circleMap, zero_add, sub_neg_eq_add, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im,
      zero_mul, sub_zero, add_zero]
    have := Real.sin_sq_add_cos_sq θ
    nlinarith
  have hhalf : (2 * Real.cos (η / 2)) ^ 2 = 2 + 2 * Real.cos η := by
    rw [mul_pow, Real.cos_sq (η / 2), show 2 * (η / 2) = η by ring]; ring
  have hle : ‖circleMap 0 r θ - (-1)‖ ^ 2 ≤ (2 * Real.cos (η / 2)) ^ 2 := by
    rw [hsq, hhalf]
    have h1 : 2 * r * Real.cos θ ≤ 2 * r * Real.cos η :=
      mul_le_mul_of_nonneg_left hθ'.le (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (by positivity : (0 : ℝ) ≤ 1 + r + 2 * Real.cos η)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hle

/-- **Convergence away from `w = 1`.**  Off the sector `|θ| ≤ η`, the integrals of
`log |Φ(r e^{iθ})|` converge as `r → 1⁻`.  Divisor extraction on a closed disc containing the
arc but not `1`, and dominated convergence with the integrable majorant
`C + Σ_u d_u (log 2 + log(1 + |u|) − log |sin(θ − arg u)|)`. -/
theorem tendsto_integral_compl_sector_log_norm {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ {1}ᶜ)
    (hmeas : Measurable Φ) (h0 : Φ 0 ≠ 0) {η : ℝ} (hη : 0 < η) (hη2 : η ≤ π / 2) :
    Tendsto (fun r => ∫ θ in (0 : ℝ)..2 * π,
        (sectorAngles η)ᶜ.indicator (fun θ => Real.log ‖Φ (circleMap 0 r θ)‖) θ) (𝓝[<] 1)
      (𝓝 (∫ θ in (0 : ℝ)..2 * π,
        (sectorAngles η)ᶜ.indicator (fun θ => Real.log ‖Φ (circleMap 0 1 θ)‖) θ)) := by
  classical
  set R : ℝ := 2 * Real.cos (η / 2) with hRdef
  have hpi := Real.pi_pos
  have hcos2 : Real.cos (η / 2) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (x := 0) (y := η / 2) le_rfl
      (by linarith) (by linarith)
    rwa [Real.cos_zero] at h
  have hcos2' : 1 / 2 < Real.cos (η / 2) := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (x := η / 2) (y := π / 3)
      (by linarith) (by linarith) (by linarith)
    rwa [Real.cos_pi_div_three] at h
  set B : Set ℂ := closedBall (-1 : ℂ) R with hB
  have hB1 : B ⊆ {1}ᶜ := by
    intro z hz h1
    rw [Set.mem_singleton_iff] at h1
    rw [hB, mem_closedBall, h1, dist_eq_norm] at hz
    norm_num at hz
    linarith
  have hanB : AnalyticOnNhd ℂ Φ B := fun z hz =>
    hΦ.analyticAt (isOpen_compl_singleton.mem_nhds (hB1 hz))
  have h0B : (0 : ℂ) ∈ B := by
    rw [hB, mem_closedBall, dist_eq_norm]; norm_num; linarith
  have hord0 : analyticOrderAt Φ 0 ≠ ⊤ := by
    rw [(hanB 0 h0B).analyticOrderAt_eq_zero.mpr h0]; exact ENat.zero_ne_top
  have hord : ∀ u : (B : Set ℂ), meromorphicOrderAt Φ u ≠ ⊤ := by
    intro u
    rw [(hanB u u.2).meromorphicOrderAt_eq]
    have := AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hanB
      (convex_closedBall _ _).isPreconnected h0B u.2 hord0
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp this
    rw [← hm]; simp
  have hfin : (divisor Φ B).support.Finite := (divisor Φ B).finiteSupport (isCompact_closedBall _ _)
  obtain ⟨g, hg, hg0, hfac⟩ := hanB.meromorphicOn.extract_zeros_poles hord hfin
  have hlog := MeromorphicOn.extract_zeros_poles_log hg0 hfac
  set T := hfin.toFinset with hT
  set d : ℂ → ℝ := fun u => (divisor Φ B u : ℝ) with hd
  have hd0 : ∀ u, 0 ≤ d u := fun u => by
    simp only [hd]; exact_mod_cast AnalyticOnNhd.divisor_nonneg hanB u
  have hsum : (∑ᶠ u, fun x : ℂ => (divisor Φ B u : ℝ) * Real.log ‖x - u‖) =
      fun x => ∑ u ∈ T, d u * Real.log ‖x - u‖ := by
    rw [finsum_eq_sum_of_support_subset (s := T)]
    · funext x; simp [Finset.sum_apply, hd]
    · intro u hu
      simp only [Function.mem_support] at hu
      simp only [hT, Set.Finite.coe_toFinset, Function.mem_support]
      intro hzero
      apply hu
      funext x; simp [hzero]
  rw [hsum] at hlog
  -- the exceptional set of the logarithmic factorization is countable
  set E : Set ℂ := {z | Real.log ‖Φ z‖ ≠ ∑ u ∈ T, d u * Real.log ‖z - u‖ + Real.log ‖g z‖} ∩ B
    with hE
  have hEc : E.Countable := by
    have hdisc := isDiscrete_of_codiscreteWithin (U := B)
      (s := {z | Real.log ‖Φ z‖ ≠ ∑ u ∈ T, d u * Real.log ‖z - u‖ + Real.log ‖g z‖})
      (by
        have : {z | Real.log ‖Φ z‖ ≠ ∑ u ∈ T, d u * Real.log ‖z - u‖ + Real.log ‖g z‖}ᶜ =
            {z | Real.log ‖Φ z‖ = ∑ u ∈ T, d u * Real.log ‖z - u‖ + Real.log ‖g z‖} := by
          ext z; simp
        rw [this]
        exact hlog)
    exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
  -- the zero-free factor is bounded on the disc
  have hgcont : ContinuousOn (fun z => Real.log ‖g z‖) B :=
    ContinuousOn.log hg.continuousOn.norm fun z hz => norm_ne_zero_iff.mpr (hg0 ⟨z, hz⟩)
  obtain ⟨Cg, hCg⟩ := (isCompact_closedBall (-1 : ℂ) R).exists_bound_of_continuousOn hgcont
  -- the majorant
  set G : ℝ → ℝ := fun θ => |Cg| + ∑ u ∈ T, d u * (Real.log 2 + Real.log (1 + ‖u‖) -
    Real.log (Real.sin (θ - Complex.arg u))) with hG
  have hlogsin : ∀ x : ℝ, Real.log (Real.sin x) ≤ 0 := fun x => by
    rw [← Real.log_abs]; exact Real.log_nonpos (abs_nonneg _) (Real.abs_sin_le_one _)
  have hterm0 : ∀ u θ, 0 ≤ Real.log 2 + Real.log (1 + ‖u‖) -
      Real.log (Real.sin (θ - Complex.arg u)) := fun u θ => by
    have := hlogsin (θ - Complex.arg u)
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h3 : 0 ≤ Real.log (1 + ‖u‖) := Real.log_nonneg (by linarith [norm_nonneg u])
    linarith
  have hG0 : ∀ θ, 0 ≤ G θ := fun θ =>
    add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun u _ => mul_nonneg (hd0 u) (hterm0 u θ))
  have hGint : IntervalIntegrable G volume 0 (2 * π) := by
    have hsum : IntervalIntegrable (∑ u ∈ T, fun θ : ℝ => d u * (Real.log 2 +
        Real.log (1 + ‖u‖) - Real.log (Real.sin (θ - Complex.arg u)))) volume 0 (2 * π) := by
      refine IntervalIntegrable.sum T fun u _ => ?_
      refine (intervalIntegrable_const.sub ?_).const_mul _
      have h := (intervalIntegrable_log_sin (a := 0 - Complex.arg u)
        (b := 2 * π - Complex.arg u)).comp_sub_right (Complex.arg u)
      simp only [sub_add_cancel, Function.comp_apply] at h
      exact h
    have heq : (fun θ => ∑ u ∈ T, d u * (Real.log 2 + Real.log (1 + ‖u‖) -
        Real.log (Real.sin (θ - Complex.arg u)))) = ∑ u ∈ T, fun θ : ℝ => d u * (Real.log 2 +
        Real.log (1 + ‖u‖) - Real.log (Real.sin (θ - Complex.arg u))) := by
      funext θ; simp [Finset.sum_apply]
    exact intervalIntegrable_const.add (heq ▸ hsum)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence G ?_ ?_ hGint ?_
  · -- measurability
    refine Eventually.of_forall fun r => ?_
    exact ((Real.measurable_log.comp (hmeas.comp (continuous_circleMap 0 r).measurable).norm
      ).indicator (measurableSet_sectorAngles η).compl).aestronglyMeasurable
  · -- the domination
    filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with r hr
    have hr0 : (0 : ℝ) < r := by linarith [hr.1]
    set X : Set ℝ := circleMap 0 r ⁻¹' E ∪
      ⋃ u ∈ T, {θ : ℝ | Real.sin (θ - Complex.arg u) = 0} with hX
    have hXc : X.Countable := (hEc.preimage_circleMap 0 hr0.ne').union
      ((T.countable_toSet).biUnion fun u _ => countable_setOf_sin_sub_eq_zero _)
    filter_upwards [hXc.measure_zero volume |> measure_eq_zero_iff_ae_notMem.mp] with θ hθX _
    by_cases hθ : θ ∈ sectorAngles η
    · rw [Set.indicator_of_notMem (by simpa using hθ), norm_zero]; exact hG0 θ
    rw [Set.indicator_of_mem (by simpa using hθ), Real.norm_eq_abs]
    have hzB : circleMap 0 r θ ∈ B := by
      rw [hB, mem_closedBall, dist_eq_norm]
      exact norm_circleMap_add_one_le hη hη2 hr0.le hr.2.le hθ
    have hzE : circleMap 0 r θ ∉ E := fun h => hθX (Or.inl h)
    have hid : Real.log ‖Φ (circleMap 0 r θ)‖ = ∑ u ∈ T, d u * Real.log ‖circleMap 0 r θ - u‖ +
        Real.log ‖g (circleMap 0 r θ)‖ := by
      by_contra hne; exact hzE ⟨hne, hzB⟩
    have hsin : ∀ u ∈ T, Real.sin (θ - Complex.arg u) ≠ 0 := fun u hu h =>
      hθX (Or.inr (Set.mem_biUnion hu h))
    rw [hid]
    calc |∑ u ∈ T, d u * Real.log ‖circleMap 0 r θ - u‖ + Real.log ‖g (circleMap 0 r θ)‖|
        ≤ ∑ u ∈ T, d u * |Real.log ‖circleMap 0 r θ - u‖| + |Real.log ‖g (circleMap 0 r θ)‖| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun u _ => by rw [abs_mul, abs_of_nonneg (hd0 u)]
      _ ≤ ∑ u ∈ T, d u * (Real.log 2 + Real.log (1 + ‖u‖) -
            Real.log (Real.sin (θ - Complex.arg u))) + |Cg| := by
          refine add_le_add (Finset.sum_le_sum fun u hu => ?_) ?_
          · exact mul_le_mul_of_nonneg_left (abs_log_norm_circleMap_sub_le u hr.1.le hr.2.le
              (hsin u hu)) (hd0 u)
          · exact (hCg _ hzB).trans (le_abs_self _)
      _ = G θ := by rw [hG]; ring
  · -- pointwise convergence
    set Y : Set ℝ := circleMap 0 1 ⁻¹' (({z : ℂ | Φ z = 0} ∩ {1}ᶜ) ∪ {1}) with hY
    have hYc : Y.Countable :=
      ((countable_zeros_of_differentiableOn hΦ h0).union (Set.countable_singleton 1)
        ).preimage_circleMap 0 one_ne_zero
    filter_upwards [hYc.measure_zero volume |> measure_eq_zero_iff_ae_notMem.mp] with θ hθY _
    by_cases hθ : θ ∈ sectorAngles η
    · simp only [Set.indicator_of_notMem (show θ ∉ (sectorAngles η)ᶜ by simpa using hθ)]
      exact tendsto_const_nhds
    simp only [Set.indicator_of_mem (show θ ∈ (sectorAngles η)ᶜ by simpa using hθ)]
    have hne1 : circleMap 0 1 θ ≠ 1 := fun h => hθY (Or.inr h)
    have hne0 : Φ (circleMap 0 1 θ) ≠ 0 := fun h => hθY (Or.inl ⟨h, hne1⟩)
    have hcont : ContinuousAt (fun r : ℝ => Real.log ‖Φ (circleMap 0 r θ)‖) 1 := by
      have h1 : ContinuousAt (fun r : ℝ => circleMap 0 r θ) 1 := by
        unfold circleMap; fun_prop
      have h2 : ContinuousAt Φ (circleMap 0 1 θ) :=
        hΦ.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hne1)
      exact ((ContinuousAt.comp (g := Φ) (f := fun r : ℝ => circleMap 0 r θ) (x := (1 : ℝ))
        h2 h1).norm).log (norm_ne_zero_iff.mpr hne0)
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-! ## Assembly -/

/-- Sector integrals vanish as the sector shrinks. -/
theorem tendsto_integral_sectorAngles_indicator {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 (2 * π)) :
    Tendsto (fun η => ∫ θ in (0 : ℝ)..2 * π, (sectorAngles η).indicator f θ) (𝓝[>] 0) (𝓝 0) := by
  have key : Tendsto (fun η => ∫ θ in (0 : ℝ)..2 * π, (sectorAngles η).indicator f θ) (𝓝[>] 0)
      (𝓝 (∫ θ in (0 : ℝ)..2 * π, (fun _ : ℝ => (0 : ℝ)) θ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝[>] (0 : ℝ)) (f := fun _ : ℝ => (0 : ℝ))
      (F := fun η θ => (sectorAngles η).indicator f θ) (fun θ => |f θ|)
      (Eventually.of_forall fun η => ?_) (Eventually.of_forall fun η => ?_) hf.abs ?_
    · exact (hf.def'.aestronglyMeasurable).indicator (measurableSet_sectorAngles η)
    · exact Eventually.of_forall fun θ _ => by
        rw [Real.norm_eq_abs]
        exact (norm_indicator_le_norm_self f θ).trans_eq (Real.norm_eq_abs _)
    · have hae : ∀ᵐ θ ∂volume, θ ≠ 2 * π := by
        rw [ae_iff]; simp
      filter_upwards [hae] with θ hθ hmem
      rw [Set.uIoc_of_le (by positivity)] at hmem
      have hθ1 : Real.cos θ < 1 := by
        refine lt_of_le_of_ne (Real.cos_le_one θ) fun h => ?_
        rw [Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hmem.1, Real.pi_pos])
          (lt_of_le_of_ne hmem.2 hθ)] at h
        linarith [hmem.1]
      have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), Real.cos θ < Real.cos η := by
        have hcont : Tendsto Real.cos (𝓝[>] (0 : ℝ)) (𝓝 1) := by
          have := Real.continuous_cos.tendsto 0
          rw [Real.cos_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        exact hcont.eventually (lt_mem_nhds hθ1)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with η hη
      rw [Set.indicator_of_notMem]
      simp only [sectorAngles, Set.mem_setOf_eq, not_le]
      exact hη
  simpa using key

theorem intervalIntegrable_indicator_of_measurableSet {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) {S : Set ℝ} (hS : MeasurableSet S) :
    IntervalIntegrable (S.indicator f) volume a b :=
  ⟨hf.1.indicator hS, hf.2.indicator hS⟩

theorem integral_sectorAngles_indicator_eq {h : ℂ → ℝ} {η r : ℝ} (hr : 0 < r) :
    ∫ θ in (0 : ℝ)..2 * π, (sectorAngles η).indicator (fun θ => h (circleMap 0 r θ)) θ =
      2 * π * Real.circleAverage ((rightArc η).indicator h) 0 r := by
  rw [Real.circleAverage_def, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  by_cases hθ : θ ∈ sectorAngles η
  · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem ((circleMap_mem_rightArc_iff hr).mpr hθ)]
  · rw [Set.indicator_of_notMem hθ,
      Set.indicator_of_notMem (fun h' => hθ ((circleMap_mem_rightArc_iff hr).mp h'))]

theorem posLog_le_of_log_le {y A t : ℝ} (hy : Real.log y ≤ A - 2 * t) (ht : t ≤ Real.log 2) :
    Real.posLog y ≤ (|A| + 2 * Real.log 2) - 2 * t := by
  rw [Real.posLog]
  refine max_le ?_ ?_
  · linarith [abs_nonneg A]
  · linarith [le_abs_self A, Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]

theorem log_norm_one_sub_le_log_two {w : ℂ} (hw : ‖w‖ ≤ 1) (hw1 : w ≠ 1) :
    Real.log ‖1 - w‖ ≤ Real.log 2 := by
  refine Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw1))) ?_
  calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

/-- **Boundary Jensen equality.**  Let `Φ` be holomorphic off `1`, measurable, `Φ(0) ≠ 0`, with
`log |Φ(w)| ≤ A − 2 log |1 − w|` on the closed disc and `|Φ(x)| ≥ c > 0` on `[½, 1)`.  Then the
integrals of `log |Φ(r e^{iθ})|` over `[0, 2π]` converge to the boundary integral as `r → 1⁻`. -/
theorem tendsto_integral_log_norm_circleMap_nhdsLT_one {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ {1}ᶜ) (hmeas : Measurable Φ) (h0 : Φ 0 ≠ 0) {A : ℝ}
    (hup : ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 → Real.log ‖Φ w‖ ≤ A - 2 * Real.log ‖1 - w‖)
    {c x₀ : ℝ} (hc : 0 < c) (hx₀ : 1 / 2 ≤ x₀) (hx₀1 : x₀ < 1)
    (hlow : ∀ x : ℝ, x₀ ≤ x → x < 1 → c ≤ ‖Φ x‖) :
    Tendsto (fun r => ∫ θ in (0 : ℝ)..2 * π, Real.log ‖Φ (circleMap 0 r θ)‖) (𝓝[<] 1)
      (𝓝 (∫ θ in (0 : ℝ)..2 * π, Real.log ‖Φ (circleMap 0 1 θ)‖)) := by
  set A₁ : ℝ := |A| + 2 * Real.log 2 with hA₁
  have hup₁ : ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 → Real.posLog ‖Φ w‖ ≤ A₁ - 2 * Real.log ‖1 - w‖ :=
    fun w hw hw1 => posLog_le_of_log_le (hup w hw hw1) (log_norm_one_sub_le_log_two hw hw1)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  set L : ℝ → ℝ → ℝ := fun r θ => Real.log ‖Φ (circleMap 0 r θ)‖ with hL
  have hint1 : IntervalIntegrable (L 1) volume 0 (2 * π) :=
    (circleIntegrable_and_sum_log_add_le_circleAverage hΦ hmeas h0 ⟨A, hup⟩
      (U := ∅) (by simp)).1
  have hmer : ∀ r : ℝ, 0 < r → r < 1 → MeromorphicOn Φ (sphere (0 : ℂ) |r|) := by
    intro r hr0 hr1 z hz
    have hz1 : z ≠ 1 := by
      intro h; rw [h, mem_sphere_iff_norm, sub_zero, norm_one, abs_of_pos hr0] at hz; linarith
    exact (hΦ.analyticAt (isOpen_compl_singleton.mem_nhds hz1)).meromorphicAt
  have hintr : ∀ r : ℝ, 0 < r → r < 1 → IntervalIntegrable (L r) volume 0 (2 * π) :=
    fun r hr0 hr1 => (hmer r hr0 hr1).circleIntegrable_log_norm
  set D₂ : ℝ → ℝ := fun θ => A₁ - 2 * Real.log (Real.sin θ) with hD₂
  have hD₂int : IntervalIntegrable D₂ volume 0 (2 * π) :=
    intervalIntegrable_const.sub (intervalIntegrable_log_sin.const_mul 2)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  -- the choice of the sector
  have ev1 := Metric.tendsto_nhds.mp (tendsto_integral_sectorAngles_indicator hint1.abs) _ hε4
  have ev2 := Metric.tendsto_nhds.mp (tendsto_integral_sectorAngles_indicator hD₂int) _ hε4
  have hlim3 : Tendsto (fun η : ℝ => 2 * π * (4 * η * (A₁ - Real.log c + 2 * Real.log (1 / η))))
      (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous fun η : ℝ =>
        2 * π * (4 * (A₁ - Real.log c) * η - 8 * (η * Real.log η)) :=
      continuous_const.mul ((continuous_const.mul continuous_id).sub
        (continuous_const.mul Real.continuous_mul_log))
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have hval : 2 * π * (4 * (A₁ - Real.log c) * 0 - 8 * (0 * Real.log 0)) = 0 := by ring
    rw [hval] at h
    refine h.congr fun η => ?_
    rw [one_div, Real.log_inv]; ring
  have ev3 := Metric.tendsto_nhds.mp hlim3 _ hε4
  have ev4 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Set.Ioo 0 (min (1 / 4) ((1 - x₀) / 2)) :=
    Ioo_mem_nhdsGT (lt_min (by norm_num) (by linarith))
  obtain ⟨η, h1, h2, h3, h4⟩ := (ev1.and (ev2.and (ev3.and ev4))).exists
  have hη0 : 0 < η := h4.1
  have h4' : η < 1 / 4 := h4.2.trans_le (min_le_left _ _)
  have h4'' : η < (1 - x₀) / 2 := h4.2.trans_le (min_le_right _ _)
  have hηπ : η ≤ π / 2 := by linarith [Real.pi_gt_three]
  simp only [Real.dist_eq, sub_zero] at h1 h2 h3
  -- convergence away from the sector
  have hK := Metric.tendsto_nhds.mp
    (tendsto_integral_compl_sector_log_norm hΦ hmeas h0 hη0 hηπ) _ hε4
  have hr' : ∀ᶠ r in 𝓝[<] (1 : ℝ), r ∈ Set.Ioo (x₀ + η) 1 :=
    Ioo_mem_nhdsLT (by linarith)
  filter_upwards [hK, hr'] with r hrK hr
  rw [Real.dist_eq] at hrK ⊢
  have hr0 : 0 < r := by linarith [hr.1]
  set S := sectorAngles η with hS
  have hSm : MeasurableSet S := measurableSet_sectorAngles η
  have hsplit : ∀ f : ℝ → ℝ, IntervalIntegrable f volume 0 (2 * π) →
      ∫ θ in (0 : ℝ)..2 * π, f θ =
        (∫ θ in (0 : ℝ)..2 * π, S.indicator f θ) + ∫ θ in (0 : ℝ)..2 * π, Sᶜ.indicator f θ := by
    intro f hf
    rw [← intervalIntegral.integral_add (intervalIntegrable_indicator_of_measurableSet hf hSm)
      (intervalIntegrable_indicator_of_measurableSet hf hSm.compl)]
    exact intervalIntegral.integral_congr fun θ _ =>
      (congrFun (Set.indicator_self_add_compl S f) θ).symm
  rw [hsplit _ (hintr r hr0 hr.2), hsplit _ hint1]
  -- the sector part at radius `r`
  have habs : ∀ f : ℝ → ℝ, IntervalIntegrable f volume 0 (2 * π) →
      |∫ θ in (0 : ℝ)..2 * π, S.indicator f θ| ≤ ∫ θ in (0 : ℝ)..2 * π, S.indicator (|f ·|) θ := by
    intro f hf
    refine (intervalIntegral.abs_integral_le_integral_abs (by positivity)).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun θ _ => ?_
    by_cases hθ : θ ∈ S
    · simp [Set.indicator_of_mem hθ]
    · simp [Set.indicator_of_notMem hθ]
  have hplusint : IntervalIntegrable (fun θ => Real.posLog ‖Φ (circleMap 0 r θ)‖) volume 0
      (2 * π) := (hmer r hr0 hr.2).circleIntegrable_posLog_norm
  have hminusint : IntervalIntegrable (fun θ => Real.posLog ‖Φ (circleMap 0 r θ)‖⁻¹) volume 0
      (2 * π) := by
    have h := (hmer r hr0 hr.2).inv.circleIntegrable_posLog_norm
    simp only [Pi.inv_apply, norm_inv] at h
    exact h
  have hSr : |∫ θ in (0 : ℝ)..2 * π, S.indicator (L r) θ| < ε / 4 + ε / 4 := by
    refine (habs _ (hintr r hr0 hr.2)).trans_lt ?_
    have hdecomp : ∫ θ in (0 : ℝ)..2 * π, S.indicator (|L r ·|) θ =
        (∫ θ in (0 : ℝ)..2 * π, S.indicator (fun θ => Real.posLog ‖Φ (circleMap 0 r θ)‖) θ) +
          ∫ θ in (0 : ℝ)..2 * π, S.indicator
            (fun θ => Real.posLog ‖Φ (circleMap 0 r θ)‖⁻¹) θ := by
      rw [← intervalIntegral.integral_add
        (intervalIntegrable_indicator_of_measurableSet hplusint hSm)
        (intervalIntegrable_indicator_of_measurableSet hminusint hSm)]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      by_cases hθ : θ ∈ S
      · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem hθ, Set.indicator_of_mem hθ]
        exact abs_log_eq_posLog_add_posLog_inv _
      · simp [Set.indicator_of_notMem hθ]
    rw [hdecomp]
    -- the `log⁺` part
    have hplus : ∫ θ in (0 : ℝ)..2 * π, S.indicator
        (fun θ => Real.posLog ‖Φ (circleMap 0 r θ)‖) θ ≤
        ∫ θ in (0 : ℝ)..2 * π, S.indicator D₂ θ := by
      refine intervalIntegral.integral_mono_ae_restrict (by positivity)
        (intervalIntegrable_indicator_of_measurableSet hplusint hSm)
        (intervalIntegrable_indicator_of_measurableSet hD₂int hSm) ?_
      have hae : ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (2 * π))), θ ∈ Set.Ioo 0 (2 * π) := by
        rw [ae_restrict_iff' measurableSet_Icc]
        have hne0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 := by rw [ae_iff]; simp
        have hne2 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 2 * π := by rw [ae_iff]; simp
        filter_upwards [hne0, hne2] with θ h0' h2' hmem
        exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm h0'), lt_of_le_of_ne hmem.2 h2'⟩
      filter_upwards [hae] with θ hθ
      by_cases hθS : θ ∈ S
      · rw [Set.indicator_of_mem hθS, Set.indicator_of_mem hθS]
        have hz : ‖circleMap 0 r θ‖ ≤ 1 := by
          rw [norm_circleMap_zero, abs_of_pos hr0]; exact hr.2.le
        have hz1 := circleMap_zero_ne_one hr0.le hr.2.le hθ
        have := hup₁ _ hz hz1
        have hsin := log_sin_le_log_norm_one_sub_circleMap hr0.le hθ
        simp only [hD₂]
        linarith
      · simp [Set.indicator_of_notMem hθS]
    -- the `log⁻` part
    have hminus : ∫ θ in (0 : ℝ)..2 * π, S.indicator
        (fun θ => Real.posLog ‖Φ (circleMap 0 r θ)‖⁻¹) θ ≤
        2 * π * (4 * η * (A₁ - Real.log c + 2 * Real.log (1 / η))) := by
      rw [integral_sectorAngles_indicator_eq (h := fun z => Real.posLog ‖Φ z‖⁻¹) hr0]
      exact mul_le_mul_of_nonneg_left (circleAverage_indicator_posLog_inv_le hΦ hup₁ hc hx₀ hlow
        hη0 hr.1.le hr.2) (by positivity)
    have h2' : ∫ θ in (0 : ℝ)..2 * π, S.indicator D₂ θ < ε / 4 := (le_abs_self _).trans_lt h2
    have h3' : 2 * π * (4 * η * (A₁ - Real.log c + 2 * Real.log (1 / η))) < ε / 4 :=
      (le_abs_self _).trans_lt h3
    linarith
  -- the sector part at the boundary
  have hS1 : |∫ θ in (0 : ℝ)..2 * π, S.indicator (L 1) θ| < ε / 4 :=
    (habs _ hint1).trans_lt ((le_abs_self _).trans_lt h1)
  set a₁ := ∫ θ in (0 : ℝ)..2 * π, S.indicator (L r) θ
  set b₁ := ∫ θ in (0 : ℝ)..2 * π, Sᶜ.indicator (L r) θ
  set a₂ := ∫ θ in (0 : ℝ)..2 * π, S.indicator (L 1) θ
  set b₂ := ∫ θ in (0 : ℝ)..2 * π, Sᶜ.indicator (L 1) θ
  calc |a₁ + b₁ - (a₂ + b₂)| = |a₁ + -a₂ + (b₁ - b₂)| := by congr 1; ring
    _ ≤ |a₁| + |-a₂| + |b₁ - b₂| := abs_add_three _ _ _
    _ = |a₁| + |a₂| + |b₁ - b₂| := by rw [abs_neg]
    _ < ε / 4 + ε / 4 + ε / 4 + ε / 4 := by linarith
    _ = ε := by ring

/-! ## The Balazard–Saias–Yor equality -/

theorem one_le_norm_zetaDisc_ofReal {x : ℝ} (hx : 1 / 2 ≤ x) (hx1 : x < 1) :
    1 ≤ ‖zetaDisc x‖ := by
  have h1x : 0 < 1 - x := by linarith
  set σ : ℝ := (1 - x)⁻¹ with hσ
  have hσ2 : 2 ≤ σ := by
    rw [hσ, le_inv_comm₀ (by norm_num) h1x]; linarith
  have hs : halfPlaneOfDisc (x : ℂ) = (σ : ℂ) := by
    simp only [halfPlaneOfDisc, hσ]; push_cast; rfl
  have hne : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [zetaDisc, hs, zetaEntire_eq hne, norm_mul]
  have hsub : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have hζ : 1 ≤ ‖riemannZeta (σ : ℂ)‖ :=
    (one_le_re_riemannZeta_ofReal σ (by linarith)).trans (Complex.re_le_norm _)
  rw [hsub]
  nlinarith

theorem circleAverage_log_norm_zetaDisc_one_eq :
    Real.circleAverage (fun w => Real.log ‖zetaDisc w‖) 0 1 =
      (2 * π)⁻¹ * ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) := by
  obtain ⟨hci, -⟩ := circleIntegrable_and_sum_log_le_circleAverage_zetaDisc (U := ∅) (by simp)
  set H : ℝ → ℝ := fun t => Real.log ‖zetaEntire (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) with hH
  have hHeq : (fun t : ℝ => Real.log ‖zetaDisc (circleMap 0 1 (criticalLineAngle t))‖
      / (1 / 4 + t ^ 2)) = H := by
    funext t
    simp only [hH, zetaDisc, halfPlaneOfDisc_circleMap_criticalLineAngle]
  have hHint : Integrable H := by
    have := (circleIntegrable_iff_integrable_criticalLine _).mp hci
    rwa [hHeq] at this
  obtain ⟨hWint, hW0⟩ := integrable_and_integral_log_criticalLine_weight
  have hcount : {t : ℝ | riemannZeta (1 / 2 + t * I) = 0}.Countable := by
    have hinj : Function.Injective (fun t : ℝ => (1 / 2 : ℂ) + t * I) := by
      intro a b hab
      have := congrArg Complex.im hab
      simpa using this
    refine (countable_setOf_zetaEntire_eq_zero.preimage hinj).mono fun t ht => ?_
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at ht ⊢
    have hne : (1 / 2 : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; norm_num at this
    rw [zetaEntire_eq hne, ht, mul_zero]
  have hae : ∀ᵐ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)
      = H t - (1 / 2) * (Real.log (1 / 4 + t ^ 2) / (1 / 4 + t ^ 2)) := by
    have h0 : volume {t : ℝ | riemannZeta (1 / 2 + t * I) = 0} = 0 := hcount.measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with t ht
    have hne : (1 / 2 : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; norm_num at this
    have hsub : (1 / 2 : ℂ) + t * I - 1 ≠ 0 := sub_ne_zero.mpr hne
    simp only [hH]
    rw [zetaEntire_eq hne, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hsub)
      (norm_ne_zero_iff.mpr ht), norm_half_add_mul_I_sub_one, Real.log_sqrt (by positivity)]
    ring
  have hZeq : ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) = ∫ t, H t := by
    rw [integral_congr_ae hae, integral_sub hHint (hWint.const_mul (1 / 2)), integral_const_mul,
      hW0, mul_zero, sub_zero]
  rw [hZeq, circleAverage_eq_integral_criticalLine, hHeq]

/-- **The Balazard–Saias–Yor equality.**  As `r → 1⁻`, the circle averages of `log |G|`,
`G(w) = (s − 1)ζ(s)` at `s = 1/(1 − w)`, converge to
`(1/2π) ∫ log |ζ(½ + it)| dt/(¼ + t²)`.  By Jensen's formula the circle average at radius `r` is
`Σ_{|u| < r} m_u log(r/|u|)` over the zeros `u = 1 − 1/ρ` of `G`, i.e. over the zeros `ρ` of
`ζ` with `Re ρ > ½` and `|ρ − 1| < r|ρ|`; so the integral is exactly the multiplicity-weighted sum
of `log(|ρ|/|ρ − 1|)` over all zeros off the critical line. -/
theorem tendsto_circleAverage_log_norm_zetaDisc :
    Tendsto (fun r => Real.circleAverage (fun w => Real.log ‖zetaDisc w‖) 0 r) (𝓝[<] 1)
      (𝓝 ((2 * π)⁻¹ * ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2))) := by
  obtain ⟨A, -, hA⟩ := exists_log_norm_zetaDisc_le
  have h := tendsto_integral_log_norm_circleMap_nhdsLT_one differentiableOn_zetaDisc
    measurable_zetaDisc (by rw [zetaDisc_zero]; exact one_ne_zero) hA one_pos
    le_rfl (by norm_num) fun x hx hx1 => one_le_norm_zetaDisc_ofReal hx hx1
  rw [← circleAverage_log_norm_zetaDisc_one_eq, Real.circleAverage_def]
  simp only [Real.circleAverage_def, smul_eq_mul]
  exact h.const_mul _

/-- **Jensen form of the equality.**  The Jensen zero sums of `G` on the discs `|w| ≤ r` converge to
the Balazard–Saias–Yor integral as `r → 1⁻`. -/
theorem tendsto_jensenSum_zetaDisc :
    Tendsto (fun r : ℝ => ∑ᶠ u, (MeromorphicOn.divisor zetaDisc (closedBall (0 : ℂ) |r|) u : ℝ) *
        Real.log (r * ‖0 - u‖⁻¹)) (𝓝[<] 1)
      (𝓝 ((2 * π)⁻¹ * ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2))) := by
  refine tendsto_circleAverage_log_norm_zetaDisc.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hr0 : r ≠ 0 := hr.1.ne'
  have han : AnalyticOnNhd ℂ zetaDisc (closedBall 0 |r|) := by
    rw [abs_of_pos hr.1]; exact analyticOnNhd_zetaDisc_closedBall hr.2
  rw [han.circleAverage_log_norm hr0 (by rw [zetaDisc_zero]; exact one_ne_zero), zetaDisc_zero,
    norm_one, Real.log_one, add_zero]

end

end RHTower
