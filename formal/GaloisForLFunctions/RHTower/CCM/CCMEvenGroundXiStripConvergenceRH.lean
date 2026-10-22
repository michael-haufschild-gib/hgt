import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilEvenSectorCrossZeros
import GaloisForLFunctions.HTGeometry.HurwitzClosedZeroLocus
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Convergence of cross-rooted CCM ground transforms to `Ξ` on the strip implies RH

In centered coordinates `XiC(z) = ξ(½ + iz)`, the nontrivial zeros of `ζ` are the zeros of `XiC` in
the strip `|Im z| < ½`.  For a form-domain vector `u` at aperture `a`, put
`F_u(z) = f̂_u(z/(2π))` (`unitaryLaplace (timeRep a u)`), so that the polar points `w_{±1/2}` sit at
`z = ±i/2`, on the boundary of the strip.

**Theorem** (`riemannHypothesis_of_crossRooted_strip_convergence`).  Let `u_n` be vectors at
apertures `a_n` whose transforms have all zeros other than `w_{±1/2}` on `ℝ ∪ iℝ`.  If `c_n F_{u_n}`
converges to `XiC` locally uniformly on the open strip `|Im z| < ½`, then RH holds.

By `exists_crossRooted_evenGround` such vectors exist at every aperture: even-sector polar ground
states.  Their transforms vanish at `±i/2`, so for them the receiver must be applied to the
quotient by `z² + 1/4` (see `CrossRootedPolarZeroXiStripObstruction`); the theorem below applies
directly to vectors whose transforms do not vanish at the polar points.

**Proof.**
* Transforms of compactly supported integrable functions are entire
  (`differentiable_unitaryLaplace`).
* Local Hurwitz (`zero_mem_closed_of_tendstoLocallyUniformlyOn`): on an open preconnected set, a
  locally uniform limit that is analytic and not identically zero has its zeros in every closed set
  containing the approximants' zeros (sphere domination on a small ball inside the set).
* The approximants' zeros in the strip lie on the closed cross `{(z²).im = 0}`.  A zero of `XiC` on
  the cross is real (`XiC_im_eq_zero_of_sq_im_eq_zero`, `ξ` has no real zeros), and a zero of `ξ`
  with `Re s > ½` has `Re s < 1`, so its centered point lies in the strip.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real

namespace RHTower.CCMXiStrip

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FourierZeroFlip
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open RHTower.CCMRealRootedGround

/-! ## Entire transforms -/

/-- The Fourier–Laplace transform of an integrable function supported in `[-A, A]` is entire. -/
theorem differentiable_unitaryLaplace {A : ℝ} (hA : 0 ≤ A) {f : ℝ → ℂ} (hf : Integrable f)
    (hs : SupportedIn A f) : Differentiable ℂ (unitaryLaplace f) := by
  intro w₀
  set F : ℂ → ℝ → ℂ := fun w x => cexp (-(2 * π * I * w * x)) * f x with hF
  set F' : ℂ → ℝ → ℂ := fun w x => (-(2 * π * I * x)) * cexp (-(2 * π * I * w * x)) * f x
    with hF'
  set bound : ℝ → ℝ := fun x => 2 * π * A * Real.exp (2 * π * (|w₀.im| + 1) * A) * ‖f x‖
    with hbound
  have hball : Metric.ball w₀ 1 ∈ 𝓝 w₀ := Metric.ball_mem_nhds w₀ one_pos
  have hmeas : ∀ w, AEStronglyMeasurable (F w) volume := fun w =>
    ((by fun_prop : Continuous fun x : ℝ => cexp (-(2 * π * I * w * x))).aestronglyMeasurable).mul
      hf.1
  have hF'meas : AEStronglyMeasurable (F' w₀) volume :=
    ((by fun_prop : Continuous fun x : ℝ =>
      (-(2 * π * I * x)) * cexp (-(2 * π * I * w₀ * x))).aestronglyMeasurable).mul hf.1
  have hbound_le : ∀ᵐ x ∂volume, ∀ w ∈ Metric.ball w₀ 1, ‖F' w x‖ ≤ bound x := by
    refine Eventually.of_forall fun x w hw => ?_
    by_cases hx : x ∈ Icc (-A) A
    · have hwim : |w.im| ≤ |w₀.im| + 1 := by
        have h1 : |(w - w₀).im| ≤ ‖w - w₀‖ := Complex.abs_im_le_norm _
        rw [Complex.sub_im] at h1
        have h2 : dist w w₀ < 1 := Metric.mem_ball.mp hw
        rw [dist_eq_norm] at h2
        have h3 := abs_sub_abs_le_abs_sub w.im w₀.im
        linarith
      have hexp := norm_cexp_le_of_mem_Icc (a := A) w hx
      have hexp' : Real.exp (2 * π * |w.im| * A) ≤ Real.exp (2 * π * (|w₀.im| + 1) * A) := by
        apply Real.exp_le_exp.mpr
        have hπ2 : 0 ≤ 2 * π := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwim hπ2) hA
      have hxA : |x| ≤ A := abs_le.mpr ⟨hx.1, hx.2⟩
      have hnx : ‖(-(2 * π * I * (x : ℂ)))‖ ≤ 2 * π * A := by
        rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        norm_num
        have := Real.pi_pos
        nlinarith
      simp only [hF', hbound, norm_mul]
      have hfx := norm_nonneg (f x)
      have hc := norm_nonneg (cexp (-(2 * π * I * w * x)))
      have h2pA : 0 ≤ 2 * π * A := by positivity
      calc ‖(-(2 * π * I * (x : ℂ)))‖ * ‖cexp (-(2 * π * I * w * x))‖ * ‖f x‖
          ≤ (2 * π * A) * Real.exp (2 * π * (|w₀.im| + 1) * A) * ‖f x‖ := by
            gcongr
            exact hexp.trans hexp'
        _ = 2 * π * A * Real.exp (2 * π * (|w₀.im| + 1) * A) * ‖f x‖ := by ring
    · simp only [hF', hbound, hs x hx, mul_zero, norm_zero, le_refl]
  have hbound_int : Integrable bound volume := hf.norm.const_mul _
  have hderiv : ∀ᵐ x ∂volume, ∀ w ∈ Metric.ball w₀ 1,
      HasDerivAt (fun w => F w x) (F' w x) w := by
    refine Eventually.of_forall fun x w _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => -(2 * π * I * w * x)) (-(2 * π * I * x)) w := by
      have h := (hasDerivAt_id' w).const_mul (-(2 * π * I * (x : ℂ)))
      rw [mul_one] at h
      have heq : (fun w : ℂ => -(2 * π * I * w * x)) = fun w : ℂ => -(2 * π * I * x) * w := by
        funext v; ring
      rw [heq]
      exact h
    have h2 := (h1.cexp).mul_const (f x)
    simpa [hF, hF', mul_comm, mul_assoc, mul_left_comm] using h2
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (x₀ := w₀) (bound := bound) hball (Eventually.of_forall hmeas)
    (integrable_exp_mul_of_supportedIn hf hs w₀) hF'meas hbound_le hbound_int hderiv
  exact h.2.differentiableAt

/-! ## Local Hurwitz on an open set -/

/-- **Local Hurwitz closed-locus transfer.** -/
theorem zero_mem_closed_of_tendstoLocallyUniformlyOn {F : ℂ → ℂ} {Fn : ℕ → ℂ → ℂ} {U S : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hconv : TendstoLocallyUniformlyOn Fn F atTop U) (hF : AnalyticOnNhd ℂ F U)
    (hFn : ∀ᶠ n in atTop, DifferentiableOn ℂ (Fn n) U) (hS : IsClosed S)
    (hzeroS : ∀ᶠ n in atTop, ∀ w ∈ U, Fn n w = 0 → w ∈ S)
    {b z : ℂ} (hb : b ∈ U) (hFb : F b ≠ 0) (hz : z ∈ U) (hFz : F z = 0) : z ∈ S := by
  rw [← hS.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hnotEventuallyZero : ¬ ∀ᶠ w in 𝓝 z, F w = 0 := by
    intro hev
    exact hFb (hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz hev hb)
  have hpunct : ∀ᶠ w in 𝓝[≠] z, F w ≠ 0 :=
    (hF z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnotEventuallyZero
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  obtain ⟨η, hη, hηU⟩ := Metric.isOpen_iff.mp hU z hz
  set r : ℝ := min (min (ε / 2) (δ / 2)) (η / 2) with hrdef
  have hr : 0 < r := lt_min (lt_min (half_pos hε) (half_pos hδ)) (half_pos hη)
  have hrε : r < ε := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (half_lt_self hε)
  have hrδ : r < δ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (half_lt_self hδ)
  have hrη : r < η := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hη)
  have hballU : closedBall z r ⊆ U := (closedBall_subset_ball hrη).trans hηU
  have hsphere : ∀ w ∈ sphere z r, F w ≠ 0 := by
    intro w hw
    apply hδsub
    refine ⟨Metric.mem_ball.mpr ((Metric.mem_sphere.mp hw).trans_lt hrδ), ?_⟩
    exact Set.mem_compl_singleton_iff.mpr (Metric.ne_of_mem_sphere hw hr.ne')
  have hsphU : sphere z r ⊆ U := sphere_subset_closedBall.trans hballU
  have hsphereNonempty : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hFcont : ContinuousOn F U := hF.continuousOn
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere z r).exists_isMinOn hsphereNonempty
    ((hFcont.mono hsphU).norm)
  have hminPos : 0 < ‖F w₀‖ := norm_pos_iff.mpr (hsphere w₀ hw₀)
  have hconvSphere : TendstoUniformlyOn Fn F atTop (sphere z r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv _ hsphU (isCompact_sphere z r)
  have hclose : ∀ᶠ n in atTop, ∀ w ∈ sphere z r, dist (F w) (Fn n w) < ‖F w₀‖ / 3 :=
    (Metric.tendstoUniformlyOn_iff.mp hconvSphere) (‖F w₀‖ / 3) (div_pos hminPos (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hFn.and (hclose.and hzeroS))
  obtain ⟨hdn, hcl, hzs⟩ := hN N le_rfl
  have hFd : DifferentiableOn ℂ F (closedBall z r) :=
    fun w hw => (hF w (hballU hw)).differentiableAt.differentiableWithinAt
  have hFnd : DifferentiableOn ℂ (Fn N) (closedBall z r) := hdn.mono hballU
  by_cases hnz : Fn N z = 0
  · exact ⟨z, hzs z hz hnz, by rw [dist_self]; exact hε⟩
  · let g : ℂ → ℂ := fun w => Fn N w - F w
    have hgd : DiffContOnCl ℂ g (ball z r) := (hFnd.sub hFd).diffContOnCl_ball (le_refl _)
    have hFdc : DiffContOnCl ℂ F (ball z r) := hFd.diffContOnCl_ball (le_refl _)
    have hg0 : g z ≠ 0 := by simp only [g, hFz, sub_zero]; exact hnz
    have hdom : ∀ w ∈ sphere z r, 3 * ‖g w‖ ≤ ‖F w‖ := by
      intro w hw
      have hcloseW := hcl w hw
      have hminW := hmin hw
      change ‖F w₀‖ ≤ ‖F w‖ at hminW
      have hnorm : ‖g w‖ = dist (F w) (Fn N w) := by
        simp only [g, dist_eq_norm]; rw [norm_sub_rev]
      rw [hnorm]
      nlinarith
    obtain ⟨w, hw, hwzero⟩ := exists_zero_of_sphere_domination hr hgd hFdc hFz hg0 hdom
    have hw0 : Fn N w = 0 := by simpa only [g, sub_add_cancel] using hwzero
    refine ⟨w, hzs w (hballU hw) hw0, ?_⟩
    have hdist : dist z w ≤ r := by simpa [dist_comm] using Metric.mem_closedBall.mp hw
    exact hdist.trans_lt hrε

/-! ## The strip receiver -/

/-- The centered critical strip `|Im z| < ½`. -/
def centeredStrip : Set ℂ := {z | |z.im| < 1 / 2}

theorem isOpen_centeredStrip : IsOpen centeredStrip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem isPreconnected_centeredStrip : IsPreconnected centeredStrip := by
  have hconv : Convex ℝ centeredStrip := by
    intro x hx y hy s t hs ht hst
    simp only [centeredStrip, mem_setOf_eq] at hx hy ⊢
    have him : (s • x + t • y).im = s * x.im + t * y.im := by
      simp
    rw [him]
    calc |s * x.im + t * y.im| ≤ |s * x.im| + |t * y.im| := abs_add_le _ _
      _ = s * |x.im| + t * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ < 1 / 2 := by
        rcases eq_or_lt_of_le hs with h | h
        · rw [← h] at hst ⊢; rw [zero_add] at hst; rw [hst]; linarith
        · nlinarith
  exact hconv.isPreconnected

/-- **CCM approximants with zeros on `ℝ ∪ iℝ` converging to `Ξ` on the strip prove RH.** -/
theorem riemannHypothesis_of_crossRooted_strip_convergence
    (a : ℕ → SuzukiPositiveAperture) (u : ∀ n, CCMArchimedeanFormDomain (a n)) (c : ℕ → ℂ)
    (hcross : ∀ n, ∀ w : ℂ, unitaryLaplace (timeRep (a n) (u n)) w = 0 →
      w ≠ polarPoint (1 / 2) → w ≠ polarPoint (-1 / 2) → w.re = 0 ∨ w.im = 0)
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => c n * unitaryLaplace (timeRep (a n) (u n)) (z / (2 * π))) XiC atTop
      centeredStrip) :
    RiemannHypothesis := by
  set Fn : ℕ → ℂ → ℂ := fun n z => c n * unitaryLaplace (timeRep (a n) (u n)) (z / (2 * π))
    with hFn
  set S : Set ℂ := {z | (z ^ 2).im = 0} with hSdef
  have hS : IsClosed S := isClosed_eq (Complex.continuous_im.comp (continuous_pow 2))
    continuous_const
  have h0 : (0 : ℂ) ∈ centeredStrip := by simp [centeredStrip]
  have hdiff : ∀ n, Differentiable ℂ (Fn n) := by
    intro n
    have hd := differentiable_unitaryLaplace (a n).2.le (integrable_timeRep (a n) (u n))
      (supportedIn_timeRep (a n) (u n))
    exact (hd.comp (differentiable_id.div_const _)).const_mul (c n)
  -- eventually `c n ≠ 0`
  have hc : ∀ᶠ n in atTop, c n ≠ 0 := by
    have hpt : Tendsto (fun n => Fn n 0) atTop (𝓝 (XiC 0)) :=
      hconv.tendsto_at h0
    have hne : ∀ᶠ n in atTop, Fn n 0 ≠ 0 := hpt.eventually_ne XiC_zero_ne
    filter_upwards [hne] with n hn hc0
    apply hn
    simp only [hFn, hc0, zero_mul]
  have hzeroS : ∀ᶠ n in atTop, ∀ w ∈ centeredStrip, Fn n w = 0 → w ∈ S := by
    filter_upwards [hc] with n hcn w hw hzero
    have hT : unitaryLaplace (timeRep (a n) (u n)) (w / (2 * π)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hcn
    have hπ : (2 * π : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * π := by positivity
      exact_mod_cast this.ne'
    have hpol : ∀ s : ℝ, |s| = 1 / 2 → w / (2 * π) ≠ polarPoint s := by
      intro s hs heq
      have hw' : w = I * s := by
        rw [div_eq_iff hπ] at heq
        rw [heq, polarPoint]
        field_simp
      have hwim : w.im = s := by rw [hw']; simp
      simp only [centeredStrip, mem_setOf_eq] at hw
      rw [hwim, hs] at hw
      exact lt_irrefl _ hw
    have hcr := hcross n _ hT (hpol (1 / 2) (by norm_num [abs_of_pos]))
      (hpol (-1 / 2) (by norm_num [abs_of_neg]))
    show (w ^ 2).im = 0
    have hre : (w / (2 * π)).re = w.re / (2 * π) := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
    have him : (w / (2 * π)).im = w.im / (2 * π) := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im]
    have hpos : (0 : ℝ) < 2 * π := by positivity
    rw [sq, Complex.mul_im]
    rcases hcr with h | h
    · rw [hre, div_eq_zero_iff] at h
      rcases h with h | h
      · rw [h]; ring
      · exact absurd h hpos.ne'
    · rw [him, div_eq_zero_iff] at h
      rcases h with h | h
      · rw [h]; ring
      · exact absurd h hpos.ne'
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  let z : ℂ := (ρ - 1 / 2) * (-I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = ρ := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have hzIm : z.im = 1 / 2 - ρ.re := by simp [z]
  have hρ1 : ρ.re < 1 := by
    by_contra hge
    exact xi_ne_zero_of_one_le_re (not_lt.mp hge) hzero
  have hρh : 1 / 2 < ρ.re := mem_rightHalf.mp hρ
  have hzU : z ∈ centeredStrip := by
    simp only [centeredStrip, mem_setOf_eq, hzIm]
    rw [abs_lt]
    constructor <;> linarith
  have hzS : z ∈ S := zero_mem_closed_of_tendstoLocallyUniformlyOn isOpen_centeredStrip
    isPreconnected_centeredStrip hconv (fun w _ => XiC_analytic w (Set.mem_univ w))
    (Eventually.of_forall fun n => (hdiff n).differentiableOn) hS hzeroS h0 XiC_zero_ne hzU hXiC
  have hzreal : z.im = 0 := XiC_im_eq_zero_of_sq_im_eq_zero hXiC hzS
  have hre : ρ.re = 1 / 2 := by linarith [hzreal, hzIm]
  exact (ne_of_gt hρh) hre

/-- Even-sector polar ground states with cross-rooted transforms whose normalized transforms
converge to `Ξ` on the strip give RH.  The hypotheses cannot hold together, since these transforms
vanish at `±i/2` (`RHTower.CCMPolarObstruction.not_evenGround_strip_convergence`). -/
theorem riemannHypothesis_of_evenGround_strip_convergence
    (a : ℕ → SuzukiPositiveAperture) (u : ∀ n, CCMArchimedeanFormDomain (a n)) (c : ℕ → ℂ)
    (hground : ∀ n, RHTower.CCMEvenSector.IsEvenGround (a n) (u n) ∧
      ∀ w : ℂ, unitaryLaplace (timeRep (a n) (u n)) w = 0 →
        w ≠ polarPoint (1 / 2) → w ≠ polarPoint (-1 / 2) → w.re = 0 ∨ w.im = 0)
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => c n * unitaryLaplace (timeRep (a n) (u n)) (z / (2 * π))) XiC atTop
      centeredStrip) :
    RiemannHypothesis :=
  riemannHypothesis_of_crossRooted_strip_convergence a u c (fun n => (hground n).2) hconv

end RHTower.CCMXiStrip
