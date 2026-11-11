import GaloisForLFunctions.HTGeometry.JordanWindowArgumentPrinciple
import GaloisForLFunctions.PrimeTorusTheory.TheHullOverTheTorus

/-!
# Holomorphic disc deformations of a pure divisor

Boundary fibres whose zeros lie on one vertical line extend purity to the
closed parameter disc when zero-free anchors lie on both sides. Hurwitz then
forces every fibre to have the same zero set. This is the analytic step for
contracting prime coordinates while preserving a pure Dirichlet divisor.
-/

open Complex Metric Set Filter Topology

noncomputable section
namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open GaloisForLFunctions.HTGeometry

private theorem realPart_isLinear : IsLinearMap ℝ Complex.re :=
  ⟨Complex.reLm.map_add, Complex.reLm.map_smul⟩

/-- Boundary values lying in a disc that avoids zero give a zero-free analytic
parameter disc. -/
theorem unitDisc_ne_zero_of_boundary_close
    {f : ℂ → ℂ} (han : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1))
    (hcont : ContinuousOn f (closedBall (0 : ℂ) 1))
    {b : ℂ} {r : ℝ} (hr : r < ‖b‖)
    (hboundary : ∀ w ∈ sphere (0 : ℂ) 1, ‖f w - b‖ ≤ r)
    {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) : f w ≠ 0 := by
  have hdc : DiffContOnCl ℂ (fun w => f w - b) (ball (0 : ℂ) 1) := by
    constructor
    · exact han.differentiableOn.sub_const b
    · rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
      exact hcont.sub continuousOn_const
  have hnorm : ‖f w - b‖ ≤ r :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc
      (by simpa only [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hboundary)
      (by rwa [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)])
  intro hz
  rw [hz, zero_sub, norm_neg] at hnorm
  exact (not_le_of_gt hr) hnorm

/-- A continuous homotopy of analytic discs cannot acquire an interior zero
without a boundary zero. -/
theorem unitDisc_ne_zero_of_continuous_homotopy
    {H : ℝ → ℂ → ℂ}
    (hcont : Continuous fun p : ℝ × ↥(closedBall (0 : ℂ) 1) => H p.1 p.2)
    (han : ∀ t, AnalyticOnNhd ℂ (H t) (ball (0 : ℂ) 1))
    (hboundary : ∀ t w, w ∈ sphere (0 : ℂ) 1 → H t w ≠ 0)
    (hstart : ∀ w ∈ ball (0 : ℂ) 1, H 0 w ≠ 0)
    (t : ℝ) {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) : H t w ≠ 0 := by
  have hfc (u : ℝ) : ContinuousOn (H u) (closedBall (0 : ℂ) 1) := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact hcont.comp (continuous_const.prodMk continuous_id)
  have hcircle (θ : ℝ) : exp (I * (θ : ℂ)) ∈ sphere (0 : ℂ) 1 := by
    simp [Complex.norm_exp]
  let circle : ℝ → ↥(closedBall (0 : ℂ) 1) := fun θ =>
    ⟨exp (I * (θ : ℂ)), sphere_subset_closedBall (hcircle θ)⟩
  have hcc : Continuous circle := by
    apply Continuous.subtype_mk
    fun_prop
  have hloops : ∀ u, H u (exp (I * (0 : ℂ))) =
      H u (exp (I * ((2 * Real.pi : ℝ) : ℂ))) := by
    intro u
    have he : exp (I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show I * ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * I by push_cast; ring]
      exact Complex.exp_two_pi_mul_I
    simp only [mul_zero, Complex.exp_zero, he]
  have hwind := RHTower.windingNumber_homotopy_invariant
    (H := fun u θ => H u (exp (I * (θ : ℂ))))
    (hcont.comp (continuous_fst.prodMk (hcc.comp continuous_snd)))
    (fun u θ => hboundary u _ (hcircle θ)) hloops 0 t
  rw [windingNumber_unitCircle_eq_unitDiscZeroMultiplicity
      (han 0) (hfc 0) (hboundary 0),
    windingNumber_unitCircle_eq_unitDiscZeroMultiplicity
      (han t) (hfc t) (hboundary t)] at hwind
  have hcount0 : unitDiscZeroMultiplicity (H 0) = 0 :=
    (unitDiscZeroMultiplicity_eq_zero_iff (han 0) (hfc 0) (hboundary 0)).mpr hstart
  have hcount : unitDiscZeroMultiplicity (H t) = 0 := by
    rw [hcount0] at hwind
    exact_mod_cast hwind.symm
  rcases eq_or_lt_of_le (mem_closedBall.mp hw) with heq | hlt
  · exact hboundary t w (mem_sphere.mpr heq)
  · exact (unitDiscZeroMultiplicity_eq_zero_iff
      (han t) (hfc t) (hboundary t)).mp hcount w (mem_ball.mpr hlt)

/-- Over a convex parameter domain, boundary nonvanishing and one zero-free
disc suffice for nonvanishing on every closed disc. -/
theorem unitDisc_ne_zero_of_convex_parameter
    {U : Set ℂ} (hU : Convex ℝ U) {G : ℂ → ℂ → ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2)
      (U ×ˢ closedBall (0 : ℂ) 1))
    (han : ∀ s ∈ U, AnalyticOnNhd ℂ (G s) (ball (0 : ℂ) 1))
    (hboundary : ∀ s ∈ U, ∀ w ∈ sphere (0 : ℂ) 1, G s w ≠ 0)
    {a : ℂ} (ha : a ∈ U)
    (hstart : ∀ w ∈ ball (0 : ℂ) 1, G a w ≠ 0)
    {s w : ℂ} (hs : s ∈ U) (hw : w ∈ closedBall (0 : ℂ) 1) : G s w ≠ 0 := by
  let clamp : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hclamp (t : ℝ) : 0 ≤ clamp t ∧ clamp t ≤ 1 := by
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hclampc : Continuous clamp :=
    continuous_const.max (continuous_const.min continuous_id)
  let path : ℝ → ℂ := fun t => (1 - clamp t) • a + clamp t • s
  have hpathc : Continuous path := by
    exact ((continuous_const.sub hclampc).smul continuous_const).add
      (hclampc.smul continuous_const)
  have hpath (t : ℝ) : path t ∈ U :=
    hU ha hs (by linarith [(hclamp t).2]) (hclamp t).1 (by ring)
  have hc : Continuous fun p : ℝ × ↥(closedBall (0 : ℂ) 1) => G (path p.1) p.2 := by
    exact hcont.comp_continuous
      ((hpathc.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
      (fun p => ⟨hpath p.1, p.2.property⟩)
  have h := unitDisc_ne_zero_of_continuous_homotopy hc
    (fun t => han _ (hpath t)) (fun t z hz => hboundary _ (hpath t) z hz)
    (by simpa [path, clamp] using hstart) 1 hw
  simpa [path, clamp] using h

/-- Joint continuity gives locally uniform convergence when the first parameter
converges inside its domain. -/
theorem tendstoLocallyUniformlyOn_of_continuousOn_parameter
    {A U : Set ℂ} (hU : IsOpen U) {G : ℂ → ℂ → ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2) (A ×ˢ U))
    {u : ℕ → ℂ} {a : ℂ} (hu : Tendsto u atTop (𝓝 a))
    (huA : ∀ n, u n ∈ A) (ha : a ∈ A) :
    TendstoLocallyUniformlyOn (fun n => G (u n)) (G a) atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨v, hv, hvG⟩ := hK.mem_uniformity_of_prod
    (hcont.mono (Set.prod_mono Subset.rfl hKU)) ha (dist_mem_uniformity hε)
  have huw : Tendsto u atTop (𝓝[A] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu, Eventually.of_forall huA⟩
  filter_upwards [huw.eventually hv] with n hn z hz
  have hh : dist (G (u n) z) (G a z) < ε := hvG (u n) hn z hz
  simpa only [dist_comm] using hh

/-- If every parameter fibre has zeros only on one vertical line, an interior
parameter zero forces the entire parameter disc to vanish at that point. -/
theorem eq_zero_on_unitDisc_of_pure_family
    {x c : ℝ} {G : ℂ → ℂ → ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2)
      ({s : ℂ | x < s.re} ×ˢ closedBall (0 : ℂ) 1))
    (han : ∀ s, x < s.re → AnalyticOnNhd ℂ (G s) (ball (0 : ℂ) 1))
    (hpure : ∀ s, x < s.re → ∀ w ∈ closedBall (0 : ℂ) 1,
      G s w = 0 → s.re = c)
    {s w : ℂ} (hs : x < s.re) (hw : w ∈ ball (0 : ℂ) 1)
    (hz : G s w = 0) : ∀ v ∈ closedBall (0 : ℂ) 1, G s v = 0 := by
  have hsc : s.re = c := hpure s hs w (ball_subset_closedBall hw) hz
  let u : ℕ → ℂ := fun n => s + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hu_pos (n : ℕ) : 0 < (1 / ((n : ℝ) + 1) : ℝ) := by positivity
  have hu_re (n : ℕ) : (u n).re = s.re + 1 / ((n : ℝ) + 1) := by
    simp only [u, Complex.add_re, Complex.ofReal_re]
  have huA (n : ℕ) : x < (u n).re := by rw [hu_re]; linarith [hu_pos n]
  have hulim : Tendsto u atTop (𝓝 s) := by
    have h := (tendsto_const_nhds (x := s)).add
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    simpa only [u, Function.comp_apply, Complex.ofReal_zero, add_zero] using h
  have hconv := tendstoLocallyUniformlyOn_of_continuousOn_parameter isOpen_ball
    (hcont.mono (Set.prod_mono Subset.rfl ball_subset_closedBall)) hulim huA hs
  have hne (n : ℕ) (v : ℂ) (hv : v ∈ ball (0 : ℂ) 1) : G (u n) v ≠ 0 := by
    intro hvz
    have h := hpure (u n) (huA n) v (ball_subset_closedBall hv) hvz
    rw [hu_re, hsc] at h
    linarith [hu_pos n]
  have he := PrimeTorusTheory.eventually_eq_zero_of_limit isOpen_ball hconv
    (fun n => (han (u n) (huA n)).differentiableOn)
    (han s hs).differentiableOn hne hw hz
  have hball : EqOn (G s) 0 (ball (0 : ℂ) 1) :=
    (han s hs).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) 1).isPreconnected hw he
  have hc : ContinuousOn (G s) (closedBall (0 : ℂ) 1) := by
    exact hcont.comp (continuousOn_const.prodMk continuousOn_id)
      (fun v hv => ⟨hs, hv⟩)
  exact hball.of_subset_closure hc continuousOn_const ball_subset_closedBall
    (by rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)])

/-- A pure holomorphic family has the same zero set at every point of the
closed parameter disc. The boundary follows from Hurwitz in the other variable. -/
theorem unitDisc_zero_iff_center_of_pure_family
    {x c : ℝ} {G : ℂ → ℂ → ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2)
      ({s : ℂ | x < s.re} ×ˢ closedBall (0 : ℂ) 1))
    (han : ∀ s, x < s.re → AnalyticOnNhd ℂ (G s) (ball (0 : ℂ) 1))
    (hans : ∀ w ∈ closedBall (0 : ℂ) 1,
      AnalyticOnNhd ℂ (fun s => G s w) {s : ℂ | x < s.re})
    (hpure : ∀ s, x < s.re → ∀ w ∈ closedBall (0 : ℂ) 1,
      G s w = 0 → s.re = c)
    {s w : ℂ} (hs : x < s.re) (hw : w ∈ closedBall (0 : ℂ) 1) :
    G s w = 0 ↔ G s 0 = 0 := by
  have h0ball : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self zero_lt_one
  have h0closed := ball_subset_closedBall h0ball
  constructor
  · intro hz
    by_contra h0
    have hU : IsOpen {z : ℂ | x < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hev : ∀ᶠ z in 𝓝 s, x < z.re ∧ G z 0 ≠ 0 := by
      have hUevent : ∀ᶠ z in 𝓝 s, x < z.re := hU.mem_nhds hs
      exact hUevent.and
        ((hans 0 h0closed s hs).continuousAt.eventually
          (isOpen_compl_singleton.mem_nhds h0))
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
    let u : ℕ → ℂ := fun n => (1 - 1 / ((n : ℝ) + 1)) • w
    have hq (n : ℕ) : 0 < (1 / ((n : ℝ) + 1) : ℝ) ∧
        (1 / ((n : ℝ) + 1) : ℝ) ≤ 1 := by
      constructor
      · positivity
      · exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hu (n : ℕ) : u n ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right]
      have hn : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := sub_nonneg.mpr (hq n).2
      calc
        ‖u n‖ = (1 - 1 / ((n : ℝ) + 1)) * ‖w‖ := by
          dsimp only [u]
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
        _ ≤ (1 - 1 / ((n : ℝ) + 1)) * 1 :=
          mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_zero_right] using hw) hn
        _ < 1 := by linarith [(hq n).1]
    have hulim : Tendsto u atTop (𝓝 w) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).smul
        (tendsto_const_nhds (x := w))
      simpa only [u, sub_zero, one_smul] using h
    have hswap : ContinuousOn (fun p : ℂ × ℂ => G p.2 p.1)
        (closedBall (0 : ℂ) 1 ×ˢ ball s r) := by
      exact hcont.comp continuous_swap.continuousOn
        (fun p hp => ⟨(hball hp.2).1, hp.1⟩)
    have hconv := tendstoLocallyUniformlyOn_of_continuousOn_parameter
      (G := fun v z => G z v) (U := ball s r) isOpen_ball
      hswap hulim (fun n => ball_subset_closedBall (hu n)) hw
    have hne (n : ℕ) (z : ℂ) (hzr : z ∈ ball s r) : G z (u n) ≠ 0 := by
      intro hz0
      exact (hball hzr).2
        (eq_zero_on_unitDisc_of_pure_family hcont han hpure
          (hball hzr).1 (hu n) hz0 0 h0closed)
    have he := PrimeTorusTheory.eventually_eq_zero_of_limit isOpen_ball hconv
      (fun n => (hans (u n) (ball_subset_closedBall (hu n))).differentiableOn.mono
        (fun z hz => (hball hz).1))
      ((hans w hw).differentiableOn.mono (fun z hz => (hball hz).1))
      hne (mem_ball_self hr) hz
    have hpre : IsPreconnected {z : ℂ | x < z.re} :=
      (convex_halfSpace_gt realPart_isLinear x).isPreconnected
    have hall := (hans w hw).eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hs he
    have ha : x < ((max x c + 1 : ℝ) : ℂ).re := by
      simp only [Complex.ofReal_re]
      linarith [le_max_left x c]
    have hbad := hpure _ ha w hw (hall ha)
    simp only [Complex.ofReal_re] at hbad
    linarith [le_max_right x c]
  · intro hz
    exact eq_zero_on_unitDisc_of_pure_family hcont han hpure hs h0ball hz w hw

/-- Purity on the parameter circle extends to the closed disc when one zero-free
anchor is available on each side of the vertical line. -/
theorem unitDisc_pure_of_boundary_and_anchors
    {x c : ℝ} (hxc : x < c) {G : ℂ → ℂ → ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2)
      ({s : ℂ | x < s.re} ×ˢ closedBall (0 : ℂ) 1))
    (han : ∀ s, x < s.re → AnalyticOnNhd ℂ (G s) (ball (0 : ℂ) 1))
    (hboundary : ∀ s, x < s.re → ∀ w ∈ sphere (0 : ℂ) 1,
      G s w = 0 → s.re = c)
    {a b : ℂ} (ha : x < a.re) (hac : a.re < c) (hb : c < b.re)
    (hleft : ∀ w ∈ ball (0 : ℂ) 1, G a w ≠ 0)
    (hright : ∀ w ∈ ball (0 : ℂ) 1, G b w ≠ 0)
    {s w : ℂ} (hs : x < s.re) (hw : w ∈ closedBall (0 : ℂ) 1)
    (hz : G s w = 0) : s.re = c := by
  by_contra hsc
  rcases lt_or_gt_of_ne hsc with hlt | hgt
  · have hU : Convex ℝ {z : ℂ | x < z.re ∧ z.re < c} :=
      (convex_halfSpace_gt realPart_isLinear x).inter (convex_halfSpace_lt realPart_isLinear c)
    exact unitDisc_ne_zero_of_convex_parameter hU
      (hcont.mono (Set.prod_mono (fun z hz => hz.1) Subset.rfl))
      (fun z hz => han z hz.1)
      (fun z hz v hv hvz => (ne_of_lt hz.2) (hboundary z hz.1 v hv hvz))
      ⟨ha, hac⟩ hleft ⟨hs, hlt⟩ hw hz
  · have hU : Convex ℝ {z : ℂ | c < z.re} := convex_halfSpace_gt realPart_isLinear c
    exact unitDisc_ne_zero_of_convex_parameter hU
      (hcont.mono (Set.prod_mono (fun z hz => lt_trans hxc hz) Subset.rfl))
      (fun z hz => han z (lt_trans hxc hz))
      (fun z hz v hv hvz => (ne_of_gt hz) (hboundary z (lt_trans hxc hz) v hv hvz))
      hb hright hgt hw hz

/-- Contracting a pure unitary family to its central fibre preserves its zeros,
provided there are zero-free disc anchors on both sides of the pure line. -/
theorem unitDisc_zero_iff_center_of_boundary_and_anchors
    {x c : ℝ} (hxc : x < c) {G : ℂ → ℂ → ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2)
      ({s : ℂ | x < s.re} ×ˢ closedBall (0 : ℂ) 1))
    (han : ∀ s, x < s.re → AnalyticOnNhd ℂ (G s) (ball (0 : ℂ) 1))
    (hans : ∀ w ∈ closedBall (0 : ℂ) 1,
      AnalyticOnNhd ℂ (fun s => G s w) {s : ℂ | x < s.re})
    (hboundary : ∀ s, x < s.re → ∀ w ∈ sphere (0 : ℂ) 1,
      G s w = 0 → s.re = c)
    {a b : ℂ} (ha : x < a.re) (hac : a.re < c) (hb : c < b.re)
    (hleft : ∀ w ∈ ball (0 : ℂ) 1, G a w ≠ 0)
    (hright : ∀ w ∈ ball (0 : ℂ) 1, G b w ≠ 0)
    {s w : ℂ} (hs : x < s.re) (hw : w ∈ closedBall (0 : ℂ) 1) :
    G s w = 0 ↔ G s 0 = 0 := by
  exact unitDisc_zero_iff_center_of_pure_family hcont han hans
    (fun z hz v hv hvz => unitDisc_pure_of_boundary_and_anchors hxc hcont han hboundary
      ha hac hb hleft hright hz hv hvz) hs hw

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
