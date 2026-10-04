import GaloisForLFunctions.RHTower.SoninDampedPrimePolarCurrent
import GaloisForLFunctions.HTGeometry.L2MeromorphicAlgebra
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeAbelCompleteness
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# No fixed-carrier meromorphic half-plane continuation of the actual current

The literal two-leg, all-prime-power current cannot be continued as a physical
Sonin L²-valued meromorphic family to any half-plane containing negative
damping. Differences of two continuous physical head probes cancel the complete
expanding-leg term before applying meromorphic uniqueness. A regular point at
negative damping would then contradict the existing unconditional Hardy-zero
nonextension theorem.

The exact finite polar segment is entire as a physical vector. Consequently the
obstruction persists for every nonnegative lower endpoint, including the original
logarithmic endpoint log 2. Evaluation at the literal ground indicator transfers
the obstruction to bounded-operator-valued meromorphic families.

This does not rule out boundary admission of the original logarithmic source,
varying carriers or relative quotients, and supplies no RH conclusion.
-/

noncomputable section
open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower

private theorem no_far_head_row {z : ℂ}
    (hzlo : -(1/2 : ℝ) < z.re) (hzhi : z.re < 0) (c : ℂ) :
    ¬ ∃ f : SoninL2, ∀ w : ℂ, 2 < w.re →
      w * soninHeadMellin f w = -regularizedCriticalMellinDefect (z+w-1) + c := by
  rintro ⟨f, hf⟩
  let A : ℂ → ℂ := fun u =>
    -((u+1-z) * soninHeadMellin f (u+1-z)) + c
  have hA : AnalyticOnNhd ℂ A {u : ℂ | z.re-1/2 < u.re} := by
    intro u hu
    have hw : 1/2 < (u+1-z).re := by
      change z.re-1/2 < u.re at hu
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
      linarith
    have hshift : AnalyticAt ℂ (fun v : ℂ => v+1-z) u := by fun_prop
    have hm : AnalyticAt ℂ (fun v => soninHeadMellin f (v+1-z)) u :=
      AnalyticAt.comp (f := fun v : ℂ => v+1-z)
        (analyticOnNhd_soninHeadMellin f (u+1-z) hw) hshift
    exact (hshift.mul hm).neg.add analyticAt_const
  have hsafe : ∀ u : ℂ, 2 < u.re → A u = regularizedCriticalMellinDefect u := by
    intro u hu
    have hw : 2 < (u+1-z).re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
      linarith
    have h := hf (u+1-z) hw
    rw [show z+(u+1-z)-1 = u by ring] at h
    dsimp only [A]
    linear_combination -h
  have hAU : AnalyticOnNhd ℂ A {u : ℂ | 0 < u.re} := by
    intro u hu
    apply hA
    change 0 < u.re at hu
    change z.re-1/2 < u.re
    linarith
  have hevent : A =ᶠ[𝓝 (3 : ℂ)] regularizedCriticalMellinDefect := by
    have hopen : IsOpen {u : ℂ | 2 < u.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (3 : ℂ) ∈ {u : ℂ | 2 < u.re})] with u hu
    exact hsafe u hu
  have heq := hAU.eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane
    (convex_halfSpace_re_gt 0).isPreconnected
    (by norm_num : (3 : ℂ) ∈ {u : ℂ | 0 < u.re}) hevent
  exact no_analytic_extension_regularizedCriticalMellinDefect_pastHardy
    (c := z.re-1/2) (by linarith) (by linarith) A hA (fun u hu => heq hu)

private theorem mero_zero_from_safe {c : ℝ} (hc : c < 0) {H : ℂ → ℂ}
    (hH : MeromorphicOn H {z : ℂ | c < z.re}) {z0 : ℂ} (hz0 : c < z0.re)
    (hreg : AnalyticAt ℂ H z0) (hsafe : ∀ z : ℂ, 1/2 < z.re → H z = 0) : H z0 = 0 := by
  have htwo : c < (2 : ℂ).re := by norm_num; linarith
  have htop2 : meromorphicOrderAt H 2 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hopen : IsOpen {z : ℂ | 1/2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : ∀ᶠ z in 𝓝 (2 : ℂ), H z = 0 := by
      filter_upwards [hopen.mem_nhds (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1/2 < z.re})] with z hz
      exact hsafe z hz
    exact hev.filter_mono nhdsWithin_le_nhds
  have htop : meromorphicOrderAt H z0 = ⊤ := by
    by_contra hn
    exact (hH.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt c).isPreconnected hz0 htwo hn) htop2
  rw [hreg.meromorphicOrderAt_eq, ENat.map_eq_top_iff] at htop
  have he : H =ᶠ[𝓝 z0] (fun _ => 0) := analyticOrderAt_eq_top.mp htop
  exact he.eq_of_nhds

/-- The complete physical current has no Banach-valued meromorphic continuation
on any half-plane crossing zero damping. -/
private theorem no_current_family_in_strip
    {c : ℝ} (hclo : -(1/2 : ℝ) < c) (hchi : c < 0) :
    ¬ ∃ F : ℂ → SoninL2, MeromorphicOn F {z : ℂ | c < z.re} ∧
      ∀ z : ℂ, 1/2 < z.re → F z = soninDampedPrimePolarCurrent z := by
  rintro ⟨F, hF, hsource⟩
  have hm : c < ((c/2 : ℝ) : ℂ).re ∧ ((c/2 : ℝ) : ℂ).re < 0 := by
    simp only [Complex.ofReal_re]
    constructor <;> linarith
  have hopen : IsOpen {z : ℂ | c < z.re ∧ z.re < 0} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hnear : ∀ᶠ z in 𝓝 ((c/2 : ℝ) : ℂ), c < z.re ∧ z.re < 0 :=
    hopen.mem_nhds hm
  obtain ⟨z0, hF0, hz0⟩ := ((hF _ hm.1).eventually_analyticAt.and
    (hnear.filter_mono nhdsWithin_le_nhds)).exists
  have hzlo : -(1/2 : ℝ) < z0.re := hclo.trans hz0.1
  apply no_far_head_row hzlo hz0.2
    (3 * soninHeadMellin (F z0) 3 + regularizedCriticalMellinDefect (z0+3-1))
  refine ⟨F z0, ?_⟩
  intro w hw
  have hw' : 1/2 < w.re := by linarith
  have hthree : 1/2 < (3 : ℂ).re := by norm_num
  let L : SoninL2 →L[ℂ] ℂ :=
    w • soninHeadMellinCLM w hw' - (3 : ℂ) • soninHeadMellinCLM 3 hthree
  have hL (f : SoninL2) :
      L f = w * soninHeadMellin f w - 3 * soninHeadMellin f 3 := by
    change w * soninHeadMellinCLM w hw' f - 3 * soninHeadMellinCLM 3 hthree f = _
    rw [soninHeadMellinCLM_apply, soninHeadMellinCLM_apply]
  have hR (a : ℂ) (ha : 2 < a.re) :
      AnalyticOnNhd ℂ (fun z => regularizedCriticalMellinDefect (z+a-1))
        {z : ℂ | c < z.re} := by
    intro z hz
    have harg : 0 < (z+a-1).re := by
      change c < z.re at hz
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
      linarith
    exact AnalyticAt.comp (f := fun v : ℂ => v+a-1)
      (analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane (z+a-1) harg)
      (by fun_prop)
  let H : ℂ → ℂ := fun z => L (F z) + regularizedCriticalMellinDefect (z+w-1) -
    regularizedCriticalMellinDefect (z+3-1)
  have hHm : MeromorphicOn H {z : ℂ | c < z.re} := by
    intro z hz
    exact ((meromorphicAt_continuousLinearMap L F z (hF z hz)).add
      ((hR w hw z hz).meromorphicAt)).sub
        ((hR 3 (by norm_num) z hz).meromorphicAt)
  have hHa : AnalyticAt ℂ H z0 :=
    (((L.analyticAt _).comp hF0).add (hR w hw z0 hz0.1)).sub
      (hR 3 (by norm_num) z0 hz0.1)
  have hzero : H z0 = 0 := by
    apply mero_zero_from_safe hchi hHm hz0.1 hHa
    intro z hz
    dsimp only [H]
    rw [hL, hsource z hz, soninHeadMellin_dampedPrimePolarCurrent hz hw',
      soninHeadMellin_dampedPrimePolarCurrent hz hthree]
    ring
  dsimp only [H] at hzero
  rw [hL] at hzero
  linear_combination hzero

/-- No fixed physical L² meromorphic family agrees with the complete current
on its original half-plane and extends through zero damping. -/
theorem not_exists_meromorphic_soninDampedPrimePolarCurrent :
    ¬ ∃ c : ℝ, c < 0 ∧ ∃ F : ℂ → SoninL2,
      MeromorphicOn F {z : ℂ | c < z.re} ∧
        ∀ z : ℂ, 1/2 < z.re → F z = soninDampedPrimePolarCurrent z := by
  rintro ⟨c, hc, F, hF, hs⟩
  let d : ℝ := max c (-(1/4 : ℝ))
  have hdlo : -(1/2 : ℝ) < d := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hdhi : d < 0 := max_lt hc (by norm_num)
  apply no_current_family_in_strip hdlo hdhi
  refine ⟨F, ?_, hs⟩
  intro z hz
  apply hF z
  change d < z.re at hz
  exact lt_of_le_of_lt (show c ≤ d from le_max_left _ _) hz

/-- Evaluation at the literal ground indicator transfers the obstruction to
bounded-operator-valued meromorphic continuations of the actual current. -/
theorem not_exists_meromorphic_soninDampedCurrentOperator :
    ¬ ∃ c : ℝ, c < 0 ∧ ∃ O : ℂ → (SoninL2 →L[ℂ] SoninL2),
      MeromorphicOn O {z : ℂ | c < z.re} ∧ ∀ z : ℂ, 1/2 < z.re →
        O z (bandIndicator 1) = soninDampedPrimePolarCurrent z := by
  rintro ⟨c, hc, O, hO, hs⟩
  apply not_exists_meromorphic_soninDampedPrimePolarCurrent
  refine ⟨c, hc, (fun z => O z (bandIndicator 1)), ?_, hs⟩
  intro z hz
  exact meromorphicAt_continuousLinearMap
    (ContinuousLinearMap.apply ℂ SoninL2 (bandIndicator 1)) O z (hO z hz)

private theorem differentiable_compact_vector_laplace
    {v : ℝ → SoninL2} (hv : Continuous v) (a b : ℝ) :
    Differentiable ℂ (fun z : ℂ => ∫ u in Icc a b, Complex.exp (-z*u) • v u) := by
  intro z0
  let F : ℂ → ℝ → SoninL2 := fun z u => Complex.exp (-z*u) • v u
  let F' : ℂ → ℝ → SoninL2 := fun z u =>
    (Complex.exp (-z*u) * (-(u : ℂ))) • v u
  have hcont (z : ℂ) : Continuous (F z) := by
    dsimp only [F]
    exact (by fun_prop : Continuous (fun u : ℝ => Complex.exp (-z*u))).smul hv
  have hcont' : Continuous (fun p : ℂ × ℝ => F' p.1 p.2) := by
    dsimp only [F']
    exact (by fun_prop : Continuous (fun p : ℂ × ℝ =>
      Complex.exp (-p.1*p.2) * (-(p.2 : ℂ)))).smul (hv.comp continuous_snd)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z0 1).prod
    (isCompact_Icc : IsCompact (Icc a b))).exists_bound_of_continuousOn hcont'.continuousOn
  have hder (u : ℝ) (z : ℂ) : HasDerivAt (fun q => F q u) (F' z u) z := by
    have he := (((hasDerivAt_id z).neg).mul_const (u : ℂ)).cexp
    simpa only [F, F', Pi.neg_apply, id_eq, neg_mul, one_mul] using he.smul_const (v u)
  have hbound : ∀ᵐ u ∂(volume.restrict (Icc a b)),
      ∀ z ∈ Metric.ball z0 1, ‖F' z u‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu z hz
    exact hC (z,u) ⟨Metric.ball_subset_closedBall hz, hu⟩
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ : ℝ => C)
    (x₀ := z0) (s := Metric.ball z0 1) (μ := volume.restrict (Icc a b))
    (Metric.ball_mem_nhds z0 zero_lt_one)
    (Eventually.of_forall fun z => (hcont z).aestronglyMeasurable)
    ((hcont z0).continuousOn.integrableOn_Icc)
    ((hcont'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    hbound (integrable_const C) (Eventually.of_forall fun u z _ => hder u z)
  exact hkey.2.differentiableAt

theorem analyticAt_soninDampedFinitePolarCurrent {b : ℝ} (hb : 0 ≤ b) (z : ℂ) :
    AnalyticAt ℂ (soninDampedFinitePolarCurrent b) z := by
  let v : ℝ → SoninL2 := fun u =>
    rayDilate (Real.exp u) (bandIndicator 1) + rayDilate (Real.exp (-u)) (bandIndicator 1)
  have hv : Continuous v := (continuous_dilationOrbit (bandIndicator 1)).add
    ((continuous_dilationOrbit (bandIndicator 1)).comp continuous_neg)
  let L : ℂ → SoninL2 := fun q => ∫ u in Icc (0 : ℝ) b, Complex.exp (-q*u) • v u
  have hL : Differentiable ℂ L := differentiable_compact_vector_laplace hv 0 b
  have heq : soninDampedFinitePolarCurrent b = fun q => L (q-1/2) + L (q+1/2) := by
    funext q
    rw [soninDampedFinitePolarCurrent, intervalIntegral.integral_of_le hb,
      ← integral_Icc_eq_integral_Ioc]
    change (∫ u in Icc (0 : ℝ) b,
      (Complex.exp (-(q-1/2)*u) + Complex.exp (-(q+1/2)*u)) • v u) = _
    simp_rw [add_smul]
    apply integral_add
    · exact ((by fun_prop : Continuous (fun u : ℝ => Complex.exp (-(q-1/2)*u))).smul hv).continuousOn.integrableOn_Icc
    · exact ((by fun_prop : Continuous (fun u : ℝ => Complex.exp (-(q+1/2)*u))).smul hv).continuousOn.integrableOn_Icc
  rw [heq]
  have hd : Differentiable ℂ (fun q => L (q-1/2) + L (q+1/2)) := by
    intro q
    exact ((hL (q-1/2)).comp q (differentiableAt_id.sub_const _)).add
      ((hL (q+1/2)).comp q (differentiableAt_id.add_const _))
  exact hd.differentiableOn.analyticOnNhd isOpen_univ z (mem_univ z)

/-- The literal finite polar endpoint does not permit a meromorphic continuation
of the complete physical current across zero damping. -/
theorem not_exists_meromorphic_soninDampedPrimePolarCurrentFrom :
    ¬ ∃ b : ℝ, 0 ≤ b ∧ ∃ c : ℝ, c < 0 ∧ ∃ F : ℂ → SoninL2,
      MeromorphicOn F {z : ℂ | c < z.re} ∧ ∀ z : ℂ, 1/2 < z.re →
        F z = soninDampedPrimePolarCurrentFrom b z := by
  rintro ⟨b, hb, c, hc, F, hF, hs⟩
  apply not_exists_meromorphic_soninDampedPrimePolarCurrent
  refine ⟨c, hc, (fun z => F z - soninDampedFinitePolarCurrent b z), ?_, ?_⟩
  · intro z hz
    exact (hF z hz).sub (analyticAt_soninDampedFinitePolarCurrent hb z).meromorphicAt
  · intro z hz
    change F z - soninDampedFinitePolarCurrent b z = soninDampedPrimePolarCurrent z
    rw [hs z hz, soninDampedPrimePolarCurrentFrom_eq hb hz]
    exact add_sub_cancel_right _ _

/-- No bounded-operator-valued meromorphic family has the original complete
current as its physical ground column throughout the convergence half-plane. -/
theorem not_exists_meromorphic_soninDampedCurrentOperatorFrom :
    ¬ ∃ b : ℝ, 0 ≤ b ∧ ∃ c : ℝ, c < 0 ∧ ∃ O : ℂ → (SoninL2 →L[ℂ] SoninL2),
      MeromorphicOn O {z : ℂ | c < z.re} ∧ ∀ z : ℂ, 1/2 < z.re →
        O z (bandIndicator 1) = soninDampedPrimePolarCurrentFrom b z := by
  rintro ⟨b, hb, c, hc, O, hO, hs⟩
  apply not_exists_meromorphic_soninDampedPrimePolarCurrentFrom
  refine ⟨b, hb, c, hc, (fun z => O z (bandIndicator 1)), ?_, hs⟩
  intro z hz
  exact meromorphicAt_continuousLinearMap
    (ContinuousLinearMap.apply ℂ SoninL2 (bandIndicator 1)) O z (hO z hz)

end RHTower
