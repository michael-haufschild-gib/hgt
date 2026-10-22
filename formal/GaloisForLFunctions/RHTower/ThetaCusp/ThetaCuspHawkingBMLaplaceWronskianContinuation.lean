import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceJetHolomorphy
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceWronskian
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! The exact physical Wronskian normalization survives frequency continuation. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- All factors in the original spatial Wronskian are analytic off the real frequency axis. -/
theorem wronskian_frequency_analyticAt (w chi : ℂ) (hw : w.im ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo 0 1) : AnalyticAt ℂ (fun u => wronskian u chi z) w := by
  have hH := horizon_frequency_analyticAt w chi hw hz
  have hH1 := horizonFirst_frequency_analyticAt w chi hw hz
  have hN := (normalizable_frequency_entire chi hz).analyticAt w
  have hN1 := (normalizableFirst_frequency_entire chi hz).analyticAt w
  exact (show AnalyticAt ℂ (fun _ : ℂ => integratingFactor z) w from analyticAt_const).mul
    ((hH.mul hN1).sub (hH1.mul hN))

private theorem normalization_on_component (chi : ℂ) {z : ℝ} (hz : z ∈ Ioo 0 1)
    {U : Set ℂ} (hU : IsPreconnected U) (hi : ∀ u ∈ U, u.im ≠ 0)
    {v : ℂ} (hv : v ∈ U) (hvc : Chamber v chi) :
    EqOn (fun w => wronskian w chi z) (fun w => -connection w chi/2) U := by
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun u hu => wronskian_frequency_analyticAt u chi (hi u hu) hz)
    (fun u hu => (connection_frequency_analyticAt u chi (hi u hu)).neg.div
      (show AnalyticAt ℂ (fun _ : ℂ => (2:ℂ)) u from analyticAt_const) (by norm_num)) hU hv
  have he : ∀ᶠ u : ℂ in 𝓝 v, |chi.im| < u.re :=
    Complex.continuous_re.continuousAt.eventually_const_lt hvc
  filter_upwards [he] with u hu
  exact wronskian_eq hu hz

/-- The original Gamma-normalized Wronskian identity holds on both complete nonreal
frequency half-planes, including connection zeros. -/
theorem wronskian_eq_continued (w chi : ℂ) (hw : w.im ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo 0 1) : wronskian w chi z = -connection w chi/2 := by
  let v : ℂ := ⟨|chi.im|+1,w.im⟩
  have hvc : Chamber v chi := by dsimp [Chamber,v]; linarith
  rcases lt_or_gt_of_ne hw with hw | hw
  · exact normalization_on_component chi hz (convex_halfSpace_im_lt 0).isPreconnected
      (fun u hu => ne_of_lt hu) (show v ∈ {u : ℂ | u.im < 0} from hw) hvc hw
  · exact normalization_on_component chi hz (convex_halfSpace_im_gt 0).isPreconnected
      (fun u hu => ne_of_gt hu) (show v ∈ {u : ℂ | 0 < u.im} from hw) hvc hw

private theorem connection_nonzero_on_component (chi : ℂ)
    {U : Set ℂ} (hU : IsPreconnected U) (hi : ∀ u ∈ U, u.im ≠ 0)
    {v : ℂ} (hv : v ∈ U) (hvc : Chamber v chi) :
    ∀ w ∈ U, ∀ᶠ u in 𝓝[≠] w, connection u chi ≠ 0 := by
  have ha : AnalyticOnNhd ℂ (fun u => connection u chi) U :=
    fun u hu => connection_frequency_analyticAt u chi (hi u hu)
  intro w hw
  rcases (ha w hw).eventually_eq_zero_or_eventually_ne_zero with he | he
  · have hall := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hw he
    exact False.elim ((connection_ne_zero hvc) (hall hv))
  · exact he

/-- The original connection has only isolated zeros off the real frequency axis;
its nontriviality comes from the proved physical convergence chamber. -/
theorem connection_eventually_ne_zero (w chi : ℂ) (hw : w.im ≠ 0) :
    ∀ᶠ u in 𝓝[≠] w, connection u chi ≠ 0 := by
  let v : ℂ := ⟨|chi.im|+1,w.im⟩
  have hvc : Chamber v chi := by dsimp [Chamber,v]; linarith
  rcases lt_or_gt_of_ne hw with hw | hw
  · exact connection_nonzero_on_component chi (convex_halfSpace_im_lt 0).isPreconnected
      (fun u hu => ne_of_lt hu) (show v ∈ {u : ℂ | u.im < 0} from hw) hvc w hw
  · exact connection_nonzero_on_component chi (convex_halfSpace_im_gt 0).isPreconnected
      (fun u hu => ne_of_gt hu) (show v ∈ {u : ℂ | 0 < u.im} from hw) hvc w hw

end
end RHTower.D4BMLaplaceRadial
