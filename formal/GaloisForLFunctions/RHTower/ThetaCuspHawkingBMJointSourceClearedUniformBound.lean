import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceClearedPrincipalODE
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceCompactFrequencyBounds
import GaloisForLFunctions.HTGeometry.SymmetricHorizonGrowth

/-! One compact-frequency bound on the entire actual denominator-cleared principal response. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology D4BMLaplaceRadial D4BMModularCore GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Uniform forcing control retains the full cleared source over a compact nonreal frequency set. -/
theorem clearedPrincipalForcing_compact_bound (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (Ω : Set ℂ) (hΩ : IsCompact Ω) (hi : ∀ w ∈ Ω, w.im ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ Ω, ∀ t < 0,
      ‖clearedPrincipalForcing q branch w a i t‖ ≤ B*Real.exp ((w.re+2)*t) := by
  apply reducedCoefficient_family_norm_le_exp _ _ _ _ _ Ω hΩ
  · exact (clearedOnset_entire _).continuous.continuousOn
  · intro w hw
    exact (connection_frequency_analyticAt w (principalFrequency q i) (hi w hw)).continuousAt.neg.continuousWithinAt

/-- The entire cleared principal family has one horizon growth coefficient on a compact frequency set.
Analytic frequency limits retain this same bound at every interior connection zero. -/
theorem clearedPrincipalDifference_compact_bound (q : XiZeroCopy) (branch : Bool) (a : ℂ) (i : Fin 3)
    (Ω : Set ℂ) (hΩ : IsCompact Ω)
    (hstrip : ∀ w ∈ Ω, w.im ≠ 0 ∧ -2 < w.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ interior Ω, ∀ t < 0,
      ‖clearedPrincipalDifference q branch w a i t‖ ≤ C*Real.exp (-|w.re| *t) := by
  let U (w : ℂ) := clearedPrincipalDifference q branch w a i
  let V (w : ℂ) := clearedPrincipalDifferenceFirst q branch w a i
  let A : ℝ := 4*‖principalExponent q i*(principalExponent q i-1)‖
  obtain ⟨B,hB,hf⟩ := clearedPrincipalForcing_compact_bound q branch a i Ω hΩ (fun w hw => (hstrip w hw).1)
  let D (w : ℂ) := symmetricHorizonGrowthCoefficient w (U w (-1)) (V w (-1)) A B
  have hD : ContinuousOn D Ω := by
    intro w hw
    have h := hstrip w hw
    have hd := clearedPrincipalDifference_analyticAt q branch w a h.1 h.2 i (-1) (by norm_num)
    have hw0 : w ≠ 0 := by intro he; apply h.1; simp [he]
    have hg : ContinuousAt (fun u : ℂ => (u,U u (-1),V u (-1),A,B)) w :=
      continuousAt_id.prodMk (hd.1.continuousAt.prodMk (hd.2.continuousAt.prodMk
        (continuousAt_const.prodMk continuousAt_const)))
    exact ((symmetricHorizonGrowthCoefficient_continuousAt w (U w (-1)) (V w (-1)) A B hw0).comp_of_eq
      hg rfl).continuousWithinAt
  obtain ⟨C,hC⟩ := hΩ.exists_bound_of_continuousOn hD
  let C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hregular (w : ℂ) (hw : w ∈ Ω) (hs : w-2*physicalRate q branch ≠ 0)
      (hc : connection w (principalFrequency q i) ≠ 0) (t : ℝ) (ht : t < 0) :
      ‖U w t‖ ≤ C'*Real.exp (-|w.re| *t) := by
    have h := hstrip w hw
    have hw0 : w ≠ 0 := by intro he; apply h.1; simp [he]
    have hd (r : ℝ) (hr : r < 0) := clearedPrincipalDifference_hasDerivAt q branch w a h.1 h.2 i hs hc r hr
    have he := forcedSecondOrder_horizon_bound_symmetric w hw0 (U w) (V w)
      (principalPotential q i) (clearedPrincipalForcing q branch w a i) A B (by dsimp [A]; positivity) hB
      (fun r hr => (hd r hr).1) (fun r hr => (hd r hr).2)
      (principalPotential_norm_le_exp q i) (hf w hw) t ht
    exact he.trans (mul_le_mul_of_nonneg_right ((le_abs_self (D w)).trans
      ((show |D w| ≤ C from hC w hw).trans (le_max_left _ _))) (Real.exp_pos _).le)
  refine ⟨C',hC',fun w hw t ht => ?_⟩
  have h := hstrip w (interior_subset hw)
  have hlim := (clearedPrincipalDifference_analyticAt q branch w a h.1 h.2 i t ht).1.continuousAt.norm
  have hlim' : ContinuousAt (fun u : ℂ => C'*Real.exp (-|u.re| *t)) w := by fun_prop
  apply le_of_tendsto_of_tendsto (b := 𝓝[≠] w)
    (hlim.mono_left nhdsWithin_le_nhds) (hlim'.mono_left nhdsWithin_le_nhds)
  have hmem0 : ∀ᶠ u in 𝓝 w, u ∈ Ω :=
    mem_of_superset (isOpen_interior.mem_nhds hw) interior_subset
  have hmem : ∀ᶠ u in 𝓝[≠] w, u ∈ Ω := hmem0.filter_mono nhdsWithin_le_nhds
  filter_upwards [hmem,principal_denominators_eventually_ne_zero q branch w h.1 i] with u hu hd
  exact hregular u hu hd.1 hd.2 t ht

end
end RHTower.D4BMJointSource
