import GaloisForLFunctions.RHTower.MobiusDivisorClockGraphSource
import GaloisForLFunctions.RHTower.MobiusDivisorCompactClockCone
import GaloisForLFunctions.RHTower.CHMDCompactBVKernel
import GaloisForLFunctions.HTGeometry.ClosedConeBochnerIntegral

/-! # Positive literal clock control in the full arithmetic graph

Positive regularization transports compact-clock separation into the complete
source graph. Removing regularization reaches every continuous BV target
fixed by the chosen compact cutoff. All arithmetic jumps are retained.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry

namespace RHTower
open CHMDDoobGraph

def criticalClockGraphCone (χ : ℝ → ℝ) (hχ : BoundedVariationOn χ univ) (T : ℝ) :
    ProperCone ℝ SourceGraph :=
  ⟨(PointedCone.hull ℝ (Set.range fun t : {t : ℝ // T < t} =>
    criticalClockGraph χ hχ t)).closure, isClosed_closure⟩

theorem criticalClockGraph_mem_cone (χ : ℝ → ℝ) (hχ : BoundedVariationOn χ univ)
    {T t : ℝ} (ht : T < t) : criticalClockGraph χ hχ t ∈ criticalClockGraphCone χ hχ T :=
  subset_closure (PointedCone.subset_hull ⟨⟨t, ht⟩, rfl⟩)

theorem compactKernelControl_criticalClockProfile (a : ℝ≥0) (b t : ℝ) (χ ρ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hρ : BoundedVariationOn ρ univ)
    (hcχ : Continuous χ) (hcρ : Continuous ρ) (hsχ : HasCompactSupport χ)
    (hsρ : HasCompactSupport ρ)
    (hfit : ∀ x y, y ∉ Icc (0 : ℝ) (a : ℝ) → χ x * ρ (x + b - y) = 0) :
    compactKernelControl a χ ρ hχ hρ hcχ hcρ hsχ b (criticalClockProfile a t) =
      ∫ s : ℝ, ρ s • criticalClockGraph χ hχ (t - b + s) := by
  rw [show criticalClockProfile a t =
    ⟨fun y => criticalAbelLogProfile (t - y),
      continuous_criticalAbelLogProfile.comp (continuous_const.sub continuous_subtype_val)⟩ from rfl]
  rw [compactKernelControl_eq_average a b χ ρ (fun y => criticalAbelLogProfile (t - y))
    hχ hρ (boundedVariationOn_criticalAbelLogProfile_translate t) hcχ hcρ
    (continuous_criticalAbelLogProfile.comp (continuous_const.sub continuous_id)) hsχ hsρ hfit]
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    change ρ s • cutoffKernelGraph χ (fun y => criticalAbelLogProfile (t - y)) hχ
      (boundedVariationOn_criticalAbelLogProfile_translate t) b s =
      ρ s • criticalClockGraph χ hχ (t - b + s)
    congr 1
    unfold cutoffKernelGraph cutoffTranslateGraph criticalClockGraph
    congr 1
    funext x
    change χ x * criticalAbelLogProfile (t - (-(s - b - x))) =
      χ x * criticalAbelLogProfile (t - b + s - x)
    congr 2
    ring

theorem criticalClockGraph_average_mem_cone (χ ρ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hcχ : Continuous χ) (hsχ : HasCompactSupport χ)
    (hcρ : Continuous ρ) (hsρ : HasCompactSupport ρ) (hρ : ∀ s, 0 ≤ ρ s)
    {T b R t : ℝ} (hR : ∀ s, ρ s ≠ 0 → |s| ≤ R) (ht : T + b + R < t) :
    (∫ s : ℝ, ρ s • criticalClockGraph χ hχ (t - b + s)) ∈
      criticalClockGraphCone χ hχ T := by
  apply integral_mem_properCone
  · exact (hcρ.smul ((continuous_criticalClockGraph χ hχ hcχ hsχ).comp
      (continuous_const.add continuous_id))).integrable_of_hasCompactSupport hsρ.smul_right
  · exact Eventually.of_forall fun s => by
      by_cases hs : ρ s = 0
      · simp only [hs, zero_smul]
        exact (criticalClockGraphCone χ hχ T).toPointedCone.zero_mem
      · apply (criticalClockGraphCone χ hχ T).smul_mem
          (criticalClockGraph_mem_cone χ hχ (by linarith [(abs_le.mp (hR s hs)).1])) (hρ s)

theorem compactKernelControl_mem_clockCone (a : ℝ≥0) (b T : ℝ) (χ ρ : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hρ : BoundedVariationOn ρ univ)
    (hcχ : Continuous χ) (hcρ : Continuous ρ) (hsχ : HasCompactSupport χ)
    (hsρ : HasCompactSupport ρ) (hnρ : ∀ s, 0 ≤ ρ s)
    (hfit : ∀ x y, y ∉ Icc (0 : ℝ) (a : ℝ) → χ x * ρ (x + b - y) = 0)
    (f : C(CriticalClockWindow a, ℝ)) :
    compactKernelControl a χ ρ hχ hρ hcχ hcρ hsχ b f ∈ criticalClockGraphCone χ hχ T := by
  let S := compactKernelControl a χ ρ hχ hρ hcχ hcρ hsχ b
  by_contra hf
  obtain ⟨L, hL, hLf⟩ := (criticalClockGraphCone χ hχ T).hyperplane_separation_point hf
  have hne : L.comp S ≠ 0 := by
    intro he
    have hz : L (S f) = 0 := by
      change (L.comp S) f = 0
      exact congrArg (fun M : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ => M f) he
    exact (ne_of_lt hLf) hz
  obtain ⟨R, _, hR⟩ := hsρ.isBounded.exists_pos_norm_le
  obtain ⟨t, ht, hneg⟩ := exists_negative_criticalClockProfile_pairing a (L.comp S) hne
    (T + b + R)
  have hm : S (criticalClockProfile a t) ∈ criticalClockGraphCone χ hχ T := by
    rw [show S (criticalClockProfile a t) =
      ∫ s : ℝ, ρ s • criticalClockGraph χ hχ (t - b + s) from
        compactKernelControl_criticalClockProfile a b t χ ρ hχ hρ hcχ hcρ hsχ hsρ hfit]
    exact criticalClockGraph_average_mem_cone χ ρ hχ hcχ hsχ hcρ hsρ hnρ
      (fun s hs => by simpa only [Real.norm_eq_abs] using hR s (subset_tsupport ρ hs)) ht
  exact (not_lt_of_ge (hL _ hm)) hneg

theorem criticalClockGraph_positiveCone_contains_bvTarget (χ v : ℝ → ℝ)
    (hχ : BoundedVariationOn χ univ) (hv : BoundedVariationOn v univ)
    (hcχ : Continuous χ) (hcv : Continuous v) (hsχ : HasCompactSupport χ)
    (hfix : ∀ x, χ x * v x = v x) (T : ℝ) :
    bvLift v hv ∈ criticalClockGraphCone χ hχ T := by
  have hm (n : ℕ) : (∫ s : ℝ, CHMDDoobGraph.mollifier n s • cutoffKernelGraph χ v hχ hv 0 s) ∈
      criticalClockGraphCone χ hχ T := by
    obtain ⟨a, b, hfit⟩ := exists_cutoff_kernel_interval hsχ (mollifier_compact n)
    let F : ℝ → ℝ := fun y => v (y - b)
    have hF : BoundedVariationOn F univ :=
      ne_top_of_le_ne_top hv (eVariationOn.comp_le_of_monotoneOn v (fun y => y - b)
        (fun _ _ _ _ h => sub_le_sub_right h b) (fun _ _ => mem_univ _))
    have hcF : Continuous F := hcv.comp (continuous_id.sub continuous_const)
    have hρ := boundedVariationOn_of_contDiff_compact
      ((mollifier_contDiff n).of_le (by norm_num)) (mollifier_compact n)
    have he := compactKernelControl_eq_average a b χ (CHMDDoobGraph.mollifier n) F hχ hρ hF
      hcχ (mollifier_contDiff n).continuous hcF hsχ (mollifier_compact n) hfit
    have hmem := compactKernelControl_mem_clockCone a b T χ (CHMDDoobGraph.mollifier n) hχ hρ
      hcχ (mollifier_contDiff n).continuous hsχ (mollifier_compact n) (mollifier_nonneg n) hfit
      ⟨fun y => F y, hcF.comp continuous_subtype_val⟩
    rw [he] at hmem
    convert hmem using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun s => by
      change CHMDDoobGraph.mollifier n s • cutoffKernelGraph χ v hχ hv 0 s =
        CHMDDoobGraph.mollifier n s • cutoffKernelGraph χ F hχ hF b s
      congr 1
      unfold cutoffKernelGraph cutoffTranslateGraph
      congr 1
      funext x
      change χ x * v (-(s - 0 - x)) = χ x * v (-(s - b - x) - b)
      congr 2
      ring
  have hlim := (criticalClockGraphCone χ hχ T).isClosed.mem_of_tendsto
    (cutoffKernelGraph_mollifier_tendsto χ v hχ hv hcχ hcv hsχ) (Eventually.of_forall hm)
  have he : cutoffKernelGraph χ v hχ hv 0 0 = bvLift v hv := by
    unfold cutoffKernelGraph cutoffTranslateGraph
    congr 1
    funext x
    change χ x * v (-(0 - 0 - x)) = v x
    rw [show -(0 - 0 - x) = x by ring]
    exact hfix x
  rw [he] at hlim
  exact hlim

end RHTower
