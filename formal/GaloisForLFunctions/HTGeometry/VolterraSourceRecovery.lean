import GaloisForLFunctions.HTGeometry.VolterraWindowedEquation

/-!
# Causal source recovery for continuous Volterra responses

Zhang, arXiv:2608.22995v1, reconstructs sources from histories on the forward
image. The same mechanism gives an all-time, prefix-causal inverse for the
corpus's continuous linear Volterra responses. Compactness supplies every local
bound; no small-kernel, nonresonance, or prescribed bound is required.
-/

open MeasureTheory
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- Continuous source and memory data automatically satisfy all window bounds. -/
theorem continuousVolterra_locallyBounded
    (f : C(ℝ, X)) (K : C(ℝ × ℝ, X →L[ℝ] X)) :
    VolterraLocallyBounded f (fun t s => K (t, s)) := by
  intro T _hT
  obtain ⟨F, hF⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    f.continuous.continuousOn
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := -T) (b := T)).prod
    (isCompact_Icc (a := -T) (b := T))).exists_bound_of_continuousOn
    K.continuous.continuousOn
  refine ⟨max M 0, max F 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro t s ht hs
    exact (hM (t, s) ⟨abs_le.mp ht, abs_le.mp hs⟩).trans (le_max_left _ _)
  · intro t ht
    exact (hF t (abs_le.mp ht)).trans (le_max_left _ _)

/-- The existing Picard response, now as an actual continuous history. -/
def continuousVolterraResponse
    (K : C(ℝ × ℝ, X →L[ℝ] X)) (f : C(ℝ, X)) : C(ℝ, X) :=
  ⟨volterraSolution f (fun t s => K (t, s)),
    continuous_volterraSolution_of_locallyBounded f.continuous K.continuous
      (continuousVolterra_locallyBounded f K)⟩

/-- Subtracting the retarded memory reconstructs the source. -/
def continuousVolterraSource
    (K : C(ℝ × ℝ, X →L[ℝ] X)) (u : C(ℝ, X)) : C(ℝ, X) :=
  ⟨fun t => u t - ∫ s in (0 : ℝ)..t, K (t, s) (u s),
    u.continuous.sub (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (continuous_apply_pair (K := fun t s => K (t, s)) K.continuous u.continuous) continuous_id)⟩

/-- Exact source recovery on the entire real time axis. -/
theorem continuousVolterraSource_response
    (K : C(ℝ × ℝ, X →L[ℝ] X)) (f : C(ℝ, X)) :
    continuousVolterraSource K (continuousVolterraResponse K f) = f := by
  ext t
  change volterraSolution f (fun t s => K (t, s)) t - _ = f t
  rw [volterraSolution_eq_of_locallyBounded f.continuous K.continuous
    (continuousVolterra_locallyBounded f K) t]
  exact add_sub_cancel_right _ _

/-- No two continuous sources produce the same complete response. -/
theorem continuousVolterraResponse_injective (K : C(ℝ × ℝ, X →L[ℝ] X)) :
    Function.Injective (continuousVolterraResponse K) :=
  (show Function.LeftInverse (continuousVolterraSource K) (continuousVolterraResponse K)
    from continuousVolterraSource_response K).injective

/-- Equality of response prefixes is exactly equality of source prefixes. -/
theorem continuousVolterraResponse_prefix_iff
    (K : C(ℝ × ℝ, X →L[ℝ] X)) (f g : C(ℝ, X)) (T : ℝ) :
    Set.EqOn (continuousVolterraResponse K f) (continuousVolterraResponse K g)
      (Set.uIcc 0 T) ↔ Set.EqOn f g (Set.uIcc 0 T) := by
  constructor
  · intro h t ht
    have hf := congrArg (fun u : C(ℝ, X) => u t) (continuousVolterraSource_response K f)
    have hg := congrArg (fun u : C(ℝ, X) => u t) (continuousVolterraSource_response K g)
    rw [← hf, ← hg]
    change continuousVolterraResponse K f t - _ = continuousVolterraResponse K g t - _
    rw [h ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    exact congrArg (K (t, s)) (h (Set.uIcc_subset_uIcc_left ht hs))
  · intro h
    have hiter : ∀ n, Set.EqOn
        (volterraIterate f (fun t s => K (t, s)) n)
        (volterraIterate g (fun t s => K (t, s)) n) (Set.uIcc 0 T) := by
      intro n
      induction n with
      | zero => exact h
      | succ n ih =>
        intro t ht
        rw [volterraIterate_succ, volterraIterate_succ, h ht]
        congr 1
        apply intervalIntegral.integral_congr
        intro s hs
        exact congrArg (K (t, s)) (ih (Set.uIcc_subset_uIcc_left ht hs))
    intro t ht
    change volterraSolution f (fun t s => K (t, s)) t =
      volterraSolution g (fun t s => K (t, s)) t
    rw [volterraSolution, volterraSolution, h ht]
    congr 1
    apply tsum_congr
    intro n
    rw [hiter (n + 1) ht, hiter n ht]

/-- The initial observation always equals the initial source. -/
theorem continuousVolterraResponse_zero
    (K : C(ℝ × ℝ, X →L[ℝ] X)) (f : C(ℝ, X)) :
    continuousVolterraResponse K f 0 = f 0 := by
  have h := congrArg (fun u : C(ℝ, X) => u 0) (continuousVolterraSource_response K f)
  simpa only [continuousVolterraSource, ContinuousMap.coe_mk,
    intervalIntegral.integral_same, sub_zero] using h

end
end GaloisForLFunctions.HTGeometry
