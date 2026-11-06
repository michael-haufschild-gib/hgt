import GaloisForLFunctions.RHTower.Suzuki.SuzukiHlogCompactEmbedding

/-!
# Physical and Fourier tails give compactness

A bounded family with uniformly vanishing physical and Fourier tails is
precompact in L². A compact time-band operator approximates the family:
its error is bounded by the two tails.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RHTower

/-- Uniform physical and Fourier tightness makes a bounded L² family totally bounded. -/
theorem totallyBounded_of_uniform_physical_and_fourier_tails
    (S : Set SoninL2) {B : ℝ} (hbound : ∀ f ∈ S, ‖f‖ ≤ B)
    (hphysical : ∀ ε > 0, ∃ a : ℝ, 0 < a ∧ ∀ f ∈ S,
      ‖f - indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f‖ < ε)
    (hfourier : ∀ ε > 0, ∃ t : ℝ, 0 < t ∧ ∀ f ∈ S,
      ‖f - fourierCutoff (centralInterval t) (measurableSet_centralInterval t) f‖ < ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨a, ha, hpa⟩ := hphysical (ε / 3) (by positivity)
  obtain ⟨t, _, hft⟩ := hfourier (ε / 3) (by positivity)
  let P : SoninL2 →L[ℂ] SoninL2 :=
    indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
  let F : SoninL2 →L[ℂ] SoninL2 :=
    fourierCutoff (centralInterval t) (measurableSet_centralInterval t)
  let K : SoninL2 →L[ℂ] SoninL2 := P * F
  have hKcompact : IsCompactOperator K :=
    isCompactOperator_indicatorCutoff_fourierCutoff_central a t ha
  have hcompact : IsCompact (closure (K '' Metric.closedBall 0 B)) :=
    hKcompact.isCompact_closure_image_closedBall B
  obtain ⟨centers, hfinite, hcover⟩ :=
    Metric.totallyBounded_iff.mp hcompact.totallyBounded (ε / 3) (by positivity)
  refine ⟨centers, hfinite, ?_⟩
  intro f hf
  have hfball : f ∈ Metric.closedBall (0 : SoninL2) B := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbound f hf
  have hKmem : K f ∈ closure (K '' Metric.closedBall 0 B) :=
    subset_closure ⟨f, hfball, rfl⟩
  rcases Set.mem_iUnion.mp (hcover hKmem) with ⟨v, hv⟩
  rcases Set.mem_iUnion.mp hv with ⟨hv, hKball⟩
  refine Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv, ?_⟩⟩
  rw [Metric.mem_ball] at hKball ⊢
  have happrox : dist f (K f) < 2 * ε / 3 := by
    rw [dist_eq_norm]
    have heq : f - K f = (f - P f) + P (f - F f) := by
      change f - P (F f) = _
      rw [map_sub]
      abel
    have hcontract : ‖P (f - F f)‖ ≤ ‖f - F f‖ := by
      dsimp only [P]
      rw [indicatorCutoff_eq_physicalForbidden_starProjection]
      exact (physicalForbidden (centralInterval a)
        (measurableSet_centralInterval a)).norm_starProjection_apply_le _
    rw [heq]
    have ht := (norm_add_le (f - P f) (P (f - F f))).trans
      (add_le_add le_rfl hcontract)
    have hp := hpa f hf
    have hf' := hft f hf
    change ‖f - P f‖ < ε / 3 at hp
    change ‖f - F f‖ < ε / 3 at hf'
    linarith only [ht, hp, hf']
  exact (dist_triangle f (K f) v).trans_lt (by linarith only [happrox, hKball])

/-- The closure of a bounded, physically and Fourier tight family is compact in L². -/
theorem isCompact_closure_of_uniform_physical_and_fourier_tails
    (S : Set SoninL2) {B : ℝ} (hbound : ∀ f ∈ S, ‖f‖ ≤ B)
    (hphysical : ∀ ε > 0, ∃ a : ℝ, 0 < a ∧ ∀ f ∈ S,
      ‖f - indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f‖ < ε)
    (hfourier : ∀ ε > 0, ∃ t : ℝ, 0 < t ∧ ∀ f ∈ S,
      ‖f - fourierCutoff (centralInterval t) (measurableSet_centralInterval t) f‖ < ε) :
    IsCompact (closure S) :=
  (totallyBounded_of_uniform_physical_and_fourier_tails S hbound hphysical hfourier).closure.isCompact_of_isClosed
    isClosed_closure

#print axioms totallyBounded_of_uniform_physical_and_fourier_tails
#print axioms isCompact_closure_of_uniform_physical_and_fourier_tails
end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
