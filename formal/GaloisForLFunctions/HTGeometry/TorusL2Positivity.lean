import GaloisForLFunctions.HTGeometry.InfiniteTorusCharacter
import GaloisForLFunctions.HTGeometry.JordanL2Quadratic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Extending corrected torus positivity to measurable tests

Character density and continuous-function density in `L²` extend a closed
quadratic inequality from finite packets to every square-integrable test.
Jordan multipliers give the corresponding signed-integral formulation.
-/

open MeasureTheory Set Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A continuous quadratic inequality verified on finite character packets
holds on every square-integrable function. -/
theorem torus_corrected_quadratic_nonneg_of_character_span
    {I : Type*} [Countable I] (μ : Measure (UnitAddTorus I))
    [IsFiniteMeasure μ] [μ.WeaklyRegular] {m : ℕ}
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (L : Fin m → Lp ℂ 2 μ →L[ℂ] ℂ)
    (h : ∀ f : C(UnitAddTorus I, ℂ),
      f ∈ Submodule.span ℂ (Set.range (torusCharacter (ι := I))) →
      0 ≤ (inner ℂ (A (ContinuousMap.toLp 2 μ ℂ f))
        (ContinuousMap.toLp 2 μ ℂ f)).re +
        ∑ i, ‖L i (ContinuousMap.toLp 2 μ ℂ f)‖ ^ 2) :
    ∀ u : Lp ℂ 2 μ, 0 ≤ (inner ℂ (A u) u).re + ∑ i, ‖L i u‖ ^ 2 := by
  let P := fun u : Lp ℂ 2 μ =>
    0 ≤ (inner ℂ (A u) u).re + ∑ i, ‖L i u‖ ^ 2
  have hclosed : IsClosed {u | P u} :=
    isClosed_le continuous_const
      ((Complex.continuous_re.comp (A.continuous.inner continuous_id)).add
        (continuous_finsetSum _ fun i _ => ((L i).continuous.norm.pow 2)))
  have hall (f : C(UnitAddTorus I, ℂ)) : P (ContinuousMap.toLp 2 μ ℂ f) := by
    have hc : IsClosed {g : C(UnitAddTorus I, ℂ) | P (ContinuousMap.toLp 2 μ ℂ g)} :=
      hclosed.preimage (ContinuousMap.toLp 2 μ ℂ).continuous
    have hsub : (Submodule.span ℂ (Set.range (torusCharacter (ι := I))) :
        Set C(UnitAddTorus I, ℂ)) ⊆ {g | P (ContinuousMap.toLp 2 μ ℂ g)} := h
    have hclosure := hc.closure_subset_iff.mpr hsub
    rw [← Submodule.topologicalClosure_coe, span_torusCharacter_closure_eq_top] at hclosure
    exact hclosure Submodule.mem_top
  have hdense := ContinuousMap.toLp_denseRange ℂ μ (p := 2) ℂ (by norm_num)
  have hsub : Set.range (ContinuousMap.toLp 2 μ ℂ) ⊆ {u | P u} := by
    rintro _ ⟨f, rfl⟩
    exact hall f
  have hc := hclosed.closure_subset_iff.mpr hsub
  rw [hdense.closure_range] at hc
  exact fun u => hc (Set.mem_univ u)


/-- Repaired signed positivity on character packets extends to all tests in
`L²` of the total variation, including indicators of negative Hahn sets. -/
theorem torus_signed_corrected_nonneg_of_character_span
    {I : Type*} [Countable I] (P N : Measure (UnitAddTorus I))
    [IsFiniteMeasure P] [IsFiniteMeasure N] [(P + N).WeaklyRegular]
    (hmut : P ⟂ₘ N) {m : ℕ} (q : Fin m → C(UnitAddTorus I, ℂ))
    (h : ∀ f : C(UnitAddTorus I, ℂ),
      f ∈ Submodule.span ℂ (Set.range (torusCharacter (ι := I))) →
      0 ≤ (∫ x, ‖f x‖ ^ 2 ∂P) - (∫ x, ‖f x‖ ^ 2 ∂N) +
        ∑ i, ‖(∫ x, q i x * f x ∂P) - ∫ x, q i x * f x ∂N‖ ^ 2) :
    ∀ f : UnitAddTorus I → ℂ, MemLp f 2 (P + N) →
      0 ≤ (∫ x, ‖f x‖ ^ 2 ∂P) - (∫ x, ‖f x‖ ^ 2 ∂N) +
        ∑ i, ‖(∫ x, q i x * f x ∂P) - ∫ x, q i x * f x ∂N‖ ^ 2 := by
  let A := jordanSignMul hmut
  have hq (i : Fin m) : MemLp (q i) 2 (P + N) :=
    ContinuousMap.memLp (p := 2) (P + N) ℂ (q i)
  let L : Fin m → Lp ℂ 2 (P + N) →L[ℂ] ℂ := fun i =>
    _root_.HTGeometry.complexMulBilinear.lpPairing (P + N) 2 2
      (A ((hq i).toLp (q i)))
  have hpacket (f : C(UnitAddTorus I, ℂ))
      (hmem : f ∈ Submodule.span ℂ (Set.range (torusCharacter (ι := I)))) :
      0 ≤ (inner ℂ (A (ContinuousMap.toLp 2 (P + N) ℂ f))
        (ContinuousMap.toLp 2 (P + N) ℂ f)).re +
        ∑ i, ‖L i (ContinuousMap.toLp 2 (P + N) ℂ f)‖ ^ 2 := by
    have hf : MemLp f 2 (P + N) := ContinuousMap.memLp (p := 2) (P + N) ℂ f
    have he : hf.toLp f = ContinuousMap.toLp 2 (P + N) ℂ f := by
      apply Lp.ext
      exact hf.coeFn_toLp.trans (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (P + N) f).symm
    rw [← he]
    simpa only [A, L, jordanSignMul_energy, jordanSignMul_pairing] using h f hmem
  have hall := torus_corrected_quadratic_nonneg_of_character_span (P + N) A L hpacket
  intro f hf
  have hr := hall (hf.toLp f)
  simpa only [A, L, jordanSignMul_energy, jordanSignMul_pairing] using hr

end

end GaloisForLFunctions.HTGeometry
