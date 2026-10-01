import GaloisForLFunctions.RHTower.ThetaTemperedMultiplicityJets
import GaloisForLFunctions.HTGeometry.PointSupportStructure
import GaloisForLFunctions.HTGeometry.SchwartzTranslation

/-!
# Point-supported tempered Xi-kernel functionals

Literal vanishing on every Schwartz test with a zero germ at a real point
is equivalent to membership in the original algebraic signed Dirac-jet
span. Finite order follows from Schwartz continuity. Combining this
structure theorem with the actual Xi multiplier leaves precisely the jets
whose order is below the actual zero multiplicity.
-/

noncomputable section

open scoped SchwartzMap Topology
open Filter

namespace RHTower

/-- A genuine zero germ kills every iterated derivative of the original test. -/
theorem thetaSchwartz_iteratedDeriv_eq_zero_of_vanish_near
    (φ : 𝓢(ℝ, ℂ)) (t : ℝ)
    (hφ : ∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → φ x = 0) (r : ℕ) :
    iteratedDeriv r (φ : ℝ → ℂ) t = 0 := by
  obtain ⟨δ, hδ, hφ⟩ := hφ
  have hgerm : (φ : ℝ → ℂ) =ᶠ[𝓝 t] (fun _ => (0 : ℂ)) :=
    Filter.eventually_of_mem (Metric.closedBall_mem_nhds t hδ) fun x hx =>
      hφ x (by
        have hd : dist x t ≤ δ := Metric.mem_closedBall.mp hx
        simpa only [Real.dist_eq] using hd)
  simpa only [iteratedDeriv_fun_const_zero] using hgerm.iteratedDeriv_eq r

/-- Every actual point-supported tempered functional has finite derivative order. -/
theorem thetaTemperedPointSupport_exists_derivative_representation
    (Q : 𝓢'(ℝ, ℂ)) (t : ℝ)
    (hQ : ∀ ψ : 𝓢(ℝ, ℂ),
      (∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → ψ x = 0) → Q ψ = 0) :
    ∃ (N : ℕ) (c : ℕ → ℂ), ∀ φ : 𝓢(ℝ, ℂ),
      Q φ = ∑ r ∈ Finset.range (N + 1), iteratedDeriv r (φ : ℝ → ℂ) t • c r := by
  have hzero : ∀ ψ : 𝓢(ℝ, ℂ),
      (∃ δ > 0, ∀ x : ℝ, |x| ≤ δ → ψ x = 0) →
      (Q.comp (SchwartzMap.translateCLM ℂ (-t))) ψ = 0 := by
    intro ψ hψ
    obtain ⟨δ, hδ, hψ⟩ := hψ
    apply hQ
    refine ⟨δ, hδ, ?_⟩
    intro x hx
    change ψ (x + -t) = 0
    exact hψ (x + -t) (by simpa only [sub_eq_add_neg] using hx)
  obtain ⟨N, c, hc⟩ :=
    GaloisForLFunctions.HTGeometry.exists_delta_representation
      (Q.comp (SchwartzMap.translateCLM ℂ (-t))) hzero
  refine ⟨N, c, fun φ => ?_⟩
  have h := hc (SchwartzMap.translateCLM ℂ t φ)
  rw [ContinuousLinearMap.comp_apply, SchwartzMap.translateCLM_neg_left] at h
  change Q φ = ∑ r ∈ Finset.range (N + 1),
    iteratedDeriv r (fun x : ℝ => φ (x + t)) 0 • c r at h
  simpa only [iteratedDeriv_comp_add_const, zero_add] using h

/-- Evaluation of the original finite signed Dirac-jet sum. -/
theorem thetaRealDiracJetSum_apply
    (t : ℝ) (N : ℕ) (a : ℕ → ℂ) (φ : 𝓢(ℝ, ℂ)) :
    thetaRealDiracJetSum t N a φ =
      ∑ r ∈ Finset.range N, a r * ((-1 : ℂ) ^ r * iteratedDeriv r (φ : ℝ → ℂ) t) := by
  simp only [thetaRealDiracJetSum, sum_apply, smul_apply,
    thetaRealDiracJet_apply, smul_eq_mul]

/-- Point support gives an actual finite sum of the original signed Dirac jets. -/
theorem thetaTemperedPointSupport_exists_diracJetSum
    (Q : 𝓢'(ℝ, ℂ)) (t : ℝ)
    (hQ : ∀ ψ : 𝓢(ℝ, ℂ),
      (∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → ψ x = 0) → Q ψ = 0) :
    ∃ (N : ℕ) (a : ℕ → ℂ), Q = thetaRealDiracJetSum t N a := by
  obtain ⟨N, c, hc⟩ := thetaTemperedPointSupport_exists_derivative_representation Q t hQ
  refine ⟨N + 1, fun r => (-1 : ℂ) ^ r * c r, ?_⟩
  apply ContinuousLinearMap.ext
  intro φ
  change Q φ = thetaRealDiracJetSum t (N + 1) (fun r => (-1 : ℂ) ^ r * c r) φ
  rw [hc, thetaRealDiracJetSum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_eq_mul]
  have hsign : (-1 : ℂ) ^ r * (-1 : ℂ) ^ r = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    iteratedDeriv r (φ : ℝ → ℂ) t * c r =
        ((-1 : ℂ) ^ r * (-1 : ℂ) ^ r) * (iteratedDeriv r (φ : ℝ → ℂ) t * c r) := by
          rw [hsign, one_mul]
    _ = ((-1 : ℂ) ^ r * c r) *
        ((-1 : ℂ) ^ r * iteratedDeriv r (φ : ℝ → ℂ) t) := by ring

/-- Literal support at a point is exactly the full original algebraic Dirac-jet span. -/
theorem thetaTemperedPointSupport_iff_diracJetSpan (Q : 𝓢'(ℝ, ℂ)) (t : ℝ) :
    (∀ ψ : 𝓢(ℝ, ℂ),
      (∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → ψ x = 0) → Q ψ = 0) ↔
      Q ∈ thetaRealDiracJetSpan t := by
  constructor
  · intro hQ
    obtain ⟨N, a, rfl⟩ := thetaTemperedPointSupport_exists_diracJetSum Q t hQ
    change (∑ r ∈ Finset.range N, a r • thetaRealDiracJet t r) ∈
      Submodule.span ℂ (Set.range (thetaRealDiracJet t))
    exact Submodule.sum_mem _ fun r _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  · intro hQ ψ hψ
    let ev : 𝓢'(ℝ, ℂ) →L[ℂ] ℂ :=
      PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ ψ
    have hspan : thetaRealDiracJetSpan t ≤ LinearMap.ker ev.toLinearMap := by
      change Submodule.span ℂ (Set.range (thetaRealDiracJet t)) ≤ _
      apply Submodule.span_le.mpr
      rintro _ ⟨r, rfl⟩
      change thetaRealDiracJet t r ψ = 0
      rw [thetaRealDiracJet_apply,
        thetaSchwartz_iteratedDeriv_eq_zero_of_vanish_near ψ t hψ r, mul_zero]
    exact hspan hQ

/-- All point-supported actual Xi-kernel functionals have precisely the lower-order jet span. -/
theorem thetaTemperedPointSupport_Xi_kernel_iff_lowerJetSpan
    (Q : 𝓢'(ℝ, ℂ)) (t : ℝ) :
    ((∀ ψ : 𝓢(ℝ, ℂ),
        (∃ δ > 0, ∀ x : ℝ, |x - t| ≤ δ → ψ x = 0) → Q ψ = 0) ∧
      thetaXiTemperedMultiplier Q = 0) ↔
      Q ∈ thetaXiTemperedLowerJetSpan t := by
  rw [thetaTemperedPointSupport_iff_diracJetSpan]
  rw [← thetaXiTemperedMultiplier_ker_inter_diracJetSpan t]
  rfl

end RHTower
