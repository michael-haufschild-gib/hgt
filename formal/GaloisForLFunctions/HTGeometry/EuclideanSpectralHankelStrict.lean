import GaloisForLFunctions.HTGeometry.FiniteSpectralHankelRank
import GaloisForLFunctions.HTGeometry.FiniteStateSpaceHankelRank
import GaloisForLFunctions.HTGeometry.ObservablePushforwardHankelStrict

/-!
# Euclidean spectral sampling gives strict Hankel geometry

At positive clock spacing `tau`, a spectral energy `E` is reported by the Euclidean transfer node
`exp (-tau E)`.  Sampling a positive spectral measure at integer multiples of `tau` therefore
produces a moment sequence.  The reporter is injective, so infinite support of the energy measure
remains infinite support after observation.  Every finite sampled-correlator Hankel determinant is
strictly positive.

This is the value-level core shared by Källén--Lehmann representations, lattice Euclidean
correlators, relaxation spectra, and thermal response.  It uses no field equation or time flow.
-/

open Set MeasureTheory

namespace HTGeometry

noncomputable section

/-- The reported Euclidean node of a spectral energy at clock spacing `tau`. -/
def euclideanSpectralNode (tau energy : ℝ) : ℝ :=
  Real.exp (-tau * energy)

/-- Integer-clock samples of a positive Euclidean spectral correlation. -/
def euclideanSpectralMoments (mu : Measure ℝ) (tau : ℝ) (n : ℕ) : ℝ :=
  ∫ energy, euclideanSpectralNode tau energy ^ n ∂mu

/-- A nonzero Euclidean clock spacing separates spectral energies. -/
theorem euclideanSpectralNode_injective {tau : ℝ} (htau : tau ≠ 0) :
    Function.Injective (euclideanSpectralNode tau) := by
  intro energy₁ energy₂ h
  have hexponent := Real.exp_injective h
  apply mul_left_cancel₀ htau
  linarith

/-- Infinite energy support remains infinite after Euclidean spectral reporting. -/
theorem euclideanSpectralNode_infiniteSupport
    {mu : Measure ℝ} {tau : ℝ} (htau : tau ≠ 0)
    (hmuinf : ∀ F : Finset ℝ, 0 < mu {energy : ℝ | energy ∉ F}) :
    ∀ F : Finset ℝ, 0 < mu {energy | euclideanSpectralNode tau energy ∉ F} := by
  intro F
  let S : Set ℝ := euclideanSpectralNode tau ⁻¹' (↑F : Set ℝ)
  have hSfinite : S.Finite :=
    Set.Finite.preimage (euclideanSpectralNode_injective htau).injOn F.finite_toSet
  let G : Finset ℝ := hSfinite.toFinset
  have hset : {energy : ℝ | euclideanSpectralNode tau energy ∉ F} =
      {energy : ℝ | energy ∉ G} := by
    ext energy
    simp [G, S]
  rw [hset]
  exact hmuinf G

/-- The Euclidean samples are the ordinary moments of the observed spectral pushforward. -/
theorem euclideanSpectralMoments_eq_pushforward_moment
    (mu : Measure ℝ) (tau : ℝ) (n : ℕ) :
    euclideanSpectralMoments mu tau n =
      ∫ node, node ^ n ∂observablePushforwardMeasure mu (euclideanSpectralNode tau) := by
  rw [euclideanSpectralMoments,
    integral_pow_observablePushforwardMeasure mu (by fun_prop) n]

/-- **Euclidean spectral strictness.**  An integrable positive infinite spectral palette makes
every finite sampled-correlator Hankel determinant positive. -/
theorem det_momentHankelMatrix_euclideanSpectralMoments_pos
    {mu : Measure ℝ} {tau : ℝ} (htau : tau ≠ 0)
    (hint : ∀ n, Integrable (fun energy ↦ euclideanSpectralNode tau energy ^ n) mu)
    (hmuinf : ∀ F : Finset ℝ, 0 < mu {energy : ℝ | energy ∉ F})
    (n : ℕ) :
    0 < (momentHankelMatrix (euclideanSpectralMoments mu tau) n).det :=
  det_momentHankelMatrix_pos_of_observable_infiniteSupport
    mu (euclideanSpectralNode tau) (by fun_prop)
    (euclideanSpectralMoments mu tau) (fun _ ↦ rfl) hint
    (euclideanSpectralNode_infiniteSupport htau hmuinf) n

/-- An infinite positive Euclidean spectrum cannot have any prescribed finite modal width. -/
theorem euclideanSpectralMoments_not_finiteModalWidthAtMost
    {mu : Measure ℝ} {tau : ℝ} (htau : tau ≠ 0)
    (hint : ∀ n, Integrable (fun energy ↦ euclideanSpectralNode tau energy ^ n) mu)
    (hmuinf : ∀ F : Finset ℝ, 0 < mu {energy : ℝ | energy ∉ F})
    (d : ℕ) :
    ¬ FiniteModalWidthAtMost d (euclideanSpectralMoments mu tau) := by
  apply not_finiteModalWidthAtMost_of_det_ne_zero
  simpa [algebraicHankelMatrix, momentHankelMatrix] using
    ne_of_gt (det_momentHankelMatrix_euclideanSpectralMoments_pos
      htau hint hmuinf (d + 1))

/-- An infinite positive Euclidean spectrum escapes every uniformly bounded local linear
hidden-state model. -/
theorem euclideanSpectralMoments_not_fixedStateSpaceDimensionLocalClosure
    {mu : Measure ℝ} {tau : ℝ} (htau : tau ≠ 0)
    (hint : ∀ n, Integrable (fun energy ↦ euclideanSpectralNode tau energy ^ n) mu)
    (hmuinf : ∀ F : Finset ℝ, 0 < mu {energy : ℝ | energy ∉ F})
    (d : ℕ) :
    ¬ FixedStateSpaceDimensionLocalClosure d (euclideanSpectralMoments mu tau) := by
  apply not_fixedStateSpaceDimensionLocalClosure_of_det_ne_zero
  exact ne_of_gt (det_momentHankelMatrix_euclideanSpectralMoments_pos
    htau hint hmuinf (d + 1))

end

end HTGeometry
