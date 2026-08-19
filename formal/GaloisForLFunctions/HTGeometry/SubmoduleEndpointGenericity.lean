/-
# Endpoint completeness at a maximally projective parameter of a Hermitian matrix subspace

The genericity law for a real Hermitian matrix subspace produces a *dense* set of coordinate
vectors with maximally projective spectrum, and endpoint visibility of the canonical eigenvectors
is an *open* condition wherever the spectrum is simple.  The two therefore meet: from one base
point with simple spectrum at which every ordered pair is endpoint visible, there is a coordinate
vector which is simultaneously maximally projective and endpoint complete.

This is the induction step of the extension lemma in the coordinates of an arbitrary architecture:
applied to the exact traceless local-Hamiltonian subspace of a tensor-tree system it produces a
maximally projective, endpoint-complete local Hamiltonian.

Main results:
* `submoduleLinearFamily` — the complexified canonical coordinate family.
* `exists_analyticBranches_submoduleLinearFamily` — analytic eigenvalue branches at a simple point.
* `exists_mem_realHermitianSubmoduleMaximalSet_endpointComplete` — **the intersection**.
-/
import GaloisForLFunctions.HTGeometry.RealParameterEndpointIntersection
import GaloisForLFunctions.HTGeometry.TracelessLocalHamiltonianGenericityLaw
import GaloisForLFunctions.HTGeometry.HermitianInertia

open Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {S : Type u} [Fintype S] [DecidableEq S]

/-- The complexified canonical coordinate family of a real matrix submodule. -/
def submoduleLinearFamily (L : Submodule ℝ (Matrix S S ℂ)) :
    (Fin (Module.finrank ℝ L) → ℂ) → Matrix S S ℂ :=
  fun θ => ∑ t, θ t • realMatrixSubmoduleGenerator L t

omit [DecidableEq S] in
theorem submoduleLinearFamily_apply (L : Submodule ℝ (Matrix S S ℂ))
    (θ : Fin (Module.finrank ℝ L) → ℂ) :
    submoduleLinearFamily L θ = ∑ t, θ t • realMatrixSubmoduleGenerator L t := rfl

omit [DecidableEq S] in
/-- On real coordinates the complexified family is the canonical affine coordinate family. -/
theorem submoduleLinearFamily_ofReal (L : Submodule ℝ (Matrix S S ℂ))
    (q : Fin (Module.finrank ℝ L) → ℝ) :
    submoduleLinearFamily L (fun t => ((q t : ℝ) : ℂ))
      = realAffineMatrix 0 (realMatrixSubmoduleGenerator L) q := by
  refine Matrix.ext fun a b => ?_
  simp [submoduleLinearFamily, realAffineMatrix, Matrix.sum_apply]

omit [DecidableEq S] in
/-- Canonical Hermitian witness for the coordinate family of a Hermitian matrix submodule. -/
theorem realHermitianSubmoduleFamily_isHermitian (L : Submodule ℝ (Matrix S S ℂ))
    (hL : L ≤ selfAdjoint.submodule ℝ (Matrix S S ℂ))
    (q : Fin (Module.finrank ℝ L) → ℝ) :
    (realAffineMatrix 0 (realMatrixSubmoduleGenerator L) q).IsHermitian :=
  realAffineMatrix_isHermitian 0 (realMatrixSubmoduleGenerator L) Matrix.isHermitian_zero
    (realMatrixSubmoduleGenerator_isHermitian L hL) q

/-- **Analytic eigenvalue branches of a Hermitian matrix subspace at a simple point.** -/
theorem exists_analyticBranches_submoduleLinearFamily (L : Submodule ℝ (Matrix S S ℂ))
    (hL : L ≤ selfAdjoint.submodule ℝ (Matrix S S ℂ))
    (q₀ : Fin (Module.finrank ℝ L) → ℝ)
    (hinj : Function.Injective (realHermitianSubmoduleFamily_isHermitian L hL q₀).eigenvalues) :
    ∃ branch : S → (Fin (Module.finrank ℝ L) → ℂ) → ℂ,
      (∀ x, AnalyticAt ℂ (branch x) (fun t => ((q₀ t : ℝ) : ℂ))) ∧
      ∀ x, branch x (fun t => ((q₀ t : ℝ) : ℂ)) =
        (((realHermitianSubmoduleFamily_isHermitian L hL q₀).eigenvalues x : ℝ) : ℂ) := by
  classical
  set hHerm := realHermitianSubmoduleFamily_isHermitian L hL q₀ with hHermDef
  have hU1 : (hHerm.eigenvectorUnitary : Matrix S S ℂ)ᴴ *
      (hHerm.eigenvectorUnitary : Matrix S S ℂ) = 1 := by
    have h := Unitary.coe_star_mul_self hHerm.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose] at h
  have hbase : (hHerm.eigenvectorUnitary : Matrix S S ℂ)ᴴ *
      (∑ t, ((q₀ t : ℝ) : ℂ) • realMatrixSubmoduleGenerator L t) *
      (hHerm.eigenvectorUnitary : Matrix S S ℂ)
      = Matrix.diagonal (fun i => ((hHerm.eigenvalues i : ℝ) : ℂ)) := by
    have h : (∑ t, ((q₀ t : ℝ) : ℂ) • realMatrixSubmoduleGenerator L t)
        = realAffineMatrix 0 (realMatrixSubmoduleGenerator L) q₀ :=
      submoduleLinearFamily_ofReal L q₀
    rw [h]
    exact conjTranspose_mul_mul_eigenvectorUnitary hHerm
  have hinjC : Function.Injective (fun i => ((hHerm.eigenvalues i : ℝ) : ℂ)) := by
    intro i j hij
    have hij' : ((hHerm.eigenvalues i : ℝ) : ℂ) = ((hHerm.eigenvalues j : ℝ) : ℂ) := hij
    exact hinj (Complex.ofReal_injective hij')
  choose branch hban hb0 _hroot using fun x =>
    exists_analyticBranches_linearFamily (realMatrixSubmoduleGenerator L)
      (fun t => ((q₀ t : ℝ) : ℂ)) hU1 (fun i => ((hHerm.eigenvalues i : ℝ) : ℂ)) hinjC hbase x
  exact ⟨branch, hban, hb0⟩

variable {A : Type u} [Fintype A] [DecidableEq A]

/-- **The induction step in the coordinates of a Hermitian matrix subspace.**  From a base
coordinate vector whose spectrum is maximally projective and whose canonical eigenvectors are
pairwise endpoint visible, there is a coordinate vector which is simultaneously maximally
projective and endpoint complete. -/
theorem exists_mem_realHermitianSubmoduleMaximalSet_endpointComplete
    (L : Submodule ℝ (Matrix (A × Bool) (A × Bool) ℂ))
    (hL : L ≤ selfAdjoint.submodule ℝ (Matrix (A × Bool) (A × Bool) ℂ))
    (q₀ : Fin (Module.finrank ℝ L) → ℝ)
    (hmax₀ : MaximallyProjectiveEnergy
      (realHermitianSubmoduleFamily_isHermitian L hL q₀).eigenvalues) :
    ∃ branch : (A × Bool) → (Fin (Module.finrank ℝ L) → ℂ) → ℂ,
      (∀ x, AnalyticAt ℂ (branch x) (fun t => ((q₀ t : ℝ) : ℂ))) ∧
      (∀ x, branch x (fun t => ((q₀ t : ℝ) : ℂ)) =
        (((realHermitianSubmoduleFamily_isHermitian L hL q₀).eigenvalues x : ℝ) : ℂ)) ∧
      ((∀ p : (A × Bool) × (A × Bool), p.1 ≠ p.2 →
          layerReducedTransition
            (realEndpointEigenvector (submoduleLinearFamily L) branch p.1 q₀)
            (realEndpointEigenvector (submoduleLinearFamily L) branch p.2 q₀) ≠ 0) →
        ∃ q ∈ realHermitianSubmoduleMaximalSet L hL,
          ∀ p : (A × Bool) × (A × Bool), p.1 ≠ p.2 →
            layerReducedTransition
              (realEndpointEigenvector (submoduleLinearFamily L) branch p.1 q)
              (realEndpointEigenvector (submoduleLinearFamily L) branch p.2 q) ≠ 0) := by
  classical
  obtain ⟨branch, hban, hb0⟩ :=
    exists_analyticBranches_submoduleLinearFamily L hL q₀
      (MaximallyProjectiveEnergy.injective hmax₀)
  refine ⟨branch, hban, hb0, fun hcomplete => ?_⟩
  have hdense : Dense (realHermitianSubmoduleMaximalSet L hL) :=
    (realHermitianSubmoduleMaximalSet_dense_residual_fullMeasure L hL
      (realAffineMatrix 0 (realMatrixSubmoduleGenerator L) q₀)
      (realAffineMatrix_mem_submodule L q₀)
      (realHermitianSubmoduleFamily_isHermitian L hL q₀) hmax₀).1
  have hH : AnalyticAt ℂ (submoduleLinearFamily L) (fun t => ((q₀ t : ℝ) : ℂ)) :=
    analyticAt_linearMatrixFamily (realMatrixSubmoduleGenerator L) _
  exact exists_mem_dense_realParameter_endpointComplete hH hban hcomplete hdense

end

end GaloisForLFunctions.HTGeometry
