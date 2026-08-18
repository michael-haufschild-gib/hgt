import Mathlib
import GaloisForLFunctions.HTGeometry.BivariateRootCovering

/-!
# The space of complex points of an algebra, and its chart into the root locus

For an algebra `B` over the polynomial ring `ℂ[X]`, the set of `ℂ`-algebra homomorphisms `B → ℂ`,
topologised by pointwise convergence, projects to the parameter line.  Where a single element `θ`
generates `B` — which by `LocalNakayamaMonogenic` happens Zariski-locally for a finite étale
algebra — this space is carried injectively into the root locus of a monic relation satisfied by
`θ`, and the root locus is already known to be a covering space (`BivariateRootCovering`).

This is the chart datum for the general (non-monogenic) simple connectedness of the affine line.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- The space of `ℂ`-points of a `ℂ`-algebra, topologised by pointwise convergence. -/
def AlgSpec (B : Type*) [CommRing B] [Algebra ℂ B] := B →ₐ[ℂ] ℂ

namespace AlgSpec

variable {B : Type*} [CommRing B] [Algebra ℂ B]

instance : FunLike (AlgSpec B) B ℂ := inferInstanceAs (FunLike (B →ₐ[ℂ] ℂ) B ℂ)

instance : AlgHomClass (AlgSpec B) ℂ B ℂ := inferInstanceAs (AlgHomClass (B →ₐ[ℂ] ℂ) ℂ B ℂ)

instance : TopologicalSpace (AlgSpec B) :=
  TopologicalSpace.induced (fun χ : AlgSpec B => (χ : B → ℂ)) inferInstance

theorem continuous_eval (b : B) : Continuous fun χ : AlgSpec B => χ b := by
  refine Continuous.comp (continuous_apply b) ?_
  exact continuous_induced_dom

theorem isInducing_coe : Topology.IsInducing (fun χ : AlgSpec B => (χ : B → ℂ)) :=
  ⟨rfl⟩

theorem isEmbedding_coe : Topology.IsEmbedding (fun χ : AlgSpec B => (χ : B → ℂ)) :=
  ⟨isInducing_coe, fun _ _ h => DFunLike.ext _ _ (fun b => congrFun h b)⟩

/-- The structure map to the parameter line, for an algebra over the polynomial ring. -/
def proj (B : Type*) [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B]
    [IsScalarTower ℂ ℂ[X] B] (χ : AlgSpec B) : ℂ :=
  χ (algebraMap ℂ[X] B X)

theorem continuous_proj (B : Type*) [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B]
    [IsScalarTower ℂ ℂ[X] B] : Continuous (proj B) :=
  continuous_eval _

section Tower

variable (B : Type*) [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- On the polynomial ring, a `ℂ`-point of `B` is evaluation at its projection. -/
theorem apply_algebraMap (χ : AlgSpec B) (q : ℂ[X]) :
    χ (algebraMap ℂ[X] B q) = q.eval (proj B χ) := by
  have h : ((χ : B →ₐ[ℂ] ℂ).comp (IsScalarTower.toAlgHom ℂ ℂ[X] B)) =
      Polynomial.aeval (proj B χ) := by
    apply Polynomial.algHom_ext
    show χ (algebraMap ℂ[X] B X) = Polynomial.aeval (proj B χ) X
    rw [Polynomial.aeval_X]
    rfl
  have hq := DFunLike.congr_fun h q
  show χ (algebraMap ℂ[X] B q) = q.eval (proj B χ)
  rw [show χ (algebraMap ℂ[X] B q) =
    ((χ : B →ₐ[ℂ] ℂ).comp (IsScalarTower.toAlgHom ℂ ℂ[X] B)) q from rfl, hq]
  simp

variable {B}

/-- Evaluation of a two-variable polynomial at a `ℂ`-point. -/
theorem apply_aeval (θ : B) (q : ℂ[X][X]) (χ : AlgSpec B) :
    χ (Polynomial.aeval θ q) = biEval q (proj B χ, χ θ) := by
  have hcomp : ((χ : B →ₐ[ℂ] ℂ) : B →+* ℂ).comp (algebraMap ℂ[X] B) =
      Polynomial.evalRingHom (proj B χ) :=
    RingHom.ext fun r => apply_algebraMap B χ r
  have h := Polynomial.hom_eval₂ q (algebraMap ℂ[X] B) ((χ : B →ₐ[ℂ] ℂ) : B →+* ℂ) θ
  rw [hcomp] at h
  simpa [Polynomial.aeval_def, biEval] using h

/-- The chart map of a `ℂ`-point into the plane, recording its projection and the value of a
chosen element. -/
def toPlane (θ : B) (χ : AlgSpec B) : ℂ × ℂ := (proj B χ, χ θ)

theorem continuous_toPlane (θ : B) : Continuous (toPlane (B := B) θ) :=
  (continuous_proj B).prodMk (continuous_eval θ)

/-- A `ℂ`-point lands on the root locus of any monic relation satisfied by `θ`. -/
theorem toPlane_mem_biRootLocus {θ : B} {p : ℂ[X][X]} (hp : Polynomial.aeval θ p = 0)
    (χ : AlgSpec B) : toPlane θ χ ∈ BiRootLocus p := by
  show biEval p (toPlane θ χ) = 0
  rw [toPlane, ← apply_aeval θ p χ, hp, map_zero]

/-- Where `θ` generates, the chart map is injective. -/
theorem toPlane_injOn {θ : B} {U : Set ℂ}
    (hgen : ∀ b : B, ∃ (q : ℂ[X][X]) (g : ℂ[X]), (∀ s ∈ U, g.eval s ≠ 0) ∧
      (algebraMap ℂ[X] B g) * b = Polynomial.aeval θ q) :
    Set.InjOn (toPlane (B := B) θ) (proj B ⁻¹' U) := by
  intro χ hχ ψ _ hEq
  have hproj : proj B χ = proj B ψ := congrArg Prod.fst hEq
  have hθ : χ θ = ψ θ := congrArg Prod.snd hEq
  apply DFunLike.ext
  intro b
  obtain ⟨q, g, hg, hb⟩ := hgen b
  have h1 : g.eval (proj B χ) * χ b = biEval q (proj B χ, χ θ) := by
    have := congrArg (fun x => χ x) hb
    simpa [apply_algebraMap B χ g, apply_aeval θ q χ] using this
  have h2 : g.eval (proj B ψ) * ψ b = biEval q (proj B ψ, ψ θ) := by
    have := congrArg (fun x => ψ x) hb
    simpa [apply_algebraMap B ψ g, apply_aeval θ q ψ] using this
  rw [hproj, hθ] at h1
  have hne : g.eval (proj B ψ) ≠ 0 := hg _ (hproj ▸ hχ)
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

end Tower

end AlgSpec

end

end GaloisForLFunctions.HTGeometry
