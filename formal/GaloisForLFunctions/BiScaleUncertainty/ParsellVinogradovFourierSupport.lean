import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fourier support on polynomial graphs

A continuous function supported on a graph is zero: on every vertical
line it vanishes outside one point, hence everywhere by continuity.
Fourier inversion transfers this to Schwartz sources. In particular,
the quadratic two-variable Parsell–Vinogradov surface cannot carry the
Fourier support of a nonzero Schwartz source.

This gives the smooth-source instance of Bi–Sun, *Lᵖ integrability of
functions with Fourier support on high codimension manifolds*, Theorem 1.1.
The argument applies to arbitrary graphs, with no regularity assumption
on the graphing function.
-/

open scoped FourierTransform

namespace GaloisForLFunctions.BiScaleUncertainty.ParsellVinogradov
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- A graph in Euclidean space, with `none` as the vertical coordinate. -/
def coordinateGraph (g : (ι → ℝ) → ℝ) : Set (EuclideanSpace ℝ (Option ι)) :=
  {x | x none = g (fun i => x (some i))}

private def vertical : EuclideanSpace ℝ (Option ι) :=
  WithLp.toLp 2 (fun j => match j with | none => 1 | some _ => 0)

/-- Every continuous function supported on an arbitrary graph vanishes. -/
theorem continuous_support_graph_iff (f : C(EuclideanSpace ℝ (Option ι), ℂ))
    (g : (ι → ℝ) → ℝ) :
    Function.support f ⊆ coordinateGraph g ↔ f = 0 := by
  constructor
  · intro hs
    apply ContinuousMap.ext
    intro x
    let v : EuclideanSpace ℝ (Option ι) := vertical
    let d := g (fun i => x (some i)) - x none
    have hh (t : ℝ) : (fun i => (x + t • v) (some i)) = fun i => x (some i) := by
      funext i
      change x (some i) + t * 0 = x (some i)
      ring
    have hv (t : ℝ) : (x + t • v) none = x none + t := by
      change x none + t * 1 = x none + t
      ring
    have hc : Continuous (fun t : ℝ => f (x + t • v)) :=
      f.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
    have he : (fun t : ℝ => f (x + t • v)) = fun _ => 0 := by
      apply Continuous.ext_on (dense_compl_singleton d) hc continuous_const
      intro t ht
      by_contra hne
      have hg := hs hne
      change (x + t • v) none = g (fun i => (x + t • v) (some i)) at hg
      rw [hh, hv] at hg
      have htd : t = d := by dsimp only [d]; linarith only [hg]
      exact ht (Set.mem_singleton_iff.mpr htd)
    have he0 := congrFun he 0
    simpa only [zero_smul, add_zero, ContinuousMap.zero_apply] using he0
  · rintro rfl
    simp

/-- Fourier inversion excludes every graph as the full support of a nonzero Schwartz transform. -/
theorem schwartz_fourier_support_graph_iff
    (f : SchwartzMap (EuclideanSpace ℝ (Option ι)) ℂ) (g : (ι → ℝ) → ℝ) :
    Function.support (⇑(𝓕 f : SchwartzMap (EuclideanSpace ℝ (Option ι)) ℂ)) ⊆
      coordinateGraph g ↔ f = 0 := by
  constructor
  · intro hs
    let F : C(EuclideanSpace ℝ (Option ι), ℂ) :=
      ⟨⇑(𝓕 f : SchwartzMap (EuclideanSpace ℝ (Option ι)) ℂ), (𝓕 f).continuous⟩
    have hF : F = 0 := (continuous_support_graph_iff F g).mp hs
    have hzero : 𝓕 f = 0 := by
      ext x
      exact congrArg (fun h : C(EuclideanSpace ℝ (Option ι), ℂ) => h x) hF
    apply (FourierTransform.fourierEquiv ℂ (SchwartzMap (EuclideanSpace ℝ (Option ι)) ℂ)).injective
    simpa using hzero
  · rintro rfl
    simp

/-- A nonzero Schwartz source has a nonzero Fourier value off every prescribed graph. -/
theorem schwartz_fourier_escape_graph
    (f : SchwartzMap (EuclideanSpace ℝ (Option ι)) ℂ) (g : (ι → ℝ) → ℝ) :
    f = 0 ∨ ∃ ξ, (𝓕 f : SchwartzMap (EuclideanSpace ℝ (Option ι)) ℂ) ξ ≠ 0 ∧
      ξ none ≠ g (fun i => ξ (some i)) := by
  by_cases hf : f = 0
  · exact Or.inl hf
  · have hn : ¬Function.support (⇑(𝓕 f : SchwartzMap (EuclideanSpace ℝ (Option ι)) ℂ)) ⊆
        coordinateGraph g :=
      fun h => hf ((schwartz_fourier_support_graph_iff f g).mp h)
    obtain ⟨ξ, hξ, hg⟩ := Set.not_subset.mp hn
    exact Or.inr ⟨ξ, hξ, hg⟩

/-- The quadratic monomial map, in coordinates `(x²; x,y,xy,y²)`. -/
def quadraticMomentLift (u : Fin 2 → ℝ) : EuclideanSpace ℝ (Option (Fin 4)) :=
  WithLp.toLp 2 (fun j => match j with
    | none => u 0 ^ 2
    | some i => ![u 0, u 1, u 0 * u 1, u 1 ^ 2] i)

/-- The two-variable, degree-two Parsell–Vinogradov surface over the unit square. -/
def quadraticMomentSurface : Set (EuclideanSpace ℝ (Option (Fin 4))) :=
  quadraticMomentLift '' Set.Icc (0 : Fin 2 → ℝ) 1

theorem quadraticMomentSurface_subset_graph :
    quadraticMomentSurface ⊆ coordinateGraph (fun u : Fin 4 → ℝ => u 0 ^ 2) := by
  rintro ξ ⟨u, _, rfl⟩
  rfl

/-- The five-dimensional quadratic surface supports no nonzero Schwartz Fourier transform. -/
theorem schwartz_fourier_support_quadraticMomentSurface_iff
    (f : SchwartzMap (EuclideanSpace ℝ (Option (Fin 4))) ℂ) :
    Function.support (⇑(𝓕 f : SchwartzMap (EuclideanSpace ℝ (Option (Fin 4))) ℂ)) ⊆
      quadraticMomentSurface ↔ f = 0 := by
  constructor
  · intro hs
    exact (schwartz_fourier_support_graph_iff f _).mp
      (hs.trans quadraticMomentSurface_subset_graph)
  · rintro rfl
    simp

#print axioms continuous_support_graph_iff
#print axioms schwartz_fourier_support_graph_iff
#print axioms schwartz_fourier_escape_graph
#print axioms schwartz_fourier_support_quadraticMomentSurface_iff

end
end GaloisForLFunctions.BiScaleUncertainty.ParsellVinogradov
