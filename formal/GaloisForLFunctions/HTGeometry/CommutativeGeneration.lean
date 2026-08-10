import GaloisForLFunctions.HTGeometry.CStarEnvelopeCommutative
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Generation in the commutative model

The envelope comparison theorems of `ShilovLocalBoundaryIdeal` reduce to one analytic input: that
the system topologically generates the ambient algebra,
`(Algebra.adjoin 𝕜 T).topologicalClosure = ⊤`.

In the commutative model this input is Stone–Weierstrass.  A self-adjoint set of continuous
functions separating the points of a compact space generates topologically
(`generates_of_separatesPoints`), and the image of a unital self-adjoint separating system in the
algebra of functions on its Shilov boundary is such a set
(`generates_envelope_image`).  So no hypothesis is left over.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ShilovLocal

open Set

/-- **Stone–Weierstrass as a generation statement.**  A self-adjoint separating set of continuous
functions on a compact space topologically generates. -/
theorem generates_of_separatesPoints {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Set C(Y, ℂ)) (hstar : ∀ f ∈ T, star f ∈ T)
    (hsep : ∀ y z : Y, y ≠ z → ∃ f ∈ T, (f : C(Y, ℂ)) y ≠ f z) :
    (Algebra.adjoin ℂ T).topologicalClosure = ⊤ := by
  have hTs : T ∪ star T = T := by
    ext f
    constructor
    · rintro (h | h)
      · exact h
      · rw [Set.mem_star] at h
        simpa using hstar _ h
    · exact fun h => Or.inl h
  have hadj : (StarAlgebra.adjoin ℂ T).toSubalgebra = Algebra.adjoin ℂ T := by
    rw [StarAlgebra.adjoin_toSubalgebra, hTs]
  have hsep' : (StarAlgebra.adjoin ℂ T).SeparatesPoints := by
    intro y z hyz
    obtain ⟨f, hf, hne⟩ := hsep y z hyz
    exact ⟨(f : Y → ℂ), ⟨f, StarAlgebra.subset_adjoin ℂ T hf, rfl⟩, hne⟩
  have hsw := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (StarAlgebra.adjoin ℂ T) hsep'
  have hcongr := congrArg StarSubalgebra.toSubalgebra hsw
  rw [StarSubalgebra.topologicalClosure_toSubalgebra_comm, hadj] at hcongr
  simpa using hcongr

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- **The generation input holds in the commutative model.**  The image of a unital self-adjoint
separating system under the envelope map topologically generates the functions on the Shilov
boundary. -/
theorem generates_envelope_image (S : Submodule ℂ C(X, ℂ)) (hstar : ∀ s ∈ S, star s ∈ S)
    (hsep : ∀ x y : X, x ≠ y → ∃ s ∈ S, (s : C(X, ℂ)) x ≠ s y) :
    (Algebra.adjoin ℂ (envelopeMap S '' (S : Set C(X, ℂ)))).topologicalClosure = ⊤ := by
  refine generates_of_separatesPoints _ ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨star s, hstar s hs, by rw [map_star]⟩
  · rintro ⟨y, hy⟩ ⟨z, hz⟩ hyz
    have hne : y ≠ z := fun h => hyz (Subtype.ext h)
    obtain ⟨s, hs, hsne⟩ := hsep y z hne
    exact ⟨envelopeMap S s, ⟨s, hs, rfl⟩, hsne⟩

/-- **The envelope comparison is bijective.**  Combining generation with an isometric comparison
map: there is no residual hypothesis in the commutative model. -/
theorem bijective_of_isometry_envelope {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (S : Submodule ℂ C(X, ℂ)) (hstar : ∀ s ∈ S, star s ∈ S)
    (hsep : ∀ x y : X, x ≠ y → ∃ s ∈ S, (s : C(X, ℂ)) x ≠ s y)
    (φ : A →ₐ[ℂ] C(shilovBoundary S, ℂ)) (hiso : Isometry φ)
    (hT : envelopeMap S '' (S : Set C(X, ℂ)) ⊆ Set.range φ) :
    Function.Bijective φ :=
  bijective_of_isometry_of_generates φ hiso hT (generates_envelope_image S hstar hsep)

end ShilovLocal

end GaloisForLFunctions.HTGeometry
