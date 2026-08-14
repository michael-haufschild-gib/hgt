import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# Algebraic independence depends only on the image of the coefficient ring

Algebraic independence of a family in `K` over a coefficient ring is a statement about the subring
of `K` that the coefficients occupy, not about the abstract ring presenting it.  Consequently two
coefficient rings with the same image in `K` are interchangeable, and independence over a larger
image implies independence over a smaller one.

This is the mechanism that lets a differential adjunction be replaced by any other presentation of
the same subfield of `K`, which is what an interchange of two adjoined generating sets produces.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The preimage of a coefficient under an injective ring map into `K` whose image contains the
image of a second coefficient ring. -/
def rangePreimage {R S : Type*} (K : Type*) [CommRing R] [CommRing S] [CommRing K]
    [Algebra R K] [Algebra S K] (c : S) : R :=
  haveI : Nonempty R := ⟨0⟩
  Function.invFun (algebraMap R K) (algebraMap S K c)

theorem algebraMap_rangePreimage {R S K : Type*} [CommRing R] [CommRing S] [CommRing K]
    [Algebra R K] [Algebra S K]
    (hsub : Set.range (algebraMap S K) ⊆ Set.range (algebraMap R K)) (c : S) :
    algebraMap R K (rangePreimage (R := R) K c) = algebraMap S K c :=
  haveI : Nonempty R := ⟨0⟩
  Function.invFun_eq (hsub (Set.mem_range_self c))

/-- The induced ring map between two coefficient rings with nested images in `K`. -/
def rangeFactor {R S K : Type*} [CommRing R] [CommRing S] [CommRing K]
    [Algebra R K] [Algebra S K] (hR : Function.Injective (algebraMap R K))
    (hsub : Set.range (algebraMap S K) ⊆ Set.range (algebraMap R K)) : S →+* R where
  toFun := rangePreimage K
  map_one' := hR (by simp [algebraMap_rangePreimage hsub])
  map_mul' a b := hR (by simp [map_mul, algebraMap_rangePreimage hsub])
  map_zero' := hR (by simp [algebraMap_rangePreimage hsub])
  map_add' a b := hR (by simp [map_add, algebraMap_rangePreimage hsub])

theorem algebraMap_rangeFactor {R S K : Type*} [CommRing R] [CommRing S] [CommRing K]
    [Algebra R K] [Algebra S K] (hR : Function.Injective (algebraMap R K))
    (hsub : Set.range (algebraMap S K) ⊆ Set.range (algebraMap R K)) (c : S) :
    algebraMap R K (rangeFactor hR hsub c) = algebraMap S K c :=
  algebraMap_rangePreimage hsub c

/-- **Coefficient transfer for algebraic independence.**  Independence over a coefficient ring whose
image in `K` contains the image of a second coefficient ring implies independence over the second
one. -/
theorem algebraicIndependent_of_range_subset {R S K ι : Type*}
    [CommRing R] [CommRing S] [CommRing K] [Algebra R K] [Algebra S K]
    (hR : Function.Injective (algebraMap R K)) (hS : Function.Injective (algebraMap S K))
    (hsub : Set.range (algebraMap S K) ⊆ Set.range (algebraMap R K))
    {v : ι → K} (hv : AlgebraicIndependent R v) : AlgebraicIndependent S v := by
  classical
  set φ : S →+* R := rangeFactor hR hsub with hφ
  have hφmap : ∀ c : S, algebraMap R K (φ c) = algebraMap S K c :=
    algebraMap_rangeFactor hR hsub
  have hφinj : Function.Injective φ := by
    intro a b hab
    refine hS ?_
    rw [← hφmap a, ← hφmap b, hab]
  refine algebraicIndependent_iff.mpr fun P hP => ?_
  have hzero : MvPolynomial.aeval v (MvPolynomial.map φ P) = 0 := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have hcomp : (algebraMap R K).comp φ = algebraMap S K := by
      ext c
      exact hφmap c
    rw [hcomp]
    rw [MvPolynomial.aeval_def] at hP
    exact hP
  exact MvPolynomial.map_injective φ hφinj (by
    rw [algebraicIndependent_iff.mp hv _ hzero, map_zero])

/-- Coefficient transfer for differential independence. -/
theorem differentialIndependent_of_range_subset {R S K ι : Type*}
    [CommRing R] [CommRing S] [CommRing K] [Algebra R K] [Algebra S K] [Differential K]
    (hR : Function.Injective (algebraMap R K)) (hS : Function.Injective (algebraMap S K))
    (hsub : Set.range (algebraMap S K) ⊆ Set.range (algebraMap R K))
    {x : ι → K} (hx : DifferentialIndependent R x) : DifferentialIndependent S x :=
  algebraicIndependent_of_range_subset hR hS hsub hx

/-- Coefficient transfer for differential algebraicity, in the direction opposite to the image
inclusion. -/
theorem differentialAlgebraicOver_of_range_subset {R S K : Type*}
    [CommRing R] [CommRing S] [CommRing K] [Algebra R K] [Algebra S K] [Differential K]
    (hR : Function.Injective (algebraMap R K)) (hS : Function.Injective (algebraMap S K))
    (hsub : Set.range (algebraMap S K) ⊆ Set.range (algebraMap R K))
    {y : K} (hy : DifferentialAlgebraicOver S y) : DifferentialAlgebraicOver R y :=
  fun h => hy (differentialIndependent_of_range_subset hR hS hsub h)

/-- The image of an intermediate field in the ambient field is its carrier. -/
theorem range_algebraMap_intermediateField {k K : Type*} [Field k] [Field K] [Algebra k K]
    (E : IntermediateField k K) : Set.range (algebraMap (↥E) K) = (E : Set K) := by
  ext y
  constructor
  · rintro ⟨⟨z, hz⟩, rfl⟩
    exact hz
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩

/-- Two intermediate fields of `K`, over possibly different bases, that occupy the same carrier
give the same differential independence statements. -/
theorem differentialIndependent_of_coe_eq {k k' K ι : Type*} [Field k] [Field k'] [Field K]
    [Algebra k K] [Algebra k' K] [Differential K]
    {E : IntermediateField k K} {E' : IntermediateField k' K}
    (h : (E : Set K) = (E' : Set K)) {x : ι → K}
    (hx : DifferentialIndependent (↥E) x) : DifferentialIndependent (↥E') x := by
  refine differentialIndependent_of_range_subset (R := ↥E) (S := ↥E')
    (algebraMap (↥E) K).injective (algebraMap (↥E') K).injective ?_ hx
  rw [range_algebraMap_intermediateField, range_algebraMap_intermediateField, h]

/-- Carrier equality transfers differential algebraicity between two presentations of the same
coefficient field. -/
theorem differentialAlgebraicOver_of_coe_eq {k k' K : Type*} [Field k] [Field k'] [Field K]
    [Algebra k K] [Algebra k' K] [Differential K]
    {E : IntermediateField k K} {E' : IntermediateField k' K}
    (h : (E : Set K) = (E' : Set K)) {y : K}
    (hy : DifferentialAlgebraicOver (↥E) y) : DifferentialAlgebraicOver (↥E') y :=
  fun hind => hy (differentialIndependent_of_coe_eq h.symm hind)

end

end GaloisForLFunctions.HTGeometry
