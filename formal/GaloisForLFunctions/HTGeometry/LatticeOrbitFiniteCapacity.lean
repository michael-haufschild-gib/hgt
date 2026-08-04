import GaloisForLFunctions.HTGeometry.CompactKernelFunctionFieldCapacity

/-!
# An infinite orbit inside a finite-transcendence field is never free

Differential independence of a family forces the transcendence degree of the ambient field to be at
least the cardinality of the index.  So in a field of finite transcendence degree over the base -- a
relative function field of a proper family, for instance -- no infinitely indexed family is
differentially independent.

The cyclic case is the one used to detect a killed lattice direction, but nothing in the argument is
cyclic: a lattice of any rank, indeed any infinite acting group, has the same finite capacity.  This
is what the compact-kernel theorem asserts for an arbitrary finitely generated subgroup of the kernel,
and the factorized form covers the situation where only the compact part of the orbit lives in the
small field.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **An infinitely indexed family in a finite-transcendence field is never differentially
independent.** -/
theorem finiteTrdeg_infinite_not_differentialIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (hfinite : Algebra.trdeg F E < Cardinal.aleph0) {ι : Type*} [Infinite ι] (x : ι → E) :
    ¬ DifferentialIndependent F x := by
  intro hx
  have hle := hx.algebraicIndependent.lift_cardinalMk_le_trdeg
  have hmk : Cardinal.aleph0 ≤ Cardinal.lift (Cardinal.mk ι) :=
    (Cardinal.aleph0_le_lift).2 (Cardinal.aleph0_le_mk ι)
  have haleph : Cardinal.aleph0 ≤ Algebra.trdeg F E :=
    (Cardinal.aleph0_le_lift).1 (le_trans hmk hle)
  exact (not_lt_of_ge haleph) hfinite

/-- **The complete orbit of an infinite lattice inside a finite-transcendence field has finite
capacity.**  Only the compact part of the orbit has to lie in the small field: an injective algebra
map carries the obstruction into the ambient differential field. -/
theorem finiteTrdeg_factorized_orbit_not_differentialIndependent
    {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Differential K]
    (hfinite : Algebra.trdeg F E < Cardinal.aleph0)
    (embed : E →ₐ[F] K) (hembed : Function.Injective embed)
    {L : Type*} [Infinite L] (compactOrbit : L → E) (orbit : L → K)
    (hfactor : ∀ l, orbit l = embed (compactOrbit l)) :
    ¬ DifferentialIndependent F orbit := by
  intro horbit
  have heq : orbit = fun l => embed (compactOrbit l) := funext hfactor
  rw [heq] at horbit
  have hcompact : AlgebraicIndependent F compactOrbit :=
    (AlgHom.algebraicIndependent_iff embed hembed).mp horbit.algebraicIndependent
  have hle := hcompact.lift_cardinalMk_le_trdeg
  have hmk : Cardinal.aleph0 ≤ Cardinal.lift (Cardinal.mk L) :=
    (Cardinal.aleph0_le_lift).2 (Cardinal.aleph0_le_mk L)
  have haleph : Cardinal.aleph0 ≤ Algebra.trdeg F E :=
    (Cardinal.aleph0_le_lift).1 (le_trans hmk hle)
  exact (not_lt_of_ge haleph) hfinite

/-- **Active-quotient necessity for a lattice of any rank.**  If every nonzero kernel direction
generates an infinite subgroup whose orbit lies in a finite-transcendence field, a completely free
orbit forces faithfulness on the quotient. -/
theorem activeQuotient_injective_of_fullOrbitFree_of_infiniteKernelOrbit
    {F E K L Q : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Differential K]
    [AddCommGroup L] [AddCommGroup Q]
    (hfinite : Algebra.trdeg F E < Cardinal.aleph0)
    (embed : E →ₐ[F] K) (hembed : Function.Injective embed)
    (orbit : L → K) (horbit : DifferentialIndependent F orbit) (q : L →+ Q)
    (hcyclic : ∀ k : L, k ≠ 0 → Function.Injective fun n : ℤ => n • k)
    (compactPart : ∀ k : L, q k = 0 → k ≠ 0 → ∃ c : ℤ → E, ∀ n : ℤ, orbit (n • k) = embed (c n)) :
    Function.Injective q := by
  refine activeQuotient_injective_of_fullOrbitFree_of_kernelCyclic_not orbit horbit q hcyclic ?_
  intro k hk hkne
  obtain ⟨c, hc⟩ := compactPart k hk hkne
  exact finiteTrdeg_factorized_orbit_not_differentialIndependent hfinite embed hembed c
    (fun n : ℤ => orbit (n • k)) hc

end

end GaloisForLFunctions.HTGeometry

open CategoryTheory

namespace AlgebraicGeometry

universe u

noncomputable section

/-- **Every orbit of an infinite lattice in a proper relative function field has finite capacity.** -/
theorem properRelativeFunctionField_orbit_not_differentialIndependent
    {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (p : X ⟶ S) [IsDominant p] [IsProper p]
    [Differential X.functionField] {L : Type*} [Infinite L] (x : L → X.functionField) :
    letI := p.functionFieldAlgebra
    ¬ GaloisForLFunctions.DifferentialIndependent S.functionField x := by
  letI := p.functionFieldAlgebra
  exact GaloisForLFunctions.HTGeometry.finiteTrdeg_infinite_not_differentialIndependent
    p.functionField_trdeg_lt_aleph0 x

end

end AlgebraicGeometry
