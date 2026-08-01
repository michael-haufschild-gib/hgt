import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Positive-degree cells do not change degree zero

Attaching relations in positive degrees means dividing by the ideal they generate.  In a graded
ring the degree-zero projection is a ring homomorphism, and it kills every generator of positive
degree, hence the whole ideal.  So no nonzero element of degree zero becomes zero in the quotient:
degree zero is preserved.

The statement is deliberately only about degree zero; positive cells do change higher degrees.

* `deningerPositiveCell_span_le_ker` : the ideal generated in positive degrees is killed by the
  degree-zero projection.
* `deningerPositiveCell_degreeZero_injective` : degree zero injects into the quotient.
* `deningerMonicQuotient_powerBasis`, `deningerMonic_isRegular` : the finite-free and
  non-zero-divisor inputs of the monic lift.
-/

namespace RHTower

section PositiveCell

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- **The degree-zero projection kills the ideal generated in positive degrees.** -/
theorem deningerPositiveCell_span_le_ker (S : Set A) (hS : ∀ s ∈ S, ∃ n, 0 < n ∧ s ∈ 𝒜 n) :
    Ideal.span S ≤ RingHom.ker (GradedRing.projZeroRingHom 𝒜) := by
  refine Ideal.span_le.mpr fun s hs => ?_
  obtain ⟨n, hn, hsn⟩ := hS s hs
  show GradedRing.projZeroRingHom 𝒜 s = 0
  show GradedRing.proj 𝒜 0 s = 0
  rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hsn (by omega)]

/-- **Degree zero is preserved.**  A degree-zero element that dies in the quotient by relations of
positive degree was already zero. -/
theorem deningerPositiveCell_degreeZero_injective (S : Set A)
    (hS : ∀ s ∈ S, ∃ n, 0 < n ∧ s ∈ 𝒜 n) {x : A} (hx : x ∈ 𝒜 0) (hmem : x ∈ Ideal.span S) :
    x = 0 := by
  have hker := deningerPositiveCell_span_le_ker 𝒜 S hS hmem
  have hproj : GradedRing.proj 𝒜 0 x = x := by
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx]
  have hzero : GradedRing.proj 𝒜 0 x = 0 := hker
  rw [hproj] at hzero
  exact hzero

/-- **Degree zero injects into the quotient.**  The composite of the inclusion of degree zero with
the quotient map is injective, which is the degree-zero invariance of a positive-cell
attachment. -/
theorem deningerPositiveCell_quotient_injOn (S : Set A) (hS : ∀ s ∈ S, ∃ n, 0 < n ∧ s ∈ 𝒜 n)
    {x y : A} (hx : x ∈ 𝒜 0) (hy : y ∈ 𝒜 0)
    (h : Ideal.Quotient.mk (Ideal.span S) x = Ideal.Quotient.mk (Ideal.span S) y) : x = y := by
  have hsub : x - y ∈ Ideal.span S := by
    rw [← Ideal.Quotient.eq]
    exact h
  have hxy : x - y ∈ 𝒜 0 := Submodule.sub_mem _ hx hy
  have := deningerPositiveCell_degreeZero_injective 𝒜 S hS hxy hsub
  exact sub_eq_zero.mp this

end PositiveCell

section MonicGenerator

/-- **A monic polynomial makes the quotient finite free.**  The quotient by a monic polynomial has
a power basis over the base, so it is finite free of rank the degree. -/
noncomputable def deningerMonicQuotient_powerBasis {A : Type*} [CommRing A] {P : Polynomial A}
    (hP : P.Monic) : PowerBasis A (AdjoinRoot P) :=
  AdjoinRoot.powerBasis' hP

/-- **A monic polynomial is a non-zero-divisor**, so the closed immersion it cuts out is regular of
codimension one. -/
theorem deningerMonic_isRegular {A : Type*} [CommRing A] [Nontrivial A] {P : Polynomial A}
    (hP : P.Monic) : IsRegular P :=
  Polynomial.Monic.isRegular hP

end MonicGenerator

end RHTower
