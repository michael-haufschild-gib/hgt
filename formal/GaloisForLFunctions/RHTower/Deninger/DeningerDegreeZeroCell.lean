import GaloisForLFunctions.RHTower.Deninger.DeningerPositiveCellDegreeZero
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Degree-zero cells quotient degree zero by exactly the ideal they generate

Positive-degree relations leave degree zero untouched; degree-zero relations do not, and this is
what the rank quotient uses.  In a graded ring the degree-zero projection is a ring homomorphism
fixing degree zero, so an ideal generated in degree zero is stable under it: a degree-zero element
lies in the ideal exactly when it is a degree-zero combination of the generators.  Together with
the first isomorphism theorem this is the degree-zero computation of the rank quotient: dividing by
the kernel of a surjective rank map returns the target.

* `deningerDegreeZeroCell_proj_mem` : **an ideal generated in degree zero is projection stable.**
* `deningerDegreeZeroCell_mem_iff` : degree-zero membership is detected in degree zero.
* `deningerRankQuotient_equiv` : **dividing by the kernel of a surjective rank map returns the
  target.**
-/

namespace RHTower

section DegreeZeroCell

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- **An ideal generated in degree zero is stable under the degree-zero projection.** -/
theorem deningerDegreeZeroCell_proj_mem (S : Set A) (hS : ∀ s ∈ S, s ∈ 𝒜 0) {y : A}
    (hy : y ∈ Ideal.span S) : GradedRing.projZeroRingHom 𝒜 y ∈ Ideal.span S := by
  induction hy using Submodule.span_induction with
  | mem s hs =>
      have hfix : GradedRing.projZeroRingHom 𝒜 s = s := by
        show GradedRing.proj 𝒜 0 s = s
        rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (hS s hs)]
      rw [hfix]
      exact Ideal.subset_span hs
  | zero =>
      rw [map_zero]
      exact Ideal.zero_mem _
  | add u w _ _ hu hw =>
      rw [map_add]
      exact Ideal.add_mem _ hu hw
  | smul a u _ hu =>
      rw [smul_eq_mul, map_mul]
      exact Ideal.mul_mem_left _ _ hu

/-- **Degree-zero membership in a degree-zero ideal is detected after projection.** -/
theorem deningerDegreeZeroCell_mem_iff (S : Set A) {x : A}
    (hx : x ∈ 𝒜 0) : x ∈ Ideal.span S ↔ GradedRing.projZeroRingHom 𝒜 x ∈ Ideal.span S := by
  have hfix : GradedRing.projZeroRingHom 𝒜 x = x := by
    show GradedRing.proj 𝒜 0 x = x
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx]
  rw [hfix]

end DegreeZeroCell

section RankQuotient

/-- **The rank quotient in degree zero.**  Dividing the degree-zero ring by the kernel of a
surjective rank map returns the target: the rank-induced relations impose exactly the difference
between the Milnor--Witt and the Milnor coefficient constants. -/
noncomputable def deningerRankQuotient_equiv {A B : Type*} [CommRing A] [CommRing B]
    (r : A →+* B) (hr : Function.Surjective r) :
    (A ⧸ RingHom.ker r) ≃+* B :=
  RingHom.quotientKerEquivOfSurjective hr

/-- The rank-induced ideal is the kernel of the rank map, so no extra relations are imposed. -/
theorem deningerRankQuotient_span_ker {A B : Type*} [CommRing A] [CommRing B] (r : A →+* B) :
    Ideal.span (RingHom.ker r : Set A) = RingHom.ker r :=
  Ideal.span_eq _

end RankQuotient

end RHTower
