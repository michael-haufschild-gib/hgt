import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.BinaryArtinSchreier
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.LaurentIdempotents

/-!
# Artin–Schreier solution descent for Laurent algebras

Over every commutative binary algebra, a Laurent solution to an equation with
constant right-hand side is constant. Subtracting the augmentation produces
an Artin–Schreier kernel element, hence an idempotent. Laurent idempotent
rigidity then kills this augmentation-zero difference. No reducedness or
finiteness assumption on the coefficient ring is needed.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {A ι : Type*} [CommRing A] [Algebra (ZMod 2) A]

/-- A Laurent solution to an Artin–Schreier equation with constant right-hand side
is itself constant, even over a nonreduced coefficient ring. -/
theorem laurent_binaryArtinSchreier_eq_augmentation
    (f : AddMonoidAlgebra A (ι → ℤ)) (a : A)
    (hf : binaryArtinSchreier _ f = AddMonoidAlgebra.single 0 a) :
    f = AddMonoidAlgebra.single 0 (laurentAugmentation f) := by
  let c : A →+* AddMonoidAlgebra A (ι → ℤ) := AddMonoidAlgebra.singleZeroRingHom
  have ha : binaryArtinSchreier A (laurentAugmentation f) = a := by
    simpa only [binaryArtinSchreier_apply, map_add, map_pow, laurentAugmentation_single] using
      congrArg (laurentAugmentation (A := A) (ι := ι)) hf
  have hg : binaryArtinSchreier _ (f - c (laurentAugmentation f)) = 0 := by
    rw [map_sub, ← binaryArtinSchreier_map c, ha]
    exact sub_eq_zero.mpr hf
  have hi : IsIdempotentElem (f - c (laurentAugmentation f)) :=
    (binaryArtinSchreierKernelEquivIdempotents _ ⟨_, hg⟩).2
  have he := laurent_idempotent_eq_augmentation _ hi
  have hz : laurentAugmentation (f - c (laurentAugmentation f)) = 0 := by
    rw [map_sub]
    change laurentAugmentation f - laurentAugmentation
      (AddMonoidAlgebra.single 0 (laurentAugmentation f)) = 0
    rw [laurentAugmentation_single, sub_self]
  change f - c (laurentAugmentation f) = c (laurentAugmentation
    (f - c (laurentAugmentation f))) at he
  rw [hz, map_zero] at he
  exact sub_eq_zero.mp he

/-- Every nonconstant Laurent coefficient of a constant Artin–Schreier solution vanishes. -/
theorem laurent_binaryArtinSchreier_eq_constantCoeff
    (f : AddMonoidAlgebra A (ι → ℤ)) (a : A)
    (hf : binaryArtinSchreier _ f = AddMonoidAlgebra.single 0 a) :
    f = AddMonoidAlgebra.single 0 (f.coeff 0) := by
  have he := laurent_binaryArtinSchreier_eq_augmentation f a hf
  have hc := congrArg (fun g : AddMonoidAlgebra A (ι → ℤ) => g.coeff 0) he
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hc
  rw [hc]
  exact he

/-- Laurent extension creates no new solutions to a constant binary Artin–Schreier equation. -/
theorem laurent_binaryArtinSchreier_constant_iff
    (f : AddMonoidAlgebra A (ι → ℤ)) (a : A) :
    binaryArtinSchreier _ f = AddMonoidAlgebra.single 0 a ↔
      ∃ b : A, binaryArtinSchreier A b = a ∧ f = AddMonoidAlgebra.single 0 b := by
  constructor
  · intro hf
    refine ⟨laurentAugmentation f, ?_, laurent_binaryArtinSchreier_eq_augmentation f a hf⟩
    simpa only [binaryArtinSchreier_apply, map_add, map_pow, laurentAugmentation_single] using
      congrArg (laurentAugmentation (A := A) (ι := ι)) hf
  · rintro ⟨b, hb, rfl⟩
    simp only [binaryArtinSchreier_apply] at hb ⊢
    rw [AddMonoidAlgebra.single_pow, nsmul_zero, ← AddMonoidAlgebra.single_add, hb]

#print axioms laurent_binaryArtinSchreier_eq_augmentation
#print axioms laurent_binaryArtinSchreier_eq_constantCoeff
#print axioms laurent_binaryArtinSchreier_constant_iff
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
