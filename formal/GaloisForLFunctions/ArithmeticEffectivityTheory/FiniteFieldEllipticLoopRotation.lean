import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLoopCharacters
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentCarrier
import GaloisForLFunctions.HTGeometry.LoopEisenstein.IntegralLoopRotation

/-!
# Idele degree rotation on the actual elliptic loop group

Every idele rotates the local Laurent variable. Its unit valuations outside
finitely many places preserve the restricted integral condition. The actual
positive Borel is preserved, and both of its idele spectral coordinates
are fixed componentwise.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein Filter
open scoped WithZero WithZeroMulInt
noncomputable section

/-- The coefficient unit of an idele at a finite place. -/
def finiteIdeleCoefficient (v : FinitePlace) : Ideles →* (v.adicCompletion K)ˣ :=
  Units.map (finiteAdeleEvaluation v).toMonoidHom

/-- The coefficient unit of an idele at infinity. -/
def infinityIdeleCoefficient : Ideles →* InfinityCompletionˣ :=
  Units.map (RingHom.snd FiniteAdeles InfinityCompletion).toMonoidHom

/-- An actual idele is a valuation unit at all but finitely many finite places. -/
theorem finiteIdeleCoefficient_eventually_unit (q : Ideles) :
    ∀ᶠ v : FinitePlace in cofinite,
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
        (finiteIdeleCoefficient v q : v.adicCompletion K) = 1 := by
  have hu : IsUnit (q : Adeles).1 := q.isUnit.map (RingHom.fst FiniteAdeles InfinityCompletion)
  exact (IsDedekindDomain.FiniteAdeleRing.isUnit_iff.mp hu).2

private def adelicDegreeRotationHom (q : Ideles) : AdelicLoop →* AdelicLoop where
  toFun g := (⟨fun v => LoopSL2.rotation (finiteIdeleCoefficient v q) (g.1 v), by
    filter_upwards [g.1.property, finiteIdeleCoefficient_eventually_unit q] with v hv hq
    exact LoopSL2.rotation_mem_integralLoop
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (finiteIdeleCoefficient v q) hq hv⟩,
    LoopSL2.rotation (infinityIdeleCoefficient q) g.2)
  map_one' := by
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      exact (LoopSL2.rotation (finiteIdeleCoefficient v q)).map_one
    · exact (LoopSL2.rotation (infinityIdeleCoefficient q)).map_one
  map_mul' g h := by
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      exact (LoopSL2.rotation (finiteIdeleCoefficient v q)).map_mul (g.1 v) (h.1 v)
    · exact (LoopSL2.rotation (infinityIdeleCoefficient q)).map_mul g.2 h.2

/-- Every actual idele acts by an automorphism of the restricted central loop group. -/
def adelicDegreeRotation (q : Ideles) : AdelicLoop ≃* AdelicLoop where
  toFun := adelicDegreeRotationHom q
  invFun := adelicDegreeRotationHom q⁻¹
  left_inv g := by
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      exact (LoopSL2.rotation (finiteIdeleCoefficient v q)).left_inv (g.1 v)
    · exact (LoopSL2.rotation (infinityIdeleCoefficient q)).left_inv g.2
  right_inv g := by
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      exact (LoopSL2.rotation (finiteIdeleCoefficient v q)).right_inv (g.1 v)
    · exact (LoopSL2.rotation (infinityIdeleCoefficient q)).right_inv g.2
  map_mul' := (adelicDegreeRotationHom q).map_mul

/-- Idele rotation preserves the literal adelic positive Borel. -/
theorem adelicDegreeRotation_mem_borel (q : Ideles) {g : AdelicLoop}
    (hg : g ∈ adelicPositiveBorel) : adelicDegreeRotation q g ∈ adelicPositiveBorel :=
  ⟨fun v => LoopSL2.rotation_mem_positiveBorel (finiteIdeleCoefficient v q) (hg.1 v),
    LoopSL2.rotation_mem_positiveBorel (infinityIdeleCoefficient q) hg.2⟩

/-- Restrict actual idele rotation to the actual adelic positive Borel. -/
def adelicBorelRotation (q : Ideles) : adelicPositiveBorel →* adelicPositiveBorel where
  toFun b := ⟨adelicDegreeRotation q b, adelicDegreeRotation_mem_borel q b.property⟩
  map_one' := Subtype.ext (adelicDegreeRotation q).map_one
  map_mul' a b := Subtype.ext ((adelicDegreeRotation q).map_mul a.1 b.1)

/-- Rotation fixes either intrinsic Borel coordinate as an actual idele. -/
theorem adelicBorelCoordinate_rotation (q : Ideles) (i : Bool) (b : adelicPositiveBorel) :
    adelicBorelCoordinate i (adelicBorelRotation q b) = adelicBorelCoordinate i b := by
  apply Units.ext
  apply Prod.ext
  · apply RestrictedProduct.ext
    intro v
    have h := LoopSL2.borelTorusHom_rotation (finiteIdeleCoefficient v q) (finiteBorelEvaluation v b)
    cases i
    · exact congrArg (fun z : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ =>
        (z.1 : v.adicCompletion K)) h
    · exact congrArg (fun z : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ =>
        (z.2 : v.adicCompletion K)) h
  · have h := LoopSL2.borelTorusHom_rotation (infinityIdeleCoefficient q) (infinityBorelEvaluation b)
    cases i
    · exact congrArg (fun z : InfinityCompletionˣ × InfinityCompletionˣ =>
        (z.1 : InfinityCompletion)) h
    · exact congrArg (fun z : InfinityCompletionˣ × InfinityCompletionˣ =>
        (z.2 : InfinityCompletion)) h

/-- Both actual idele coordinates are fixed by degree rotation. -/
theorem adelicBorelTorus_rotation (q : Ideles) (b : adelicPositiveBorel) :
    adelicBorelTorus (adelicBorelRotation q b) = adelicBorelTorus b :=
  Prod.ext (adelicBorelCoordinate_rotation q false b) (adelicBorelCoordinate_rotation q true b)

/-- Every spectral Borel character is fixed by actual idele rotation. -/
theorem adelicBorelCharacter_rotation (q : Ideles) (s t : ℂ) (b : adelicPositiveBorel) :
    adelicBorelCharacter s t (adelicBorelRotation q b) = adelicBorelCharacter s t b :=
  congrArg (ideleTorusCharacter s t) (adelicBorelTorus_rotation q b)

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicDegreeRotation
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicBorelCharacter_rotation
