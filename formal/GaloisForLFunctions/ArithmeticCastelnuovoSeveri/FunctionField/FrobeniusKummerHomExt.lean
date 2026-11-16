import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusKummerFields

/-!
# Homomorphisms determined by Frobenius radical generators

The equalizer of two constant-field homomorphisms is an intermediate
field. Agreement on the rational coordinate and radical forces that
equalizer to be the whole Frobenius radical field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (c : Kˣ) (b R n : ℕ)

/-- A homomorphism from a Frobenius radical field is determined by its two named generators. -/
theorem frobeniusKummerField_algHom_ext
    (f g : FrobeniusKummerField c b R n →ₐ[K] L)
    (hy : f (algebraMap K[X] (FrobeniusKummerField c b R n) X) =
      g (algebraMap K[X] (FrobeniusKummerField c b R n) X))
    (hz : f (AdjoinRoot.root (frobeniusKummerFieldPolynomial c b R n)) =
      g (AdjoinRoot.root (frobeniusKummerFieldPolynomial c b R n))) : f = g := by
  let E : IntermediateField K (FrobeniusKummerField c b R n) :=
    { toSubalgebra := {
        toSubsemiring := (f.toRingHom.eqLocusField g.toRingHom).toSubring.toSubsemiring
        algebraMap_mem' := fun a => by
          change f (algebraMap K (FrobeniusKummerField c b R n) a) =
            g (algebraMap K (FrobeniusKummerField c b R n) a)
          rw [f.commutes, g.commutes] }
      inv_mem' := fun _ hx => (f.toRingHom.eqLocusField g.toRingHom).inv_mem hx }
  have htop : E = ⊤ := frobeniusKummerField_eq_top_of_coordinate_root_mem c b R n E hy hz
  apply AlgHom.ext
  intro x
  have hx : x ∈ E := by rw [htop]; trivial
  exact hx

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
