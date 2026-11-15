import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldGenerators

/-!
# Homomorphisms determined by Kummer generators

The equalizer of two constant-field homomorphisms is an intermediate
field. Agreement on the rational coordinate and radical forces that
equalizer to be the whole Kummer field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (c : Kˣ) (b R n : ℕ)

/-- A homomorphism from a Kummer field is determined by its two named generators. -/
theorem kummerBranchField_algHom_ext
    (f g : KummerBranchField c b R n →ₐ[K] L)
    (hy : f (algebraMap K[X] (KummerBranchField c b R n) X) =
      g (algebraMap K[X] (KummerBranchField c b R n) X))
    (hz : f (AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) =
      g (AdjoinRoot.root (kummerBranchFieldPolynomial c b R n))) : f = g := by
  let E : IntermediateField K (KummerBranchField c b R n) :=
    { toSubalgebra := {
        toSubsemiring := (f.toRingHom.eqLocusField g.toRingHom).toSubring.toSubsemiring
        algebraMap_mem' := fun a => by
          change f (algebraMap K (KummerBranchField c b R n) a) =
            g (algebraMap K (KummerBranchField c b R n) a)
          rw [f.commutes, g.commutes] }
      inv_mem' := fun _ hx => (f.toRingHom.eqLocusField g.toRingHom).inv_mem hx }
  have htop : E = ⊤ := kummerBranchField_eq_top_of_coordinate_root_mem c b R n E hy hz
  ext x
  have hx : x ∈ E := by rw [htop]; trivial
  exact hx

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
