import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCharacter
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicBlockMatrices
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedFunctionTwist

/-! Inducing from a parabolic with unitriangular right block gives the
Harish–Chandra product with the Gelfand–Graev character. -/

noncomputable section
open GaloisForLFunctions
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

/-- Parabolic matrices whose right Levi block is upper unitriangular. -/
def rightUnitriangularParabolic (g a b : ℕ) [Fact g.Prime] :
    Subgroup (twoBlockParabolic g a b) :=
  ((upperUnitriangular g b).comap (MonoidHom.snd (Gn g a) (Gn g b))).comap twoBlockLevi

/-- The inducing function uses the given left character and the Whittaker character on the right. -/
def rightUnitriangularFunction (ψ : AddChar (ZMod g) ℂ) (α : Gn g a → ℂ)
    (u : rightUnitriangularParabolic g a b) : ℂ :=
  α (twoBlockLevi u.val).1 *
    (whittakerCharacter ψ b ⟨(twoBlockLevi u.val).2, u.property⟩ : ℂ)

private theorem induced_rightLevi (ψ : AddChar (ZMod g) ℂ) (α : Gn g a → ℂ)
    (hα : IsClass α) (x : Gn g a × Gn g b) :
    inducedFunction ((upperUnitriangular g b).comap (MonoidHom.snd (Gn g a) (Gn g b)))
      (fun z => α z.val.1 * (whittakerCharacter ψ b ⟨z.val.2, z.property⟩ : ℂ)) x =
        α x.1 * gg ψ b x.2 := by
  let p := MonoidHom.snd (Gn g a) (Gn g b)
  let U := upperUnitriangular g b
  let φ (u : U) : ℂ := whittakerCharacter ψ b u
  have hp : Function.Surjective p := fun y => ⟨(1, y), rfl⟩
  have hcl : IsClass (fun y : Gn g a × Gn g b => α y.1) :=
    fun y z => hα y.1 z.1
  change inducedFunction (U.comap p)
    (fun z => α z.val.1 * φ ⟨p z.val, z.property⟩) x = _
  rw [inducedFunction_mul_class (U.comap p) (fun z => φ ⟨p z.val, z.property⟩)
    (fun y : Gn g a × Gn g b => α y.1) (fun y z => hcl y z) x,
    inducedFunction_comap p hp U φ x]
  change α x.1 * inducedFunction U φ x.2 = _
  rw [gg_eq_inducedFunction]

/-- The Harish–Chandra product with the Gelfand–Graev character is induction
from the parabolic with unitriangular right block. -/
theorem hc_eq_induced_rightUnitriangular (ψ : AddChar (ZMod g) ℂ) (α : Gn g a → ℂ)
    (hα : IsClass α) :
    let P := twoBlockParabolic g a b
    let U := rightUnitriangularParabolic g a b
    let e := U.equivMapOfInjective P.subtype P.subtype_injective
    hc a b α (gg ψ b) (a + b) =
      inducedFunction (U.map P.subtype) (fun z => rightUnitriangularFunction ψ α (e.symm z)) := by
  dsimp only
  let P := twoBlockParabolic g a b
  let U := rightUnitriangularParabolic g a b
  let p := MonoidHom.snd (Gn g a) (Gn g b)
  let H := (upperUnitriangular g b).comap p
  let f (z : H) : ℂ := α z.val.1 *
    (whittakerCharacter ψ b ⟨z.val.2, z.property⟩ : ℂ)
  have hπ : Function.Surjective (twoBlockLevi (g := g) (a := a) (b := b)) := by
    rintro ⟨A, B⟩
    exact ⟨⟨upperBlockUnit A 0 B, inPar_upperBlockMatrix A.val 0 B.val⟩,
      twoBlockLevi_upperBlockUnit A 0 B⟩
  have he (u : P) : inducedFunction U (rightUnitriangularFunction ψ α) u =
      α (twoBlockLevi u).1 * gg ψ b (twoBlockLevi u).2 := by
    change inducedFunction (H.comap twoBlockLevi)
      (fun z => f ⟨twoBlockLevi z.val, z.property⟩) u = _
    rw [inducedFunction_comap twoBlockLevi hπ H f u]
    exact induced_rightLevi ψ α hα (twoBlockLevi u)
  rw [hc_eq_inducedFunction, ← funext he, inducedFunction_inducedFunction]

end GlobalTheory.GLq
