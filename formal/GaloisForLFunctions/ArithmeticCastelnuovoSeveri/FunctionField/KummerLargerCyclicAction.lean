import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointCyclic


/-!
# A larger cyclic group of Kummer automorphisms

Transporting the three-point Galois action to the original field embeds
a cyclic group of order `(Q+1)(q-1)` into its constant automorphism group.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
  (c : (SquareConstantField p (kummerSquareIndex d n))ˣ) (R : ℕ)

/-- The automorphisms of the three-point presentation act on the original Kummer field. -/
def primePowerKummerThreePointAutHom :
    (KummerThreePointField c (p ^ (d + 1) - 2) R (p ^ (kummerSquareIndex d n + 1))
      ≃ₐ[FractionRing (SquareConstantField p (kummerSquareIndex d n))[X]]
        KummerThreePointField c (p ^ (d + 1) - 2) R (p ^ (kummerSquareIndex d n + 1))) →*
    (SquareKummerField p (kummerSquareIndex d n) c (p ^ (d + 1) - 2) R
      ≃ₐ[SquareConstantField p (kummerSquareIndex d n)]
        SquareKummerField p (kummerSquareIndex d n) c (p ^ (d + 1) - 2) R) :=
  (AlgEquiv.autCongr (kummerThreePointEquiv c (p ^ (d + 1) - 2) R
    (p ^ (kummerSquareIndex d n + 1)))).toMonoidHom.comp
      (AlgEquiv.restrictScalarsHom (SquareConstantField p (kummerSquareIndex d n)))

/-- Changing presentation and forgetting the rational base preserve distinct automorphisms. -/
theorem primePowerKummerThreePointAutHom_injective :
    Function.Injective (primePowerKummerThreePointAutHom p d n c R) :=
  (AlgEquiv.autCongr _).injective.comp
    (AlgEquiv.restrictScalarsHom_injective (SquareConstantField p (kummerSquareIndex d n)))

/-- The cyclic group obtained from the three-point presentation, inside the actual constant automorphism group. -/
def primePowerKummerCyclicAutomorphisms :
    Subgroup (SquareKummerField p (kummerSquareIndex d n) c (p ^ (d + 1) - 2) R
      ≃ₐ[SquareConstantField p (kummerSquareIndex d n)]
        SquareKummerField p (kummerSquareIndex d n) c (p ^ (d + 1) - 2) R) :=
  (primePowerKummerThreePointAutHom p d n c R).range

/-- The actual subgroup of constant-field automorphisms is cyclic. -/
theorem primePowerKummerCyclicAutomorphisms_isCyclic :
    IsCyclic (primePowerKummerCyclicAutomorphisms p d n c R) := by
  letI := primePowerKummerThreePoint_isCyclic p d n c R
  apply isCyclic_of_surjective (primePowerKummerThreePointAutHom p d n c R).rangeRestrict
  rintro ⟨σ, τ, hτ⟩
  exact ⟨τ, Subtype.ext hτ⟩

/-- The actual constant automorphism group contains a subgroup of order `(Q+1)(q-1)`. -/
theorem primePowerKummerCyclicAutomorphisms_card :
    Nat.card (primePowerKummerCyclicAutomorphisms p d n c R) = primePowerKummerCyclicDegree p d n := by
  let f := primePowerKummerThreePointAutHom p d n c R
  have hinj : Function.Injective f.rangeRestrict := by
    intro σ τ h
    exact primePowerKummerThreePointAutHom_injective p d n c R (congrArg Subtype.val h)
  have hsurj : Function.Surjective f.rangeRestrict := by
    rintro ⟨σ, τ, hτ⟩
    exact ⟨τ, Subtype.ext hτ⟩
  exact (Nat.card_congr (Equiv.ofBijective f.rangeRestrict ⟨hinj, hsurj⟩)).symm.trans
    (primePowerKummerThreePoint_card_aut p d n c R)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
