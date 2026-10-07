import GaloisForLFunctions.RHTower.XiCubicDiscriminantPackets
import GaloisForLFunctions.HTGeometry.MultiquadraticAdjoinDegree

/-!
# Finite quadratic stages of the actual marked cubic discriminants

Every finite discriminant packet contributes its full quadratic degree. An
unused marked discriminant remains nonsquare over each preceding finite stage.
-/

open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower
open XiGlobalKummer

local instance : CharZero MeromorphicPlane :=
  charZero_of_injective_ringHom constPlane_injective

/-- A chosen square root of each actual cubic discriminant in the fixed algebraic closure. -/
def xiCubicDiscriminantRoot (n : ℕ) : Ω :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap K Ω (xiCubicDiscriminant (Real.log (n + 2)))) (by norm_num : 0 < 2))

theorem xiCubicDiscriminantRoot_sq (n : ℕ) :
    xiCubicDiscriminantRoot n * xiCubicDiscriminantRoot n =
      algebraMap K Ω (xiCubicDiscriminant (Real.log (n + 2))) := by
  simpa only [xiCubicDiscriminantRoot, pow_two] using
    Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
      (algebraMap K Ω (xiCubicDiscriminant (Real.log (n + 2)))) (by norm_num : 0 < 2))

/-- The finite quadratic sign field of the actual marked cubic channels. -/
def xiCubicQuadraticStage (S : Finset ℕ) : IntermediateField K Ω :=
  IntermediateField.adjoin K (xiCubicDiscriminantRoot '' (S : Set ℕ))

/-- The actual discriminant radicals give every independent quadratic degree. -/
theorem xiCubicQuadraticStage_finrank (S : Finset ℕ) :
    Module.finrank K (xiCubicQuadraticStage S) = 2 ^ S.card := by
  exact (multiquadratic_degree_and_twists (F := K) (L := Ω)
    (fun n : ℕ => xiCubicDiscriminant (Real.log (n + 2))) xiCubicDiscriminantRoot
    (by norm_num) xiCubicDiscriminantRoot_sq xiCubicDiscriminant_packet_not_isSquare S).1

/-- Any base class killed by the finite sign field is a finite discriminant twist. -/
theorem xiCubicQuadraticStage_square_twist (S : Finset ℕ) (a : K)
    (ha : IsSquare (algebraMap K (xiCubicQuadraticStage S) a)) :
    ∃ T : Finset ℕ, T ⊆ S ∧
      IsSquare (a * ∏ n ∈ T, xiCubicDiscriminant (Real.log (n + 2))) := by
  exact (multiquadratic_degree_and_twists (F := K) (L := Ω)
    (fun n : ℕ => xiCubicDiscriminant (Real.log (n + 2))) xiCubicDiscriminantRoot
    (by norm_num) xiCubicDiscriminantRoot_sq xiCubicDiscriminant_packet_not_isSquare S).2 a ha

/-- Every unused marked discriminant survives the previously adjoined sign radicals. -/
theorem xiCubicDiscriminant_not_isSquare_quadraticStage (S : Finset ℕ) {n : ℕ}
    (hn : n ∉ S) :
    ¬ IsSquare (algebraMap K (xiCubicQuadraticStage S)
      (xiCubicDiscriminant (Real.log (n + 2)))) := by
  classical
  intro hs
  obtain ⟨T, hT, hsq⟩ := xiCubicQuadraticStage_square_twist S _ hs
  have hnT : n ∉ T := fun h => hn (hT h)
  apply xiCubicDiscriminant_packet_not_isSquare (insert n T) (Finset.insert_nonempty _ _)
  rwa [Finset.prod_insert hnT]

end RHTower
