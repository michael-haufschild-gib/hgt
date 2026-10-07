import GaloisForLFunctions.RHTower.XiReflectedSquareClasses
import GaloisForLFunctions.HTGeometry.MultiquadraticAdjoinDegree

open Complex Filter Topology
open scoped IntermediateField
noncomputable section
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry
local instance : CharZero K := charZero_of_injective_algebraMap constPlane_injective

def orientedFactor (j : Bool × ℕ) : ℂ → ℂ :=
  if j.1 then reflectedFactor (j.2 + 2) else deletionFactor (j.2 + 2)

def orientedElement (j : Bool × ℕ) : K :=
  if j.1 then reflectedElement (j.2 + 2) else factorElement (j.2 + 2)

theorem orientedFactor_differentiable (j : Bool × ℕ) : Differentiable ℂ (orientedFactor j) := by
  rcases j with ⟨b, n⟩
  cases b with
  | false => exact deletionFactor_differentiable (n + 2)
  | true => exact reflectedFactor_differentiable (n + 2)

theorem orientedElement_eq_ofMeromorphic (j : Bool × ℕ) :
    orientedElement j = ofMeromorphic (orientedFactor j)
      (fun z => ((orientedFactor_differentiable j).analyticAt z).meromorphicAt) := by
  rcases j with ⟨b, n⟩
  cases b <;> rfl

theorem exists_odd_zero_orientedFactor (j : Bool × ℕ) :
    ∃ s : ℂ, orientedFactor j s = 0 ∧ Odd (analyticOrderAt (orientedFactor j) s).toNat := by
  rcases j with ⟨b, n⟩
  cases b with
  | false =>
    exact exists_odd_zero_of_not_isSquare_plane (deletionFactor_differentiable (n + 2))
      (by norm_num [orientedFactor, deletionFactor, xi_zero]) (factorElement_not_isSquare (by omega))
  | true => exact exists_odd_zero_reflectedFactor (by omega)

theorem xi_ne_zero_of_orientedFactor_zero {j : Bool × ℕ} {s : ℂ}
    (hz : orientedFactor j s = 0) : xi s ≠ 0 := by
  rcases j with ⟨b, n⟩
  cases b with
  | false =>
    change deletionFactor (n + 2) s = 0 at hz
    intro hx
    simp only [deletionFactor, hx, mul_zero, sub_zero] at hz
    exact one_ne_zero hz
  | true => exact xi_ne_zero_of_reflectedFactor_zero hz

theorem orientedFactor_label_injective_at_zero {j k : Bool × ℕ} {s : ℂ}
    (hj : orientedFactor j s = 0) (hk : orientedFactor k s = 0) : j = k := by
  rcases j with ⟨b, n⟩
  rcases k with ⟨c, m⟩
  cases b <;> cases c
  · have he := deletionFactor_label_injective_at_zero (by omega) (by omega) hj hk
    exact Prod.ext rfl (Nat.add_right_cancel he)
  · exact False.elim ((deletionFactor_ne_zero_of_reflectedFactor_zero
      (by omega) (by omega) hk) hj)
  · exact False.elim ((deletionFactor_ne_zero_of_reflectedFactor_zero
      (by omega) (by omega) hj) hk)
  · have he := reflectedFactor_label_injective_at_zero (by omega) (by omega) hj hk
    exact Prod.ext rfl (Nat.add_right_cancel he)

def pairedRadicand (j : Bool × ℕ) : K := xiElement * orientedElement j

def pairedRadicandFunction (j : Bool × ℕ) (s : ℂ) : ℂ := xi s * orientedFactor j s

theorem pairedRadicandFunction_differentiable (j : Bool × ℕ) :
    Differentiable ℂ (pairedRadicandFunction j) :=
  xi_differentiable.mul (orientedFactor_differentiable j)

theorem pairedRadicand_eq_ofMeromorphic (j : Bool × ℕ) :
    pairedRadicand j = ofMeromorphic (pairedRadicandFunction j)
      (fun z => ((pairedRadicandFunction_differentiable j).analyticAt z).meromorphicAt) := by
  rw [pairedRadicand, xiElement, orientedElement_eq_ofMeromorphic, ofMeromorphic_mul]
  rfl

/-- All actual radical classes in both orientations are independent. -/
theorem paired_radicands_not_isSquare (S : Finset (Bool × ℕ)) (hS : S.Nonempty) :
    ¬ IsSquare (∏ j ∈ S, pairedRadicand j) := by
  classical
  obtain ⟨j, hj⟩ := hS
  obtain ⟨z, hz, hodd⟩ := exists_odd_zero_orientedFactor j
  have hxi := xi_ne_zero_of_orientedFactor_zero hz
  have ho : Odd (analyticOrderAt (pairedRadicandFunction j) z).toNat := by
    change Odd (analyticOrderAt (xi * orientedFactor j) z).toNat
    rw [analyticOrderAt_mul (xi_differentiable.analyticAt z)
      ((orientedFactor_differentiable j).analyticAt z),
      (xi_differentiable.analyticAt z).analyticOrderAt_eq_zero.mpr hxi, zero_add]
    exact hodd
  have hothers (k : Bool × ℕ) (_hk : k ∈ S) (hkj : k ≠ j) :
      pairedRadicandFunction k z ≠ 0 :=
    mul_ne_zero hxi (fun hkz => hkj (orientedFactor_label_injective_at_zero hkz hz))
  have hns := entire_packet_not_isSquare_of_odd_factor pairedRadicandFunction
    pairedRadicandFunction_differentiable (differentiable_const (1 : ℂ)) S hj ho
    (by norm_num) hothers
  simp only [← pairedRadicand_eq_ofMeromorphic] at hns
  change ¬ IsSquare ((1 : K) * ∏ j ∈ S, pairedRadicand j) at hns
  simpa only [one_mul] using hns

/-- The original roots are retained literally in the first orientation. -/
def pairedRoot : Bool × ℕ → Ω
  | (false, n) => root n
  | (true, n) => Classical.choose (IsAlgClosed.exists_pow_nat_eq
      (algebraMap K Ω (pairedRadicand (true, n))) (by decide : 0 < 2))

theorem pairedRoot_sq (j : Bool × ℕ) :
    pairedRoot j * pairedRoot j = algebraMap K Ω (pairedRadicand j) := by
  rcases j with ⟨b, n⟩
  cases b with
  | false => exact root_sq n
  | true =>
    simpa only [pairedRoot, pow_two] using Classical.choose_spec
      (IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (pairedRadicand (true, n)))
        (by decide : 0 < 2))

def pairedFiniteField (S : Finset (Bool × ℕ)) : IntermediateField K Ω :=
  IntermediateField.adjoin K (pairedRoot '' (S : Set (Bool × ℕ)))

theorem pairedFiniteField_finrank (S : Finset (Bool × ℕ)) :
    Module.finrank K (pairedFiniteField S) = 2 ^ S.card :=
  (multiquadratic_degree_and_twists pairedRadicand pairedRoot (by norm_num)
    pairedRoot_sq paired_radicands_not_isSquare S).1

/-- Adding both orientations at every finite label doubles the Kummer rank. -/
theorem paired_full_label_finrank (S : Finset ℕ) :
    Module.finrank K (pairedFiniteField (Finset.univ ×ˢ S)) = 2 ^ (2 * S.card) := by
  rw [pairedFiniteField_finrank, Finset.card_product]
  simp

end RHTower.XiGlobalKummer
