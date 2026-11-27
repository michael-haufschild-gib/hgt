import GaloisForLFunctions.ZeroConfigurationGeometry.TheCurveCameraIdentifiesAtTheGenus
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Moments

/-! # Reciprocal power sums and complementary elementary coefficients -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half

open Finset

variable {I J : Type*} [Fintype I] [Fintype J]

def cutoff (n : ℕ) := (n-1)/2

def elementary (u : I → ℝ) (j : ℕ) := (univ.val.map u).esymm j

def Agrees (u : I → ℝ) (v : J → ℝ) (k : ℕ) := ∀ j, 1 ≤ j → j ≤ k → moment u j=moment v j

private def complexList (u : I → ℝ) := univ.val.map (fun i => (u i : ℂ))

private theorem complex_elementary (u : I → ℝ) (j : ℕ) :
    (complexList u).esymm j = (elementary u j : ℂ) := by
  simp only [complexList,elementary,esymm_map_val,Complex.ofReal_sum,Complex.ofReal_prod]

private theorem complex_moment (u : I → ℝ) (j : ℕ) :
    ((complexList u).map fun x => x^j).sum = (moment u j : ℂ) := by
  simp only [complexList,Multiset.map_map,moment,Complex.ofReal_sum,Complex.ofReal_pow]
  rfl

theorem agrees_iff_elementary (u : I → ℝ) (v : J → ℝ) (k : ℕ) :
    Agrees u v k ↔ ∀ j ≤ k, elementary u j=elementary v j := by
  have h := ZeroConfigurationGeometry.powerSum_eq_iff_esymm_eq (complexList u) (complexList v) k
  simpa only [Agrees,complex_moment,complex_elementary,Complex.ofReal_inj] using h

/-- Taking the complement of each occupied subset exchanges reciprocal weights and
the complementary elementary coefficient when the total product is one. -/
theorem elementary_inv (u : I → ℝ) (ht : ∏ i, u i = 1) {j : ℕ} (hj : j ≤ Fintype.card I) :
    elementary (fun i => (u i)⁻¹) j = elementary u (Fintype.card I-j) := by
  classical
  simp only [elementary,esymm_map_val]
  refine sum_bij' (fun s _ => sᶜ) (fun s _ => sᶜ) ?_ ?_ (fun s _ => compl_compl s) (fun s _ => compl_compl s) ?_
  · intro s hs
    exact mem_powersetCard.mpr ⟨subset_univ _,by rw [card_compl,(mem_powersetCard.mp hs).2]⟩
  · intro s hs
    exact mem_powersetCard.mpr ⟨subset_univ _,by rw [card_compl,(mem_powersetCard.mp hs).2]; omega⟩
  · intro s _
    rw [prod_inv_distrib]
    exact inv_eq_of_mul_eq_one_right ((prod_mul_prod_compl s u).trans ht)

/-- For any aperture up to the dimension, the unfitted traces are encoded by the
opposite ends of the polynomial coefficient list. -/
theorem reciprocal_agrees_iff (u : I → ℝ) (ht : ∏ i, u i = 1) {k : ℕ} (hk : k ≤ Fintype.card I) :
    Agrees u (fun i => (u i)⁻¹) k ↔
      ∀ j ≤ k, elementary u j = elementary u (Fintype.card I-j) := by
  rw [agrees_iff_elementary]
  exact forall_congr' fun j => forall_congr' fun hj => by rw [elementary_inv u ht (hj.trans hk)]

/-- Each complementary pair has an index in the tested half, except the central
coefficient in even dimension which is already its own complement. -/
theorem reciprocal_matches_iff (u : I → ℝ) (ht : ∏ i, u i = 1) :
    Matches u (fun i => (u i)⁻¹) ↔ Agrees u (fun i => (u i)⁻¹) (cutoff (Fintype.card I)) := by
  refine ⟨fun h j _ _ => moment_congr h j,?_⟩
  let n := Fintype.card I
  have bound : cutoff n ≤ n := by unfold cutoff; omega
  intro h
  have low := (reciprocal_agrees_iff u ht bound).mp h
  have all : Agrees u (fun i => (u i)⁻¹) n := by
    apply (reciprocal_agrees_iff u ht le_rfl).mpr
    intro j hj
    change elementary u j = elementary u (n-j)
    by_cases hsmall : j ≤ cutoff n
    · exact low j hsmall
    · by_cases middle : j=n-j
      · exact congrArg (elementary u) middle
      · have h' : n-j ≤ cutoff n := by unfold cutoff at *; omega
        have hh := low (n-j) h'
        change elementary u (n-j) = elementary u (n-(n-j)) at hh
        rw [Nat.sub_sub_self (show j ≤ n from hj)] at hh
        exact hh.symm
  apply (matches_iff_moments _ _).mpr
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hp
  · simp only [moment,pow_zero]
  · exact all j hp hj

#print axioms agrees_iff_elementary
#print axioms elementary_inv
#print axioms reciprocal_matches_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half
