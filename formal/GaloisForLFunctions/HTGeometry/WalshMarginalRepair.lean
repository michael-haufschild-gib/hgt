import GaloisForLFunctions.HTGeometry.WalshProbabilityRepair

/-!
# Exact independence from the l-bit Walsh correction

The probability-law correction from `WalshProbabilityRepair` has uniform
marginals on every support up to the repaired degree. This applies Lemma 3.1 of
*Ordinary two-point correlations of multiplicative functions* to the corpus's
real l-bit characters. Cylinder reconstruction extends the integer subcube
mechanism already used in `TwoLocalPauliReplicaJetDepthLaw` to arbitrary real
probability laws and arbitrary prescribed bits.

Higher-degree moments retain their exact common rescaling, and total variation
is bounded by the selected coefficient mass divided by one plus that mass.
-/


open Finset
namespace GaloisForLFunctions.HTGeometry
open FourierLLogL
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance marginalBooleanFintype : Fintype (I → Bool) :=
  Fintype.ofFinite _

/-- The existing real Walsh character as a product on its actual support. -/
theorem lbitWalshCharacterReal_eq_prod (S : Finset I) (x : I → Bool) :
    lbitWalshCharacterReal S x = ∏ i ∈ S, (lbitSign (x i) : ℝ) := by
  simp [lbitWalshCharacterReal, lbitWalshCharacter]

/-- Walsh resolution of a cylinder indicator, with arbitrary prescribed bits. -/
theorem sum_walsh_subsets_eq_cylinder (S : Finset I) (x b : I → Bool) :
    (∑ T ∈ S.powerset, lbitWalshCharacterReal T x * lbitWalshCharacterReal T b) =
      if (∀ i ∈ S, x i = b i) then (2 : ℝ) ^ S.card else 0 := by
  simp_rw [lbitWalshCharacterReal_eq_prod, ← prod_mul_distrib]
  rw [← prod_one_add]
  by_cases hx : ∀ i ∈ S, x i = b i
  · rw [if_pos hx]
    calc
      _ = ∏ _i ∈ S, (2 : ℝ) := by
        apply prod_congr rfl
        intro i hi
        rw [hx i hi]
        cases b i <;> norm_num [lbitSign]
      _ = _ := prod_const _
  · rw [if_neg hx]
    push Not at hx
    obtain ⟨i, hi, hne⟩ := hx
    apply prod_eq_zero hi
    cases hxi : x i <;> cases hbi : b i <;> simp_all [lbitSign]

/-- Every cylinder probability is determined by exactly the Walsh modes on its support. -/
theorem law_prob_cylinder_eq_walsh (P : Law (I → Bool)) (S : Finset I) (b : I → Bool) :
    P.prob (fun x => ∀ i ∈ S, x i = b i) =
      (∑ T ∈ S.powerset, lawWalshCoefficient P T * lbitWalshCharacterReal T b) /
        (2 : ℝ) ^ S.card := by
  have h : (2 : ℝ) ^ S.card * P.prob (fun x => ∀ i ∈ S, x i = b i) =
      ∑ T ∈ S.powerset, lawWalshCoefficient P T * lbitWalshCharacterReal T b := by
    rw [Law.prob, ← Law.Ex_lmul]
    calc
      _ = P.Ex (fun x => ∑ T ∈ S.powerset,
          lbitWalshCharacterReal T x * lbitWalshCharacterReal T b) := by
        congr 1
        funext x
        rw [sum_walsh_subsets_eq_cylinder]
        split_ifs <;> simp
      _ = _ := by
        rw [Law.Ex_finset_sum]
        apply sum_congr rfl
        intro T _
        exact Law.Ex_mul _ _ _
  apply (eq_div_iff (by positivity)).mpr
  simpa only [mul_comm] using h

/-- Remove all Walsh modes up to the requested degree. -/
def walshDegreeRepairedLaw (P : Law (I → Bool)) (k : ℕ) : Law (I → Bool) :=
  walshRepairedLaw P (univ.filter fun T : Finset I => T.card ≤ k)

/-- Exact coefficient formula for degree repair, including the untouched higher degrees. -/
theorem lawWalshCoefficient_degreeRepaired (P : Law (I → Bool)) (k : ℕ) (T : Finset I) :
    lawWalshCoefficient (walshDegreeRepairedLaw P k) T =
      if T = ∅ then 1 else if T.card ≤ k then 0 else
        lawWalshCoefficient P T /
          (1 + walshRemovalBudget P (univ.filter fun U : Finset I => U.card ≤ k)) := by
  by_cases hT : T = ∅
  · subst T; simp
  · rw [walshDegreeRepairedLaw, lawWalshCoefficient_repaired]
    by_cases hcard : T.card ≤ k <;> simp [hT, hcard]

/-- Repair gives exact uniform marginals on every set up to the selected degree. -/
theorem walshDegreeRepairedLaw_uniform_marginal (P : Law (I → Bool))
    (S : Finset I) (k : ℕ) (b : I → Bool) :
    (walshDegreeRepairedLaw P (S.card + k)).prob (fun x => ∀ i ∈ S, x i = b i) =
      1 / (2 : ℝ) ^ S.card := by
  rw [law_prob_cylinder_eq_walsh]
  congr 1
  rw [sum_eq_single ∅]
  · simp [lbitWalshCharacterReal_eq_prod]
  · intro T hT hne
    have hcard : T.card ≤ S.card + k :=
      (card_le_card (mem_powerset.mp hT)).trans (Nat.le_add_right _ _)
    simp [lawWalshCoefficient_degreeRepaired, hne, hcard]
  · simp

/-- The exact-independence correction keeps the sharper total variation bound. -/
theorem walshDegreeRepairedLaw_totalVariation_le (P : Law (I → Bool)) (k : ℕ) :
    (∑ x, |walshDegreeRepairedLaw P k x - P x|) / 2 ≤
      walshRemovalBudget P (univ.filter fun T : Finset I => T.card ≤ k) /
        (1 + walshRemovalBudget P (univ.filter fun T : Finset I => T.card ≤ k)) :=
  walshRepairedLaw_totalVariation_le P _

end
end GaloisForLFunctions.HTGeometry
