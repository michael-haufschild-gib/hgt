import GaloisForLFunctions.HTGeometry.LBitSupportLocalReporterLaw
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Finite.Law

/-!
# Exact removal of selected Boolean correlations

Apply the Fourier correction in Lemma 3.1 of *Ordinary two-point correlations of
multiplicative functions* (OpenAI, September 24, 2026) to the corpus's real l-bit
Walsh characters and finite probability laws. The selected nonconstant moments
vanish exactly. Viewing the correction as added nonnegative mass gives total
variation at most `a / (1 + a)`, where `a` is their absolute coefficient sum.

Source: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf
-/

open Finset
namespace GaloisForLFunctions.HTGeometry
open FourierLLogL
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance repairBooleanFintype : Fintype (I → Bool) :=
  Fintype.ofFinite _

private theorem realWalsh_empty :
    lbitWalshCharacterReal (∅ : Finset I) = fun _ => 1 := by
  funext x
  simp [lbitWalshCharacterReal, lbitWalshCharacter]

/-- Walsh moment of a probability law on a finite Boolean cube. -/
def lawWalshCoefficient (P : Law (I → Bool)) (S : Finset I) : ℝ :=
  P.Ex (lbitWalshCharacterReal S)

/-- The constant Walsh moment is the total probability. -/
@[simp] theorem lawWalshCoefficient_empty (P : Law (I → Bool)) :
    lawWalshCoefficient P ∅ = 1 := by
  rw [lawWalshCoefficient, realWalsh_empty, Law.Ex_const]

/-- Uniform-law orthogonality in the existing real Walsh coordinates. -/
theorem uniform_walsh_inner (S T : Finset I) :
    (Law.uniform (I → Bool)).Ex
      (fun x => lbitWalshCharacterReal S x * lbitWalshCharacterReal T x) =
        if S = T then 1 else 0 := by
  unfold Law.Ex Law.uniform
  change (∑ x : I → Bool, (Fintype.card (I → Bool) : ℝ)⁻¹ *
    (lbitWalshCharacterReal S x * lbitWalshCharacterReal T x)) = _
  rw [← mul_sum, sum_lbitWalshCharacterReal_mul, card_lbitSupportSliceConfigurations]
  push_cast
  by_cases h : S = T <;> simp [h]

/-- Uniform Walsh moments vanish outside the constant mode. -/
theorem lawWalshCoefficient_uniform (S : Finset I) :
    lawWalshCoefficient (Law.uniform (I → Bool)) S = if S = ∅ then 1 else 0 := by
  simpa only [realWalsh_empty, mul_one, lawWalshCoefficient] using
    uniform_walsh_inner S ∅

/-- The total nonconstant Walsh mass selected for removal. -/
def walshRemovalBudget (P : Law (I → Bool)) (F : Finset (Finset I)) : ℝ :=
  ∑ S ∈ F.erase ∅, |lawWalshCoefficient P S|

/-- The selected nonconstant Walsh polynomial. -/
def walshRemovalPolynomial (P : Law (I → Bool)) (F : Finset (Finset I))
    (x : I → Bool) : ℝ :=
  ∑ S ∈ F.erase ∅, lawWalshCoefficient P S * lbitWalshCharacterReal S x

theorem walshRemovalBudget_nonneg (P : Law (I → Bool)) (F : Finset (Finset I)) :
    0 ≤ walshRemovalBudget P F := sum_nonneg fun _ _ => abs_nonneg _

/-- Every value of the removed polynomial is bounded by its coefficient mass. -/
theorem abs_walshRemovalPolynomial_le (P : Law (I → Bool))
    (F : Finset (Finset I)) (x : I → Bool) :
    |walshRemovalPolynomial P F x| ≤ walshRemovalBudget P F := by
  refine (abs_sum_le_sum_abs _ _).trans_eq ?_
  apply sum_congr rfl
  intro S _
  rw [abs_mul, show |lbitWalshCharacterReal S x| = 1 from abs_lbitWalshCharacter S x,
    mul_one]

/-- The correction polynomial has exactly zero uniform mean. -/
theorem uniform_walshRemovalPolynomial (P : Law (I → Bool)) (F : Finset (Finset I)) :
    (Law.uniform (I → Bool)).Ex (walshRemovalPolynomial P F) = 0 := by
  change (Law.uniform (I → Bool)).Ex
    (fun x => ∑ S ∈ F.erase ∅, lawWalshCoefficient P S * lbitWalshCharacterReal S x) = 0
  rw [Law.Ex_finset_sum]
  apply sum_eq_zero
  intro S hS
  rw [Law.Ex_lmul]
  change lawWalshCoefficient P S * lawWalshCoefficient (Law.uniform (I → Bool)) S = 0
  rw [lawWalshCoefficient_uniform, if_neg (mem_erase.mp hS).1, mul_zero]

/-- Nonnegative added mass, whose total mass is the removal budget. -/
def walshRepairMass (P : Law (I → Bool)) (F : Finset (Finset I))
    (x : I → Bool) : ℝ :=
  Law.uniform (I → Bool) x * (walshRemovalBudget P F - walshRemovalPolynomial P F x)

theorem walshRepairMass_nonneg (P : Law (I → Bool)) (F : Finset (Finset I))
    (x : I → Bool) : 0 ≤ walshRepairMass P F x := by
  apply mul_nonneg ((Law.uniform (I → Bool)).nonneg x)
  exact sub_nonneg.mpr ((le_abs_self _).trans (abs_walshRemovalPolynomial_le P F x))

theorem sum_walshRepairMass (P : Law (I → Bool)) (F : Finset (Finset I)) :
    (∑ x, walshRepairMass P F x) = walshRemovalBudget P F := by
  change (Law.uniform (I → Bool)).Ex
    (fun x => walshRemovalBudget P F - walshRemovalPolynomial P F x) = _
  rw [Law.Ex_sub, Law.Ex_const, uniform_walshRemovalPolynomial, sub_zero]

/-- A probability law with the selected nonconstant Walsh moments removed. -/
def walshRepairedLaw (P : Law (I → Bool)) (F : Finset (Finset I)) : Law (I → Bool) :=
  ⟨fun x => (P x + walshRepairMass P F x) / (1 + walshRemovalBudget P F), by
    constructor
    · intro x
      exact div_nonneg (add_nonneg (P.nonneg x) (walshRepairMass_nonneg P F x))
        (by have := walshRemovalBudget_nonneg P F; positivity)
    · rw [← sum_div, sum_add_distrib, P.total, sum_walshRepairMass]
      exact div_self (by have := walshRemovalBudget_nonneg P F; positivity)⟩

/-- Exact coefficient transport: selected moments vanish; all others are rescaled. -/
theorem lawWalshCoefficient_repaired (P : Law (I → Bool)) (F : Finset (Finset I))
    (T : Finset I) :
    lawWalshCoefficient (walshRepairedLaw P F) T =
      (lawWalshCoefficient P T -
          (if T ∈ F.erase ∅ then lawWalshCoefficient P T else 0) +
        walshRemovalBudget P F * (if T = ∅ then 1 else 0)) /
      (1 + walshRemovalBudget P F) := by
  have hproj : (Law.uniform (I → Bool)).Ex
      (fun x => walshRemovalPolynomial P F x * lbitWalshCharacterReal T x) =
        if T ∈ F.erase ∅ then lawWalshCoefficient P T else 0 := by
    simp only [walshRemovalPolynomial, sum_mul]
    rw [Law.Ex_finset_sum]
    simp_rw [mul_assoc, Law.Ex_lmul, uniform_walsh_inner]
    simp
  have hmass : (∑ x, walshRepairMass P F x * lbitWalshCharacterReal T x) =
      walshRemovalBudget P F * (if T = ∅ then 1 else 0) -
        (if T ∈ F.erase ∅ then lawWalshCoefficient P T else 0) := by
    simp only [walshRepairMass, mul_assoc]
    change (Law.uniform (I → Bool)).Ex
      (fun x => (walshRemovalBudget P F - walshRemovalPolynomial P F x) *
        lbitWalshCharacterReal T x) = _
    simp_rw [sub_mul]
    rw [Law.Ex_sub, Law.Ex_lmul, hproj]
    change walshRemovalBudget P F * lawWalshCoefficient (Law.uniform (I → Bool)) T - _ = _
    rw [lawWalshCoefficient_uniform]
  change (∑ x, ((P x + walshRepairMass P F x) / (1 + walshRemovalBudget P F)) *
      lbitWalshCharacterReal T x) = _
  simp_rw [div_mul_eq_mul_div, add_mul]
  rw [← sum_div, sum_add_distrib, hmass]
  change (lawWalshCoefficient P T + _) / _ = _
  congr 1
  ring

/-- Every selected nonempty support is exactly decorrelated. -/
theorem lawWalshCoefficient_repaired_selected (P : Law (I → Bool))
    (F : Finset (Finset I)) (T : Finset I) :
    lawWalshCoefficient (walshRepairedLaw P (insert T F)) T = if T = ∅ then 1 else 0 := by
  by_cases hT : T = ∅
  · subst T; simp
  · rw [lawWalshCoefficient_repaired]
    simp [hT]

/-- Total variation cost is at most budget / (1 + budget). -/
theorem walshRepairedLaw_totalVariation_le (P : Law (I → Bool))
    (F : Finset (Finset I)) :
    (∑ x, |walshRepairedLaw P F x - P x|) / 2 ≤
      walshRemovalBudget P F / (1 + walshRemovalBudget P F) := by
  let a := walshRemovalBudget P F
  have ha : 0 ≤ a := walshRemovalBudget_nonneg P F
  have hd : 0 < 1 + a := by positivity
  have hpoint : ∀ x, |walshRepairedLaw P F x - P x| ≤
      (walshRepairMass P F x + a * P x) / (1 + a) := by
    intro x
    change |(P x + walshRepairMass P F x) / (1 + a) - P x| ≤ _
    have heq : (P x + walshRepairMass P F x) / (1 + a) - P x =
        (walshRepairMass P F x - a * P x) / (1 + a) := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos hd]
    apply div_le_div_of_nonneg_right _ hd.le
    have hu := walshRepairMass_nonneg P F x
    have hv := mul_nonneg ha (P.nonneg x)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsum := sum_le_sum (fun x (_ : x ∈ (univ : Finset (I → Bool))) => hpoint x)
  rw [← sum_div, sum_add_distrib, sum_walshRepairMass, ← mul_sum, P.total, mul_one] at hsum
  change (∑ x, |walshRepairedLaw P F x - P x|) / 2 ≤ a / (1 + a)
  calc
    _ ≤ (a + a) / (1 + a) / 2 := div_le_div_of_nonneg_right hsum (by positivity)
    _ = a / (1 + a) := by ring

end
end GaloisForLFunctions.HTGeometry
