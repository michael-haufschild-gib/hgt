import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PolynomialTailFilters
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Separated signed windows

Strict tail signs persist on bounded intervals. Recursion then produces infinitely many disjoint windows of each sign.
-/

noncomputable section
open MeasureTheory Set Filter Polynomial
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations

/-- Every strict tail integral sign already occurs on a bounded interval. -/
theorem exists_bounded_tail_sign (f : ℝ → ℝ) (b ε : ℝ)
    (hf : IntegrableOn f (Iio b)) (h : ε * (∫ u in Iio b, f u) < 0) :
    ∃ a < b, ε * (∫ u in Ico a b, f u) < 0 := by
  have ht := (tendsto_integral_Ico_integral_Iio b hf
    (tendsto_id : Tendsto (fun a : ℝ => a) atBot atBot)).const_mul ε
  have he : ∀ᶠ a : ℝ in atBot, ε * (∫ u in Ico a b, f u) < 0 :=
    ht.eventually (gt_mem_nhds h)
  obtain ⟨a, ha, hab⟩ := (he.and (eventually_lt_atBot b)).exists
  exact ⟨a, hab, ha⟩

/-- Both signs of the critical-state tail form have compactly supported polynomial witnesses. -/
theorem criticalState_bounded_polynomial_both_signs {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (b : ℝ) :
    (∃ a < b, ∃ P : ℝ[X], (∫ u in Ico a b,
      P.eval (Real.exp (u - b)) ^ 2 * (F u * Real.exp (10 * (u - b)))) < 0) ∧
    (∃ a < b, ∃ P : ℝ[X], 0 < (∫ u in Ico a b,
      P.eval (Real.exp (u - b)) ^ 2 * (F u * Real.exp (10 * (u - b))))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hsign := criticalState_tailProbeQuadratic_both_signs hW ht hF (-b)
  have hi (P : ℝ[X]) : IntegrableOn (fun u =>
      P.eval (Real.exp (u - b)) ^ 2 * (F u * Real.exp (10 * (u - b)))) (Iio b) := by
    have hi := integrable_tailProbePolynomial hd (-b) (P ^ 2)
    have he : (fun u => (P ^ 2).eval (Real.exp (u + -b)) *
        (F u * Real.exp (10 * (u + -b)))) =
        (fun u => P.eval (Real.exp (u - b)) ^ 2 *
          (F u * Real.exp (10 * (u - b)))) := by
      funext u
      rw [_root_.Polynomial.eval_pow (p := P) (x := Real.exp (u + -b)) 2]
      simp only [sub_eq_add_neg]
    rw [he, neg_neg] at hi
    exact hi
  constructor
  · obtain ⟨P, hP⟩ := hsign.1
    rw [tailProbeQuadratic_eq_integral hd] at hP
    simp only [neg_neg, ← sub_eq_add_neg] at hP
    obtain ⟨a, hab, ha⟩ := exists_bounded_tail_sign _ b 1 (hi P) (by simpa only [one_mul] using hP)
    exact ⟨a, hab, P, by simpa only [one_mul] using ha⟩
  · obtain ⟨P, hP⟩ := hsign.2
    rw [tailProbeQuadratic_eq_integral hd] at hP
    simp only [neg_neg, ← sub_eq_add_neg] at hP
    obtain ⟨a, hab, ha⟩ := exists_bounded_tail_sign _ b (-1) (hi P) (by simpa only [neg_one_mul, neg_lt_zero] using hP)
    exact ⟨a, hab, P, by simpa only [neg_one_mul, neg_lt_zero] using ha⟩

/-- Witnesses available on every left ray can be separated into an infinite sequence of bounded windows. -/
theorem exists_separated_left_windows {A : Type*} (R : ℝ → ℝ → A → Prop)
    (hR : ∀ b : ℝ, ∃ a < b, ∃ v : A, R a b v) (B : ℝ) :
    ∃ a b : ℕ → ℝ, ∃ v : ℕ → A, b 0 = B ∧
      (∀ n, a n < b n ∧ R (a n) (b n) (v n)) ∧
      (∀ i j, i < j → b j < a i) ∧
      Pairwise (fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j))) := by
  classical
  choose l hl v hv using hR
  let b : ℕ → ℝ := fun n => Nat.rec B (fun _ x => l x - 1) n
  have hb (n : ℕ) : b (n + 1) = l (b n) - 1 := rfl
  have hanti : StrictAnti b := strictAnti_nat_of_succ_lt (fun n => by
    rw [hb]
    linarith only [hl (b n)])
  have hsep (i j : ℕ) (hij : i < j) : b j < l (b i) := by
    have hle := hanti.antitone (show i + 1 ≤ j by omega)
    rw [hb] at hle
    linarith only [hle]
  refine ⟨fun n => l (b n), b, fun n => v (b n), rfl,
    fun n => ⟨hl (b n), hv (b n)⟩, hsep, ?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro u hui huj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have h := hsep i j hij
    exact (not_lt_of_ge hui.1) (huj.2.trans h)
  · have h := hsep j i hji
    exact (not_lt_of_ge huj.1) (hui.2.trans h)

/-- Every critical-state ray contains infinitely many separated negative polynomial-square windows. -/
theorem criticalState_separated_negative_windows {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (B : ℝ) :
    ∃ a b : ℕ → ℝ, ∃ P : ℕ → ℝ[X], b 0 = B ∧
      (∀ n, a n < b n ∧ (∫ u in Ico (a n) (b n),
        (P n).eval (Real.exp (u - b n)) ^ 2 * (F u * Real.exp (10 * (u - b n)))) < 0) ∧
      (∀ i j, i < j → b j < a i) ∧
      Pairwise (fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j))) :=
  exists_separated_left_windows _
    (fun b => (criticalState_bounded_polynomial_both_signs hW ht hF b).1) B

/-- Every critical-state ray also contains infinitely many separated positive polynomial-square windows. -/
theorem criticalState_separated_positive_windows {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (B : ℝ) :
    ∃ a b : ℕ → ℝ, ∃ P : ℕ → ℝ[X], b 0 = B ∧
      (∀ n, a n < b n ∧ 0 < (∫ u in Ico (a n) (b n),
        (P n).eval (Real.exp (u - b n)) ^ 2 * (F u * Real.exp (10 * (u - b n))))) ∧
      (∀ i j, i < j → b j < a i) ∧
      Pairwise (fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j))) :=
  exists_separated_left_windows _
    (fun b => (criticalState_bounded_polynomial_both_signs hW ht hF b).2) B

/-- Each sign admits infinitely many separated witnesses, with no shared interval requirement. -/
theorem criticalState_separated_signed_windows {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (B ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ a b : ℕ → ℝ, ∃ P : ℕ → ℝ[X], b 0 = B ∧
      (∀ n, a n < b n ∧ ε * (∫ u in Ico (a n) (b n),
        (P n).eval (Real.exp (u - b n)) ^ 2 * (F u * Real.exp (10 * (u - b n)))) < 0) ∧
      (∀ i j, i < j → b j < a i) ∧
      Pairwise (fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j))) := by
  rcases hε with rfl | rfl
  · simpa only [one_mul] using criticalState_separated_negative_windows hW ht hF B
  · simpa only [neg_one_mul, neg_lt_zero] using criticalState_separated_positive_windows hW ht hF B

/-- RH holds, or every critical-state ray contains infinitely many separated windows of each strict sign. -/
theorem riemannHypothesis_or_separated_signed_windows :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∀ B ε : ℝ, ε = 1 ∨ ε = -1 →
        ∃ a b : ℕ → ℝ, ∃ P : ℕ → ℝ[X], b 0 = B ∧
          (∀ n, a n < b n ∧ ε * (∫ u in Ico (a n) (b n),
            (P n).eval (Real.exp (u - b n)) ^ 2 * (F u * Real.exp (10 * (u - b n)))) < 0) ∧
          (∀ i j, i < j → b j < a i) ∧
          Pairwise (fun i j => Disjoint (Ico (a i) (b i)) (Ico (a j) (b j))) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with
    hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, criticalState_separated_signed_windows hW ht hF⟩

#print axioms riemannHypothesis_or_separated_signed_windows
#print axioms criticalState_separated_negative_windows
#print axioms criticalState_separated_positive_windows

#print axioms criticalState_bounded_polynomial_both_signs
end GaloisForLFunctions.ExclusionOfTheCriticalState
