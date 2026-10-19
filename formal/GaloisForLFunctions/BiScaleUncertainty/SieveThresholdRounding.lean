import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Threshold rounding preserves sufficiently accurate real resonant products. -/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.Threshold
set_option autoImplicit false

/-- Retain only source coordinates larger than the noise radius. -/
def source (δ a : ℝ) : ℝ := if δ < |a| then a else 0

/-- On retained coordinates, use the competitor sign and the source magnitude. -/
def target (δ a b : ℝ) : ℝ :=
  if δ < |a| then (if 0 ≤ b then |a| else -|a|) else 0

theorem source_error (δ a : ℝ) (hδ : 0 ≤ δ) : |a-source δ a| ≤ δ := by
  by_cases ha : δ < |a|
  · simpa [source, ha] using hδ
  · simpa [source, ha] using le_of_not_gt ha

theorem target_error (δ a b : ℝ) (hδ : 0 ≤ δ)
    (h : abs (|a|-|b|) ≤ δ) : |b-target δ a b| ≤ 2*δ := by
  by_cases ha : δ < |a|
  · have he : |b-target δ a b| ≤ δ := by
      by_cases hb : 0 ≤ b
      · simpa [target, ha, hb, abs_of_nonneg hb, abs_sub_comm] using h
      · have hb' : b < 0 := lt_of_not_ge hb
        simpa [target, ha, hb, abs_of_neg hb', sub_eq_add_neg, add_comm] using h
    linarith
  · have hab := (abs_le.mp h).1
    have ha' := le_of_not_gt ha
    simpa [target, ha] using (show |b| ≤ 2*δ by linarith)

private theorem retained_target_mul_pos (δ a b : ℝ) (hδ : 0 ≤ δ)
    (ha : δ < |a|) (h : abs (|a|-|b|) ≤ δ) : 0 < target δ a b * b := by
  have hab := (abs_le.mp h).2
  have hbabs : 0 < |b| := by linarith
  have haabs : 0 < |a| := lt_of_le_of_lt hδ ha
  by_cases hb : 0 ≤ b
  · have hbpos : 0 < b := by rwa [abs_of_nonneg hb] at hbabs
    simpa [target, ha, hb] using mul_pos haabs hbpos
  · have hbneg : b < 0 := lt_of_not_ge hb
    simpa [target, ha, hb] using mul_pos_of_neg_of_neg (neg_neg_of_pos haabs) hbneg

private theorem close_product_sign (a b : ℝ) (h : |a-b| < |a|) : 0 < a*b := by
  have hab := abs_lt.mp h
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha] at hab
    have ha' : 0 < a := lt_of_le_of_lt (abs_nonneg _) (by simpa [abs_of_nonneg ha] using h)
    have hb : 0 < b := by linarith
    exact mul_pos ha' hb
  · have ha' : a < 0 := lt_of_not_ge ha
    rw [abs_of_neg ha'] at hab
    have hb : b < 0 := by linarith
    exact mul_pos_of_neg_of_neg ha' hb

/-- Rounding turns noisy degree-five/six products into exact products. -/
theorem products_eq {m : ℕ} (hm : m = 5 ∨ m = 6)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (a b : Fin m → ℝ)
    (hmag : ∀ i, abs (|a i|-|b i|) ≤ δ)
    (hprod : |(∏ i, a i)-(∏ i, b i)| ≤ δ^6) :
    (∏ i, source δ (a i)) = ∏ i, target δ (a i) (b i) := by
  classical
  by_cases hz : ∃ i, ¬δ < |a i|
  · obtain ⟨i, hi⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (show source δ (a i) = 0 by simp [source, hi]),
      Finset.prod_eq_zero (Finset.mem_univ i) (show target δ (a i) (b i) = 0 by simp [target, hi])]
  · have ha : ∀ i, δ < |a i| := fun i => by by_contra hi; exact hz ⟨i, hi⟩
    have hmpos : 0 < m := by rcases hm with rfl | rfl <;> norm_num
    have hlarge : δ^m < |∏ i, a i| := by
      rw [Finset.abs_prod]
      by_cases hd0 : δ = 0
      · subst δ
        simpa [Nat.ne_of_gt hmpos] using
          (Finset.prod_pos (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => ha i))
      · have hdp : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hd0)
        have hp := Finset.prod_lt_prod_of_nonempty
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hdp)
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => ha i)
          (show (Finset.univ : Finset (Fin m)).Nonempty from
            ⟨⟨0, hmpos⟩, Finset.mem_univ _⟩)
        simpa using hp
    have hexp : δ^6 ≤ δ^m := by
      rcases hm with rfl | rfl
      · have hp := mul_le_mul_of_nonneg_left hδ1 (pow_nonneg hδ 5)
        simpa [pow_succ] using hp
      · exact le_rfl
    have hab : 0 < (∏ i, a i) * (∏ i, b i) :=
      close_product_sign _ _ (hprod.trans_lt (hexp.trans_lt hlarge))
    have htb : 0 < (∏ i, target δ (a i) (b i)) * (∏ i, b i) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_pos fun i _ => retained_target_mul_pos δ (a i) (b i) hδ (ha i) (hmag i)
    have habs : |∏ i, target δ (a i) (b i)| = |∏ i, a i| := by
      rw [Finset.abs_prod, Finset.abs_prod]
      apply Finset.prod_congr rfl
      intro i _
      simp only [target, if_pos (ha i)]
      split_ifs <;> simp
    have heq : (∏ i, target δ (a i) (b i)) = ∏ i, a i := by
      rcases abs_eq_abs.mp habs with he | he
      · exact he
      · rw [he] at htb
        nlinarith only [hab, htb]
    simpa [source, ha] using heq.symm

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.Threshold
