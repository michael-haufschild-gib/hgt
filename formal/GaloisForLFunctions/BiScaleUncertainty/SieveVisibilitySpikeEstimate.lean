import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Cubic product errors for a single signed coordinate perturbation. -/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
set_option autoImplicit false

/-- Insert one signed coordinate while leaving all other coordinates at their base values. -/
def spikeProfile (a : ℕ → ℝ) (q : ℕ) (t : ℝ) (u : ℕ) : ℝ := if u = q then t else a u

/-- If every changed nonzero product has at least three spike factors, its error is cubic. -/
theorem spike_product_error {ι : Type*} [Fintype ι] (o : ι → ℕ) (a : ℕ → ℝ)
    (q : ℕ) (t M : ℝ) (hc : Fintype.card ι ≤ 6) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hM : 1 ≤ M) (ha : ∀ u, |a u| ≤ M)
    (hdeg : (∀ i, o i ≠ q → a (o i) ≠ 0) →
      Odd ((univ.filter fun i => o i = q).card) →
        3 ≤ (univ.filter fun i => o i = q).card) :
    |(∏ i, spikeProfile a q t (o i))-(∏ i, spikeProfile a q (-t) (o i))| ≤
      2*M^6*t^3 := by
  classical
  by_cases hz : ∃ i, o i ≠ q ∧ a (o i) = 0
  · obtain ⟨i, hi, hai⟩ := hz
    have hf (x : ℝ) : spikeProfile a q x (o i) = 0 := by simp [spikeProfile, hi, hai]
    rw [Finset.prod_eq_zero (mem_univ i) (hf t),
      Finset.prod_eq_zero (mem_univ i) (hf (-t)), sub_self, abs_zero]
    positivity
  · let k : ℕ := (univ.filter fun i => o i = q).card
    let s : Finset ι := univ.filter fun i => o i ≠ q
    let B : ℝ := ∏ i ∈ s, a (o i)
    have hp (x : ℝ) : (∏ i, spikeProfile a q x (o i)) = x^k*B := by
      unfold spikeProfile
      rw [Finset.prod_ite]
      simp only [Finset.prod_const]
      rfl
    have hB : |B| ≤ M^6 := by
      calc
        _ = ∏ i ∈ s, |a (o i)| := Finset.abs_prod _ _
        _ ≤ ∏ _i ∈ s, M := Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => ha (o i))
        _ = M^s.card := by simp
        _ ≤ M^6 := pow_le_pow_right₀ hM ((card_filter_le _ _).trans (by simpa using hc))
    rw [hp t, hp (-t)]
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_pow, sub_self, abs_zero]
      positivity
    · have h3 : 3 ≤ k := hdeg (fun i hi hai => hz ⟨i, hi, hai⟩) hk
      have ht3 : t^k ≤ t^3 := pow_le_pow_of_le_one ht ht1 h3
      calc
        _ = 2*t^k*|B| := by
          rw [hk.neg_pow]
          rw [show t^k*B-(-(t^k))*B = (2*t^k)*B by ring, abs_mul,
            abs_of_nonneg (by positivity : 0 ≤ 2*t^k)]
        _ ≤ 2*t^3*M^6 :=
          mul_le_mul (mul_le_mul_of_nonneg_left ht3 (by positivity)) hB
            (abs_nonneg _) (by positivity)
        _ = _ := by ring

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
