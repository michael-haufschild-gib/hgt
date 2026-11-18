import GaloisForLFunctions.SignedArithmeticCorrespondences.PowerContactsAndTheirOppositeDegrees
import GaloisForLFunctions.SelectiveArithmetic.TheLiouvilleTwistFailsBeyondTheTrivialAperture

/-!
# The surviving intersection of the Liouville twin

Adding the twisted and ordinary graph contacts before taking a limit retains
all even exponents. Their opposite degrees both vanish, so the surviving
constant is a product of untwisted masses. There is no separation factor.
-/

noncomputable section

namespace GaloisForLFunctions.SignedArithmeticCorrespondences

open Filter Topology MeasureTheory _root_.RHTower
open scoped ArithmeticFunction.vonMangoldt

private theorem contact_summable (w : ℕ → ℝ) {f g : ℝ → ℝ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (s : ℝ) :
    Summable (fun n : ℕ => (2*w n/Real.sqrt n) *
      ∫ u : ℝ, f u * g (u+(Real.log n-s))) := by
  obtain ⟨l,hl⟩ := hf.bddBelow
  obtain ⟨b,hb⟩ := hg.bddAbove
  let B := ⌈Real.exp (b-l+s)⌉₊
  apply summable_of_ne_finset_zero (s := Finset.range (B+1))
  intro n hn
  have hn' : B < n := by simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hn
  have he : Real.exp (b-l+s) < n := (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr hn')
  have hlog := Real.log_lt_log (Real.exp_pos _) he
  rw [Real.log_exp] at hlog
  have hz (u : ℝ) : f u * g (u+(Real.log n-s)) = 0 := by
    by_cases hu : f u = 0
    · rw [hu,zero_mul]
    apply mul_eq_zero_of_right
    by_contra h
    linarith only [hl (subset_tsupport f hu), hb (subset_tsupport g h), hlog]
  simp only [hz,integral_zero,mul_zero]

/-- Exact mixed graph height surviving the contact sign twist at every separation. -/
theorem contact_add_liouville (f g : ℝ → ℝ) (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) (t : ℝ) :
    contact (fun n => Λ n) f g t + contact SelectiveArithmetic.liouvilleWeight f g t =
      2 * contact (powerWeight 2) f g t := by
  classical
  unfold contact
  rw [← (contact_summable _ hf hg t).tsum_add (contact_summable _ hf hg t), ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hs : (∃ k : ℕ, k^2 = n) ↔ IsSquare n := by
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨k,sq k⟩
    · rintro ⟨k,rfl⟩
      exact ⟨k,sq k⟩
  simp only [powerWeight, hs, SelectiveArithmetic.liouvilleWeight]
  by_cases hn : IsSquare n <;> simp only [hn,if_true,if_false] <;> ring

/-- The two contacts, each measured with its original sign and normalization,
have an unscaled mixed limit. It vanishes precisely when one profile has mass zero. -/
theorem tendsto_contact_add_liouville {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Tendsto (fun t : ℝ => contact (fun n => Λ n) f g t +
      contact SelectiveArithmetic.liouvilleWeight f g t) atTop
      (𝓝 (2*(∫ u : ℝ, f u)*(∫ v : ℝ, g v))) := by
  have h := (tendsto_power_contact (2 : ℕ+) hf hg hfc hgc).const_mul 2
  simp only [contact_add_liouville f g hfc hgc]
  convert h using 1 <;>
    norm_num [ccmRealExponentialMoment, ccmRealExponentialTilt, mul_assoc]

/-- Keeping the ordinary pole normalization on the sign twin reverses both
profiles' leading cross term. Its discrepancy is present already at order √X. -/
theorem tendsto_liouville_contact {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Tendsto (fun t : ℝ => Real.exp (-(1/2)*t) * contact SelectiveArithmetic.liouvilleWeight f g t)
      atTop (𝓝 (-(2*ccmRealExponentialMoment (-(1/2)) f * ccmRealExponentialMoment (1/2) g))) := by
  have hone : Tendsto (fun t : ℝ => Real.exp (-(1/2)*t) * contact (fun n => Λ n) f g t)
      atTop (𝓝 (2*ccmRealExponentialMoment (-(1/2)) f * ccmRealExponentialMoment (1/2) g)) := by
    convert tendsto_power_contact (1 : ℕ+) hf hg hfc hgc using 1 <;> norm_num [powerWeight]
  have hdec : Tendsto (fun t : ℝ => Real.exp (-(1/2)*t)) atTop (𝓝 0) := by
    simpa only [neg_mul,Function.comp_def] using Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<1/2) tendsto_id))
  have h := (hdec.mul (tendsto_contact_add_liouville hf hg hfc hgc)).sub hone
  rw [zero_mul,zero_sub] at h
  exact h.congr fun t => by dsimp only; ring

#print axioms contact_add_liouville
#print axioms tendsto_contact_add_liouville
#print axioms tendsto_liouville_contact

end GaloisForLFunctions.SignedArithmeticCorrespondences
