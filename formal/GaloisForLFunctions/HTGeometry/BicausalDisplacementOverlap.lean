import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-!
# Bicausal displacement--overlap conservation

If one contiguous mass partition is shifted forward by `h` before a turning seam and the
unshifted partition is used after it, the two aggregate targets overlap on exactly one interval of
width `h`.  Thus causal displacement is conserved as duplicate target capacity at a reversal.
-/

/-- Aggregate target obtained from the forward-shifted side of a bicausal partition. -/
def bicausalLeftTarget (a s h : ℝ) : Set ℝ := Set.Ioc a (s + h)

/-- Aggregate target obtained from the unshifted side of a bicausal partition. -/
def bicausalRightTarget (s b : ℝ) : Set ℝ := Set.Ioc s b

/-- Exact duplicate-capacity interval at the bicausal turning seam. -/
def bicausalSeam (s h : ℝ) : Set ℝ := Set.Ioc s (s + h)

/-- The mixed aggregate targets overlap on exactly the displacement interval. -/
theorem bicausalLeftTarget_inter_rightTarget
    {a s h b : ℝ} (has : a ≤ s) (hshb : s + h ≤ b) :
    bicausalLeftTarget a s h ∩ bicausalRightTarget s b = bicausalSeam s h := by
  ext x
  simp only [bicausalLeftTarget, bicausalRightTarget, bicausalSeam, mem_inter_iff,
    mem_Ioc]
  constructor
  · rintro ⟨⟨_hax, hxsh⟩, ⟨hsx, _hxb⟩⟩
    exact ⟨hsx, hxsh⟩
  · rintro ⟨hsx, hxsh⟩
    exact ⟨⟨has.trans_lt hsx, hxsh⟩, ⟨hsx, hxsh.trans hshb⟩⟩

/-- Away from the duplicate seam, the mixed aggregate targets cover one contiguous interval. -/
theorem bicausalLeftTarget_union_rightTarget
    {a s h b : ℝ} (has : a ≤ s) (hh : 0 ≤ h) (hshb : s + h ≤ b) :
    bicausalLeftTarget a s h ∪ bicausalRightTarget s b = Set.Ioc a b := by
  ext x
  simp only [bicausalLeftTarget, bicausalRightTarget, mem_union, mem_Ioc]
  constructor
  · rintro (⟨hax, hxsh⟩ | ⟨hsx, hxb⟩)
    · exact ⟨hax, hxsh.trans hshb⟩
    · exact ⟨has.trans_lt hsx, hxb⟩
  · rintro ⟨hax, hxb⟩
    by_cases hx : x ≤ s + h
    · exact Or.inl ⟨hax, hx⟩
    · exact Or.inr ⟨lt_of_le_of_lt (le_add_of_nonneg_right hh) (lt_of_not_ge hx), hxb⟩

/-- Duplicate target capacity has exact real volume equal to the causal displacement. -/
theorem volume_bicausalSeam {s h : ℝ} (hh : 0 ≤ h) :
    (volume (bicausalSeam s h)).toReal = h := by
  rw [bicausalSeam, Real.volume_Ioc, ENNReal.toReal_ofReal]
  · ring
  · linarith

/-- Integral form of displacement--overlap conservation.  The second seam integral is the exact
capacity surcharge paid when forward and past transports are spliced. -/
theorem bicausal_intervalIntegral_conservation
    {a s h b : ℝ} {Phi : ℝ → ℝ}
    (has : a ≤ s) (hh : 0 ≤ h) (hshb : s + h ≤ b)
    (hint : IntervalIntegrable Phi volume a b) :
    (∫ x : ℝ in a..s + h, Phi x) + (∫ x : ℝ in s..b, Phi x) =
      (∫ x : ℝ in a..b, Phi x) + (∫ x : ℝ in s..s + h, Phi x) := by
  have hasH : a ≤ s + h := has.trans (le_add_of_nonneg_right hh)
  have hsb : s ≤ b := (le_add_of_nonneg_right hh).trans hshb
  have hab : a ≤ b := has.trans hsb
  have h_as : IntervalIntegrable Phi volume a s := by
    apply hint.mono_set
    rw [uIcc_of_le has, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hsb
  have h_s_sh : IntervalIntegrable Phi volume s (s + h) := by
    apply hint.mono_set
    rw [uIcc_of_le (le_add_of_nonneg_right hh), uIcc_of_le hab]
    exact Icc_subset_Icc has hshb
  have h_sh_b : IntervalIntegrable Phi volume (s + h) b := by
    apply hint.mono_set
    rw [uIcc_of_le hshb, uIcc_of_le hab]
    exact Icc_subset_Icc hasH le_rfl
  have h_a_sh : IntervalIntegrable Phi volume a (s + h) := h_as.trans h_s_sh
  have h_s_b : IntervalIntegrable Phi volume s b := h_s_sh.trans h_sh_b
  have h1 := intervalIntegral.integral_add_adjacent_intervals h_as h_s_sh
  have h2 := intervalIntegral.integral_add_adjacent_intervals h_s_sh h_sh_b
  have h3 := intervalIntegral.integral_add_adjacent_intervals h_a_sh h_sh_b
  linarith

end GaloisForLFunctions.HTGeometry
