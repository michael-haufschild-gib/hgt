import Mathlib.Order.Interval.Set.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Counting levels of an unordered harmonic sequence

The reciprocal counting law underlying the Weyl asymptotics of Ponge and
Tian (arXiv:2605.25591) does not require sorting a sequence whose terms
are asymptotic to c/n. A finite exceptional head only changes the count
by a bounded amount. All counts below use strict superlevel sets.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace GaloisForLFunctions.HarmonicSuperlevel

/-- Number of indices with weight strictly above the reciprocal threshold. -/
def count (a : ℕ → ℝ) (t : ℝ) : ℕ := {n : ℕ | 1 < t*a n}.ncard

private theorem bracket {a : ℕ → ℝ} {b c d : ℝ} (hb : 0 ≤ b) (hbc : b < c) (hcd : c < d)
    (h : Tendsto (fun n : ℕ => (n:ℝ)*a n) atTop (𝓝 c)) :
    ∃ M : ℕ, ∀ t : ℝ, 0 < t → {n : ℕ | 1 < t*a n}.Finite ∧
      b*t-((M:ℝ)+1) ≤ count a t ∧ (count a t : ℝ) ≤ d*t+((M:ℝ)+1) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((h.eventually_const_lt hbc).and (h.eventually_lt_const hcd))
  refine ⟨M,fun t ht => ?_⟩
  let S := {n : ℕ | 1 < t*a n}
  have hu : S ⊆ Iio (M+⌊d*t⌋₊+1) := by
    intro n hn
    change 1 < t*a n at hn
    by_cases hm : n < M
    · exact show n < M+⌊d*t⌋₊+1 by omega
    have hd := (hM n (le_of_not_gt hm)).2
    have h₁ := mul_le_mul_of_nonneg_left (show 1 ≤ t*a n from hn.le) (Nat.cast_nonneg n : 0 ≤ (n:ℝ))
    have h₂ := mul_lt_mul_of_pos_right hd ht
    have hn' : n ≤ ⌊d*t⌋₊ := Nat.le_floor (by linarith only [h₁,h₂])
    exact show n < M+⌊d*t⌋₊+1 by omega
  have hfin := (finite_Iio _).subset hu
  have hlow : Ioc M ⌊b*t⌋₊ ⊆ S := by
    intro n hn
    have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.zero_le M |>.trans_lt hn.1)
    have h₁ := mul_lt_mul_of_pos_right (hM n hn.1.le).1 ht
    have h₂ : (n:ℝ) ≤ b*t := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le (mul_nonneg hb ht.le))
    apply (mul_lt_mul_iff_right₀ hn₀).mp
    linarith only [h₁,h₂]
  have hlo := ncard_le_ncard hlow hfin
  have hhi := ncard_le_ncard hu (finite_Iio _)
  rw [ncard_Ioc_nat] at hlo
  rw [ncard_Iio_nat] at hhi
  change ⌊b*t⌋₊-M ≤ count a t at hlo
  change count a t ≤ M+⌊d*t⌋₊+1 at hhi
  have hl : (⌊b*t⌋₊ : ℝ) ≤ count a t + (M:ℝ) := by
    exact_mod_cast (show ⌊b*t⌋₊ ≤ count a t + M by omega)
  have hr : (count a t : ℝ) ≤ M + (⌊d*t⌋₊ : ℝ) + 1 := by exact_mod_cast hhi
  refine ⟨hfin,by linarith only [hl,Nat.lt_floor_add_one (b*t)],?_⟩
  linarith only [hr,Nat.floor_le (mul_nonneg ((hb.trans_lt hbc).trans hcd).le ht.le)]

/-- Every positive threshold has finitely many exceedances. Their number
divided by the reciprocal threshold tends to the coefficient c. -/
theorem harmonic_counting_law {a : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun n : ℕ => (n:ℝ)*a n) atTop (𝓝 c)) :
    (∀ t : ℝ, 0 < t → {n : ℕ | 1 < t*a n}.Finite) ∧
      Tendsto (fun t : ℝ => (count a t : ℝ)/t) atTop (𝓝 c) := by
  obtain ⟨_,hfin⟩ := bracket le_rfl hc (lt_add_one c) h
  refine ⟨fun t ht => (hfin t ht).1,tendsto_order.mpr ⟨?_,?_⟩⟩
  · intro v hv
    obtain ⟨b,hb,hbc⟩ := exists_between (max_lt hv hc)
    obtain ⟨M,hM⟩ := bracket ((le_max_right v 0).trans hb.le) hbc (lt_add_one c) h
    have he : Tendsto (fun t : ℝ => ((M:ℝ)+1)/t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hs := he.eventually_lt_const (sub_pos.mpr ((le_max_left v 0).trans_lt hb))
    filter_upwards [hs,eventually_gt_atTop (0:ℝ)] with t ht hpos
    apply (lt_div_iff₀ hpos).mpr
    have hh := (div_lt_iff₀ hpos).mp ht
    linarith only [(hM t hpos).2.1,hh]
  · intro v hv
    obtain ⟨d,hd,hdv⟩ := exists_between hv
    obtain ⟨M,hM⟩ := bracket le_rfl hc hd h
    have he : Tendsto (fun t : ℝ => ((M:ℝ)+1)/t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    filter_upwards [he.eventually_lt_const (sub_pos.mpr hdv),eventually_gt_atTop (0:ℝ)] with t ht hpos
    apply (div_lt_iff₀ hpos).mpr
    have hh := (div_lt_iff₀ hpos).mp ht
    linarith only [(hM t hpos).2.2,hh]

#print axioms harmonic_counting_law

end GaloisForLFunctions.HarmonicSuperlevel
