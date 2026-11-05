import GaloisForLFunctions.CompletedArithmeticForms.ThetaPairCenterTailSpectrum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Absolute convergence of integrated theta-pair spectra

The radial Bessel envelope bounds the complete ordered-pair tail series
by a product of two geometric series, with an explicit rectangular
truncation error uniform in frequency.
-/

open scoped BigOperators
open Finset
namespace GaloisForLFunctions.CompletedArithmeticForms
noncomputable section

private theorem geometric_square_summable {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (B : ℝ) :
    Summable (fun p : ℕ × ℕ => B * a ^ p.1 * a ^ p.2) := by
  have ha : ‖a‖ < 1 := by rwa [Real.norm_of_nonneg ha0]
  have hg := summable_geometric_of_norm_lt_one ha
  have hgn : Summable (fun n : ℕ => ‖a ^ n‖) := by
    simpa only [norm_pow, Real.norm_of_nonneg ha0] using hg
  simpa only [mul_assoc] using (summable_mul_of_summable_norm hgn hgn).mul_left B

private theorem geometric_square_sum {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (B : ℝ) :
    (∑' p : ℕ × ℕ, B * a ^ p.1 * a ^ p.2) = B / (1 - a) ^ 2 := by
  have ha : ‖a‖ < 1 := by rwa [Real.norm_of_nonneg ha0]
  have hg := summable_geometric_of_norm_lt_one ha
  have hp : Summable (fun p : ℕ × ℕ => a ^ p.1 * a ^ p.2) := by
    simpa only [one_mul] using geometric_square_summable ha0 ha1 1
  simp_rw [mul_assoc]
  rw [tsum_mul_left, ← hg.tsum_mul_tsum hg hp, tsum_geometric_of_norm_lt_one ha]
  have hd : 1 - a ≠ 0 := (sub_pos.mpr ha1).ne'
  field_simp [hd]

private theorem geometric_square_partial (a B : ℝ) (M : ℕ) :
    (∑ p ∈ (range M ×ˢ range M), B * a ^ p.1 * a ^ p.2) =
      B * (∑ n ∈ range M, a ^ n) ^ 2 := by
  rw [Finset.sum_product (range M) (range M) (fun p : ℕ × ℕ => B * a ^ p.1 * a ^ p.2)]
  simp only [← mul_sum, ← sum_mul]
  ring

/-- A rectangular truncation of a geometrically dominated double series has an explicit tail. -/
private theorem abs_geometric_square_remainder {f : ℕ × ℕ → ℝ} {a B : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hB : 0 ≤ B)
    (hb : ∀ p, |f p| ≤ B * a ^ p.1 * a ^ p.2) (M : ℕ) :
    |(∑' p : ℕ × ℕ, f p) - ∑ p ∈ (range M ×ˢ range M), f p| ≤
      2 * B * a ^ M / (1 - a) ^ 2 := by
  let S := (range M ×ˢ range M)
  let G : ℕ × ℕ → ℝ := fun p => B * a ^ p.1 * a ^ p.2
  have hG : Summable G := geometric_square_summable ha0 ha1 B
  have habs : Summable (fun p => |f p|) :=
    Summable.of_nonneg_of_le (fun p => abs_nonneg _) hb hG
  have hnorm : Summable (fun p => ‖f p‖) := by
    simpa only [Real.norm_eq_abs] using habs
  have hf : Summable f := hnorm.of_norm
  have hsplit := hf.sum_add_tsum_subtype_compl S
  have he : (∑' p : ℕ × ℕ, f p) - ∑ p ∈ S, f p =
      ∑' p : {p // p ∉ S}, f p := by rw [← hsplit]; abel
  have ht : |(∑' p : ℕ × ℕ, f p) - ∑ p ∈ S, f p| ≤
      ∑' p : {p // p ∉ S}, G p := by
    rw [he]
    have hn := norm_tsum_le_tsum_norm (hnorm.subtype (fun p => p ∉ S))
    simp only [Real.norm_eq_abs] at hn
    exact hn.trans (Summable.tsum_le_tsum (fun p => hb p)
      (habs.subtype _) (hG.subtype _))
  have hD : 0 < 1 - a := sub_pos.mpr ha1
  have hgeom : (∑ n ∈ range M, a ^ n) = (1 - a ^ M) / (1 - a) := by
    rw [geom_sum_eq ha1.ne M]
    field_simp [hD.ne', sub_ne_zero.mpr ha1.ne]
    ring
  have hsum := hG.sum_add_tsum_subtype_compl S
  change (∑ p ∈ (range M ×ˢ range M), B * a ^ p.1 * a ^ p.2) + _ =
    (∑' p : ℕ × ℕ, B * a ^ p.1 * a ^ p.2) at hsum
  rw [geometric_square_partial, hgeom, geometric_square_sum ha0 ha1] at hsum
  have hmul := congrArg (fun x : ℝ => x * (1 - a) ^ 2) hsum
  field_simp [hD.ne'] at hmul
  have htG : (∑' p : {p // p ∉ S}, G p) ≤ 2 * B * a ^ M / (1 - a) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
    nlinarith only [hmul, mul_nonneg hB (sq_nonneg (a ^ M))]
  exact ht.trans htG

/-- Ordered-pair tails are dominated by a product of two geometric sequences. -/
theorem thetaPairCenterTailSpectrum_geometric_bound {r : ℝ} (hr : 0 ≤ r)
    (b : ℝ) (p : ℕ × ℕ) :
    |thetaPairCenterTailSpectrum (p.1 + 1) (p.2 + 1) r b| ≤
      (4 * besselFirstAtomTailCost 0 * Real.exp (-(Real.pi * Real.exp r))) *
        Real.exp (-(Real.pi * Real.exp r)) ^ p.1 *
        Real.exp (-(Real.pi * Real.exp r)) ^ p.2 := by
  let q := Real.pi * Real.exp r
  let a := Real.exp (-q)
  have hq : 0 < q := mul_pos Real.pi_pos (Real.exp_pos r)
  have hb := abs_thetaPairCenterTailSpectrum_uniform_le
    (Nat.succ_pos p.1) (Nat.succ_pos p.2) hr b
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] at hb
  have he : Real.exp (-q * ((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) ≤
      a * a ^ p.1 * a ^ p.2 := by
    dsimp only [a]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_nonneg hq.le (mul_nonneg (Nat.cast_nonneg p.1) (Nat.cast_nonneg p.2))
    nlinarith only [h]
  calc
    _ ≤ 4 * besselFirstAtomTailCost 0 *
        Real.exp (-q * ((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1)) := by
      convert hb using 1
      congr 2
      dsimp only [q]
      ring
    _ ≤ 4 * besselFirstAtomTailCost 0 * (a * a ^ p.1 * a ^ p.2) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num) (besselFirstAtomTailCost_nonneg _))
    _ = _ := by ring

/-- The literal ordered-pair center-tail spectra form an absolutely convergent double series. -/
theorem summable_abs_thetaPairCenterTailSpectrum {r : ℝ} (hr : 0 ≤ r) (b : ℝ) :
    Summable (fun p : ℕ × ℕ => |thetaPairCenterTailSpectrum (p.1 + 1) (p.2 + 1) r b|) := by
  have hq : 0 < Real.pi * Real.exp r := mul_pos Real.pi_pos (Real.exp_pos r)
  have ha0 : 0 ≤ Real.exp (-(Real.pi * Real.exp r)) := (Real.exp_pos _).le
  have ha1 : Real.exp (-(Real.pi * Real.exp r)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos hq)
  exact Summable.of_nonneg_of_le (fun p => abs_nonneg _)
    (thetaPairCenterTailSpectrum_geometric_bound hr b)
    (geometric_square_summable ha0 ha1 _)

/-- The complete absolutely convergent sum of ordered-pair center-tail spectra. -/
def thetaPairCenterTailSum (r b : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, thetaPairCenterTailSpectrum (p.1 + 1) (p.2 + 1) r b

/-- A finite rectangle approximates the full pair-tail series with explicit exponential error. -/
theorem thetaPairCenterTailSum_remainder_le {r : ℝ} (hr : 0 ≤ r) (b : ℝ) (M : ℕ) :
    |thetaPairCenterTailSum r b -
      ∑ p ∈ (Finset.range M ×ˢ Finset.range M),
        thetaPairCenterTailSpectrum (p.1 + 1) (p.2 + 1) r b| ≤
      8 * besselFirstAtomTailCost 0 *
        Real.exp (-(Real.pi * Real.exp r) * ((M : ℝ) + 1)) /
          (1 - Real.exp (-(Real.pi * Real.exp r))) ^ 2 := by
  let q := Real.pi * Real.exp r
  let a := Real.exp (-q)
  have hq : 0 < q := mul_pos Real.pi_pos (Real.exp_pos r)
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have ha1 : a < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hq)
  have hB : 0 ≤ 4 * besselFirstAtomTailCost 0 * a :=
    mul_nonneg (mul_nonneg (by norm_num) (besselFirstAtomTailCost_nonneg _)) ha0
  have h := abs_geometric_square_remainder ha0 ha1 hB
    (thetaPairCenterTailSpectrum_geometric_bound hr b) M
  have he : a * a ^ M = Real.exp (-q * ((M : ℝ) + 1)) := by
    dsimp only [a]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  change |thetaPairCenterTailSum r b - _| ≤ _ at h
  calc
    _ ≤ 2 * (4 * besselFirstAtomTailCost 0 * a) * a ^ M / (1 - a) ^ 2 := h
    _ = _ := by
      rw [show 2 * (4 * besselFirstAtomTailCost 0 * a) * a ^ M =
        8 * besselFirstAtomTailCost 0 * (a * a ^ M) by ring, he]

end
end GaloisForLFunctions.CompletedArithmeticForms
