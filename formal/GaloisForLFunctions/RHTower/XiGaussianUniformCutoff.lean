import GaloisForLFunctions.RHTower.XiGaussianPhaseTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A single spectral cutoff controls phase tails at every positive heat time

Away from time zero, positive anchor-time summability controls the norm tail
relative to the actual critical reserve. Near zero, the complete imaginary
channel is already uniformly small. Their combination controls phase tails
on the entire positive time axis, retaining the finite head exactly.
-/

open scoped Real BigOperators
open Filter Topology Complex
noncomputable section

namespace RHTower

def xiGaussianCoefficientAnchorAt (N : ℕ) (s : {s : ℝ // 0 < s}) : ℝ :=
  ∑ j ∈ Finset.range N, ∑' q : XiZeroCopy,
    ‖xiPolynomialGaussianHeatTerm (Polynomial.X ^ j) s q‖

theorem xiGaussianCoefficientAnchorAt_nonneg (N : ℕ) (s : {s : ℝ // 0 < s}) :
    0 ≤ xiGaussianCoefficientAnchorAt N s :=
  Finset.sum_nonneg fun _ _ => tsum_nonneg fun _ => norm_nonneg _

theorem tsum_norm_xiGaussian_rangeSum_le_anchorAt (N : ℕ) (a : ℕ → ℝ)
    (s : {s : ℝ // 0 < s}) :
    (∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) s q‖) ≤
        (∑ j ∈ Finset.range N, a j ^ 2) * xiGaussianCoefficientAnchorAt N s := by
  have hs : Summable (fun q : XiZeroCopy =>
      ∑ j ∈ Finset.range N, ‖xiPolynomialGaussianHeatTerm (Polynomial.X ^ j) s q‖) :=
    summable_sum fun j _ => summable_norm_xiPolynomialGaussianHeatTerm s.property _
  have h := Summable.tsum_le_tsum (norm_xiPolynomialGaussianHeatTerm_rangeSum_le N a s)
    (summable_norm_xiPolynomialGaussianHeatTerm s.property _) (hs.mul_left _)
  rw [tsum_mul_left, Summable.tsum_finsetSum
    (fun j _ => summable_norm_xiPolynomialGaussianHeatTerm s.property (Polynomial.X ^ j))] at h
  exact h

/-- Arbitrary positive anchor time supplies uniform exponential tail decay. -/
theorem xiGaussianTailEnergy_le_anchorAt (N : ℕ) (a : ℕ → ℝ)
    (s : {s : ℝ // 0 < s}) (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) (R : ℝ) :
    xiGaussianTailEnergy
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 R ≤
        Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * R)) * xiGaussianCoefficientAnchorAt N s *
          (∑ j ∈ Finset.range N, a j ^ 2) := by
  classical
  let Q := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
  let S : Set XiZeroCopy := {q : XiZeroCopy | R < (xiSpectralPoint q ^ 2).re}
  have ht := summable_norm_xiPolynomialGaussianHeatTerm t.1.property Q
  have hs := summable_norm_xiPolynomialGaussianHeatTerm s.property Q
  have hp (q : S) : ‖xiPolynomialGaussianHeatTerm Q t.1 q.1‖ ≤
      Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * R)) * ‖xiPolynomialGaussianHeatTerm Q s q.1‖ := by
    rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm]
    have he : Real.exp (-((t.1 : ℝ) * (xiSpectralPoint q.1 ^ 2).re)) ≤
        Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * R)) *
          Real.exp (-((s : ℝ) * (xiSpectralPoint q.1 ^ 2).re)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have hm := mul_le_mul_of_nonneg_left q.property.le (sub_nonneg.mpr t.property)
      nlinarith only [hm]
    exact (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq (mul_left_comm _ _ _)
  have h : (∑' q : S, ‖xiPolynomialGaussianHeatTerm Q t.1 q.1‖) ≤
      ∑' q : S, Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * R)) *
        ‖xiPolynomialGaussianHeatTerm Q s q.1‖ :=
    Summable.tsum_le_tsum hp (ht.subtype S) ((hs.subtype S).mul_left _)
  rw [tsum_mul_left] at h
  have hsub := Summable.tsum_subtype_le _ S (fun _ => norm_nonneg _) hs
  have hanchor := tsum_norm_xiGaussian_rangeSum_le_anchorAt N a s
  exact (h.trans (mul_le_mul_of_nonneg_left (hsub.trans hanchor)
    (Real.exp_pos _).le)).trans_eq (by ring)

/-- A single cutoff controls the full norm tail uniformly on every interval bounded away
from zero, relative to actual real-channel energy and uniformly in coefficients. -/
theorem exists_xiGaussianTail_uniform_away_zero (N : ℕ)
    (δ ε : {x : ℝ // 0 < x}) :
    ∃ R : ℝ, 0 < R ∧
      ∀ (a : ℕ → ℝ) (t : {t : {t : ℝ // 0 < t} // (δ : ℝ) ≤ (t : ℝ)}),
        xiGaussianTailEnergy
          (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 R ≤
            (ε : ℝ) * xiGaussianRealChannelEnergy
              (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 := by
  obtain ⟨c, hc, L, hL, hfloor⟩ := exists_xiGaussianRealChannel_allTime_floor N
  let s : {s : ℝ // 0 < s} := ⟨(δ : ℝ) / 2, half_pos δ.property⟩
  let C := xiGaussianCoefficientAnchorAt N s
  have hC : 0 ≤ C := xiGaussianCoefficientAnchorAt_nonneg N s
  have hec : 0 < (ε : ℝ) * c := mul_pos ε.property hc
  have he : Tendsto (fun R : ℝ => Real.exp (-((s : ℝ) * R))) atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (s : ℝ) s.property
  have hlim : Tendsto (fun R : ℝ => C * Real.exp ((δ : ℝ) * L) *
      Real.exp (-((s : ℝ) * R))) atTop (nhds 0) := by
    simpa only [mul_zero] using he.const_mul (C * Real.exp ((δ : ℝ) * L))
  obtain ⟨R, hbudget, hR⟩ :=
    ((hlim.eventually_lt_const hec).and (eventually_gt_atTop L)).exists
  refine ⟨R, by linarith only [hL, hR], ?_⟩
  intro a t
  have hst : (s : ℝ) ≤ (t.1 : ℝ) := by
    change (δ : ℝ) / 2 ≤ (t.1 : ℝ)
    linarith only [δ.property, t.property]
  have htail := xiGaussianTailEnergy_le_anchorAt N a s ⟨t.1, hst⟩ R
  have hexp : Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * R)) ≤
      Real.exp ((δ : ℝ) * L) * Real.exp (-((s : ℝ) * R)) *
        Real.exp (-(L * (t.1 : ℝ))) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have hp := mul_nonneg (sub_nonneg.mpr t.property) (sub_nonneg.mpr hR.le)
    change -(((t.1 : ℝ) - (δ : ℝ) / 2) * R) ≤
      (δ : ℝ) * L + -((δ : ℝ) / 2 * R) + -(L * (t.1 : ℝ))
    nlinarith only [hp]
  have hbound : Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * R)) * C ≤
      (ε : ℝ) * c * Real.exp (-(L * (t.1 : ℝ))) := by
    calc
      _ ≤ (Real.exp ((δ : ℝ) * L) * Real.exp (-((s : ℝ) * R)) *
          Real.exp (-(L * (t.1 : ℝ)))) * C := mul_le_mul_of_nonneg_right hexp hC
      _ = (C * Real.exp ((δ : ℝ) * L) * Real.exp (-((s : ℝ) * R))) *
          Real.exp (-(L * (t.1 : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget.le (Real.exp_pos _).le
  calc
    _ ≤ Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * R)) * C *
        (∑ j ∈ Finset.range N, a j ^ 2) := htail
    _ ≤ (ε : ℝ) * c * Real.exp (-(L * (t.1 : ℝ))) *
        (∑ j ∈ Finset.range N, a j ^ 2) :=
      mul_le_mul_of_nonneg_right hbound (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = (ε : ℝ) * (c * Real.exp (-(L * (t.1 : ℝ))) *
        (∑ j ∈ Finset.range N, a j ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hfloor a t.1) ε.property.le

/-- One finite spectral cutoff controls the entire imaginary tail for every positive heat
time and every coefficient vector at a fixed finite Hankel order. -/
theorem exists_xiGaussianTailPhase_allTime_relative (N : ℕ) (ε : {ε : ℝ // 0 < ε}) :
    ∃ R : ℝ, 0 < R ∧ ∀ (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
      xiGaussianTailPhaseEnergy
        (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t R ≤
          (ε : ℝ) * xiGaussianRealChannelEnergy
            (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t := by
  obtain ⟨τ₀, hτ₀⟩ := eventually_atBot.mp (eventually_xiGaussianImaginary_le_realChannel N ε)
  let δ : {δ : ℝ // 0 < δ} := ⟨Real.exp τ₀, Real.exp_pos τ₀⟩
  obtain ⟨R, hR, htail⟩ := exists_xiGaussianTail_uniform_away_zero N δ ε
  refine ⟨R, hR, ?_⟩
  intro a t
  by_cases hδt : (δ : ℝ) ≤ (t : ℝ)
  · exact (xiGaussianTailPhaseEnergy_le_energy _ t R).trans (htail a ⟨t, hδt⟩)
  · have htδ : (t : ℝ) ≤ Real.exp τ₀ := (not_le.mp hδt).le
    have hlog : Real.log (t : ℝ) ≤ τ₀ := (Real.log_le_iff_le_exp t.property).mpr htδ
    have hsmall := hτ₀ (Real.log (t : ℝ)) hlog a
    simp only [Real.exp_log t.property] at hsmall
    exact (xiGaussianTailPhaseEnergy_le_full _ t R).trans hsmall

end RHTower
