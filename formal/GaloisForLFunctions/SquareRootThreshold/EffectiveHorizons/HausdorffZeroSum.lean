import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffAtoms
import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffCounts
import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HausdorffSummation

/-!
# The complete Hausdorff zero sum near a broad saddle

The positive core is compared with all possible negative terms: low
ordinates, the Gaussian region, and the power tail.
-/

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle

open _root_.RHTower

/-- Negative part of the real Hausdorff atom. -/
def negativeAtom (R : ℝ) (k r : ℕ) (q : XiZeroCopy) : ℝ :=
  max (-(hausdorffAtomTerm R k r q).re) 0

theorem negativeAtom_nonneg (R : ℝ) (k r : ℕ) (q : XiZeroCopy) :
    0 ≤ negativeAtom R k r q := le_max_right _ _

theorem negativeAtom_le_norm (R : ℝ) (k r : ℕ) (q : XiZeroCopy) :
    negativeAtom R k r q ≤ ‖hausdorffAtomTerm R k r q‖ := by
  exact max_le ((neg_le_abs _).trans (Complex.abs_re_le_norm _)) (norm_nonneg _)

/-- The possible negative part in the Gaussian region carries the small band-complement factor. -/
theorem negativeAtom_le_gaussian_shell {R s w : ℝ} (k r : ℕ) (hR : 0 < R)
    (hs : 0 < s) (hr : 0 < r) (hs4 : 4 ≤ s) (hw : 32 ≤ w)
    (hbalance : ((k + 1 : ℕ) : ℝ) * (R * s ^ 2 - 1) = r)
    (hpr : 200 * ((k + 1 : ℕ) : ℝ) ≤ r)
    (hwidth : ((k + 1 : ℕ) : ℝ) * w ^ 2 = s ^ 2)
    (q : XiZeroCopy) (hlo : s / 4 ≤ |(q.1 : ℂ).im|) (hhi : |(q.1 : ℂ).im| ≤ 4 * s) :
    negativeAtom R k r q ≤
      (Real.exp 1 * realKernel R (k + 1) r s *
        Real.exp (-min ((k + 1 : ℕ) : ℝ) (w ^ 2) / 131072)) *
          Real.exp (-(⌊|( |(q.1 : ℂ).im| - s)| / w⌋₊ : ℝ) / 32) := by
  have hp : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hM := realKernel_saddle_pos hs (Nat.succ_pos k) hr hbalance
  by_cases hsign : 0 ≤ (hausdorffAtomTerm R k r q).re
  · have hz : negativeAtom R k r q = 0 := max_eq_right (neg_nonpos.mpr hsign)
    rw [hz]
    positivity
  obtain ⟨y, hy, heq⟩ := atom_eq_kernel_abs_ordinate R k r q
  have hgap : s / 8 < |( |(q.1 : ℂ).im| - s)| ∨
      w ^ 2 / 64 < |( |(q.1 : ℂ).im| - s)| := by
    by_cases h₁ : |( |(q.1 : ℂ).im| - s)| ≤ s / 8
    · right
      by_contra h₂
      apply hsign
      rw [heq]
      exact re_kernel_nonneg_of_saddle_band hs (Nat.succ_pos k) hr
        (by linarith only [hpr, hp]) hbalance hwidth hs4
        (by linarith only [hw]) h₁ (le_of_not_gt h₂) hy
    · exact Or.inl (lt_of_not_ge h₁)
  have hw0 : 0 < w := by linarith only [hw]
  have hsplit := gaussian_le_small_mul_geometric hs hw0
    (abs_nonneg (|(q.1 : ℂ).im| - s)) hwidth hgap
    (Nat.floor_le (div_nonneg (abs_nonneg _) hw0.le))
  have hnorm := norm_kernel_le_saddle_gaussian hR hs (Nat.succ_pos k) hr
    hbalance hpr hwidth hw hlo hhi hy
  have hexp : (-((|(q.1 : ℂ).im| - s) / w) ^ 2 / 16) =
      (-(|( |(q.1 : ℂ).im| - s)| / w) ^ 2 / 16) := by
    rw [div_pow, div_pow, sq_abs]
  rw [hexp, ← heq] at hnorm
  have hmul := mul_le_mul_of_nonneg_left hsplit (show 0 ≤ Real.exp 1 * realKernel R (k + 1) r s by positivity)
  have hneg := negativeAtom_le_norm R k r q
  nlinarith only [hneg, hnorm, hmul]

/-- Uniform finite sums of the possible negative part in the Gaussian region. -/
theorem exists_negative_gaussian_sum_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ S : ℝ, 16 ≤ S ∧ ∀ R s w : ℝ, ∀ k r : ℕ,
      0 < R → S ≤ s → 32 ≤ w → w ≤ s → 0 < r →
      ((k + 1 : ℕ) : ℝ) * (R * s ^ 2 - 1) = r →
      200 * ((k + 1 : ℕ) : ℝ) ≤ r →
      ((k + 1 : ℕ) : ℝ) * w ^ 2 = s ^ 2 →
      ∀ F : Finset XiZeroCopy,
      (∀ q ∈ F, s / 4 ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 4 * s) →
      ∑ q ∈ F, negativeAtom R k r q ≤
        C * gaussianSumConstant * Real.exp 1 * realKernel R (k + 1) r s * w * Real.log s *
          Real.exp (-min ((k + 1 : ℕ) : ℝ) (w ^ 2) / 131072) := by
  classical
  obtain ⟨C, hC, S, hS, hcount⟩ := exists_radial_shell_card_upper
  refine ⟨C, hC, S, hS, ?_⟩
  intro R s w k r hR hs hw hws hr hbalance hpr hwidth F hF
  have hs0 : 0 < s := by linarith only [hS, hs]
  have hM := realKernel_saddle_pos hs0 (Nat.succ_pos k) hr hbalance
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg (by linarith only [hS, hs])
  let index := fun q : XiZeroCopy => ⌊|( |(q.1 : ℂ).im| - s)| / w⌋₊
  have hcard : ∀ n : ℕ, ((F.filter (fun q => index q = n)).card : ℝ) ≤
      (C * w * Real.log s) * ((n : ℝ) + 1) := by
    intro n
    have h := hcount s w hs (by linarith only [hw]) hws n
      (F.filter (fun q => index q = n)) (by
        intro q hq
        obtain ⟨hqF, hqn⟩ := Finset.mem_filter.mp hq
        exact ⟨(hF q hqF).1, (hF q hqF).2, hqn⟩)
    nlinarith only [h]
  have hterm : ∀ q ∈ F, negativeAtom R k r q ≤
      (Real.exp 1 * realKernel R (k + 1) r s *
        Real.exp (-min ((k + 1 : ℕ) : ℝ) (w ^ 2) / 131072)) * Real.exp (-(index q : ℝ) / 32) := by
    intro q hq
    exact negativeAtom_le_gaussian_shell k r hR hs0 hr
      (by linarith only [hS, hs]) hw hbalance hpr hwidth q (hF q hq).1 (hF q hq).2
  have h := sum_le_gaussianSumConstant F index (negativeAtom R k r)
    (by positivity) (by positivity) hcard hterm
  nlinarith only [h]

/-- Power tails are bounded after grouping copies in intervals of one saddle height. -/
theorem exists_negative_power_sum_bound :
    ∃ S : ℝ, 4 ≤ S ∧ ∀ R s w : ℝ, ∀ k r : ℕ,
      0 < R → S ≤ s → 32 ≤ w → 4 ≤ k + 1 → 0 < r →
      ((k + 1 : ℕ) : ℝ) * (R * s ^ 2 - 1) = r →
      200 * ((k + 1 : ℕ) : ℝ) ≤ r →
      ((k + 1 : ℕ) : ℝ) * w ^ 2 = s ^ 2 →
      ∀ F : Finset XiZeroCopy, (∀ q ∈ F, 4 * s ≤ |(q.1 : ℂ).im|) →
      ∑ q ∈ F, negativeAtom R k r q ≤
        4096 * Real.exp 1 * realKernel R (k + 1) r s * s * Real.log s * (4 : ℝ)⁻¹ ^ (k + 1) := by
  classical
  obtain ⟨S, hS, hcount⟩ := exists_total_card_upper
  refine ⟨S, hS, ?_⟩
  intro R s w k r hR hs hw hp hr hbalance hpr hwidth F hF
  have hs0 : 0 < s := by linarith only [hS, hs]
  have hlogs : 1 ≤ Real.log s := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ s by linarith only [Real.exp_one_lt_d9, hS, hs])
    rwa [Real.log_exp] at h
  have hM := realKernel_saddle_pos hs0 (Nat.succ_pos k) hr hbalance
  let index := fun q : XiZeroCopy => ⌊|(q.1 : ℂ).im| / s⌋₊
  have hindex : ∀ q ∈ F, 4 ≤ index q := by
    intro q hq
    apply Nat.le_floor
    exact (le_div_iff₀ hs0).mpr (hF q hq)
  have hcard : ∀ n : ℕ, 4 ≤ n → ((F.filter (fun q => index q = n)).card : ℝ) ≤
      (2 * s * Real.log s) * ((n : ℝ) + 1) ^ 2 := by
    intro n hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn1 : 0 < (n : ℝ) + 1 := by positivity
    have hT : S ≤ ((n : ℝ) + 1) * s := by nlinarith only [hs, mul_nonneg hn0 hs0.le]
    have hc := hcount (((n : ℝ) + 1) * s) hT (F.filter (fun q => index q = n)) (by
      intro q hq
      obtain ⟨_, hqn⟩ := Finset.mem_filter.mp hq
      have h := Nat.lt_floor_add_one (|(q.1 : ℂ).im| / s)
      change |(q.1 : ℂ).im| / s < (index q : ℝ) + 1 at h
      rw [hqn, div_lt_iff₀ hs0] at h
      exact h.le)
    have hnlog : Real.log ((n : ℝ) + 1) ≤ n := by
      have h := Real.log_le_sub_one_of_pos hn1
      linarith only [h]
    have hnl := mul_le_mul_of_nonneg_left hlogs hn0
    have hlogT : Real.log (((n : ℝ) + 1) * s) ≤ ((n : ℝ) + 1) * Real.log s := by
      rw [Real.log_mul hn1.ne' hs0.ne']
      nlinarith only [hnlog, hnl]
    have h := mul_le_mul_of_nonneg_left hlogT (show 0 ≤ 2 * (((n : ℝ) + 1) * s) by positivity)
    nlinarith only [hc, h]
  have hterm : ∀ q ∈ F, negativeAtom R k r q ≤
      (Real.exp 1 * realKernel R (k + 1) r s) * (index q : ℝ)⁻¹ ^ (k + 1) := by
    intro q hq
    obtain ⟨y, hy, heq⟩ := atom_eq_kernel_abs_ordinate R k r q
    have hnorm := norm_kernel_le_saddle_power hR hs0 (Nat.succ_pos k) hr
      hbalance hpr hwidth hw (hF q hq) hy
    rw [← heq] at hnorm
    have hidx : (4 : ℝ) ≤ index q := by exact_mod_cast hindex q hq
    have hidx0 : (0 : ℝ) < index q := by linarith only [hidx]
    have hratio : 0 < |(q.1 : ℂ).im| / s := by
      exact div_pos (by linarith only [hF q hq, hs0]) hs0
    have hfloor := Nat.floor_le (div_nonneg (abs_nonneg (q.1 : ℂ).im) hs0.le)
    change (index q : ℝ) ≤ |(q.1 : ℂ).im| / s at hfloor
    have hinv := (inv_le_inv₀ hratio hidx0).mpr hfloor
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (|(q.1 : ℂ).im| / s)⁻¹) hinv (k + 1)
    have hmul := mul_le_mul_of_nonneg_left hpow (show 0 ≤ Real.exp 1 * realKernel R (k + 1) r s by positivity)
    exact (negativeAtom_le_norm R k r q).trans (hnorm.trans hmul)
  have h := sum_le_power_tail F index (negativeAtom R k r)
    (by positivity) (by positivity) hp hindex hcard hterm
  nlinarith only [h]

/-- Every possible negative term is paid by one of the three saddle tails. -/
theorem exists_negative_sum_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ S : ℝ, 16 ≤ S ∧ ∀ s w T : ℝ, ∀ k r : ℕ,
      S ≤ s → 32 ≤ w → w ≤ s → 500 ≤ T → 4 ≤ k + 1 → 0 < r →
      ((k + 1 : ℕ) : ℝ) * (primeArchEndpointHausdorffRadius * s ^ 2 - 1) = r →
      200 * ((k + 1 : ℕ) : ℝ) ≤ r →
      ((k + 1 : ℕ) : ℝ) * w ^ 2 = s ^ 2 →
      10 * ((k + 1 : ℕ) : ℝ) * primeArchEndpointHausdorffRadius * T ^ 2 = r →
      ∀ F : Finset XiZeroCopy,
      ∑ q ∈ F, negativeAtom primeArchEndpointHausdorffRadius k r q ≤
        C * realKernel primeArchEndpointHausdorffRadius (k + 1) r s * w * Real.log s *
          Real.exp (-min ((k + 1 : ℕ) : ℝ) (w ^ 2) / 131072) +
        4096 * Real.exp 1 * realKernel primeArchEndpointHausdorffRadius (k + 1) r s * s *
          Real.log s * (4 : ℝ)⁻¹ ^ (k + 1) +
        2 * realKernel primeArchEndpointHausdorffRadius (k + 1) r s * s * Real.log s *
          Real.exp (-4 * ((k + 1 : ℕ) : ℝ)) := by
  classical
  obtain ⟨Cg, hCg, Sg, hSg, hgauss⟩ := exists_negative_gaussian_sum_bound
  obtain ⟨Sp, hSp, hpower⟩ := exists_negative_power_sum_bound
  obtain ⟨Sl, hSl, hcount⟩ := exists_total_card_upper
  have hG := gaussianSumConstant_pos
  have hCgG : 0 ≤ Cg * gaussianSumConstant * Real.exp 1 := by positivity
  refine ⟨Cg * gaussianSumConstant * Real.exp 1 + 1, by linarith only [hCgG],
    max Sg (max Sp Sl), hSg.trans (le_max_left _ _), ?_⟩
  intro s w T k r hs hw hws hT hp hr hbalance hpr hwidth hthermal F
  have hsg : Sg ≤ s := (le_max_left _ _).trans hs
  have hsp : Sp ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hsl : Sl ≤ s := (le_max_right _ _).trans ((le_max_right _ _).trans hs)
  have hs0 : 0 < s := by linarith only [hSg, hsg]
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg (by linarith only [hSg, hsg])
  have hM := realKernel_saddle_pos hs0 (Nat.succ_pos k) hr hbalance
  let f := negativeAtom primeArchEndpointHausdorffRadius k r
  let L := F.filter (fun q => |(q.1 : ℂ).im| ≤ s / 4)
  let H := F.filter (fun q => ¬ |(q.1 : ℂ).im| ≤ s / 4)
  let B := H.filter (fun q => |(q.1 : ℂ).im| ≤ 4 * s)
  let P := H.filter (fun q => ¬ |(q.1 : ℂ).im| ≤ 4 * s)
  have hlow : ∑ q ∈ L, f q ≤
      2 * realKernel primeArchEndpointHausdorffRadius (k + 1) r s * s * Real.log s *
        Real.exp (-4 * ((k + 1 : ℕ) : ℝ)) := by
    have hcard := hcount s hsl L (by
      intro q hq
      have h := (Finset.mem_filter.mp hq).2
      linarith only [h, hs0])
    have hterm : ∀ q ∈ L, f q ≤ realKernel primeArchEndpointHausdorffRadius (k + 1) r s *
        Real.exp (-4 * ((k + 1 : ℕ) : ℝ)) := by
      intro q hq
      exact (negativeAtom_le_norm _ k r q).trans
        (norm_atom_le_saddle_low k r primeArchEndpointHausdorffRadius_pos hs0
          hbalance hpr hT hthermal (xiThermalNode_le_primeArchEndpointHausdorffRadius q)
          (Finset.mem_filter.mp hq).2)
    have hsum := Finset.sum_le_sum hterm
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have hmul := mul_le_mul_of_nonneg_right hcard
      (show 0 ≤ realKernel primeArchEndpointHausdorffRadius (k + 1) r s *
        Real.exp (-4 * ((k + 1 : ℕ) : ℝ)) by positivity)
    nlinarith only [hsum, hmul]
  have hmid := hgauss primeArchEndpointHausdorffRadius s w k r
    primeArchEndpointHausdorffRadius_pos hsg hw hws hr hbalance hpr hwidth B (by
      intro q hq
      obtain ⟨hqH, hhi⟩ := Finset.mem_filter.mp hq
      have hlo := (Finset.mem_filter.mp hqH).2
      exact ⟨(lt_of_not_ge hlo).le, hhi⟩)
  have hfar := hpower primeArchEndpointHausdorffRadius s w k r
    primeArchEndpointHausdorffRadius_pos hsp hw hp hr hbalance hpr hwidth P (by
      intro q hq
      exact (lt_of_not_ge (Finset.mem_filter.mp hq).2).le)
  have hsplit₁ : (∑ q ∈ L, f q) + ∑ q ∈ H, f q = ∑ q ∈ F, f q :=
    Finset.sum_filter_add_sum_filter_not F (fun q => |(q.1 : ℂ).im| ≤ s / 4) f
  have hsplit₂ : (∑ q ∈ B, f q) + ∑ q ∈ P, f q = ∑ q ∈ H, f q :=
    Finset.sum_filter_add_sum_filter_not H (fun q => |(q.1 : ℂ).im| ≤ 4 * s) f
  have hextra : 0 ≤ realKernel primeArchEndpointHausdorffRadius (k + 1) r s * w *
      Real.log s * Real.exp (-min ((k + 1 : ℕ) : ℝ) (w ^ 2) / 131072) := by positivity
  change ∑ q ∈ F, f q ≤ _
  nlinarith only [hlow, hmid, hfar, hsplit₁, hsplit₂, hextra]

/-- Absolute convergence of the source series controls its negative part. -/
theorem summable_negativeAtom (R : ℝ) (k r : ℕ) : Summable (negativeAtom R k r) := by
  have hs : Summable (fun q => hausdorffAtomTerm R k r q) :=
    summable_xiCentralScaledHausdorffTerm R k r
  have hre : Summable (fun q => (hausdorffAtomTerm R k r q).re) :=
    ⟨_, Complex.hasSum_re hs.hasSum⟩
  exact Summable.of_nonneg_of_le (negativeAtom_nonneg R k r)
    (fun q => max_le (neg_le_abs _) (abs_nonneg _)) hre.abs

/-- A positive finite core can only lose the total negative part of the series. -/
theorem core_sum_le_source_add_negative (R : ℝ) (k r : ℕ) (F : Finset XiZeroCopy) :
    ∑ q ∈ F, (hausdorffAtomTerm R k r q).re ≤
      scaledHausdorffMomentDifference R normalizedPrimeArchMoment k r +
        ∑' q, negativeAtom R k r q := by
  have hs : Summable (fun q => hausdorffAtomTerm R k r q) :=
    summable_xiCentralScaledHausdorffTerm R k r
  have hre : Summable (fun q => (hausdorffAtomTerm R k r q).re) :=
    ⟨_, Complex.hasSum_re hs.hasSum⟩
  have hn := summable_negativeAtom R k r
  have hpos : ∀ q, 0 ≤ (hausdorffAtomTerm R k r q).re + negativeAtom R k r q := by
    intro q
    have h := le_max_left (-(hausdorffAtomTerm R k r q).re) 0
    change -(hausdorffAtomTerm R k r q).re ≤ negativeAtom R k r q at h
    linarith only [h]
  have hfinite : ∑ q ∈ F, (hausdorffAtomTerm R k r q).re ≤
      ∑ q ∈ F, ((hausdorffAtomTerm R k r q).re + negativeAtom R k r q) := by
    apply Finset.sum_le_sum
    intro q _
    linarith only [negativeAtom_nonneg R k r q]
  have hsum := Summable.sum_le_tsum F (fun q _ => hpos q) (hre.add hn)
  rw [hre.tsum_add hn] at hsum
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum]
  change _ ≤ (∑' q, hausdorffAtomTerm R k r q).re + _
  rw [Complex.re_tsum hs]
  exact hfinite.trans hsum

end GaloisForLFunctions.SquareRootThreshold.HausdorffSaddle
