import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicHighLadderGap
import GaloisForLFunctions.RHTower.Sieve.SetIntegralBlockSplit

/-!
# Harmonic error of a high geometric-ladder suffix

Above a quadratic cutoff, prime/cofactor products in the ladder gap are globally distinct.  Thus
the suffix support has overlap one.  Combining that fact with the endpoint-window cardinality bound
gives a closed mean-square budget for the suffix, while retaining the full designated-prime range.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Harmonic support defect restricted to ladder steps `J, ..., L - 1`. -/
def harmonicLadderProductDefectIco
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) (J L : ℕ) (w : ℝ) : ℂ :=
  ∑ x ∈ ladderIndexIco P Q eta J L,
    harmonicMoebiusPhase w x.2 *
      logPoly (harmonicRamareCofactorCoeff P) (ladderGapSetAt A₀ B₀ Q eta x) w

theorem continuous_harmonicLadderProductDefectIco
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) (J L : ℕ) :
    Continuous (harmonicLadderProductDefectIco P A₀ B₀ Q eta J L) := by
  refine continuous_finsetSum _ fun x _ => ?_
  exact ((continuous_moebiusPhase x.2).div_const _).mul (continuous_logPoly _ _)

/-- Exact prefix/suffix decomposition of the global harmonic support defect. -/
theorem harmonicLadderProductDefect_eq_add_Ico
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) {J L : ℕ} (hJL : J ≤ L) (w : ℝ) :
    harmonicLadderProductDefect P A₀ B₀ Q eta L w =
      harmonicLadderProductDefect P A₀ B₀ Q eta J w +
        harmonicLadderProductDefectIco P A₀ B₀ Q eta J L w := by
  rw [harmonicLadderProductDefect, harmonicLadderProductDefect,
    harmonicLadderProductDefectIco, ladderIndex, ladderIndex, ladderIndexIco,
    Finset.sum_sigma, Finset.sum_sigma, Finset.sum_sigma]
  exact (Finset.sum_range_add_sum_Ico (fun j =>
    ∑ p ∈ geomBlock P Q (1 + eta) j,
      harmonicMoebiusPhase w p *
        logPoly (harmonicRamareCofactorCoeff P)
          (ladderGapSetAt A₀ B₀ Q eta ⟨j, p⟩) w) hJL).symm

/-- Closed high-suffix mean-square budget. -/
def menonHarmonicHighLadderErrorBudget
    (A₀ B₀ : ℕ) (eta U W : ℝ) : ℝ :=
  ((1 + eta) / (A₀ : ℝ)) ^ 2 *
    ((5 * Real.pi / 2 * W +
        5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ)) *
      (((A₀ : ℝ) + (B₀ : ℝ)) * eta *
          (1 + Real.log ⌊(B₀ : ℝ) / U⌋₊) +
        6 * (⌊(B₀ : ℝ) / U⌋₊ : ℝ)))

set_option maxHeartbeats 300000 in
/-- Mean square of the high harmonic support defect.  Product injectivity makes the support
overlap exactly at most one, and endpoint-window counting controls its total cardinality. -/
theorem integral_Icc_normSq_harmonicLadderProductDefectIco_le_closed
    {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q eta U W : ℝ} (hQ : 1 ≤ Q) (heta : 0 ≤ eta) (hW : 1 ≤ W)
    {J L : ℕ} (hPprime : ∀ p ∈ P, p.Prime)
    (hJU : U ≤ Q * (1 + eta) ^ J) (hU : 0 < U)
    (hU2 : (B₀ : ℝ) < U ^ 2) :
    (∫ w in Set.Icc (-W) W,
      ‖harmonicLadderProductDefectIco P A₀ B₀ Q eta J L w‖ ^ 2) ≤
        menonHarmonicHighLadderErrorBudget A₀ B₀ eta U W := by
  classical
  set N : ℕ := ⌊(B₀ : ℝ) * (1 + eta)⌋₊ with hN
  set Omega : ℝ := (1 + eta) / (A₀ : ℝ) with hOmega
  have hOmega0 : 0 < Omega := by
    rw [hOmega]
    have hA0R : (0 : ℝ) < (A₀ : ℝ) := by exact_mod_cast hA
    positivity
  have hfull : ∀ x ∈ ladderIndexIco P Q eta J L,
      x ∈ ladderIndex P Q eta L := by
    intro x hx
    rw [ladderIndexIco, Finset.mem_sigma] at hx
    rw [ladderIndex, Finset.mem_sigma]
    have hj := hx.1
    rw [Finset.mem_Ico] at hj
    exact ⟨Finset.mem_range.2 hj.2, hx.2⟩
  have hpos : ∀ x ∈ ladderIndexIco P Q eta J L, 0 < x.2 := by
    intro x hx
    have hx' := hx
    rw [ladderIndexIco, Finset.mem_sigma] at hx'
    exact (hPprime x.2 (geomBlock_subset P Q (1 + eta) x.1 hx'.2)).pos
  have hDpos : ∀ x ∈ ladderIndexIco P Q eta J L,
      ∀ m ∈ ladderGapSetAt A₀ B₀ Q eta x, 0 < m := by
    intro x _ m hm
    exact ladderGapSetAt_pos hA (lt_of_lt_of_le zero_lt_one hQ) heta x.1
      (Finset.mem_sdiff.1 hm).1
  have hDN : ∀ x ∈ ladderIndexIco P Q eta J L,
      (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m) ⊆
        Finset.Icc 1 N := by
    intro x hx n hn
    have hupper := ladderGapSetAt_image_subset A₀ B₀ hQ heta L x (hfull x hx) hn
    rw [Finset.mem_Icc] at hupper ⊢
    rw [Finset.mem_image] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    exact ⟨Nat.mul_pos (hpos x hx) (hDpos x hx m hm), by simpa [N] using hupper.2⟩
  have hinj := ladderGapPairsIco_product_injective
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (U := U)
    (J := J) (L := L) hA (lt_of_lt_of_le zero_lt_one hQ) heta hPprime hJU hU hU2
  have hOverlap : ∀ n ∈ Finset.Icc 1 N,
      (((ladderIndexIco P Q eta J L).filter (fun x =>
        n ∈ (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m))).card : ℝ) ≤ 1 := by
    intro n _
    have hcard : ((ladderIndexIco P Q eta J L).filter (fun x =>
        n ∈ (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      have hx' := Finset.mem_filter.1 hx
      have hy' := Finset.mem_filter.1 hy
      rw [Finset.mem_image] at hx' hy'
      obtain ⟨mx, hmx, hnx⟩ := hx'.2
      obtain ⟨my, hmy, hny⟩ := hy'.2
      have hzx : (⟨x, mx⟩ : ((_ : ((_ : ℕ) × ℕ)) × ℕ)) ∈
          ladderGapPairsIco P A₀ B₀ Q eta J L := by
        rw [ladderGapPairsIco, Finset.mem_sigma]
        exact ⟨hx'.1, hmx⟩
      have hzy : (⟨y, my⟩ : ((_ : ((_ : ℕ) × ℕ)) × ℕ)) ∈
          ladderGapPairsIco P A₀ B₀ Q eta J L := by
        rw [ladderGapPairsIco, Finset.mem_sigma]
        exact ⟨hy'.1, hmy⟩
      have hpair := hinj hzx hzy (hnx.trans hny.symm)
      exact congrArg Sigma.fst hpair
    exact_mod_cast hcard
  have hcoeff : ∀ x ∈ ladderIndexIco P Q eta J L,
      ∀ n ∈ (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m),
        ‖harmonicPrimeShiftCoeff x.2 (harmonicRamareCofactorCoeff P) n‖ ≤ Omega := by
    intro x hx n hn
    simpa [Omega] using norm_harmonicPrimeShiftCoeff_ladderGap_le
      hA (lt_of_lt_of_le zero_lt_one hQ) heta hPprime (hfull x hx) hn
  have hrep : ∀ w : ℝ,
      harmonicLadderProductDefectIco P A₀ B₀ Q eta J L w =
        ∑ x ∈ ladderIndexIco P Q eta J L,
          logPoly (harmonicPrimeShiftCoeff x.2 (harmonicRamareCofactorCoeff P))
            ((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)) w := by
    intro w
    rw [harmonicLadderProductDefectIco]
    refine Finset.sum_congr rfl fun x hx => ?_
    exact harmonicMoebiusPhase_mul_logPoly (hpos x hx)
      (harmonicRamareCofactorCoeff P) (hDpos x hx) w
  have hcongr :
      (∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefectIco P A₀ B₀ Q eta J L w‖ ^ 2) =
      ∫ w in Set.Icc (-W) W,
        ‖∑ x ∈ ladderIndexIco P Q eta J L,
          logPoly (harmonicPrimeShiftCoeff x.2 (harmonicRamareCofactorCoeff P))
            ((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)) w‖ ^ 2 := by
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => by rw [hrep w]
  rw [hcongr]
  have hmain := integral_Icc_normSq_sum_logPoly_le_support_bound
    (ladderIndexIco P Q eta J L)
    (fun x => harmonicPrimeShiftCoeff x.2 (harmonicRamareCofactorCoeff P))
    (fun x => (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m))
    hDN hOmega0 hcoeff (by norm_num : (0 : ℝ) ≤ 1) hOverlap hW
  have himageCard : ∀ x ∈ ladderIndexIco P Q eta J L,
      (((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)).card : ℝ) =
        ((ladderGapSetAt A₀ B₀ Q eta x).card : ℝ) := by
    intro x hx
    have hmul : Set.InjOn (fun m => x.2 * m)
        (ladderGapSetAt A₀ B₀ Q eta x : Set ℕ) := by
      intro m₁ _ m₂ _ heq
      exact Nat.eq_of_mul_eq_mul_left (hpos x hx) heq
    exact_mod_cast Finset.card_image_of_injOn hmul
  have hcards :
      (∑ x ∈ ladderIndexIco P Q eta J L,
          (((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)).card : ℝ)) =
        ((ladderGapPairsIco P A₀ B₀ Q eta J L).card : ℝ) := by
    rw [ladderGapPairsIco, Finset.card_sigma, Nat.cast_sum]
    exact Finset.sum_congr rfl himageCard
  rw [hcards] at hmain
  have hgap := card_ladderGapPairsIco_le_harmonic
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (U := U)
    (J := J) (L := L) hA (lt_of_lt_of_le zero_lt_one hQ) heta hPprime hJU hU hU2
  refine hmain.trans ?_
  rw [menonHarmonicHighLadderErrorBudget]
  dsimp only [Omega, N] at hmain ⊢
  have hmean0 : 0 ≤ 5 * Real.pi / 2 * W +
      5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) := by positivity
  have hscale0 : 0 ≤ ((1 + eta) / (A₀ : ℝ)) ^ 2 := sq_nonneg _
  have hmean := mul_le_mul_of_nonneg_left hgap hmean0
  simpa only [one_mul] using mul_le_mul_of_nonneg_left hmean hscale0

/-- Full global harmonic defect controlled by a prefix budget and the injective high-suffix budget. -/
theorem integral_Icc_normSq_harmonicLadderProductDefect_le_prefix_add_high
    {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q eta U W : ℝ} (hQ : 1 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W)
    {J L : ℕ} (hJL : J ≤ L) (hPprime : ∀ p ∈ P, p.Prime)
    (hPge : ∀ p ∈ P, Q ≤ (p : ℝ))
    (hJU : U ≤ Q * (1 + eta) ^ J) (hU : 0 < U)
    (hU2 : (B₀ : ℝ) < U ^ 2) :
    (∫ w in Set.Icc (-W) W,
      ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ 2) ≤
      2 * menonHarmonicLadderErrorBudget A₀ B₀ Q eta W J +
        2 * menonHarmonicHighLadderErrorBudget A₀ B₀ eta U W := by
  have hsplit := setIntegral_normSq_add_le
    (continuous_harmonicLadderProductDefect P A₀ B₀ Q eta J)
    (continuous_harmonicLadderProductDefectIco P A₀ B₀ Q eta J L)
    measurableSet_Icc (Set.Subset.rfl : Set.Icc (-W) W ⊆ Set.Icc (-W) W)
  have hrewrite :
      (∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ 2) =
      ∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefect P A₀ B₀ Q eta J w +
          harmonicLadderProductDefectIco P A₀ B₀ Q eta J L w‖ ^ 2 := by
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => by
      rw [harmonicLadderProductDefect_eq_add_Ico P A₀ B₀ Q eta hJL w]
  rw [hrewrite]
  have hlo := integral_Icc_normSq_harmonicLadderProductDefect_le_closed
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    hA hQ heta hW hPprime hPge (L := J)
  have hhi := integral_Icc_normSq_harmonicLadderProductDefectIco_le_closed
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (U := U) (W := W)
    (J := J) (L := L) hA hQ.le heta hW hPprime hJU hU hU2
  exact hsplit.trans (add_le_add
    (mul_le_mul_of_nonneg_left hlo (by norm_num))
    (mul_le_mul_of_nonneg_left hhi (by norm_num)))

end

end RHTower.Sieve
