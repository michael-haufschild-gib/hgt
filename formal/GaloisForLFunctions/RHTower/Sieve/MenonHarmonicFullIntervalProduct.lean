import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicGlobalFrequencyAssembly
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicProductCostBounds
import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare

/-!
# Harmonic product cost on a full receiver interval

On an all-small frequency set the cofactor integral may be enlarged to the complete symmetric
receiver interval.  The ordinary coefficient-energy mean-value theorem then gives the sharp
`W + N` scale and avoids the restricted-set square-root kernel loss.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Full-interval coefficient-energy cost for one genuine harmonic prime/cofactor product. -/
def menonHarmonicFullIntervalProductCost
    (_P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta W V : ℝ) (j : ℕ) : ℝ :=
  let L₀ : ℕ := ⌈(A₀ : ℝ) /
    ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊
  let N : ℕ := ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊
  let D : Finset ℕ := geomCofactorBlockAt A₀ B₀ Q eta j
  V ^ 2 * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ)) *
    (D.card : ℝ) * (1 / (L₀ : ℝ)) ^ 2)

/-- A prime supremum on any measurable subset of `[-W,W]`, with the cofactor paid on the full
interval by its actual reciprocal coefficient energy. -/
theorem setIntegral_normSq_harmonicProduct_geom_le_fullInterval
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W V : ℝ}
    (hW : 1 ≤ W) (j : ℕ)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) /
      ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hprime : ∀ w ∈ E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ ≤ V) :
    (∫ w in E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
        logPoly (harmonicRamareCofactorCoeff P)
          (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ 2) ≤
      menonHarmonicFullIntervalProductCost P A₀ B₀ Q eta W V j := by
  let L₀ : ℕ := ⌈(A₀ : ℝ) /
    ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊
  let N : ℕ := ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊
  let D : Finset ℕ := geomCofactorBlockAt A₀ B₀ Q eta j
  have hD0 : (0 : ℕ) ∉ D := by
    intro hzero
    have hz := (Finset.mem_Icc.1 (by simpa only [D, geomCofactorBlockAt] using hzero)).1
    have hL : 1 ≤ L₀ := by simpa only [L₀] using hleft
    omega
  have hDN : ∀ n ∈ D, n ≤ N := by
    intro n hn
    exact (Finset.mem_Icc.1 (by simpa only [D, L₀, N, geomCofactorBlockAt] using hn)).2
  have hDL : ∀ n ∈ D, L₀ ≤ n := by
    intro n hn
    exact (Finset.mem_Icc.1 (by simpa only [D, L₀, N, geomCofactorBlockAt] using hn)).1
  have henergy := sum_normSq_harmonicRamareCofactorCoeff_le_card_div_sq
    P D (by simpa only [L₀] using hleft) hDL
  have hmean := integral_Icc_normSq_logPoly_le_energy
    (harmonicRamareCofactorCoeff P) hD0 hDN hW
  have hcoef : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ) := by
    positivity
  have hmean' :
      (∫ w in Set.Icc (-W) W,
        ‖logPoly (harmonicRamareCofactorCoeff P) D w‖ ^ 2) ≤
        (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ)) *
          ((D.card : ℝ) * (1 / (L₀ : ℝ)) ^ 2) :=
    hmean.trans (mul_le_mul_of_nonneg_left henergy hcoef)
  have hrestricted :
      (∫ w in E, ‖logPoly (harmonicRamareCofactorCoeff P) D w‖ ^ 2) ≤
        (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ)) *
          ((D.card : ℝ) * (1 / (L₀ : ℝ)) ^ 2) := by
    refine (MeasureTheory.setIntegral_mono_set
      ((continuous_logPoly (harmonicRamareCofactorCoeff P) D).norm.pow 2).integrableOn_Icc
      (Filter.Eventually.of_forall fun w => sq_nonneg
        ‖logPoly (harmonicRamareCofactorCoeff P) D w‖)
      (Filter.Eventually.of_forall hEs)).trans hmean'
  have hproduct := setIntegral_normSq_harmonicBlockProduct_le_supMeanSquare
    (harmonicRamareCofactorCoeff P) (geomBlock P Q (1 + eta) j) D
      hEm hEs hprime hrestricted
  simpa only [menonHarmonicFullIntervalProductCost, L₀, N, D, mul_assoc] using hproduct

/-- On Menon's final shell the full-interval product cost is at most the prime threshold squared
times `600 (1 + W Q_j / x)`.  Both natural cofactor endpoints remain in the definition on the
left. -/
theorem menonFinalRangeFullIntervalProductCost_le
    {P : Finset ℕ} {x Q eta W V : ℝ} (hx : 1 ≤ x) (hQ : 0 < Q)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hW : 0 ≤ W) (j : ℕ)
    (hQjTop : Q * (1 + eta) ^ j ≤ 3 * x) :
    menonHarmonicFullIntervalProductCost P ⌈x⌉₊ (menonFinalRangeTopNat x)
        Q eta W V j ≤
      600 * V ^ 2 * (1 + W * (Q * (1 + eta) ^ j) / x) := by
  let q : ℝ := Q * (1 + eta) ^ j
  let L₀ : ℕ := ⌈(⌈x⌉₊ : ℝ) / (q * (1 + eta))⌉₊
  let N : ℕ := ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
  let D : Finset ℕ := geomCofactorBlockAt ⌈x⌉₊ (menonFinalRangeTopNat x) Q eta j
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hq0 : 0 < q := by dsimp only [q]; positivity
  have hfactor :
      (D.card : ℝ) * (1 / (L₀ : ℝ)) ^ 2 ≤ 24 * q / x := by
    have h := finalRangeCofactorReciprocalCardFactor_le
      hx hQ heta heta1 j hQjTop
    simpa only [D, L₀, q, mul_comm] using h
  have hfactor0 : 0 ≤ (D.card : ℝ) * (1 / (L₀ : ℝ)) ^ 2 := by positivity
  have hfactorUpper0 : 0 ≤ 24 * q / x := by positivity
  have htop : ((menonFinalRangeTopNat x : ℕ) : ℝ) ≤ 3 * x := by
    rw [menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have hfloor : (N : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) / q := by
    dsimp only [N]
    exact Nat.floor_le (by positivity)
  have hNq : (N : ℝ) * q / x ≤ 3 := by
    have hNq' : (N : ℝ) * q ≤ 3 * x := by
      calc
        (N : ℝ) * q ≤ ((menonFinalRangeTopNat x : ℕ) : ℝ) := by
          have hm := mul_le_mul_of_nonneg_right hfloor hq0.le
          rwa [div_mul_cancel₀ _ (ne_of_gt hq0)] at hm
        _ ≤ 3 * x := htop
    rwa [div_le_iff₀ hx0]
  have hmean :
      5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ) ≤
        10 * W + 8 * (N : ℝ) := by
    have hpi : 5 * Real.pi / 2 ≤ 10 := by nlinarith [Real.pi_lt_four]
    have hexp : 5 * Real.exp 1 / 2 ≤ 8 := by
      nlinarith [Real.exp_one_lt_three]
    exact add_le_add
      (mul_le_mul_of_nonneg_right hpi hW)
      (mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg N))
  have hmean0 : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ) := by
    positivity
  have hscale :
      (10 * W + 8 * (N : ℝ)) * (24 * q / x) ≤
        600 * (1 + W * q / x) := by
    have hWq0 : 0 ≤ W * q / x := by positivity
    have hNq0 : 0 ≤ (N : ℝ) * q / x := by positivity
    calc
      (10 * W + 8 * (N : ℝ)) * (24 * q / x) =
          240 * (W * q / x) + 192 * ((N : ℝ) * q / x) := by ring
      _ ≤ 240 * (W * q / x) + 192 * 3 := by gcongr
      _ ≤ 600 * (1 + W * q / x) := by nlinarith
  rw [menonHarmonicFullIntervalProductCost]
  calc
    V ^ 2 *
        ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ)) *
          (D.card : ℝ) * (1 / (L₀ : ℝ)) ^ 2) =
      V ^ 2 * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ)) *
        ((D.card : ℝ) * (1 / (L₀ : ℝ)) ^ 2)) := by ring
    _ ≤ V ^ 2 * ((10 * W + 8 * (N : ℝ)) * (24 * q / x)) := by
      gcongr
    _ ≤ V ^ 2 * (600 * (1 + W * q / x)) := by gcongr
    _ = 600 * V ^ 2 * (1 + W * (Q * (1 + eta) ^ j) / x) := by
      dsimp only [q]
      ring

/-- Complete ordinary all-small ladder with every cofactor paid on the full receiver interval and
the literal global support defect retained once. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_ordinary_allSmall_fullInterval_exactDefect
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta theta W : ℝ}
    (hQ : 1 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊) :
    let E := allBlocksSmall P Q eta L
      (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
    (∫ w in E,
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ 2) ≤
      2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        menonHarmonicFullIntervalProductCost P A₀ B₀ Q eta W
          (((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) /
            (Q * (1 + eta) ^ j)) j +
        2 * ∫ w in E,
          ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ 2 := by
  classical
  let E := allBlocksSmall P Q eta L
    (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
  have hEm : MeasurableSet E := by
    simpa only [E] using measurableSet_allBlocksSmall P Q eta L
      (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
  have hEs : E ⊆ Set.Icc (-W) W := by
    simpa only [E] using allBlocksSmall_subset P Q eta L
      (fun j => ((geomBlock P Q (1 + eta) j).card : ℝ) * theta) W
  have hbase := setIntegral_normSq_harmonicRamareBilinear_le_ladder_error
    (P := P) A₀ B₀ (lt_trans zero_lt_one hQ) heta hL hPprime hPrange hEm hEs
  refine hbase.trans (add_le_add ?_ le_rfl)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg L))
  exact setIntegral_normSq_harmonicProduct_geom_le_fullInterval
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    (V := ((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) /
      (Q * (1 + eta) ^ j)) hW j (hleft j hj) hEm hEs
      (fun w hw =>
        norm_harmonicPrimeBlockPoly_le_of_mem_ordinary_allBlocksSmall
          (lt_trans zero_lt_one hQ) heta hj (by simpa only [E] using hw))

end

end RHTower.Sieve
