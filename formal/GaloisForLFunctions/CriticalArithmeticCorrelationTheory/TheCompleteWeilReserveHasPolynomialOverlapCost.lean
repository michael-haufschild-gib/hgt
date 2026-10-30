import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BoundedOverlapKeepsACompleteWeilReserve
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheGammaReserveSurvivesGrowingOverlap

/-!
# An effective complete defect reserve at growing overlap

The exact ratio-prime identity retains the full prime defect at a fixed mass
cost. A polynomial Fourier reserve and an ordered prefix-tail split then
control the complete signed form with an explicit cutoff and overlap cost.
-/

noncomputable section
open MeasureTheory Finset Filter Topology RHTower Zeta23
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics ArithmeticEffectivityTheory

/-- The exact prime defect needs only a fixed, horizon-independent counterterm. -/
theorem atomicWeilForm_add_full_poleDefect_le (N : ℕ) (x : ℕ → ℝ) :
    atomicWeilForm N x + poleDefect N x ≤
      (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  rw [atomicWeilForm_add_poleDefect, mul_sum]
  exact sum_le_sum fun n hn => mul_le_mul_of_nonneg_right
    (row_le (mem_Icc.mp hn).1 (mem_Icc.mp hn).2) (sq_nonneg _)

/-- Mass cost of joining separated prefix energy to a Fourier reserve. -/
def gammaPaymentCost (c δ : ℝ) (L : ℕ) : ℝ :=
  |Real.log c| + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost +
    growingReserveCost * c + 2 * Real.pi * (1 + 2 * c * Real.exp 1) +
    (1 - δ) * ((1 + 4 / δ) *
      (Real.log (2 * (L : ℝ)) + ((Real.log 4 + 4) + (Real.log 8 + 4))) +
        Real.log (2 * (L : ℝ)))

private theorem gamma_payment_explicit {c δ : ℝ} (hc1 : 1 ≤ c)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hδa : δ ≤ growingMassConstant / c ^ 7)
    {L N : ℕ} (hL1 : 1 ≤ L) (hLc : 4 * c ≤ (L : ℝ))
    (hLδ : 128 * Real.exp 2 * c / δ ≤ (L : ℝ)) (hLN : L ≤ N) (x : ℕ → ℝ) :
    Real.log N * (∑ n ∈ Icc 1 N, x n ^ 2) -
        (1 - δ / 2) * poleDefect N x - gammaPaymentCost c δ L * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      archForm (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) /
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL1
  have hL1R : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hcN : c ≤ (N : ℝ) := by
    have hLN' : (L : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [hLc, hLN', hc]
  let A := separatedCrossMassCost
  let B := 1 + 2 * c * Real.exp 1
  let C₀ := |Real.log c| + 2 * |gammaHardyPhaseRate 0| + 2 * c * A
  let b := growingReserveCost * c
  let R := Real.log (2 * (L : ℝ))
  let J := (Real.log 4 + 4) + (Real.log 8 + 4)
  let T := (1 + 4 / δ) * (R + J) + R
  let C := C₀ + b + 2 * Real.pi * B + (1 - δ) * T
  have hA : 0 ≤ A := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    dsimp only [A, separatedCrossMassCost]
    positivity
  have hB : 1 ≤ B := by dsimp only [B]; positivity
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hb : 0 ≤ b := mul_nonneg growingReserveCost_nonneg hc.le
  have hR : 0 ≤ R := Real.log_nonneg (by linarith only [hL1R])
  have hJ : 0 ≤ J := by
    have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    have h8 := Real.log_nonneg (show (1 : ℝ) ≤ 8 by norm_num)
    dsimp only [J]
    linarith only [h4, h8]
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hδle : 0 ≤ 1 - δ := by linarith only [hδ1]
  let M := N / L
  let w := c / (N : ℝ)
  let g := atomDilate tiltedUnitSpline w
  let y := atomicTailCoefficients M x
  let S := ∑ n ∈ Icc 1 N, x n ^ 2
  let S₀ := ∑ n ∈ Icc 1 M, x n ^ 2
  let S₁ := ∑ n ∈ Icc 1 N, y n ^ 2
  let G := w * ∫ u, tiltedUnitSpline u ^ 2
  have hM : 1 ≤ M := Nat.div_pos hLN (by omega)
  have hMN : M ≤ N := Nat.div_le_self N L
  have hN : 1 ≤ N := hL1.trans hLN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hML : (M : ℝ) * L ≤ N := by exact_mod_cast Nat.div_mul_le_self N L
  have hNML : (N : ℝ) < (M + 1) * L := by
    have ht := Nat.lt_mul_div_succ N (show 0 < L by omega)
    have ht' : N < (M + 1) * L := by simpa only [M, Nat.mul_comm] using ht
    exact_mod_cast ht'
  have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNRM : (N : ℝ) ≤ 2 * L * M := by
    nlinarith only [hNML, mul_nonneg (sub_nonneg.mpr hM1R) hLR.le]
  have hw : 0 < w := div_pos hc hNR
  have hwN : w * N = c := by dsimp only [w]; field_simp [hNR.ne']
  have hwM : w * M ≤ c / L := by
    apply (le_div_iff₀ hLR).mpr
    calc
      _ = w * ((M : ℝ) * L) := by ring
      _ ≤ w * N := mul_le_mul_of_nonneg_left hML hw.le
      _ = c := hwN
  have hwMc : w * M ≤ c := by
    calc
      _ ≤ w * N := mul_le_mul_of_nonneg_left (by exact_mod_cast hMN) hw.le
      _ = c := hwN
  have hw1 : w ≤ 1 := by
    apply (div_le_one hNR).mpr
    have hLNR : (L : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [hLc, hLNR, hc]
  have hsep : w ≤ atomSpacing M / 2 := by
    have hfour : 4 * w * M ≤ 1 := by
      have hl : 4 * (c / (L : ℝ)) ≤ 1 := by
        rw [← mul_div_assoc, div_le_one hLR]
        exact hLc
      nlinarith only [hwM, hl]
    have hbound : w ≤ (1 / ((M : ℝ) + 1)) / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < M + 1)).mpr
      nlinarith only [hfour, mul_nonneg hw.le (sub_nonneg.mpr hM1R)]
    exact hbound.trans (div_le_div_of_nonneg_right (atomSpacing_bounds hM).1 (by norm_num))
  have hsmall : 32 * Real.exp 2 * w * M ≤ δ / 4 := by
    have hcost : 32 * Real.exp 2 * (c / (L : ℝ)) ≤ δ / 4 := by
      have hl := (div_le_iff₀ hδ).mp hLδ
      have hd : (128 * Real.exp 2 * c) / (L : ℝ) ≤ δ :=
        (div_le_iff₀ hLR).mpr (by nlinarith only [hl])
      have he : (128 * Real.exp 2 * c) / (L : ℝ) = 4 * (32 * Real.exp 2 * (c / L)) := by ring
      rw [he] at hd
      linarith only [hd]
    calc
      _ = (32 * Real.exp 2) * (w * M) := by ring
      _ ≤ (32 * Real.exp 2) * (c / (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hwM (by positivity)
      _ ≤ _ := hcost
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hratio : Real.log N - Real.log M ≤ R := by
    rw [← Real.log_div hNR.ne' hMR.ne']
    exact Real.log_le_log (div_pos hNR hMR) ((div_le_iff₀ hMR).mpr hNRM)
  have hS : 0 ≤ S := sum_nonneg fun n _ => sq_nonneg _
  have hS₀ : 0 ≤ S₀ := sum_nonneg fun n _ => sq_nonneg _
  have hS₁ : 0 ≤ S₁ := sum_nonneg fun n _ => sq_nonneg _
  have hsplit : S₀ + S₁ = S := sum_sq_prefix_add_tail hMN x
  have hS₀S : S₀ ≤ S := by linarith only [hsplit, hS₁]
  have hS₁S : S₁ ≤ S := by linarith only [hsplit, hS₀]
  have hG : 0 < G := mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g := hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  have hmass : (∫ u, g u ^ 2) = G := integral_atomDilate_sq hw
  have hD : 0 ≤ poleDefect N x := poleDefect_nonneg N x
  have hDM : poleDefect M x ≤ poleDefect N x := poleDefect_prefix_le hMN x
  have hlogw : Real.log (1 / w) = Real.log N - Real.log c := by
    dsimp only [w]
    rw [one_div_div, Real.log_div hNR.ne' hc.ne']
  -- Keep the unit self-energy coefficient on the separated prefix.
  have hlo : Real.log N * S₀ - C₀ * S - δ / 4 * poleDefect N x ≤
      archForm (atomicTest M x g) / G := by
    have hraw := archForm_atomicTest_ge_separated_defect hg hgc hsupp hM hw hw1 hsep x
    rw [hmass] at hraw
    have hcoef : Real.log N - C₀ ≤
        2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - 2 * w * M * separatedCrossMassCost := by
      have habs : Real.log c - 2 * gammaHardyPhaseRate 0 ≤ |Real.log c| + 2 * |gammaHardyPhaseRate 0| := by
        linarith only [le_abs_self (Real.log c), neg_le_abs (gammaHardyPhaseRate 0)]
      have hcost := mul_le_mul_of_nonneg_right hwMc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)
      rw [hlogw]
      dsimp only [C₀, A]
      dsimp only [A] at hcost
      linarith only [habs, hcost]
    have hpay : 32 * Real.exp 2 * w * M * poleDefect M x ≤ δ / 4 * poleDefect N x :=
      mul_le_mul hsmall hDM (poleDefect_nonneg M x) (by positivity)
    have hleft := mul_le_mul_of_nonneg_right hcoef hS₀
    have hmassCost := mul_le_mul_of_nonneg_left hS₀S hC₀
    have hl : Real.log N * S₀ - C₀ * S - δ / 4 * poleDefect N x ≤
        (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - 2 * w * M * separatedCrossMassCost) *
          S₀ - 32 * Real.exp 2 * w * M * poleDefect M x := by
      linarith only [hleft, hpay, hmassCost]
    apply (le_div_iff₀ hG).mpr
    have hlG := mul_le_mul_of_nonneg_left hl hG.le
    simpa only [mul_comm G] using hlG.trans hraw
  -- The explicit Fourier floor supplies a positive logarithmic reserve on the tail.
  have hhi : δ * Real.log N * S₁ - b * S ≤ archForm (atomicTest N y g) / G := by
    have hh0 := archForm_atomicTest_ge_growing hc1 hcN y
    have hh : (growingMassConstant / c ^ 7 * Real.log N - b) * S₁ ≤
        archForm (atomicTest N y g) / G := by
      apply (le_div_iff₀ hG).mpr
      convert hh0 using 1 <;> ring
    have ha := mul_le_mul_of_nonneg_right hδa (mul_nonneg hlog hS₁)
    have hbS := mul_le_mul_of_nonneg_left hS₁S hb
    change ((growingMassConstant / c ^ 7) * Real.log N - b) * S₁ ≤ archForm (atomicTest N y g) / G at hh
    linarith only [hh, ha, hbS]
  have hordered := atomicTest_prefix_tail_ordered hsupp hM
    (by have hp := atomSpacing_pos hM; linarith only [hsep, hp]) N x
  obtain ⟨boundary, hleft, hright⟩ := hordered
  have hcross := archForm_add_ge_of_ordered
    (contDiff_atomicTest hg M x) (hasCompactSupport_atomicTest hsupp M x)
    (contDiff_atomicTest hg N y) (hasCompactSupport_atomicTest hsupp N y) hleft hright
  rw [← atomicTest_eq_prefix_add_tail hMN x g] at hcross
  have hloMass : (∫ u, atomicTest M x g u ^ 2) = S₀ * G := by
    rw [integral_atomicTest_sq hg hgc hsupp
      (by have hp := atomSpacing_pos hM; linarith only [hsep, hp]), hmass]
  have hhiMass : (∫ u, atomicTest N y g u ^ 2) ≤ G * B * S₁ := by
    have h := integral_atomicTest_sq_le_of_le_horizon hg.continuous hgc hc hcN hsupp y
    rw [hmass] at h
    simpa only [B, mul_assoc, mul_left_comm, mul_comm] using h
  have hphysical : (∫ u, atomicTest M x g u ^ 2) + (∫ u, atomicTest N y g u ^ 2) ≤ G * B * S := by
    have hlow := mul_le_mul_of_nonneg_right hB (mul_nonneg hG.le hS₀)
    have hsplitMass := congrArg (fun z : ℝ => G * B * z) hsplit
    rw [hloMass]
    linarith only [hhiMass, hlow, hsplitMass]
  have hcombined : archForm (atomicTest M x g) / G + archForm (atomicTest N y g) / G -
      2 * Real.pi * B * S ≤ archForm (atomicTest N x g) / G := by
    apply (le_div_iff₀ hG).mpr
    have he : (archForm (atomicTest M x g) / G + archForm (atomicTest N y g) / G -
        2 * Real.pi * B * S) * G = archForm (atomicTest M x g) + archForm (atomicTest N y g) -
          2 * Real.pi * (G * B * S) := by field_simp [hG.ne']
    rw [he]
    have hpaid := mul_le_mul_of_nonneg_left hphysical (by positivity : 0 ≤ 2 * Real.pi)
    linarith only [hcross, hpaid]
  -- Pay the tail logarithm at near-unit defect cost before combining the source bounds.
  have htail : Real.log N * S₁ ≤ (1 + δ / 4) * poleDefect N x + T * S := by
    have ht := log_mul_tail_mass_le_defect hM hMN x (show 0 < 4 / δ by positivity)
    have he : 1 / (4 / δ) = δ / 4 := by field_simp [hδ.ne']
    rw [he] at ht
    have hcut : cutoffPrimeCost M N ≤ R + J := by
      unfold cutoffPrimeCost
      dsimp only [J]
      linarith only [hratio]
    have hcoeff : (1 + 4 / δ) * cutoffPrimeCost M N + Real.log N - Real.log M ≤ T := by
      have hc' := mul_le_mul_of_nonneg_left hcut (by positivity : 0 ≤ 1 + 4 / δ)
      dsimp only [T]
      linarith only [hc', hratio]
    have hm := mul_le_mul_of_nonneg_right hcoeff hS
    change Real.log N * S₁ ≤ _ at ht
    linarith only [ht, hm]
  have htpay := mul_le_mul_of_nonneg_left htail hδle
  have hgain : (δ / 4 + (1 - δ) * (1 + δ / 4)) * poleDefect N x ≤
      (1 - δ / 2) * poleDefect N x := by
    nlinarith only [mul_nonneg (sq_nonneg δ) hD]
  change Real.log N * S - (1 - δ / 2) * poleDefect N x - C * S ≤ _
  dsimp only [C]
  have hsplitLog := congrArg (fun z : ℝ => Real.log N * z) hsplit
  linarith only [hlo, hhi, hcombined, htpay, hgain, hsplitLog]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
