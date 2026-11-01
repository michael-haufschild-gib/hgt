import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilReserveHasPolynomialOverlapCost
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.Conductor.PrefixDefectLocalization

/-!
# The separated prefix keeps its full prime-defect reserve

Only edges above the arithmetic cutoff pay the logarithmic tail. The ordered
Gamma split therefore retains half the prefix defect in addition to the
polynomial fraction of the whole-horizon defect.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology RHTower Zeta23
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics ArithmeticEffectivityTheory

private theorem gamma_payment_with_prefix {c δ : ℝ} (hc1 : 1 ≤ c)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hδa : δ ≤ growingMassConstant / c ^ 7)
    {L N : ℕ} (hL1 : 1 ≤ L) (hLc : 4 * c ≤ (L : ℝ))
    (hLδ : 128 * Real.exp 2 * c / δ ≤ (L : ℝ)) (hLN : L ≤ N) (x : ℕ → ℝ) :
    Real.log N * (∑ n ∈ Icc 1 N, x n ^ 2) -
        (1 - δ / 2) * poleDefect N x + (1 / 2 : ℝ) * poleDefect (N / L) x - gammaPaymentCost c δ L * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
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
  have hB : 1 ≤ B := by
    have hp : 0 ≤ 2 * c * Real.exp 1 := by positivity
    dsimp only [B]
    linarith only [hp]
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
      calc
        _ = ((growingMassConstant / c ^ 7 * Real.log N - b) * G) * S₁ := by ring
        _ ≤ _ := hh0
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
  have htail : Real.log N * S₁ ≤
      (1 + δ / 4) * (poleDefect N x - poleDefect M x) + T * S := by
    have ht := log_mul_tail_mass_le_defect_increment hM hMN x (show 0 < 4 / δ by positivity)
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
  have hprefix_coefficient : (1 / 2 : ℝ) ≤ (1 - δ) * (1 + δ / 4) := by
    have hh := mul_le_mul (show (1 / 2 : ℝ) ≤ 1 - δ by linarith only [hδ1])
      (show (1 : ℝ) ≤ 1 + δ / 4 by linarith only [hδ]) zero_le_one
      (show 0 ≤ 1 - δ by linarith only [hδ1])
    simpa only [mul_one] using hh
  have hkeep := mul_le_mul_of_nonneg_right hprefix_coefficient (poleDefect_nonneg M x)
  change Real.log N * S - (1 - δ / 2) * poleDefect N x +
    (1 / 2 : ℝ) * poleDefect M x - C * S ≤ _
  dsimp only [C]
  have hsplitLog := congrArg (fun z : ℝ => Real.log N * z) hsplit
  linarith only [hlo, hhi, hcombined, htpay, hgain, hkeep, hsplitLog]


private theorem prefix_fraction_le_half {c : ℝ} (hc : 1 ≤ c) :
    growingDefectFraction c ≤ 1 / 2 := by
  have hp : (1 : ℝ) ≤ c ^ 7 := one_le_pow₀ hc
  have hd : 0 ≤ min growingMassConstant (1 / 2) :=
    le_min growingMassConstant_pos.le (by norm_num)
  exact (div_le_self hd hp).trans (min_le_right _ _)

private theorem prefix_cutoff_bounds (c : ℝ) :
    3 ≤ growingDefectCutoff c ∧ 4 * c ≤ (growingDefectCutoff c : ℝ) ∧
      128 * Real.exp 2 * c / growingDefectFraction c ≤ (growingDefectCutoff c : ℝ) := by
  have hceil := Nat.le_ceil
    (max 3 (max (4 * c) (128 * Real.exp 2 * c / growingDefectFraction c)))
  have hcast : max 3 (max (4 * c) (128 * Real.exp 2 * c / growingDefectFraction c)) ≤
      (growingDefectCutoff c : ℝ) := by
    unfold growingDefectCutoff
    push_cast
    linarith only [hceil]
  have h3 : (3 : ℝ) ≤ growingDefectCutoff c := (le_max_left _ _).trans hcast
  exact ⟨by exact_mod_cast h3,
    (le_max_left _ _).trans ((le_max_right _ _).trans hcast),
    (le_max_right _ _).trans ((le_max_right _ _).trans hcast)⟩

/-- Half the separated-prefix defect survives all signed source payments. -/
theorem tiltedUnitSpline_complete_prefix_reserve_explicit {c : ℝ} (hc1 : 1 ≤ c)
    {N : ℕ} (hN : growingDefectCutoff c ≤ N) (x : ℕ → ℝ) :
    (1 / 2 : ℝ) * poleDefect (N / growingDefectCutoff c) x +
      growingDefectFraction c / 4 * poleDefect N x -
        growingCompleteReserveCost c * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      weilQuad (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) /
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hδ := growingDefectFraction_pos hc
  obtain ⟨hL3, hLc, hLδ⟩ := prefix_cutoff_bounds c
  have hN3 : 3 ≤ N := hL3.trans hN
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcN : c ≤ (N : ℝ) := by
    have hLN : (growingDefectCutoff c : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [hLc, hLN, hc]
  have hw : 0 < c / N := div_pos hc hNR
  have hw1 : c / N ≤ 1 := (div_le_one hNR).mpr hcN
  have hδa : growingDefectFraction c ≤ growingMassConstant / c ^ 7 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (pow_nonneg hc.le 7)
  have hgamma := gamma_payment_with_prefix hc1 hδ (prefix_fraction_le_half hc1)
    hδa (by omega : 1 ≤ growingDefectCutoff c) hLc hLδ hN x
  let g := atomDilate tiltedUnitSpline (c / N)
  let G := (c / N) * ∫ u, tiltedUnitSpline u ^ 2
  let S := ∑ n ∈ Icc 1 N, x n ^ 2
  let D := poleDefect N x
  let ε := growingDefectFraction c / 8
  have hε : 0 < ε := div_pos hδ (by norm_num)
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g := hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  have hmass : (∫ u, g u ^ 2) = G := integral_atomDilate_sq hw
  have hG : 0 < G := mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hprime := atomicWeilForm_add_full_poleDefect_le N x
  have hnr0 := abs_nonRatioForm_le_relative_defect hg.continuous hgc hsupp
    hw.le hw1 hc hε hN1 (le_rfl : c / (N : ℝ) ≤ c / N) x
  rw [hmass] at hnr0
  have hnr : nonRatioForm g N x / G ≤ ε * D + nonRatioRelativeCost c ε * S := by
    apply (div_le_iff₀ hG).mpr
    exact (le_abs_self _).trans (by simpa only [mul_comm] using hnr0)
  let P := (∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
    (∫ u, atomicTest N x g u * Real.exp (u / 2))
  have hp0 := two_mul_abs_poleMoments_le_relative_defect hg.continuous hgc hsupp
    hw hw1 hε hN3 (le_rfl : c / (N : ℝ) ≤ c / N) x
  rw [hmass] at hp0
  have hp : -(ε * D + poleRelativeCost c ε * S) ≤ 2 * P / G := by
    apply (le_div_iff₀ hG).mpr
    have hsign := neg_abs_le P
    change 2 * |P| ≤ G * (ε * D + poleRelativeCost c ε * S) at hp0
    nlinarith only [hp0, hsign]
  have hsource : (1 - 2 * ε) * D -
      ((Real.log 4 + 4) + nonRatioRelativeCost c ε + poleRelativeCost c ε) * S ≤
        overlapArithmeticEnergy g N x := by
    have heq : primeSum (atomicTest N x g) / G =
        atomicWeilForm N x + nonRatioForm g N x / G := by
      rw [primeSum_atomicTest_eq_ratio_add hg.continuous hgc hsupp hw.le, hmass]
      field_simp
    unfold overlapArithmeticEnergy overlapPrimeEnergy
    rw [hmass, heq]
    change _ ≤ Real.log N * S - (atomicWeilForm N x + nonRatioForm g N x / G) + 2 * P / G
    change atomicWeilForm N x + D ≤ (Real.log N + (Real.log 4 + 4)) * S at hprime
    linarith only [hprime, hnr, hp]
  have he := weilQuad_atomicTest_div_eq_arithmetic_add_gamma hg hsupp N x
  rw [hmass] at he
  change Real.log N * S - (1 - growingDefectFraction c / 2) * D +
    (1 / 2 : ℝ) * poleDefect (N / growingDefectCutoff c) x -
    gammaPaymentCost c (growingDefectFraction c) (growingDefectCutoff c) * S ≤
      archForm (atomicTest N x g) / G at hgamma
  change (1 / 2 : ℝ) * poleDefect (N / growingDefectCutoff c) x +
    growingDefectFraction c / 4 * D - growingCompleteReserveCost c * S ≤ _
  rw [he]
  dsimp only [growingCompleteReserveCost, ε] at hsource ⊢
  linarith only [hsource, hgamma]


/-- The complete reserve retains both the prefix defect and its global seventh-power fraction. -/
theorem exists_tiltedUnitSpline_complete_prefix_reserve_polynomial :
    ∃ a C H : ℝ, 0 < a ∧ a ≤ 1 / 8 ∧ 0 < C ∧ 0 < H ∧
      ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, H * c ^ 8 ≤ (N : ℝ) → ∀ x : ℕ → ℝ,
        (1 / 2 : ℝ) * poleDefect (N / growingDefectCutoff c) x +
          a / c ^ 7 * poleDefect N x - C * c ^ 9 * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
          weilQuad (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) /
            ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) := by
  obtain ⟨C, hC, hcost⟩ := exists_growingCompleteReserveCost_polynomial_bound
  obtain ⟨H, hH, hcut⟩ := exists_growingDefectCutoff_polynomial_bound
  let d := min growingMassConstant (1 / 2)
  have hd : 0 < d := lt_min growingMassConstant_pos (by norm_num)
  have hd8 : d / 4 ≤ (1 / 8 : ℝ) := by
    have hh : d ≤ 1 / 2 := min_le_right _ _
    linarith only [hh]
  refine ⟨d / 4, C, H, by positivity, hd8, hC, zero_lt_one.trans_le hH, ?_⟩
  intro c hc N hN x
  have hcutN : growingDefectCutoff c ≤ N := by
    exact_mod_cast (hcut c hc).trans hN
  have he := tiltedUnitSpline_complete_prefix_reserve_explicit hc hcutN x
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 :=
    sum_nonneg fun n _ => sq_nonneg (x n)
  have hpay := mul_le_mul_of_nonneg_right (hcost c hc) hS
  have hid : growingDefectFraction c / 4 = (d / 4) / c ^ 7 := by
    dsimp only [growingDefectFraction, d]
    ring
  rw [hid] at he
  linarith only [he, hpay]

/-- The same two reserves in the finite complete-Weil matrix. -/
theorem exists_completeWeilEnergy_prefix_reserve_polynomial :
    ∃ a C H : ℝ, 0 < a ∧ a ≤ 1 / 8 ∧ 0 < C ∧ 0 < H ∧
      ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, H * c ^ 8 ≤ (N : ℝ) →
        ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
          (1 / 2 : ℝ) * poleDefect (N / growingDefectCutoff c) (primeHorizonExtension x) +
            a / c ^ 7 * poleDefect N (primeHorizonExtension x) - C * c ^ 9 * ‖x‖ ^ 2 ≤
              completeWeilEnergy tiltedUnitSpline c N x := by
  obtain ⟨a, C, H, ha, ha8, hC, hH, hres⟩ := exists_tiltedUnitSpline_complete_prefix_reserve_polynomial
  refine ⟨a, C, H, ha, ha8, hC, hH, ?_⟩
  intro c hc N hN x
  have hc0 := zero_lt_one.trans_le hc
  have hNR : (0 : ℝ) < N := (mul_pos hH (pow_pos hc0 8)).trans_le hN
  have hN1 : 1 ≤ N := by exact_mod_cast (show 0 < N by exact_mod_cast hNR)
  have hw : 0 < c / N := div_pos hc0 hNR
  have hr := hres c hc N hN (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq] at hr
  have hid : completeWeilEnergy tiltedUnitSpline c N x =
      weilQuad (atomicTest N (primeHorizonExtension x) (atomDilate tiltedUnitSpline (c / N))) /
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) := by
    rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero hc0 hN1, integral_atomDilate_sq hw]
  rwa [← hid] at hr

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tiltedUnitSpline_complete_prefix_reserve_explicit
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_complete_prefix_reserve_polynomial

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeilEnergy_prefix_reserve_polynomial
