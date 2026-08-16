import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinFullXiPacket

/-!
# Route T: full exact-multiplicity Xi Mellin sum

This module closes the finite/infinite zero-series weld for the buffered Route-T kernel. It groups
bounded-height Xi zero copies by their underlying divisor support, identifies copied Xi multiplicity
with the analytic multiplicity used by the density packet, and controls the high-real packet by the
physical Ingham zero-density mass. The low-real packet and shifted high-ordinate tail are supplied by
`InghamUniformDetectorMellinFullXiPacket`.

Consequently, the complete exact-multiplicity Xi zero sum of the buffered normalized adjacent-window
Mellin kernel is absolutely summable for every `X ≥ 3` and tends to zero as `X → ∞`.
-/

open Complex Filter Metric Set Finset Topology

namespace RHTower.Sieve

noncomputable section

def inghamRouteTXiHighRealPacket (X : ℕ) : Finset RHTower.XiZeroCopy :=
  (inghamRouteTXiLowOrdinatePacket X).filter fun q =>
    7 / 10 ≤ ((q.1 : RHTower.XiDivisorSupport) : ℂ).re

private theorem inghamRouteTXiHighRealPacket_underlying_mem
    {X : ℕ} (hX : 4 ≤ X) {q : RHTower.XiZeroCopy}
    (hq : q ∈ inghamRouteTXiHighRealPacket X) :
    ((q.1 : RHTower.XiDivisorSupport) : ℂ) ∈ inghamRouteTHighZeroPacket X := by
  have hfilter := Finset.mem_filter.mp hq
  have hrect := RHTower.mem_xiZeroCopyClosedRectangle.mp hfilter.1
  have hcoords := Complex.mem_reProdIm.mp hrect
  have horder : (2 : ℝ) - X ≤ (X : ℝ) - 2 := by
    have hXR : (4 : ℝ) ≤ X := by exact_mod_cast hX
    linarith
  have hrecoords : (RHTower.xiSpectralPoint q).re ∈
      Set.Icc ((2 : ℝ) - X) ((X : ℝ) - 2) := by
    simpa [inghamRouteTXiLowOrdinatePacket, uIcc_of_le horder] using hcoords.1
  have hspectralRe : (RHTower.xiSpectralPoint q).re =
      ((q.1 : RHTower.XiDivisorSupport) : ℂ).im := by
    simp [RHTower.xiSpectralPoint, Complex.mul_re]
  have him : ((q.1 : RHTower.XiDivisorSupport) : ℂ).im ∈
      Set.Icc (2 - (X : ℝ)) ((X : ℝ) - 2) := by
    rw [← hspectralRe]
    exact hrecoords
  have hstrip := RHTower.xi_divisor_support_re_mem_open_unit q.1
  have hxi := RHTower.xi_eq_zero_of_mem_divisor_support q.1
  have hzeta := (RHTower.xi_zero_iff_zeta_zero_of_mem_strip hstrip.1 hstrip.2).mp hxi
  have hresidue : zetaResidueUnit (q.1 : ℂ) = 0 := by
    have hne : (q.1 : ℂ) ≠ 1 := riemannZeta_zero_ne_one hzeta
    rw [zetaResidueUnit, Function.update_of_ne hne, hzeta, mul_zero]
  have hcenter : inghamUniformGabrielCenter (7 / 10 : ℝ) ≤ 7 / 10 :=
    inghamUniformGabrielCenter_le_self (by norm_num)
  have hcenterFour : inghamUniformGabrielCenter (7 / 10 : ℝ) ≤ 4 := by
    linarith
  have hre : ((q.1 : RHTower.XiDivisorSupport) : ℂ).re ∈
      Set.Icc (inghamUniformGabrielCenter (7 / 10 : ℝ)) 4 :=
    ⟨hcenter.trans hfilter.2, by linarith [hstrip.2]⟩
  rw [inghamRouteTHighZeroPacket, Finset.mem_filter]
  refine ⟨mem_zetaResidueUnitClosedRectangleZeros.mpr ⟨?_, hresidue⟩, hfilter.2⟩
  apply Complex.mem_reProdIm.mpr
  constructor
  · simpa [inghamRouteTCommonZeroPacket, uIcc_of_le hcenterFour] using hre
  · simpa [inghamRouteTCommonZeroPacket, uIcc_of_le horder] using him

private theorem inghamRouteTXiHighRealPacket_fst_eq_mem
    {X : ℕ} {q r : RHTower.XiZeroCopy} (hqr : q.1 = r.1) :
    q ∈ inghamRouteTXiHighRealPacket X ↔ r ∈ inghamRouteTXiHighRealPacket X := by
  have hspectral : RHTower.xiSpectralPoint q = RHTower.xiSpectralPoint r := by
    simp only [RHTower.xiSpectralPoint, hqr]
  simp only [inghamRouteTXiHighRealPacket, Finset.mem_filter, inghamRouteTXiLowOrdinatePacket,
    RHTower.mem_xiZeroCopyClosedRectangle, hspectral, hqr]

theorem inghamRouteTXiHighRealCopiedWeight_le_highMass {X : ℕ} (hX : 4 ≤ X) :
    (∑ q ∈ inghamRouteTXiHighRealPacket X,
      (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent *
        (((q.1 : RHTower.XiDivisorSupport) : ℂ).re - 1))) ≤
      inghamRouteTHighZeroWeightedMass X := by
  classical
  let S : Finset RHTower.XiZeroCopy := inghamRouteTXiHighRealPacket X
  let B : Finset RHTower.XiDivisorSupport := S.image Sigma.fst
  let Q : Finset RHTower.XiZeroCopy := B.biUnion RHTower.xiZeroCopyFiber
  let e : RHTower.XiDivisorSupport ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  let BC : Finset ℂ := B.map e
  let f : RHTower.XiZeroCopy → ℝ := fun q =>
    (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent *
      (((q.1 : RHTower.XiDivisorSupport) : ℂ).re - 1))
  let g : ℂ → ℝ := fun w =>
    (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * (w.re - 1)) *
      inghamRouteTZeroMultiplicity w
  have hdisj : (B : Set RHTower.XiDivisorSupport).PairwiseDisjoint
      RHTower.xiZeroCopyFiber := by
    intro rho hrho tau htau hne
    change Disjoint (RHTower.xiZeroCopyFiber rho) (RHTower.xiZeroCopyFiber tau)
    rw [Finset.disjoint_left]
    intro q hqrho hqtau
    have hr := RHTower.mem_xiZeroCopyFiber.mp hqrho
    have ht := RHTower.mem_xiZeroCopyFiber.mp hqtau
    exact hne (hr.symm.trans ht)
  have hSQ : S = Q := by
    ext q
    constructor
    · intro hq
      rw [show Q = B.biUnion RHTower.xiZeroCopyFiber from rfl,
        Finset.mem_biUnion]
      refine ⟨q.1, ?_, RHTower.mem_xiZeroCopyFiber.mpr rfl⟩
      rw [show B = S.image Sigma.fst from rfl, Finset.mem_image]
      exact ⟨q, hq, rfl⟩
    · intro hq
      rw [show Q = B.biUnion RHTower.xiZeroCopyFiber from rfl,
        Finset.mem_biUnion] at hq
      obtain ⟨rho, hrhoB, hqrho⟩ := hq
      rw [show B = S.image Sigma.fst from rfl, Finset.mem_image] at hrhoB
      obtain ⟨r, hrS, hreq⟩ := hrhoB
      have hfst : q.1 = r.1 := (RHTower.mem_xiZeroCopyFiber.mp hqrho).trans hreq.symm
      exact (inghamRouteTXiHighRealPacket_fst_eq_mem hfst).2 hrS
  have hfiber (rho : RHTower.XiDivisorSupport) (hrho : rho ∈ B) :
      ∑ q ∈ RHTower.xiZeroCopyFiber rho, f q =
        ((RHTower.xiZeroCopyFiber rho).card : ℝ) *
          (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * ((rho : ℂ).re - 1)) := by
    calc
      ∑ q ∈ RHTower.xiZeroCopyFiber rho, f q =
          ∑ _q ∈ RHTower.xiZeroCopyFiber rho,
            (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * ((rho : ℂ).re - 1)) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hfst := RHTower.mem_xiZeroCopyFiber.mp hq
        simp only [f, hfst]
      _ = ((RHTower.xiZeroCopyFiber rho).card : ℝ) *
          (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * ((rho : ℂ).re - 1)) := by
        simp [nsmul_eq_mul]
  have hstripB (rho : RHTower.XiDivisorSupport) (hrho : rho ∈ B) :
      0 < (rho : ℂ).re ∧ (rho : ℂ).re < 1 := by
    rw [show B = S.image Sigma.fst from rfl, Finset.mem_image] at hrho
    obtain ⟨q, hqS, hqeq⟩ := hrho
    have hmem := inghamRouteTXiHighRealPacket_underlying_mem hX (show q ∈ inghamRouteTXiHighRealPacket X from hqS)
    rw [← hqeq]
    have hs := mem_inghamRouteTCommonZeroPacket_strip
      (Finset.mem_filter.mp hmem).1
    exact ⟨hs.1, hs.2.1⟩
  have hmult (rho : RHTower.XiDivisorSupport) (hrho : rho ∈ B) :
      ((RHTower.xiZeroCopyFiber rho).card : ℝ) =
        inghamRouteTZeroMultiplicity (rho : ℂ) := by
    have horder := analyticOrderAt_zetaResidueUnit_eq_xi_of_mem_strip (hstripB rho hrho)
    unfold inghamRouteTZeroMultiplicity
    rw [horder]
    congr 1
    rw [RHTower.card_xiZeroCopyFiber,
      MeromorphicOn.AnalyticOnNhd.divisor_apply RHTower.xi_analyticOnNhd_univ
        (Set.mem_univ _)]
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (RHTower.xi_order_ne_top (rho : ℂ))
    rw [← hm]
    simp
  have hBCsub : BC ⊆ inghamRouteTHighZeroPacket X := by
    intro w hw
    rw [show BC = B.map e from rfl, Finset.mem_map] at hw
    obtain ⟨rho, hrhoB, rfl⟩ := hw
    rw [show B = S.image Sigma.fst from rfl, Finset.mem_image] at hrhoB
    obtain ⟨q, hqS, hqeq⟩ := hrhoB
    rw [← hqeq]
    exact inghamRouteTXiHighRealPacket_underlying_mem hX hqS
  have hsum : ∑ q ∈ S, f q = ∑ w ∈ BC, g w := by
    rw [hSQ, show Q = B.biUnion RHTower.xiZeroCopyFiber from rfl,
      Finset.sum_biUnion hdisj]
    calc
      ∑ rho ∈ B, ∑ q ∈ RHTower.xiZeroCopyFiber rho, f q =
          ∑ rho ∈ B,
            ((RHTower.xiZeroCopyFiber rho).card : ℝ) *
              (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent * ((rho : ℂ).re - 1)) := by
        apply Finset.sum_congr rfl
        intro rho hrho
        exact hfiber rho hrho
      _ = ∑ rho ∈ B, g (rho : ℂ) := by
        apply Finset.sum_congr rfl
        intro rho hrho
        dsimp only [g]
        rw [hmult rho hrho]
        ring
      _ = ∑ w ∈ BC, g w := by
        rw [show BC = B.map e from rfl, Finset.sum_map]
        rfl
  have hsubsum : (∑ w ∈ BC, g w) ≤
      ∑ w ∈ inghamRouteTHighZeroPacket X, g w :=
    Finset.sum_le_sum_of_subset_of_nonneg hBCsub (fun w _ _ => by
      dsimp only [g]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (inghamRouteTZeroMultiplicity_nonneg w))
  change (∑ q ∈ S, f q) ≤ inghamRouteTHighZeroWeightedMass X
  rw [hsum]
  exact hsubsum

def inghamRouteTBufferedXiMellinHighRealPacket (X : ℕ) : ℂ :=
  ∑ q ∈ inghamRouteTXiHighRealPacket X,
    routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)

theorem norm_inghamRouteTBufferedXiMellinHighRealPacket_le
    {X : ℕ} (hX : 4 ≤ X) :
    ‖inghamRouteTBufferedXiMellinHighRealPacket X‖ ≤
      inghamRouteTHighZeroWeightedMass X := by
  have hX1 : 1 ≤ X := by omega
  have hNpos := inghamRouteTMellinPhysicalCenter_pos hX1
  have hHpos := inghamRouteTMellinBufferedPhysicalWidth_pos hX1
  unfold inghamRouteTBufferedXiMellinHighRealPacket
  calc
    ‖∑ q ∈ inghamRouteTXiHighRealPacket X,
        routeTNormalizedSmoothWindowMellin
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)‖ ≤
      ∑ q ∈ inghamRouteTXiHighRealPacket X,
        ‖routeTNormalizedSmoothWindowMellin
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ inghamRouteTXiHighRealPacket X,
        (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent *
          (((q.1 : RHTower.XiDivisorSupport) : ℂ).re - 1)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hstrip := RHTower.xi_divisor_support_re_mem_open_unit q.1
      have hkernel := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
        hNpos hHpos hstrip.2.le
      exact hkernel.trans_eq
        (inghamRouteTMellinPhysicalCenter_rpow_sub_one hX1
          (((q.1 : RHTower.XiDivisorSupport) : ℂ).re))
    _ ≤ inghamRouteTHighZeroWeightedMass X :=
      inghamRouteTXiHighRealCopiedWeight_le_highMass hX

theorem tendsto_norm_inghamRouteTBufferedXiMellinHighRealPacket_zero :
    Tendsto (fun X : ℕ => ‖inghamRouteTBufferedXiMellinHighRealPacket X‖)
      atTop (𝓝 0) := by
  refine squeeze_zero' (by filter_upwards with X; exact norm_nonneg _) ?_
    tendsto_inghamRouteTHighZeroWeightedMass_zero
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with X hX
  exact norm_inghamRouteTBufferedXiMellinHighRealPacket_le hX

def inghamRouteTBufferedXiMellinLowOrdinatePacket (X : ℕ) : ℂ :=
  ∑ q ∈ inghamRouteTXiLowOrdinatePacket X,
    routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)

theorem inghamRouteTBufferedXiMellinLowOrdinatePacket_eq_low_add_high (X : ℕ) :
    inghamRouteTBufferedXiMellinLowOrdinatePacket X =
      inghamRouteTBufferedXiMellinLowRealPacket X +
        inghamRouteTBufferedXiMellinHighRealPacket X := by
  classical
  rw [inghamRouteTBufferedXiMellinLowOrdinatePacket,
    inghamRouteTBufferedXiMellinLowRealPacket,
    inghamRouteTBufferedXiMellinHighRealPacket,
    inghamRouteTXiLowRealPacket, inghamRouteTXiHighRealPacket]
  simpa only [not_lt] using (Finset.sum_filter_add_sum_filter_not
    (inghamRouteTXiLowOrdinatePacket X)
    (fun q : RHTower.XiZeroCopy =>
      ((q.1 : RHTower.XiDivisorSupport) : ℂ).re < 7 / 10)
    (fun q => routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ))).symm

theorem tendsto_inghamRouteTBufferedXiMellinLowOrdinatePacket_zero :
    Tendsto inghamRouteTBufferedXiMellinLowOrdinatePacket atTop (𝓝 0) := by
  have hlo : Tendsto inghamRouteTBufferedXiMellinLowRealPacket atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      tendsto_norm_inghamRouteTBufferedXiMellinLowRealPacket_zero
  have hhi : Tendsto inghamRouteTBufferedXiMellinHighRealPacket atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      tendsto_norm_inghamRouteTBufferedXiMellinHighRealPacket_zero
  apply (tendsto_congr' (Filter.Eventually.of_forall fun X =>
    inghamRouteTBufferedXiMellinLowOrdinatePacket_eq_low_add_high X)).mpr
  simpa using hlo.add hhi

theorem summable_routeTBufferedXiMellin {X : ℕ} (hX : 3 ≤ X) :
    Summable (fun q : RHTower.XiZeroCopy =>
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)) := by
  obtain ⟨D, hD, hfrequency⟩ :=
    exists_routeTBufferedMellin_natOrder_frequency_bound 1
  let A : ℝ := D * inghamRouteTMellinBufferedFrequency X ^ 2
  let B : RHTower.XiZeroCopy → ℝ := fun q =>
    1 / |((q.1 : RHTower.XiDivisorSupport) : ℂ).im| ^ 2
  have hB : Summable B := summable_xiZeroCopy_one_div_abs_im_sq
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg hD (sq_nonneg _)
  have hmajor : Summable (fun q : RHTower.XiZeroCopy => A * B q) :=
    hB.mul_left A
  apply Summable.of_norm_bounded hmajor
  intro q
  let rho : ℂ := (q.1 : RHTower.XiDivisorSupport)
  let gamma : ℝ := |rho.im|
  have hstrip := RHTower.xi_divisor_support_re_mem_open_unit q.1
  obtain ⟨eta, heta, hheight⟩ := RHTower.exists_xiZeroCopy_abs_im_lower_bound
  have hgamma : 0 < gamma := by
    exact heta.trans_le (by simpa only [rho, gamma] using hheight q)
  have hweighted := hfrequency (X := X) (w := rho) hX hstrip.1 hstrip.2.le
  norm_num at hweighted
  have hkernel :
      ‖routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) rho‖ ≤ A / gamma ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hgamma)).2
    simpa only [A, gamma, sq_abs, mul_comm] using hweighted
  exact hkernel.trans_eq (by simp only [A, B, rho, gamma]; ring)

def inghamRouteTBufferedXiMellinFullZeroSum (X : ℕ) : ℂ :=
  ∑' q : RHTower.XiZeroCopy,
    routeTNormalizedSmoothWindowMellin
      (inghamRouteTMellinPhysicalCenter X)
      (inghamRouteTMellinBufferedPhysicalWidth X) (q.1 : ℂ)

theorem inghamRouteTBufferedXiMellinFullZeroSum_eq_packet_add_tail
    {X : ℕ} (hX : 4 ≤ X) :
    inghamRouteTBufferedXiMellinFullZeroSum X =
      inghamRouteTBufferedXiMellinLowOrdinatePacket X +
        inghamRouteTBufferedXiMellinShiftedHighTail X := by
  have hsum := summable_routeTBufferedXiMellin (X := X) (by omega)
  have hsplit := hsum.sum_add_tsum_compl (s := inghamRouteTXiLowOrdinatePacket X)
  simpa only [inghamRouteTBufferedXiMellinFullZeroSum,
    inghamRouteTBufferedXiMellinLowOrdinatePacket,
    inghamRouteTBufferedXiMellinShiftedHighTail] using hsplit.symm

theorem tendsto_inghamRouteTBufferedXiMellinFullZeroSum_zero :
    Tendsto inghamRouteTBufferedXiMellinFullZeroSum atTop (𝓝 0) := by
  have htail : Tendsto inghamRouteTBufferedXiMellinShiftedHighTail atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      tendsto_norm_inghamRouteTBufferedXiMellinShiftedHighTail_zero
  have hadd := tendsto_inghamRouteTBufferedXiMellinLowOrdinatePacket_zero.add htail
  apply (tendsto_congr' (show ∀ᶠ X : ℕ in atTop,
      inghamRouteTBufferedXiMellinFullZeroSum X =
        inghamRouteTBufferedXiMellinLowOrdinatePacket X +
          inghamRouteTBufferedXiMellinShiftedHighTail X by
    filter_upwards [eventually_ge_atTop (4 : ℕ)] with X hX
    exact inghamRouteTBufferedXiMellinFullZeroSum_eq_packet_add_tail hX)).mpr
  simpa using hadd

end

end RHTower.Sieve
