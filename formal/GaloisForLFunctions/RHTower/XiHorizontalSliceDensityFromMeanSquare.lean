import GaloisForLFunctions.RHTower.XiHorizontalSliceConeCriterion
import GaloisForLFunctions.RHTower.ZetaOffLineFirstMomentMollified
import GaloisForLFunctions.RHTower.XiLogDerivZeroFreePositive

/-!
# Slice positivity on most heights, from a mollified mean square

By the per-zero cone criterion (`xiSliceCoeff_nonneg_of_cone`), slice positivity can fail at height `t`
only if some zero `ρ` lies in the cone `|Im ρ − t| < |Re ρ − ½|`.  Replacing a left zero by its
reflection `1 − ρ̄`, which has the same ordinate, the failure heights in `[T₁ + ½, T₂ − ½]` are
covered by the intervals `(Im w − (Re w − ½), Im w + (Re w − ½))` over the zeros `w` of `ζ` with
`Re w > ½` in the rectangle `[½, 15/2] × [T₁, T₂]`.  Their total length is at most twice the
first horizontal moment `Σ m_w (Re w − ½)`.  The corpus bounds that moment by the mean square of
`ζ·Ψ` on the critical line (`exists_zetaOffLineFirstMoment_le_of_line_meanSquare`), so

  `|{t ∈ [T₁+½, T₂−½] : some slice coefficient at t is not ≥ 0}|
      ≤ (1/π) ((T₂−T₁)/2 · log(Msq/(T₂−T₁)) + C + K (log T₂ + log Mb))`.

With a mollified mean square `Msq ≤ c(T₂−T₁)`, the failure set has measure at most
`(log c/2π)(T₂−T₁) + O(log T₂)`.  The mean square enters as an explicit hypothesis.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped ComplexOrder Interval

namespace RHTower

noncomputable section

/-- `ζ` has finite analytic order at every point other than `1`. -/
theorem analyticOrderAt_riemannZeta_ne_top_of_ne_one {w : ℂ} (hw : w ≠ 1) :
    analyticOrderAt riemannZeta w ≠ ⊤ := by
  intro htop
  have hlocal : riemannZeta =ᶠ[nhds w] (0 : ℂ → ℂ) := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    simpa using hz
  have hpreconnected : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hglobal : Set.EqOn riemannZeta 0 ({1}ᶜ : Set ℂ) :=
    analyticOn_riemannZeta.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hpreconnected (by simpa using hw) hlocal
  have hzetaTwo : riemannZeta (2 : ℂ) = 0 := by
    simpa using hglobal (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
  exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hzetaTwo

theorem one_le_analyticOrderAt_riemannZeta_toNat {w : ℂ} (hw : w ≠ 1) (hz : riemannZeta w = 0) :
    1 ≤ (analyticOrderAt riemannZeta w).toNat := by
  have han : AnalyticAt ℂ riemannZeta w := analyticOn_riemannZeta w hw
  have h0 : analyticOrderAt riemannZeta w ≠ 0 := han.analyticOrderAt_ne_zero.mpr hz
  have htop := analyticOrderAt_riemannZeta_ne_top_of_ne_one hw
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn] at h0 ⊢
  simp only [ENat.toNat_coe]
  have : n ≠ 0 := fun h => h0 (by rw [h]; rfl)
  omega

/-- A slice failure at `t` exhibits a right zero whose cone contains `t`. -/
theorem exists_right_zero_of_not_sliceNonneg {t : ℝ} (h : ∃ n, ¬ 0 ≤ xiSliceCoeff t n) :
    ∃ w : ℂ, riemannZeta w = 0 ∧ 1 / 2 < w.re ∧ w.re < 1 ∧ |w.im - t| < w.re - 1 / 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨n, hn⟩ := h
  apply hn
  refine xiSliceCoeff_nonneg_of_cone (fun q => ?_) n
  have hstrip := xiZeroCopy_re_mem_open_unit q
  rcases lt_trichotomy (q.1 : ℂ).re (1 / 2) with hlt | heq | hgt
  · -- use the reflection partner
    have hz := riemannZeta_eq_zero_of_xiZeroCopy (lagPartner q)
    have hre : ((lagPartner q).1 : ℂ).re = 1 - (q.1 : ℂ).re := by
      rw [lagPartner_coe]; simp
    have him : ((lagPartner q).1 : ℂ).im = (q.1 : ℂ).im := lagPartner_im q
    have := hc _ hz (by rw [hre]; linarith) (by rw [hre]; linarith [hstrip.1])
    rw [hre, him] at this
    rw [abs_of_neg (by linarith)]
    linarith
  · rw [heq, sub_self, abs_zero]
    exact abs_nonneg _
  · have := hc _ (riemannZeta_eq_zero_of_xiZeroCopy q) hgt hstrip.2
    rw [abs_of_pos (by linarith)]
    exact this

/-- **Slice positivity holds off a set of small measure, given a mollified mean square.** -/
theorem exists_volume_sliceFailure_le_of_line_meanSquare :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ T₁ T₂ Msq : ℝ, 20 ≤ T₁ → T₁ < T₂ → 0 < Msq →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        volume {t ∈ Set.Icc (T₁ + 1 / 2) (T₂ - 1 / 2) | ∃ n, ¬ 0 ≤ xiSliceCoeff t n}
          ≤ ENNReal.ofReal (((T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb)) / Real.pi) := by
  classical
  obtain ⟨C, K, hC, hK, hmain⟩ := exists_zetaOffLineFirstMoment_le_of_line_meanSquare
  refine ⟨C, K, hC, hK, ?_⟩
  intro b N hN hb1 hbn hbreal Mb hMb1 hmass T₁ T₂ Msq h20 hT hMsqpos hG1 hG2 hP1 hP2 hMsq Z hZ
  have hmom := hmain b N hN hb1 hbn hbreal Mb hMb1 hmass T₁ T₂ Msq h20 hT hMsqpos hG1 hG2 hP1 hP2
    hMsq Z hZ
  set F := Z.filter (fun w => 1 / 2 < w.re) with hF
  set cover : Set ℝ := ⋃ w ∈ F, Set.Ioo (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2))
    with hcover
  -- the failure set lies in the union of the cones
  have hsub : {t ∈ Set.Icc (T₁ + 1 / 2) (T₂ - 1 / 2) | ∃ n, ¬ 0 ≤ xiSliceCoeff t n} ⊆ cover := by
    rintro t ⟨ht, hfail⟩
    obtain ⟨w, hwz, hw1, hw2, hwt⟩ := exists_right_zero_of_not_sliceNonneg hfail
    have hwZ : w ∈ Z := by
      rw [hZ]
      refine ⟨?_, hwz⟩
      rw [Complex.mem_reProdIm]
      rw [abs_lt] at hwt
      constructor
      · rw [uIcc_of_le (by norm_num)]
        exact ⟨hw1.le, by linarith⟩
      · rw [uIcc_of_le hT.le]
        constructor <;> linarith [ht.1, ht.2]
    rw [hcover, Set.mem_iUnion₂]
    refine ⟨w, Finset.mem_filter.mpr ⟨hwZ, hw1⟩, ?_⟩
    rw [abs_lt] at hwt
    constructor <;> linarith
  -- measure of the cover
  have hcoverVol : volume cover ≤ ENNReal.ofReal (∑ w ∈ F, 2 * (w.re - 1 / 2)) := by
    calc volume cover
        ≤ ∑ w ∈ F, volume (Set.Ioo (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2))) :=
          measure_biUnion_finset_le F _
      _ = ∑ w ∈ F, ENNReal.ofReal (2 * (w.re - 1 / 2)) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Real.volume_Ioo]
          congr 1
          ring
      _ = ENNReal.ofReal (∑ w ∈ F, 2 * (w.re - 1 / 2)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro w hw
          have := (Finset.mem_filter.mp hw).2
          linarith
  -- the cover length is at most twice the first moment
  have hsum : ∑ w ∈ F, 2 * (w.re - 1 / 2)
      ≤ 2 * ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
    rw [← Finset.mul_sum]
    gcongr 2 * ?_
    calc ∑ w ∈ F, (w.re - 1 / 2)
        ≤ ∑ w ∈ F, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
          refine Finset.sum_le_sum fun w hw => ?_
          have hwF := Finset.mem_filter.mp hw
          have hwZ := (hZ w).mp hwF.1
          have hw1 : w ≠ 1 := by
            intro h
            have := hwZ.1
            rw [Complex.mem_reProdIm, h] at this
            have him := this.2
            rw [uIcc_of_le hT.le] at him
            simp at him
            linarith [him.1]
          have hm := one_le_analyticOrderAt_riemannZeta_toNat hw1 hwZ.2
          have hpos : 0 ≤ w.re - 1 / 2 := by linarith [hwF.2]
          have : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta w).toNat : ℝ) := by exact_mod_cast hm
          nlinarith
      _ ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun w hw _ => ?_
          have hwZ := (hZ w).mp hw
          have hre := hwZ.1
          rw [Complex.mem_reProdIm, uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)] at hre
          exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1.1])
  calc volume {t ∈ Set.Icc (T₁ + 1 / 2) (T₂ - 1 / 2) | ∃ n, ¬ 0 ≤ xiSliceCoeff t n}
      ≤ volume cover := measure_mono hsub
    _ ≤ ENNReal.ofReal (∑ w ∈ F, 2 * (w.re - 1 / 2)) := hcoverVol
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_pos]

end

end RHTower
