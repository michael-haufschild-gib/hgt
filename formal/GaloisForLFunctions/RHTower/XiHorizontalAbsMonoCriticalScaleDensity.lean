import GaloisForLFunctions.RHTower.XiHorizontalSliceDensityFromMeanSquare
import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailMomentExponential
import GaloisForLFunctions.RHTower.XiSliceAbscissaProfile

/-!
# Absolute monotonicity at the critical scale on almost all heights

`XiHorizontalAbsMono x₀ t` says that every Taylor coefficient at `x₀` of the slice
`x ↦ ξ(½+x+it) ξ(½−x+it)` is nonnegative.  Unconditionally `x₀ = ½ − w(t)` works at every height
(Vinogradov–Korobov, `exists_xiHorizontalAbsMono_vinogradovKorobov`), and RH is `x₀ = 0` at every
height.

**Theorem** (`exists_volume_not_xiHorizontalAbsMono_le_exp`).  There are `B, K ≥ 0` such that for all
large `U` there are heights `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)` with, for every `c ≥ 2`,

  `|{t ∈ [T₁ + ½, T₂ − ½] : the slice at t is not absolutely monotone from c/log U}|
      ≤ 2 (B e^{−c/28} (T₂ − T₁) + K log² U)`.

**Corollary** (`exists_volume_not_xiHorizontalAbsMono_le_criticalScale`,
`eventually_volume_not_xiHorizontalAbsMono_le`).  For every `ε > 0` there is `c` such that for all
large `U`, the slice is absolutely monotone from `c/log U` at every height of `[U/4 + 2, U/2 − 2]`
outside a set of measure at most `εU`.  The exceptional proportion decays like `e^{−c/28}`.

So at almost every height the absolute-monotonicity abscissa is at the critical scale `O(1/log t)`,
against `½ − w(t)` at every height and `0` under RH.

Proof.  By the hyperbola criterion (`xiHorizontalAbsMono_of_hyperbola`), absolute monotonicity from
`x₀` can fail at `t` only if a zero `ρ` satisfies `(Re ρ − ½)² > (Im ρ − t)² + x₀²`.  Replacing a left
zero by its reflection `1 − ρ̄`, which has the same ordinate, the failure heights are covered by the
intervals `(Im w − (Re w − ½), Im w + (Re w − ½))` over the zeros `w` of `ζ` with `Re w > ½ + x₀`.
Their total length is at most twice the off-line first moment beyond `½ + c/log U`, which Selberg's
exponential near-line density bounds by `B e^{−c/28}(T₂ − T₁) + K log² U`
(`exists_offLineTailMoment_window_le_exp`).
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower.DeBruijn

noncomputable section

/-- **Off-centre failures exhibit a right zero in the hyperbola.**  If the slice at height `t` is not
absolutely monotone from `x₀ ≥ 0`, some zero `w` of `ζ` has `½ + x₀ < Re w < 1` and
`|Im w − t| < Re w − ½`. -/
theorem exists_right_zero_of_not_xiHorizontalAbsMono {t x₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (h : ¬ XiHorizontalAbsMono x₀ t) :
    ∃ w : ℂ, riemannZeta w = 0 ∧ 1 / 2 + x₀ < w.re ∧ w.re < 1 ∧ |w.im - t| < w.re - 1 / 2 := by
  by_contra hc
  push Not at hc
  apply h
  refine xiHorizontalAbsMono_of_hyperbola hx₀ fun q => ?_
  have hstrip := xiZeroCopy_re_mem_open_unit q
  -- a right zero `w` with the same ordinate and `Re w − ½ = |Re q − ½|`
  obtain ⟨w, hwz, hwre, hwim⟩ : ∃ w : ℂ, riemannZeta w = 0 ∧
      w.re - 1 / 2 = |(q.1 : ℂ).re - 1 / 2| ∧ w.im = (q.1 : ℂ).im := by
    rcases le_or_gt (1 / 2) (q.1 : ℂ).re with hge | hlt
    · exact ⟨q.1, riemannZeta_eq_zero_of_xiZeroCopy q, by rw [abs_of_nonneg (by linarith)], rfl⟩
    · refine ⟨(lagPartner q).1, riemannZeta_eq_zero_of_xiZeroCopy (lagPartner q), ?_,
        lagPartner_im q⟩
      rw [lagPartner_coe, abs_of_neg (by linarith)]
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      ring
  have hsq : ((q.1 : ℂ).re - 1 / 2) ^ 2 = (w.re - 1 / 2) ^ 2 := by rw [hwre, sq_abs]
  rw [hsq, ← hwim]
  have hwnn : 0 ≤ w.re - 1 / 2 := by rw [hwre]; exact abs_nonneg _
  by_cases hfar : w.re ≤ 1 / 2 + x₀
  · have : (w.re - 1 / 2) ^ 2 ≤ x₀ ^ 2 := pow_le_pow_left₀ hwnn (by linarith) 2
    nlinarith [sq_nonneg (w.im - t)]
  · push Not at hfar
    have hw1 : w.re < 1 := by
      have habs : |(q.1 : ℂ).re - 1 / 2| < 1 / 2 :=
        abs_lt.mpr ⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩
      linarith
    have hge := hc w hwz hfar hw1
    have : (w.re - 1 / 2) ^ 2 ≤ (w.im - t) ^ 2 := by
      rw [← sq_abs (w.im - t)]; exact pow_le_pow_left₀ hwnn hge 2
    nlinarith [sq_nonneg x₀]

/-- **Off-centre absolute monotonicity fails only on a set of exponentially small measure.** -/
theorem exists_volume_not_xiHorizontalAbsMono_le_exp :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ c : ℝ, 2 ≤ c →
          volume {t ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) |
              ¬ XiHorizontalAbsMono (c / Real.log U) t}
            ≤ ENNReal.ofReal (2 * (B * Real.exp (-(c / 28)) * (T₂ - T₁)
              + K * Real.log U ^ 2)) := by
  classical
  obtain ⟨B, K, hB, hK, hmom⟩ := exists_offLineTailMoment_window_le_exp
  refine ⟨B, K, hB, hK, ?_⟩
  filter_upwards [hmom, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (8 : ℝ)]
    with U hU hUe hU8
  obtain ⟨T₁, hT₁, T₂, hT₂, hsel⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun c hc => ?_⟩
  have hT : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  have hL1 : 1 ≤ Real.log U := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hUe
  have hx₀ : 0 ≤ c / Real.log U := div_nonneg (by linarith) (by linarith)
  -- the zeros of `ζ` in Selberg's box
  have hfinZ : {z : ℂ | z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧
      riemannZeta z = 0}.Finite := by
    have hxi : AnalyticOnNhd ℂ xi univ := xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ
    have hfin := entire_zeros_closedRectangle_finite hxi ⟨2, xi_ne_zero_of_one_le_re (by simp)⟩
      (((1 / 2 : ℝ) : ℂ) + T₁ * I) (((15 / 2 : ℝ) : ℂ) + T₂ * I)
    refine hfin.subset ?_
    rintro z ⟨hzR, hz0⟩
    refine ⟨by simpa using hzR, ?_⟩
    have hre := (mem_reProdIm.mp hzR).1
    have him := (mem_reProdIm.mp hzR).2
    rw [uIcc_of_le (by norm_num)] at hre
    rw [uIcc_of_le hT.le] at him
    have hz1 : z ≠ 1 := by
      intro h1; rw [h1] at him; simp at him; linarith [him.1, hT₁.1]
    exact (xi_eq_zero_iff (by linarith [hre.1]) hz1).mpr hz0
  set Z := hfinZ.toFinset with hZdef
  have hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧
      riemannZeta z = 0 := fun z => by rw [hZdef, Set.Finite.mem_toFinset]; rfl
  have hmomc := hsel Z hZ c hc
  set F := Z.filter (fun w => 1 / 2 + c / Real.log U ≤ w.re) with hF
  set cover : Set ℝ := ⋃ w ∈ F, Set.Ioo (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2))
    with hcover
  -- the failure set lies in the union of the hyperbola intervals
  have hsub : {t ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) | ¬ XiHorizontalAbsMono (c / Real.log U) t}
      ⊆ cover := by
    rintro t ⟨ht, hfail⟩
    obtain ⟨w, hwz, hw1, hw2, hwt⟩ := exists_right_zero_of_not_xiHorizontalAbsMono hx₀ hfail
    have hwZ : w ∈ Z := by
      rw [hZ]
      refine ⟨?_, hwz⟩
      rw [Complex.mem_reProdIm]
      rw [abs_lt] at hwt
      constructor
      · rw [uIcc_of_le (by norm_num)]
        exact ⟨by linarith, by linarith⟩
      · rw [uIcc_of_le hT.le]
        constructor <;> linarith [ht.1, ht.2]
    rw [hcover, Set.mem_iUnion₂]
    refine ⟨w, Finset.mem_filter.mpr ⟨hwZ, hw1.le⟩, ?_⟩
    rw [abs_lt] at hwt
    constructor <;> linarith
  -- measure of the cover
  have hFpos : ∀ w ∈ F, 0 ≤ w.re - 1 / 2 := fun w hw => by
    have := (Finset.mem_filter.mp hw).2
    linarith
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
          linarith [hFpos w hw]
  -- the cover length is at most twice the tail moment
  have hsum : ∑ w ∈ F, 2 * (w.re - 1 / 2)
      ≤ 2 * ∑ w ∈ F, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
    rw [← Finset.mul_sum]
    gcongr 2 * ?_
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
      linarith [him.1, hT₁.1]
    have hm := one_le_analyticOrderAt_riemannZeta_toNat hw1 hwZ.2
    have hpos := hFpos w hw
    have : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta w).toNat : ℝ) := by exact_mod_cast hm
    nlinarith
  calc volume {t ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) | ¬ XiHorizontalAbsMono (c / Real.log U) t}
      ≤ volume cover := measure_mono hsub
    _ ≤ ENNReal.ofReal (∑ w ∈ F, 2 * (w.re - 1 / 2)) := hcoverVol
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      linarith

/-- **Absolute monotonicity at the critical scale off an exponentially small set.**  There is
`B > 0` such that for every `c ≥ 2` and all large `U`, the slice is absolutely monotone from
`c/log U` at every height of `[U/4 + 2, U/2 − 2]` outside a set of measure at most `B e^{−c/28} U`. -/
theorem exists_volume_not_xiHorizontalAbsMono_le_criticalScale :
    ∃ B : ℝ, 0 < B ∧ ∀ c : ℝ, 2 ≤ c → ∀ᶠ U in atTop,
      volume {t ∈ Icc (U / 4 + 2) (U / 2 - 2) | ¬ XiHorizontalAbsMono (c / Real.log U) t}
        ≤ ENNReal.ofReal (B * Real.exp (-(c / 28)) * U) := by
  obtain ⟨B, K, hB, hK, hmain⟩ := exists_volume_not_xiHorizontalAbsMono_le_exp
  refine ⟨B / 2 + 1, by positivity, fun c hc => ?_⟩
  have he := Real.exp_pos (-(c / 28))
  have hlim := (tendsto_order.1 (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero)).2
    (Real.exp (-(c / 28)) / (2 * K + 1)) (by positivity)
  filter_upwards [hmain, hlim, eventually_gt_atTop (0 : ℝ)] with U hU hlog hU0
  obtain ⟨T₁, hT₁, T₂, hT₂, hvol⟩ := hU
  have hsub : {t ∈ Icc (U / 4 + 2) (U / 2 - 2) | ¬ XiHorizontalAbsMono (c / Real.log U) t}
      ⊆ {t ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) | ¬ XiHorizontalAbsMono (c / Real.log U) t} := by
    rintro t ⟨ht, hfail⟩
    exact ⟨⟨by linarith [ht.1, hT₁.2], by linarith [ht.2, hT₂.1]⟩, hfail⟩
  refine le_trans (measure_mono hsub) (le_trans (hvol c hc) (ENNReal.ofReal_le_ofReal ?_))
  have hlen : T₂ - T₁ ≤ U / 4 := by linarith [hT₁.1, hT₂.2]
  have hlog' : Real.log U ^ 2 ≤ Real.exp (-(c / 28)) / (2 * K + 1) * U := by
    rw [one_mul, add_zero, div_lt_iff₀ hU0] at hlog
    exact hlog.le
  have hK' : 2 * K * Real.log U ^ 2 ≤ Real.exp (-(c / 28)) * U := by
    have h1 : 2 * K * Real.log U ^ 2 ≤ (2 * K + 1) * Real.log U ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    have h2 : (2 * K + 1) * Real.log U ^ 2 ≤ (2 * K + 1) * (Real.exp (-(c / 28)) / (2 * K + 1) * U) :=
      mul_le_mul_of_nonneg_left hlog' (by linarith)
    have h3 : (2 * K + 1) * (Real.exp (-(c / 28)) / (2 * K + 1) * U) = Real.exp (-(c / 28)) * U := by
      field_simp
    linarith
  have hBlen : B * Real.exp (-(c / 28)) * (T₂ - T₁) ≤ B * Real.exp (-(c / 28)) * (U / 4) :=
    mul_le_mul_of_nonneg_left hlen (by positivity)
  nlinarith

/-- **Density one at the critical scale.**  For every `ε > 0` there is `c ≥ 2` such that for all
large `U` the slice is absolutely monotone from `c/log U` at every height of `[U/4 + 2, U/2 − 2]`
outside a set of measure at most `εU`. -/
theorem eventually_volume_not_xiHorizontalAbsMono_le {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 2 ≤ c ∧ ∀ᶠ U in atTop,
      volume {t ∈ Icc (U / 4 + 2) (U / 2 - 2) | ¬ XiHorizontalAbsMono (c / Real.log U) t}
        ≤ ENNReal.ofReal (ε * U) := by
  obtain ⟨B, hB, hmain⟩ := exists_volume_not_xiHorizontalAbsMono_le_criticalScale
  refine ⟨max 2 (28 * Real.log (B / ε)), le_max_left _ _, ?_⟩
  filter_upwards [hmain _ (le_max_left _ _), eventually_ge_atTop (0 : ℝ)] with U hU hU0
  refine le_trans hU (ENNReal.ofReal_le_ofReal ?_)
  have hexp : B * Real.exp (-(max 2 (28 * Real.log (B / ε)) / 28)) ≤ ε := by
    have h1 : Real.log (B / ε) ≤ max 2 (28 * Real.log (B / ε)) / 28 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith [le_max_right 2 (28 * Real.log (B / ε))]
    have h2 : Real.exp (-(max 2 (28 * Real.log (B / ε)) / 28)) ≤ Real.exp (-Real.log (B / ε)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp (-Real.log (B / ε)) = ε / B := by
      rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    calc B * Real.exp (-(max 2 (28 * Real.log (B / ε)) / 28)) ≤ B * (ε / B) :=
          mul_le_mul_of_nonneg_left (h2.trans_eq h3) hB.le
      _ = ε := by field_simp
  exact mul_le_mul_of_nonneg_right hexp hU0

end

end RHTower.DeBruijn
