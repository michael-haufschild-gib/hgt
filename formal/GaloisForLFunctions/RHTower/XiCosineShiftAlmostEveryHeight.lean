import GaloisForLFunctions.RHTower.XiCosineShiftDefectDisks
import GaloisForLFunctions.RHTower.ZetaFixedSigmaDensity

/-!
# The cosine shift of `Ξ` has only real zeros above almost every height

For `h > 0` let `A_h(z) = (Ξ(z + ih) + Ξ(z − ih))/2 = cos(hD)Ξ`. A non-real zero `z` of `A_h` lies in
the defect disk of a zero `ρ` of `ξ` with `Re ρ − ½ > h` and `|Im ρ − Re z| < ½`
(`DeBruijn.cosineShift_nonreal_zero_mem_defectDisk`, normalised by conjugation). Zeros of `ζ`
right of the fixed line `Re s = ½ + h` are `o(T)` (`eventually_zeroCount_fixedSigma_le`). Hence:

* `eventually_volume_cosineShift_nonrealHeight_le`: for every `h > 0` and `ε > 0`, for all large
  `U`, the heights `x ∈ [T₁ + 1, T₂ − 1]` (`T₁ ≈ U/4`, `T₂ ≈ U/2`) at which some `A_{h'}`,
  `h' ≥ h`, has a non-real zero with real part `x` have total measure at most `ε (T₂ − T₁)`.
  (For one fixed depth the set is countable; the union over the depths `h' ≥ h` is the
  meaningful object.)

For every `h > 0` the family `cos(hD)Ξ` is therefore real-rooted above a set of heights of full
density, unconditionally. For `h ≥ ½` it is real-rooted everywhere, and RH is real-rootedness for
every `h > 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

/-- A non-real zero of `cos(hD)Ξ` at real part `x > 0` gives a zero `ρ` of `ζ` with
`Re ρ > ½ + h`, `Re ρ < 1` and `|Im ρ − x| < ½`. -/
theorem exists_zetaZero_of_cosineShift_nonreal {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : z.im ≠ 0)
    (h0 : (XiC (z + h * I) + XiC (z - h * I)) / 2 = 0) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 + h < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - z.re| < 1 / 2 := by
  obtain ⟨w, hw, hdisk⟩ := DeBruijn.cosineShift_nonreal_zero_mem_defectDisk hh hz h0
  have hwim : w.im ^ 2 ≤ 1 / 4 :=
    DeBruijn.riemannKernel_zeros_im_sq_le w
      (by rw [DeBruijn.cosTransform_riemannKernel_eq_XiC]; exact hw)
  have hzim : 0 < z.im ^ 2 := by positivity
  -- conjugate so that the zero lies below the axis
  obtain ⟨v, hv, hvre, hvim⟩ : ∃ v : ℂ, XiC v = 0 ∧ v.re = w.re ∧ v.im = -|w.im| := by
    rcases le_or_gt 0 w.im with hpos | hneg
    · refine ⟨(starRingEnd ℂ) w, by rw [DeBruijn.XiC_conj', hw, map_zero], by simp, ?_⟩
      simp [abs_of_nonneg hpos]
    · exact ⟨w, hw, rfl, by rw [abs_of_neg hneg, neg_neg]⟩
  have hdeep : h < |w.im| := by
    have h1 : h ^ 2 < w.im ^ 2 := by nlinarith [sq_nonneg (w.re - z.re)]
    have := sq_lt_sq.mp h1
    rwa [abs_of_pos hh] at this
  have hclose : |w.re - z.re| < 1 / 2 := by
    have h1 : (w.re - z.re) ^ 2 < (1 / 2) ^ 2 := by nlinarith
    have := sq_lt_sq.mp h1
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
  set ρ : ℂ := 1 / 2 + v * I with hρ
  have hρre : ρ.re = 1 / 2 + |w.im| := by rw [hρ]; simp [hvim]
  have hρim : ρ.im = w.re := by rw [hρ]; simp [hvre]
  have hxi : xi ρ = 0 := by rw [hρ, ← hv, XiC]
  have hρ1 : ρ.re < 1 := (xi_zero_re_mem_open_unit hxi).2
  have hρne : ρ ≠ 1 := by intro h1; rw [h1] at hρ1; simp at hρ1
  refine ⟨ρ, (xi_eq_zero_iff (by rw [hρre]; positivity) hρne).mp hxi, by rw [hρre]; linarith, hρ1,
    by rw [hρim]; exact hclose⟩

/-- **Real-rootedness above almost every height.** For every `h > 0` and `ε > 0`, for all large
`U` there are `T₁ ∈ (U/4, U/4 + 1)` and `T₂ ∈ (U/2 − 1, U/2)` such that the heights
`x ∈ [T₁ + 1, T₂ − 1]` at which `cos(h'D)Ξ` has a non-real zero with real part `x` for some
`h' ≥ h` have measure at most `ε (T₂ − T₁)`. -/
theorem eventually_volume_cosineShift_nonrealHeight_le {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) :
    ∀ᶠ U in atTop, ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
      volume {x : ℝ | x ∈ Icc (T₁ + 1) (T₂ - 1) ∧
        ∃ h' : ℝ, h ≤ h' ∧ ∃ z : ℂ, z.re = x ∧ z.im ≠ 0 ∧
          (XiC (z + h' * I) + XiC (z - h' * I)) / 2 = 0}
        ≤ ENNReal.ofReal (ε * (T₂ - T₁)) := by
  classical
  have hσ : (1 : ℝ) / 2 < 1 / 2 + h := by linarith
  filter_upwards [eventually_zeroCount_fixedSigma_le hσ hε, eventually_ge_atTop (100 : ℝ)]
    with U hU hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, ?_⟩
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  set Zσ := Z.filter (fun w => 1 / 2 + h ≤ w.re)
  have hsub : {x : ℝ | x ∈ Icc (T₁ + 1) (T₂ - 1) ∧
      ∃ h' : ℝ, h ≤ h' ∧ ∃ z : ℂ, z.re = x ∧ z.im ≠ 0 ∧
          (XiC (z + h' * I) + XiC (z - h' * I)) / 2 = 0} ⊆
      ⋃ ρ ∈ Zσ, Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2) := by
    rintro x ⟨hx, h', hhh', z, hzx, hz, h0⟩
    obtain ⟨ρ, hζ, hρlo, hρ1, hρx⟩ :=
      exists_zetaZero_of_cosineShift_nonreal (lt_of_lt_of_le hh hhh') hz h0
    rw [hzx] at hρx
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hρx
    have hZρ : ρ ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le]
      refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩, hζ⟩
    refine mem_iUnion₂.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hZρ, by linarith⟩, ?_⟩
    exact ⟨by linarith, by linarith⟩
  have hcard : (Zσ.card : ℝ) ≤ ∑ w ∈ Zσ, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨hwZ, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h1
      rw [h1] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith [hwbox.2.1]
    exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0
  calc volume {x : ℝ | x ∈ Icc (T₁ + 1) (T₂ - 1) ∧
        ∃ h' : ℝ, h ≤ h' ∧ ∃ z : ℂ, z.re = x ∧ z.im ≠ 0 ∧
          (XiC (z + h' * I) + XiC (z - h' * I)) / 2 = 0}
      ≤ volume (⋃ ρ ∈ Zσ, Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2)) := measure_mono hsub
    _ ≤ ∑ ρ ∈ Zσ, volume (Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2)) := measure_biUnion_finset_le _ _
    _ = ∑ ρ ∈ Zσ, ENNReal.ofReal 1 := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Real.volume_Icc]
        congr 1
        ring
    _ = ENNReal.ofReal (Zσ.card : ℝ) := by
        rw [Finset.sum_const, ENNReal.ofReal_one, nsmul_eq_mul, mul_one, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (ε * (T₂ - T₁)) := ENNReal.ofReal_le_ofReal (hcard.trans (hc Z hZ))

end RHTower
