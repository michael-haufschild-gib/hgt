import GaloisForLFunctions.SquareRootThreshold.ZetaWindowPrimePolynomialReadsZeroCountRemainder
import GaloisForLFunctions.RHTower.ZetaRightZeroWeightedCount
import GaloisForLFunctions.RHTower.EvenLandauPairTest

/-!
# The off-line correction is small outside a sparse set of heights

The off-line correction of the bump window (`offLineCorrection`) sums, over the zeros
`ρ = ½ + δ + it`, the defect `Re K̂_ℓ(t − T − iδ) − ψ_ℓ(t − T)`, which is
`O_ℓ(δ² (1 + |t − T|)⁻⁴)` (`abs_offLineDefect_le`, the quadratic Fourier defect).  Zeros close to the
line cost `δ² ≤ v²`; deep zeros (`|δ| ≥ v`) cost only if they lie within `W` of the height.  Hence
at every height farther than `W` from the ordinates of the deep zeros,
`|Corr_ℓ(T)| ≤ C_ℓ (v² + 1/W) log(|T| + 3)` (`exists_abs_offLineCorrection_le`).

With `y = (log U)^{1/3}`, `v = y⁻²` and `W = y⁶`, the Selberg-type window count
(`exists_windowZeros_count_le`) bounds the deep zeros with ordinate in `[U/4, U/2]` by
`O(y² U e^{−y/2400} + y⁵)`; their `W`-neighbourhoods and the two margins of the window have measure
`O(U y¹¹ e^{−y/2400}) = o(U)`.  By the reflection `ρ ↦ 1 − ρ̄` the deep zeros left of the line
have the same ordinates as deep zeros right of it.  So for all `ε, η > 0` and large `U` the heights
`T ∈ [U/4, U/2]` with `|Corr_ℓ(T)| > η` lie in a measurable set of measure `≤ εU`
(`eventually_exists_sparse_windowExcludedHeights`).
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.Littlewood

/-- `γ_ρ − T = (Im ρ − T) − i(Re ρ − ½)`. -/
theorem gammaOf_sub_ofReal (ρ : ℂ) (T : ℝ) :
    gammaOf ρ - T = ((ρ.im - T : ℝ) : ℂ) - ((ρ.re - 1 / 2 : ℝ) : ℂ) * I := by
  rw [gammaOf, Complex.div_I]
  apply Complex.ext <;> simp

theorem isNontrivialZero_of_mem {ρ : zetaZeroConfig.carrier} : IsNontrivialZero (ρ : ℂ) :=
  (Set.ext_iff.mp zetaZeroConfig_carrier (ρ : ℂ)).mp ρ.2

section Defect

variable {ℓ : ℝ} (hℓ : 0 < ℓ)
include hℓ

theorem contDiff_sq_mul_bumpKernel : ContDiff ℝ 4 (fun u : ℝ => (u : ℂ) ^ 2 * bumpAutocorrelation ℓ u) :=
  (Complex.ofRealCLM.contDiff.pow 2).mul (bumpAutocorrelation_contDiff hℓ)

/-- **The defect of one zero.**  `|Re K̂_ℓ(γ_ρ − T) − ψ_ℓ(Im ρ − T)| ≤
8 δ² e^{2ℓ|δ|} Q_ℓ (1 + |Im ρ − T|)⁻⁴`, `δ = Re ρ − ½`. -/
theorem abs_offLineDefect_le (ρ : ℂ) (T : ℝ) :
    |(paperFT (bumpAutocorrelation ℓ) (gammaOf ρ - T)).re - psi ℓ 0 (ρ.im - T)| ≤
      8 * (ρ.re - 1 / 2) ^ 2 * Real.exp (|ρ.re - 1 / 2| * (2 * ℓ)) *
        quadraticDefectNorm (bumpAutocorrelation ℓ) / (1 + |ρ.im - T|) ^ 4 := by
  rw [gammaOf_sub_ofReal, psi_eq_re_paperFT hℓ]
  exact abs_re_paperFT_sub_mul_I_sub_le (by positivity) (bumpAutocorrelation_continuous hℓ)
    (bumpAutocorrelation_support hℓ) (bumpAutocorrelation_im ℓ) (bumpAutocorrelation_neg ℓ) (contDiff_sq_mul_bumpKernel hℓ) _ _

/-- **The correction away from the deep zeros.**  If every zero with `|Re ρ − ½| ≥ v` has
ordinate at distance `≥ W` from `T`, then `|Corr_ℓ(T)| ≤ C (v² + 1/W) log(|T| + 3)`. -/
theorem exists_abs_offLineCorrection_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ v W T : ℝ, 0 < W →
    (∀ ρ : zetaZeroConfig.carrier, v ≤ |(ρ : ℂ).re - 1 / 2| → W ≤ |(ρ : ℂ).im - T|) →
    |offLineCorrection ℓ T| ≤ C * (v ^ 2 + 1 / W) * Real.log (|T| + 3) := by
  obtain ⟨A₀, hA₀, hloc⟩ := RvM.zetaZeroConfig_local_count
  set Q := quadraticDefectNorm (bumpAutocorrelation ℓ) with hQdef
  have hQ : 0 ≤ Q := quadraticDefectNorm_nonneg _
  refine ⟨8 * Real.exp ℓ * Q * (24 * A₀), by positivity, fun v W T hW hfar => ?_⟩
  obtain ⟨hs, hle⟩ := window_tsum_le zetaZeroConfig hA₀ hloc T
  set c := 8 * Real.exp ℓ * Q * (v ^ 2 + 1 / W) with hc
  have hc0 : 0 ≤ c := by positivity
  have hbound : ∀ ρ : zetaZeroConfig.carrier,
      ‖(zetaZeroConfig.mult ρ : ℝ) * ((paperFT (bumpAutocorrelation ℓ) (gammaOf ρ - T)).re -
        psi ℓ 0 ((ρ : ℂ).im - T))‖ ≤
        c * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - T|) ^ 3) := by
    intro ρ
    have hρ := isNontrivialZero_of_mem (ρ := ρ)
    set δ := (ρ : ℂ).re - 1 / 2 with hδ
    set w := (ρ : ℂ).im - T with hw
    have hδ2 : |δ| < 1 / 2 := abs_lt.mpr ⟨by linarith [hρ.2.1], by linarith [hρ.2.2]⟩
    have hexp : Real.exp (|δ| * (2 * ℓ)) ≤ Real.exp ℓ :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg δ])
    have hw1 : 1 ≤ 1 + |w| := by linarith [abs_nonneg w]
    have hcore : δ ^ 2 ≤ (v ^ 2 + 1 / W) * (1 + |w|) := by
      by_cases hd : v ≤ |δ|
      · have hfar' : W ≤ 1 + |w| := by linarith [hfar ρ hd]
        have h1 : 1 ≤ 1 / W * (1 + |w|) := by
          rw [one_div, inv_mul_eq_div, le_div_iff₀ hW]; linarith
        have h2 : δ ^ 2 ≤ 1 := by nlinarith [sq_abs δ, abs_nonneg δ]
        nlinarith [sq_nonneg v]
      · push Not at hd
        have h2 : δ ^ 2 ≤ v ^ 2 := by rw [← sq_abs δ]; nlinarith [abs_nonneg δ]
        have h3 : 0 ≤ 1 / W * (1 + |w|) := by positivity
        nlinarith [sq_nonneg v]
    have hkey : δ ^ 2 / (1 + |w|) ^ 4 ≤ (v ^ 2 + 1 / W) / (1 + |w|) ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc δ ^ 2 * (1 + |w|) ^ 3 ≤ ((v ^ 2 + 1 / W) * (1 + |w|)) * (1 + |w|) ^ 3 :=
            mul_le_mul_of_nonneg_right hcore (by positivity)
        _ = (v ^ 2 + 1 / W) * (1 + |w|) ^ 4 := by ring
    have hD := abs_offLineDefect_le hℓ (ρ : ℂ) T
    rw [← hδ, ← hw, ← hQdef] at hD
    have hD' : |(paperFT (bumpAutocorrelation ℓ) (gammaOf ρ - T)).re - psi ℓ 0 w| ≤
        8 * Real.exp ℓ * Q * ((v ^ 2 + 1 / W) / (1 + |w|) ^ 3) := by
      refine hD.trans ?_
      calc 8 * δ ^ 2 * Real.exp (|δ| * (2 * ℓ)) * Q / (1 + |w|) ^ 4
          = 8 * Real.exp (|δ| * (2 * ℓ)) * Q * (δ ^ 2 / (1 + |w|) ^ 4) := by ring
        _ ≤ 8 * Real.exp ℓ * Q * ((v ^ 2 + 1 / W) / (1 + |w|) ^ 3) := by
            gcongr
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm]
    calc (zetaZeroConfig.mult ρ : ℝ) * |(paperFT (bumpAutocorrelation ℓ) (gammaOf ρ - T)).re - psi ℓ 0 w|
        ≤ (zetaZeroConfig.mult ρ : ℝ) * (8 * Real.exp ℓ * Q * ((v ^ 2 + 1 / W) / (1 + |w|) ^ 3)) :=
          mul_le_mul_of_nonneg_left hD' hm
      _ = c * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |w|) ^ 3) := by rw [hc]; ring
  have h := tsum_of_norm_bounded (hs.mul_left c).hasSum hbound
  rw [Real.norm_eq_abs] at h
  calc |offLineCorrection ℓ T| ≤ ∑' ρ : zetaZeroConfig.carrier,
        c * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - T|) ^ 3) := h
    _ = c * ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - T|) ^ 3 := tsum_mul_left
    _ ≤ c * (24 * A₀ * Real.log (|T| + 3)) := mul_le_mul_of_nonneg_left hle hc0
    _ = 8 * Real.exp ℓ * Q * (24 * A₀) * (v ^ 2 + 1 / W) * Real.log (|T| + 3) := by
        rw [hc]; ring

end Defect

/-! ### The excluded heights of a window -/

/-- The excluded heights of the window `[U/4, U/2]`: its two margins of width `W + 1` and the
`W`-neighbourhoods of the ordinates of a finite set `Z` of zeros. -/
def windowExcludedHeights (U W : ℝ) (Z : Finset ℂ) : Set ℝ :=
  Icc (U / 4) (U / 4 + W + 1) ∪ Icc (U / 2 - W - 1) (U / 2) ∪ ⋃ w ∈ Z, Icc (w.im - W) (w.im + W)

theorem measurableSet_windowExcludedHeights (U W : ℝ) (Z : Finset ℂ) : MeasurableSet (windowExcludedHeights U W Z) :=
  (measurableSet_Icc.union measurableSet_Icc).union
    (Finset.measurableSet_biUnion Z fun _ _ => measurableSet_Icc)

theorem volume_windowExcludedHeights_le {U W : ℝ} (hW : 0 ≤ W) (Z : Finset ℂ) :
    volume (windowExcludedHeights U W Z) ≤ ENNReal.ofReal (2 * (W + 1) + 2 * W * Z.card) := by
  unfold windowExcludedHeights
  have h1 : volume (Icc (U / 4) (U / 4 + W + 1)) = ENNReal.ofReal (W + 1) := by
    rw [Real.volume_Icc]; congr 1; ring
  have h2 : volume (Icc (U / 2 - W - 1) (U / 2)) = ENNReal.ofReal (W + 1) := by
    rw [Real.volume_Icc]; congr 1; ring
  have h3 : volume (⋃ w ∈ Z, Icc (w.im - W) (w.im + W)) ≤ ENNReal.ofReal (2 * W * Z.card) := by
    refine (measure_biUnion_finset_le Z _).trans (le_of_eq ?_)
    have : ∀ w ∈ Z, volume (Icc (w.im - W) (w.im + W)) = ENNReal.ofReal (2 * W) := fun w _ => by
      rw [Real.volume_Icc]; congr 1; ring
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm (2 * W),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  calc volume (Icc (U / 4) (U / 4 + W + 1) ∪ Icc (U / 2 - W - 1) (U / 2) ∪
        ⋃ w ∈ Z, Icc (w.im - W) (w.im + W))
      ≤ volume (Icc (U / 4) (U / 4 + W + 1)) + volume (Icc (U / 2 - W - 1) (U / 2)) +
          volume (⋃ w ∈ Z, Icc (w.im - W) (w.im + W)) :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal (W + 1) + ENNReal.ofReal (W + 1) + ENNReal.ofReal (2 * W * Z.card) := by
        rw [h1, h2]; exact add_le_add_right h3 _
    _ = ENNReal.ofReal (2 * (W + 1) + 2 * W * Z.card) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- A zero of `ζ` in a window, right of `½ + v`, has multiplicity at least one. -/
theorem one_le_zeroMult_of_mem_windowZeros {T₁ T₂ v : ℝ} (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂) (hv : 0 < v)
    {w : ℂ} (hw : w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re)) :
    1 ≤ RHTower.zeroMult w := by
  rw [Finset.mem_filter, mem_windowZeros_iff hT₁ hT] at hw
  obtain ⟨⟨-, hζ⟩, hre⟩ := hw
  have hre1 : w.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hζ
  have hmem : w ∈ zetaZeroConfig.carrier := by
    rw [zetaZeroConfig_carrier]; exact ⟨hζ, by linarith, hre1⟩
  have hw1 : w ≠ 1 := fun h => by rw [h, Complex.one_re] at hre1; exact lt_irrefl _ hre1
  have h1 := zetaZeroConfig.one_le_mult w hmem
  rw [zetaZeroConfig_mult] at h1
  rw [zeroMult_eq_zeta_order hw1]
  exact_mod_cast h1

/-- A zero right of `½ + v` with ordinate in `[T₁, T₂]` and within `W` of `T` puts `T` among the
excluded heights. -/
theorem mem_windowExcludedHeights_of_zero {U W v T₁ T₂ T : ℝ} (hv : 0 ≤ v) (hT₁ : 0 < T₁) (hT : T₁ ≤ T₂)
    {z : ℂ} (hz : z ∈ zetaZeroConfig.carrier) (hzv : 1 / 2 + v ≤ z.re)
    (hzT : T₁ ≤ z.im ∧ z.im ≤ T₂) (hW : |z.im - T| < W) :
    T ∈ windowExcludedHeights U W ((windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re)) := by
  rw [zetaZeroConfig_carrier] at hz
  have hzmem : z ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re) := by
    rw [Finset.mem_filter, mem_windowZeros_iff hT₁ hT]
    refine ⟨⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, hz.1⟩, hzv⟩
    · rw [uIcc_of_le (by norm_num)]
      exact ⟨by linarith, by linarith [hz.2.2]⟩
    · rw [uIcc_of_le hT]; exact hzT
  refine Or.inr (mem_iUnion₂.mpr ⟨z, hzmem, ?_⟩)
  rw [abs_lt] at hW
  exact ⟨by linarith [hW.2], by linarith [hW.1]⟩

/-- **Heights outside the excluded set are far from every deep zero.** -/
theorem far_of_notMem_windowExcludedHeights {U W v T₁ T₂ T : ℝ} (hv : 0 < v)
    (hT₁ : T₁ ∈ Ioo (U / 4) (U / 4 + 1)) (hT₂ : T₂ ∈ Ioo (U / 2 - 1) (U / 2)) (hU : 0 < U)
    (hT : T ∈ Icc (U / 4) (U / 2))
    (hTB : T ∉ windowExcludedHeights U W ((windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re))) :
    ∀ ρ : zetaZeroConfig.carrier, v ≤ |(ρ : ℂ).re - 1 / 2| → W ≤ |(ρ : ℂ).im - T| := by
  intro ρ hδ
  by_contra hlt
  push Not at hlt
  have hT₁0 : 0 < T₁ := by linarith [hT₁.1]
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hlt.le
  -- the margins
  have hm1 : U / 4 + W + 1 < T := by
    by_contra h
    exact hTB (Or.inl (Or.inl ⟨hT.1, not_lt.mp h⟩))
  have hm2 : T < U / 2 - W - 1 := by
    by_contra h
    exact hTB (Or.inl (Or.inr ⟨not_lt.mp h, hT.2⟩))
  have hT12 : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  have him : T₁ ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T₂ := by
    rw [abs_lt] at hlt
    exact ⟨by linarith [hT₁.2, hlt.1], by linarith [hT₂.1, hlt.2]⟩
  have hρ := ρ.2
  rcases le_or_gt (1 / 2) (ρ : ℂ).re with hre | hre
  · rw [abs_of_nonneg (by linarith)] at hδ
    exact hTB (mem_windowExcludedHeights_of_zero hv.le hT₁0 hT12 hρ (by linarith) him hlt)
  · rw [abs_of_neg (by linarith)] at hδ
    have hz : 1 - conj (ρ : ℂ) ∈ zetaZeroConfig.carrier :=
      one_sub_mem_zetaZeroConfig (conj_mem_zetaZeroConfig hρ)
    have hzre : (1 - conj (ρ : ℂ)).re = 1 - (ρ : ℂ).re := by simp
    have hzim : (1 - conj (ρ : ℂ)).im = (ρ : ℂ).im := by simp
    refine hTB (mem_windowExcludedHeights_of_zero hv.le hT₁0 hT12 hz (by rw [hzre]; linarith) ?_ ?_)
    · rw [hzim]; exact him
    · rw [hzim]; exact hlt

/-! ### The sparse set of bad heights -/

/-- `y = (log U)^{1/3}`. -/
def cubeRootLog (U : ℝ) : ℝ := Real.log U ^ ((3 : ℕ) : ℝ)⁻¹

theorem cubeRootLog_pow {U : ℝ} (hU : 1 ≤ U) : cubeRootLog U ^ 3 = Real.log U :=
  Real.rpow_inv_natCast_pow (Real.log_nonneg hU) (by norm_num)

theorem tendsto_cubeRootLog : Tendsto cubeRootLog atTop atTop :=
  (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop

section Sparse

variable {ℓ : ℝ} (hℓ : 0 < ℓ)
include hℓ

/-- **The off-line correction is small outside a sparse set.**  For `ε, η > 0` and all large
`U`, the heights `T ∈ [U/4, U/2]` with `|Corr_ℓ(T)| > η` lie in a measurable set of measure
`≤ εU`. -/
theorem eventually_exists_sparse_windowExcludedHeights {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ U in atTop, ∃ B : Set ℝ, MeasurableSet B ∧ volume B ≤ ENNReal.ofReal (ε * U) ∧
      ∀ T ∈ Icc (U / 4) (U / 2), T ∉ B → |offLineCorrection ℓ T| ≤ η := by
  obtain ⟨C, hC, hcorr⟩ := exists_abs_offLineCorrection_le hℓ
  obtain ⟨A, K, hA, hK, hcount⟩ := exists_windowZeros_count_le
  set D := 4 + A / (2 * π) + 2 * K / π with hD
  have hD0 : 0 < D := by positivity
  -- `y¹¹ e^{−y/2400} → 0` and `2C/y → 0`
  have hlim1 : Tendsto (fun U => D * (cubeRootLog U ^ ((11 : ℕ) : ℝ) *
      Real.exp (-(1 / 2400) * cubeRootLog U))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((11 : ℕ) : ℝ) (1 / 2400)
      (by norm_num)).comp tendsto_cubeRootLog).const_mul D
  have hlim2 : Tendsto (fun U => 2 * C / cubeRootLog U) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_cubeRootLog
  filter_upwards [hcount, hlim1.eventually (ge_mem_nhds hε), hlim2.eventually (ge_mem_nhds hη),
    tendsto_cubeRootLog.eventually_ge_atTop 2, eventually_ge_atTop 8] with U hU h1 h2 h3 h4
  obtain ⟨T₁, hT₁, T₂, hT₂, hZ⟩ := hU
  simp only [Real.rpow_natCast] at h1
  set y := cubeRootLog U with hy
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hU0 : 0 < U := by linarith
  have hL : y ^ 3 = Real.log U := cubeRootLog_pow (by linarith)
  set v : ℝ := 1 / y ^ 2 with hv
  set W : ℝ := y ^ 6 with hW
  have hv0 : 0 < v := by positivity
  have hW0 : 0 < W := by positivity
  set Z := (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v ≤ w.re) with hZdef
  have hT₁0 : 0 < T₁ := by linarith [hT₁.1]
  have hT12 : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  -- the count of the deep zeros
  have hvL : v * Real.log U = y := by rw [← hL, hv]; field_simp
  have hcnt := hZ v (by rw [← hL, hv, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
    (by
      rw [← hL, hv]
      have : 1 / y ^ 2 ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have : 2 / y ^ 3 ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      linarith)
  rw [hvL, ← hL] at hcnt
  have hcard : (Z.card : ℝ) ≤ ∑ w ∈ Z, RHTower.zeroMult w := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact Finset.sum_le_sum fun w hw => one_le_zeroMult_of_mem_windowZeros hT₁0 hT12 hv0 hw
  set E := Real.exp (-(1 / 2400) * y) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hcnt' : (Z.card : ℝ) ≤ y ^ 2 * (U / 4 * A * E + K * y ^ 3) / π := by
    refine hcard.trans (hcnt.trans (le_of_eq ?_))
    rw [hv, hE, show -(y / 2400) = -(1 / 2400) * y by ring]
    field_simp
  refine ⟨windowExcludedHeights U W Z, measurableSet_windowExcludedHeights U W Z,
    (volume_windowExcludedHeights_le hW0.le Z).trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · -- `2(W + 1) + 2W·#Z ≤ εU`
    have hUE : 1 ≤ U * E := by
      have : U = Real.exp (y ^ 3) := by rw [hL, Real.exp_log hU0]
      rw [this, hE, ← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have hy8 : y ^ 8 ≤ y ^ 11 := pow_le_pow_right₀ hy1 (by norm_num)
    have hy6 : y ^ 6 + 1 ≤ 2 * y ^ 11 := by
      have : y ^ 6 ≤ y ^ 11 := pow_le_pow_right₀ hy1 (by norm_num)
      have : 1 ≤ y ^ 11 := one_le_pow₀ hy1
      linarith
    set P := U * (y ^ 11 * E) with hP
    have hP1 : y ^ 11 ≤ P := by
      rw [hP]; nlinarith [pow_pos hy0 11]
    have hπ : 0 < π := Real.pi_pos
    calc 2 * (W + 1) + 2 * W * Z.card
        ≤ 2 * (y ^ 6 + 1) + 2 * y ^ 6 * (y ^ 2 * (U / 4 * A * E + K * y ^ 3) / π) := by
          rw [hW]; gcongr
      _ = 2 * (y ^ 6 + 1) + A / (2 * π) * (U * (y ^ 8 * E)) + 2 * K / π * y ^ 11 := by
          field_simp; ring
      _ ≤ 4 * P + A / (2 * π) * P + 2 * K / π * P := by
          have e1 : 2 * (y ^ 6 + 1) ≤ 4 * P := by linarith
          have e2 : A / (2 * π) * (U * (y ^ 8 * E)) ≤ A / (2 * π) * P := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [hP]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy8 hE0.le) hU0.le
          have e3 : 2 * K / π * y ^ 11 ≤ 2 * K / π * P :=
            mul_le_mul_of_nonneg_left hP1 (by positivity)
          linarith
      _ = U * (D * (y ^ 11 * E)) := by rw [hP, hD]; ring
      _ ≤ U * ε := mul_le_mul_of_nonneg_left h1 hU0.le
      _ = ε * U := mul_comm _ _
  · intro T hT hTB
    have hfar := far_of_notMem_windowExcludedHeights hv0 hT₁ hT₂ hU0 hT hTB
    refine (hcorr v W T hW0 hfar).trans ?_
    have hT0 : 0 < T := by linarith [hT.1]
    have hlog : Real.log (|T| + 3) ≤ y ^ 3 := by
      rw [hL, abs_of_pos hT0]
      exact Real.log_le_log (by linarith) (by linarith [hT.2])
    have hvW : v ^ 2 + 1 / W ≤ 2 / y ^ 4 := by
      rw [hv, hW]
      have : 1 / y ^ 6 ≤ 1 / y ^ 4 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hy1 (by norm_num))
      have : (1 / y ^ 2) ^ 2 = 1 / y ^ 4 := by ring
      have : 2 / y ^ 4 = 1 / y ^ 4 + 1 / y ^ 4 := by ring
      linarith
    calc C * (v ^ 2 + 1 / W) * Real.log (|T| + 3) ≤ C * (2 / y ^ 4) * y ^ 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hvW hC) hlog
            (Real.log_nonneg (by linarith [abs_nonneg T])) (by positivity)
      _ = 2 * C / y := by field_simp
      _ ≤ η := h2

end Sparse

end GaloisForLFunctions.SquareRootThreshold
