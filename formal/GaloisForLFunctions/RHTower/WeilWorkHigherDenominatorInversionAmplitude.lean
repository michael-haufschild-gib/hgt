import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorMovingKernel
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorNonstationary
import GaloisForLFunctions.HTGeometry.CompactTestTransformOrder

/-!
# Actual test amplitudes on the inversion path

The product-rule jets and their uniform bounds are derived from compactness and
the normalized Bessel estimates. They impose no new condition on the cubic datum.
-/

noncomputable section

open Complex Set RHTower.BesselKZero
open GaloisForLFunctions.HTGeometry
open scoped ContDiff

namespace RHTower.WeilHigherDenominator

def inversionTestWeight (φ : ℝ → ℂ) (y x : ℝ) : ℂ :=
  φ x * (inversionBoundaryWeight y x : ℂ)

def inversionTestWeightD (φ : ℝ → ℂ) (y x : ℝ) : ℂ :=
  deriv φ x * (inversionBoundaryWeight y x : ℂ) +
    φ x * (inversionBoundaryWeightD y x : ℂ)

def inversionTestWeightDD (φ : ℝ → ℂ) (y x : ℝ) : ℂ :=
  deriv (deriv φ) x * (inversionBoundaryWeight y x : ℂ) +
    2 * deriv φ x * (inversionBoundaryWeightD y x : ℂ) +
    φ x * (inversionBoundaryWeightDD y x : ℂ)

def inversionAmplitude (φ : ℝ → ℂ) (k y x : ℝ) : ℂ :=
  inversionTestWeight φ y x * (scaledKLog (inversionBoundaryScale y) k y x : ℂ)

def inversionAmplitudeD (φ : ℝ → ℂ) (k y x : ℝ) : ℂ :=
  inversionTestWeightD φ y x * (scaledKLog (inversionBoundaryScale y) k y x : ℂ) +
    inversionTestWeight φ y x *
      (scaledKLogD (inversionBoundaryScale y) (inversionBoundaryScaleD y) k y x : ℂ)

def inversionAmplitudeDD (φ : ℝ → ℂ) (k y x : ℝ) : ℂ :=
  inversionTestWeightDD φ y x * (scaledKLog (inversionBoundaryScale y) k y x : ℂ) +
    2 * inversionTestWeightD φ y x *
      (scaledKLogD (inversionBoundaryScale y) (inversionBoundaryScaleD y) k y x : ℂ) +
    inversionTestWeight φ y x *
      (scaledKLogDD (inversionBoundaryScale y) (inversionBoundaryScaleD y)
        (inversionBoundaryScaleDD y) k y x : ℂ)

theorem hasDerivAt_inversionTestWeight {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (inversionTestWeight φ y) (inversionTestWeightD φ y x) x := by
  exact ((hφ.differentiable (by simp) x).hasDerivAt.mul
    (hasDerivAt_inversionBoundaryWeight hx y).ofReal_comp).congr_deriv (by
      dsimp [inversionTestWeightD])

theorem hasDerivAt_inversionTestWeightD {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {x : ℝ} (hx : 0 < x) (y : ℝ) :
    HasDerivAt (inversionTestWeightD φ y) (inversionTestWeightDD φ y x) x := by
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  refine (((hφ'.differentiable (by simp) x).hasDerivAt.mul
    (hasDerivAt_inversionBoundaryWeight hx y).ofReal_comp).add
    ((hφ.differentiable (by simp) x).hasDerivAt.mul
      (hasDerivAt_inversionBoundaryWeightD hx y).ofReal_comp)).congr_deriv ?_
  dsimp [inversionTestWeightDD]
  ring

theorem hasDerivAt_inversionAmplitude {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {k y x : ℝ} (hk : 0 < k) (hy : 0 < y) (hx : 0 < x) :
    HasDerivAt (inversionAmplitude φ k y) (inversionAmplitudeD φ k y x) x := by
  exact ((hasDerivAt_inversionTestWeight hφ hx y).mul
    (hasDerivAt_scaledKLog hk hy (inversionBoundaryScale_pos hx y)
      (hasDerivAt_inversionBoundaryScale hx y)).ofReal_comp).congr_deriv (by
        dsimp [inversionAmplitudeD])

theorem hasDerivAt_inversionAmplitudeD {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {k y x : ℝ} (hk : 0 < k) (hy : 0 < y) (hx : 0 < x) :
    HasDerivAt (inversionAmplitudeD φ k y) (inversionAmplitudeDD φ k y x) x := by
  have hF := (hasDerivAt_scaledKLog hk hy (inversionBoundaryScale_pos hx y)
    (hasDerivAt_inversionBoundaryScale hx y)).ofReal_comp
  have hF' := (hasDerivAt_scaledKLogD hk hy (inversionBoundaryScale_pos hx y)
    (hasDerivAt_inversionBoundaryScale hx y) (hasDerivAt_inversionBoundaryScaleD hx y)).ofReal_comp
  refine (((hasDerivAt_inversionTestWeightD hφ hx y).mul hF).add
    ((hasDerivAt_inversionTestWeight hφ hx y).mul hF')).congr_deriv ?_
  dsimp [inversionAmplitudeDD]
  ring

theorem continuousOn_inversionAmplitudeDD {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {k y : ℝ} (hk : 0 < k) (hy : 0 < y) :
    ContinuousOn (inversionAmplitudeDD φ k y) (Ioi 0) := by
  have hd : ContinuousOn (fun x : ℝ => x ^ 2 + y ^ 2) (Ioi 0) := by fun_prop
  have hd0 : ∀ x ∈ Ioi (0 : ℝ), x ^ 2 + y ^ 2 ≠ 0 :=
    fun x hx => (inversionBoundaryDenom_pos hx y).ne'
  have hp (r : ℝ) : ContinuousOn (fun x : ℝ => (x ^ 2 + y ^ 2) ^ r) (Ioi 0) :=
    hd.rpow_const fun x hx => Or.inl (hd0 x hx)
  have hw : ContinuousOn (inversionBoundaryWeight y) (Ioi 0) := hp _
  have hw' : ContinuousOn (inversionBoundaryWeightD y) (Ioi 0) :=
    continuousOn_id.neg.mul (hp _)
  have hw'' : ContinuousOn (inversionBoundaryWeightDD y) (Ioi 0) :=
    (hp _).neg.add ((continuousOn_const.mul (continuousOn_id.pow 2)).mul (hp _))
  have hc : ContinuousOn (inversionBoundaryScale y) (Ioi 0) := continuousOn_const.div hd hd0
  have hc' : ContinuousOn (inversionBoundaryScaleD y) (Ioi 0) :=
    (continuousOn_const.mul continuousOn_id).div (hd.pow 2) fun x hx => pow_ne_zero 2 (hd0 x hx)
  have hc'' : ContinuousOn (inversionBoundaryScaleDD y) (Ioi 0) :=
    (continuousOn_const.mul ((continuousOn_const.mul (continuousOn_id.pow 2)).sub
      continuousOn_const)).div (hd.pow 3) fun x hx => pow_ne_zero 3 (hd0 x hx)
  have hK (j : ℕ) : ContinuousOn (fun x => kMoment j (k * y * inversionBoundaryScale y x))
      (Ioi 0) := (continuousOn_kMoment j).comp (continuousOn_const.mul hc)
        fun x hx => mul_pos (mul_pos hk hy) (inversionBoundaryScale_pos hx y)
  have hF : ContinuousOn (scaledKLog (inversionBoundaryScale y) k y) (Ioi 0) :=
    (hK 0).div_const _
  have hF' : ContinuousOn (scaledKLogD (inversionBoundaryScale y)
      (inversionBoundaryScaleD y) k y) (Ioi 0) :=
    (((continuousOn_const.mul hc').neg).mul (hK 1)).div_const _
  have hF'' : ContinuousOn (scaledKLogDD (inversionBoundaryScale y)
      (inversionBoundaryScaleD y) (inversionBoundaryScaleDD y) k y) (Ioi 0) :=
    ((((continuousOn_const.mul hc').pow 2).mul (hK 2)).sub
      ((continuousOn_const.mul hc'').mul (hK 1))).div_const _
  have hφ' : Continuous (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2.continuous
  have hφ'' : Continuous (deriv (deriv φ)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hφ).2).2.continuous
  have hH : ContinuousOn (inversionTestWeight φ y) (Ioi 0) :=
    hφ.continuous.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hw)
  have hH' : ContinuousOn (inversionTestWeightD φ y) (Ioi 0) :=
    (hφ'.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hw)).add
      (hφ.continuous.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hw'))
  have hH'' : ContinuousOn (inversionTestWeightDD φ y) (Ioi 0) :=
    ((hφ''.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hw)).add
      ((continuousOn_const.mul hφ'.continuousOn).mul
        (Complex.continuous_ofReal.comp_continuousOn hw'))).add
      (hφ.continuous.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hw''))
  exact ((hH''.mul (Complex.continuous_ofReal.comp_continuousOn hF)).add
    ((continuousOn_const.mul hH').mul (Complex.continuous_ofReal.comp_continuousOn hF'))).add
      (hH.mul (Complex.continuous_ofReal.comp_continuousOn hF''))

/-- Endpoint vanishing propagates through the actual amplitude and its first derivative. -/
theorem inversionAmplitude_endpoint {φ : ℝ → ℂ} {x : ℝ} (hx : x ∉ tsupport φ) (k y : ℝ) :
    inversionAmplitude φ k y x = 0 ∧ inversionAmplitudeD φ k y x = 0 := by
  have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have h1 : deriv φ x = 0 := deriv_of_notMem_tsupport hx
  simp [inversionAmplitude, inversionAmplitudeD, inversionTestWeight, inversionTestWeightD, h0, h1]

/-- A common bound for the three test, geometry and kernel jets pays all product terms. -/
theorem norm_inversionAmplitude_jets_le {φ : ℝ → ℂ} {k y x D G B : ℝ}
    (hD : 0 ≤ D) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hφ : ‖φ x‖ ≤ D) (hφ' : ‖deriv φ x‖ ≤ D) (hφ'' : ‖deriv (deriv φ) x‖ ≤ D)
    (hw : |inversionBoundaryWeight y x| ≤ G) (hw' : |inversionBoundaryWeightD y x| ≤ G)
    (hw'' : |inversionBoundaryWeightDD y x| ≤ G)
    (hF : |scaledKLog (inversionBoundaryScale y) k y x| ≤ B)
    (hF' : |scaledKLogD (inversionBoundaryScale y) (inversionBoundaryScaleD y) k y x| ≤ B)
    (hF'' : |scaledKLogDD (inversionBoundaryScale y) (inversionBoundaryScaleD y)
      (inversionBoundaryScaleDD y) k y x| ≤ B) :
    ‖inversionAmplitude φ k y x‖ ≤ 9 * D * G * B ∧
    ‖inversionAmplitudeD φ k y x‖ ≤ 9 * D * G * B ∧
    ‖inversionAmplitudeDD φ k y x‖ ≤ 9 * D * G * B := by
  have hH : ‖inversionTestWeight φ y x‖ ≤ D * G := by
    simpa [inversionTestWeight, norm_mul, Complex.norm_real] using mul_le_mul hφ hw
      (abs_nonneg _) hD
  have hH' : ‖inversionTestWeightD φ y x‖ ≤ 2 * D * G := by
    calc
      _ ≤ ‖deriv φ x‖ * |inversionBoundaryWeight y x| +
          ‖φ x‖ * |inversionBoundaryWeightD y x| := by
        simpa only [inversionTestWeightD, norm_mul, Complex.norm_real, Real.norm_eq_abs] using norm_add_le
          (deriv φ x * (inversionBoundaryWeight y x : ℂ))
          (φ x * (inversionBoundaryWeightD y x : ℂ))
      _ ≤ D * G + D * G := by gcongr
      _ = _ := by ring
  have hH'' : ‖inversionTestWeightDD φ y x‖ ≤ 4 * D * G := by
    calc
      _ ≤ ‖deriv (deriv φ) x‖ * |inversionBoundaryWeight y x| +
          2 * ‖deriv φ x‖ * |inversionBoundaryWeightD y x| +
          ‖φ x‖ * |inversionBoundaryWeightDD y x| := by
        unfold inversionTestWeightDD
        calc
          _ ≤ ‖deriv (deriv φ) x * (inversionBoundaryWeight y x : ℂ) +
            2 * deriv φ x * (inversionBoundaryWeightD y x : ℂ)‖ +
            ‖φ x * (inversionBoundaryWeightDD y x : ℂ)‖ := norm_add_le _ _
          _ ≤ _ := by
            have h := norm_add_le (deriv (deriv φ) x * (inversionBoundaryWeight y x : ℂ))
              (2 * deriv φ x * (inversionBoundaryWeightD y x : ℂ))
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat] at *
            linarith
      _ ≤ D * G + 2 * D * G + D * G := by gcongr
      _ = _ := by ring
  have h0 : ‖inversionAmplitude φ k y x‖ ≤ D * G * B := by
    unfold inversionAmplitude
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hH hF (abs_nonneg _) (mul_nonneg hD hG)
  have h1 : ‖inversionAmplitudeD φ k y x‖ ≤ 3 * D * G * B := by
    unfold inversionAmplitudeD
    calc
      _ ≤ ‖inversionTestWeightD φ y x‖ * |scaledKLog (inversionBoundaryScale y) k y x| +
          ‖inversionTestWeight φ y x‖ *
            |scaledKLogD (inversionBoundaryScale y) (inversionBoundaryScaleD y) k y x| := by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using norm_add_le
          (inversionTestWeightD φ y x * (scaledKLog (inversionBoundaryScale y) k y x : ℂ))
          (inversionTestWeight φ y x *
            (scaledKLogD (inversionBoundaryScale y) (inversionBoundaryScaleD y) k y x : ℂ))
      _ ≤ 2 * D * G * B + D * G * B := by gcongr
      _ = _ := by ring
  have h2 : ‖inversionAmplitudeDD φ k y x‖ ≤ 9 * D * G * B := by
    unfold inversionAmplitudeDD
    have h₁ := norm_add_le
      (inversionTestWeightDD φ y x * (scaledKLog (inversionBoundaryScale y) k y x : ℂ))
      (2 * inversionTestWeightD φ y x *
        (scaledKLogD (inversionBoundaryScale y) (inversionBoundaryScaleD y) k y x : ℂ))
    have h₂ := norm_add_le
      (inversionTestWeightDD φ y x * (scaledKLog (inversionBoundaryScale y) k y x : ℂ) +
        2 * inversionTestWeightD φ y x *
          (scaledKLogD (inversionBoundaryScale y) (inversionBoundaryScaleD y) k y x : ℂ))
      (inversionTestWeight φ y x * (scaledKLogDD (inversionBoundaryScale y)
        (inversionBoundaryScaleD y) (inversionBoundaryScaleDD y) k y x : ℂ))
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat] at h₁ h₂
    have h₃ : ‖inversionTestWeightDD φ y x‖ * |scaledKLog (inversionBoundaryScale y) k y x| ≤
        4 * D * G * B := by gcongr
    have h₄ : 2 * ‖inversionTestWeightD φ y x‖ *
        |scaledKLogD (inversionBoundaryScale y) (inversionBoundaryScaleD y) k y x| ≤
        2 * (2 * D * G) * B := by gcongr
    have h₅ : ‖inversionTestWeight φ y x‖ * |scaledKLogDD (inversionBoundaryScale y)
        (inversionBoundaryScaleD y) (inversionBoundaryScaleDD y) k y x| ≤ D * G * B := by gcongr
    linarith
  exact ⟨h0.trans (by nlinarith [mul_nonneg (mul_nonneg hD hG) hB]),
    h1.trans (by nlinarith [mul_nonneg (mul_nonneg hD hG) hB]), h2⟩


private lemma inversionGeometry_bounds {x y G : ℝ}
    (h : inversionBoundaryJetBudget y x ≤ G) :
    |inversionBoundaryWeight y x| ≤ G ∧ |inversionBoundaryWeightD y x| ≤ G ∧
    |inversionBoundaryWeightDD y x| ≤ G ∧ |1 / inversionBoundarySpeed y x| ≤ G ∧
    |inversionBoundarySpeedD y x| ≤ G ∧ |inversionBoundarySpeedDD y x| ≤ G ∧
    |inversionBoundaryScaleD y x / inversionBoundaryScale y x| ≤ G ∧
    |inversionBoundaryScaleDD y x / inversionBoundaryScale y x| ≤ G ∧
    |1 / inversionBoundaryScale y x| ≤ G := by
  have h0 := abs_nonneg (inversionBoundaryWeight y x)
  have h1 := abs_nonneg (inversionBoundaryWeightD y x)
  have h2 := abs_nonneg (inversionBoundaryWeightDD y x)
  have h3 := abs_nonneg (1 / inversionBoundarySpeed y x)
  have h4 := abs_nonneg (inversionBoundarySpeedD y x)
  have h5 := abs_nonneg (inversionBoundarySpeedDD y x)
  have h6 := abs_nonneg (inversionBoundaryScaleD y x / inversionBoundaryScale y x)
  have h7 := abs_nonneg (inversionBoundaryScaleDD y x / inversionBoundaryScale y x)
  have h8 := abs_nonneg (1 / inversionBoundaryScale y x)
  unfold inversionBoundaryJetBudget at h
  and_intros <;> linarith

/-- All actual amplitude and phase jets admit common bounds, uniformly in every `k ≥ 1`. -/
theorem exists_inversionAmplitude_jets_bound {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {a b : ℝ} (ha : 0 < a) :
    ∃ δ M G : ℝ, 0 < δ ∧ 0 ≤ M ∧ 0 < G ∧ δ ≤ a / 2 ∧
      ∀ y ∈ Ioc 0 δ, Real.log y ≤ -1 → ∀ k : ℝ, 1 ≤ k → ∀ x ∈ Icc a b,
        ‖inversionAmplitude φ k y x‖ ≤ M ∧ ‖inversionAmplitudeD φ k y x‖ ≤ M ∧
        ‖inversionAmplitudeDD φ k y x‖ ≤ M ∧
        |1 / inversionBoundarySpeed y x| ≤ G ∧ |inversionBoundarySpeedD y x| ≤ G ∧
        |inversionBoundarySpeedDD y x| ≤ G := by
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  have hφ'' := (contDiff_infty_iff_deriv.mp hφ').2
  obtain ⟨D₀, hD₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (((hφ.continuous.norm.add hφ'.continuous.norm).add hφ''.continuous.norm).continuousOn
      (s := Icc a b))
  let D := max D₀ 1
  have hD : 0 ≤ D := le_trans zero_le_one (le_max_right _ _)
  have htest : ∀ x ∈ Icc a b,
      ‖φ x‖ ≤ D ∧ ‖deriv φ x‖ ≤ D ∧ ‖deriv (deriv φ) x‖ ≤ D := by
    intro x hx
    have h := (le_abs_self _).trans ((hD₀ x hx).trans (le_max_left D₀ 1))
    change ‖φ x‖ + ‖deriv φ x‖ + ‖deriv (deriv φ) x‖ ≤ D at h
    have h0 := norm_nonneg (φ x)
    have h1 := norm_nonneg (deriv φ x)
    have h2 := norm_nonneg (deriv (deriv φ) x)
    exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨G, hG, hgeom⟩ := exists_inversionBoundaryJetBudget_bound (b := b) ha
  let c₀ := 1 / G
  have hc₀ : 0 < c₀ := by positivity
  have hk01 := kMoment_nonneg 0 1
  let B₂ := 2 + 2 * Real.exp 1 * kMoment 0 1
  have hB₂ : 0 ≤ B₂ := by dsimp [B₂]; positivity
  let B₀ := kMoment 0 1 + |Real.log c₀| + 1
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  let B := B₀ + 2 * G + G ^ 2 * B₂
  have hB : 0 ≤ B := by positivity
  refine ⟨min (a / 2) G, 9 * D * G * B, G, lt_min (by positivity) hG,
    by positivity, hG, min_le_left _ _, ?_⟩
  intro y hy hlog k hk x hx
  have hy0 : 0 < y := hy.1
  have hyG : y ≤ G := hy.2.trans (min_le_right _ _)
  have hyA : y ≤ a / 2 := hy.2.trans (min_le_left _ _)
  have hx0 := ha.trans_le hx.1
  obtain ⟨hw, hw', hw'', hv, hv', hv'', hc', hc'', hcInv⟩ :=
    inversionGeometry_bounds (hgeom x hx y ⟨hy0.le, hyA⟩)
  have hc : 0 < inversionBoundaryScale y x := inversionBoundaryScale_pos hx0 y
  have hbase : c₀ ≤ inversionBoundaryScale y x := by
    have h := (div_le_iff₀ hc).mp ((le_abs_self _).trans hcInv)
    exact (div_le_iff₀ hG).mpr (by simpa only [mul_comm] using h)
  have hsmall : c₀ * y ≤ 1 := by
    dsimp [c₀]
    rw [one_div_mul_eq_div]
    exact (div_le_one hG).mpr hyG
  have hF := abs_scaledKLog_le hc₀ hy0 hk hbase hsmall hlog
  have hk0 := lt_of_lt_of_le zero_lt_one hk
  have hF' := (abs_scaledKLogD_le hk0 hy0 hc hlog).trans hc'
  have hF'' := abs_scaledKLogDD_le (c' := inversionBoundaryScaleD y)
    (c'' := inversionBoundaryScaleDD y) hk0 hy0 hc hlog
  have hsq : (inversionBoundaryScaleD y x / inversionBoundaryScale y x) ^ 2 ≤ G ^ 2 := by
    calc
      _ = |inversionBoundaryScaleD y x / inversionBoundaryScale y x| ^ 2 := (sq_abs _).symm
      _ ≤ G ^ 2 := by gcongr
  have hF₂ : |scaledKLogDD (inversionBoundaryScale y) (inversionBoundaryScaleD y)
      (inversionBoundaryScaleDD y) k y x| ≤ G ^ 2 * B₂ + G := by
    exact hF''.trans (add_le_add (mul_le_mul_of_nonneg_right hsq hB₂) hc'')
  have hB0 : B₀ ≤ B := by dsimp [B]; nlinarith [mul_nonneg (sq_nonneg G) hB₂]
  have hB1 : G ≤ B := by dsimp [B]; nlinarith [mul_nonneg (sq_nonneg G) hB₂]
  have hB2 : G ^ 2 * B₂ + G ≤ B := by dsimp [B]; linarith
  have ht := htest x hx
  obtain ⟨h0, h1, h2⟩ := norm_inversionAmplitude_jets_le hD hG.le hB ht.1 ht.2.1 ht.2.2
    hw hw' hw'' (hF.trans hB0) (hF'.trans hB1) (hF₂.trans hB2)
  exact ⟨h0, h1, h2, hv, hv', hv''⟩

end RHTower.WeilHigherDenominator
