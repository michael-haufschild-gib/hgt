import GaloisForLFunctions.ArithmeticCriticalityTheory.RestrictedWeilGroundEnergyCriticalAtInfinity
import GaloisForLFunctions.RHTower.SuzukiSmallApertureTheoremOneFour
import GaloisForLFunctions.RHTower.SuzukiOriginRemainderFirstJet

/-!
# The window gauge reproduces Suzuki's main term

For a plateau gauge `M` equal to `1` on `[−r, r]` and vanishing outside `(−R, R)`, `2R < log 2`, the
ground-state representation in the gauge reads `Q(F) = J_M(F) + ∫ F² M(−𝒲M)` with a nonnegative jump
energy, and the potential is at least `−log(2R) − (3/2)R − (γ + log π)`: the window edge is felt only
through the killing `N(R − x) + N(R + x) ≥ −log(2R)`. The odd pole moment costs at most `4R³ ∫ F²`.
With the window floor `w(R) = −log(2R) − (3/2)R − (γ + log π) − 4R³`:

* **Coercivity on every short window** (`fullZeroForm_ge_windowFloor`): `Ẑ(F) ≥ w(R) ∫ F²` for real
  `F ∈ C²_c` vanishing outside `[−r, r]`, `r < R`.
* **The ground-energy floor** (`windowFloor_le_ccmRestrictedWeilGroundEnergy_self`): the restricted
  Weil ground energy satisfies `μ(A) ≥ w(A)` for every aperture `2A < log 2`.
* **Suzuki's main term** (`windowFloor_eq_suzukiMainTerm`): `w(A)` is exactly Suzuki's small-aperture
  main term `log(1/A) + μ₁ − log(2π) + ψ(2) − 1` with the limiting log ground energy `μ₁` removed,
  minus `(3/2)A + 4A³`. Together with Suzuki's asymptotic
  (`exists_ccmRestrictedWeilGroundEnergy_sub_windowFloor_le`):
  `0 ≤ μ(A) − w(A) ≤ μ₁ + C A` for small `A`.

The gauge potential carries the whole logarithmic term and every arithmetic constant of the
small-aperture asymptotic (`log 2π`, `γ`); the discarded jump energy of the gauge is what remains,
the constant `μ₁ > 0` of the limiting log operator.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The window floor `w(R) = −log(2R) − (3/2)R − (γ + log π) − 4R³`. -/
def windowFloor (R : ℝ) : ℝ := -Real.log (2 * R) - 3 / 2 * R - 2 * archConstantReal - 4 * R ^ 3

/-- **Coercivity on every short window.** -/
theorem fullZeroForm_ge_windowFloor {F : ℝ → ℝ} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hR : 2 * R < Real.log 2) (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hsupp : ∀ x, r < |x| → F x = 0) :
    windowFloor R * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  have hR0 : 0 < R := by linarith
  have hR2 : R ≤ 2 := by linarith [Real.log_two_lt_d9]
  set δ := R - r with hδdef
  have hδ : 0 < δ := by linarith
  set M := plateauGauge R δ with hMdef
  have hMd : ContDiff ℝ 2 M := contDiff_plateauGauge R δ
  have hMcs : HasCompactSupport M := hasCompactSupport_plateauGauge hδ
  have hnn : ∀ y, 0 ≤ M y := plateauGauge_nonneg R δ
  have hle : ∀ y, M y ≤ 1 := plateauGauge_le_one R δ
  have hzero : ∀ y, R ≤ |y| → M y = 0 := fun y hy => plateauGauge_eq_zero hδ hy
  have hFM : ∀ x, F x ≠ 0 → M x = 1 := fun x hx => by
    refine plateauGauge_eq_one hδ ?_
    by_contra h
    exact hx (hsupp x (by have := not_le.mp h; linarith))
  have hFx : ∀ x, F x ≠ 0 → |x| < R := fun x hx => by
    by_contra h
    exact hx (by
      have := hzero x (not_lt.mp h)
      rw [hFM x hx] at this
      norm_num at this)
  obtain ⟨K, -, hK⟩ := exists_lipschitz_bound_of_compactSupport (hMd.of_le (by norm_num)) hMcs
  have hLip : ∀ a b, |M a - M b| ≤ K * |a - b| := fun a b => hK b a
  have hC12 := markovEnergy_eq_gauge_window hF hFc hMd hMcs hle hnn hzero hFM
  have hJ := signedJumpEnergy_nonneg_of_nonneg (F := F) hnn
  have hdec8 : ∀ y, |M y| ≤ Real.exp (8 * |R|) * Real.exp (-(8 * |y|)) := by
    intro y
    by_cases hy : |y| < R
    · rw [abs_of_nonneg (hnn y), ← Real.exp_add]
      exact (hle y).trans (Real.one_le_exp (by nlinarith [le_abs_self R]))
    · rw [hzero y (not_lt.mp hy), abs_zero]
      positivity
  have hg : Continuous fun x => -poleFreeWeilOperator M x :=
    (continuous_poleFreeWeilOperator hMd.continuous hLip hdec8).neg
  obtain ⟨V, hVdef⟩ : ∃ V, V = -Real.log (2 * R) - 3 / 2 * R - 2 * archConstantReal := ⟨_, rfl⟩
  have hF2 : Integrable fun x => F x ^ 2 :=
    (hF.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hpot : V * ∫ x, F x ^ 2 ≤ ∫ x, F x ^ 2 * M x * -poleFreeWeilOperator M x := by
    rw [← integral_const_mul]
    refine integral_mono (hF2.const_mul V) ((((hF.continuous.pow 2).mul hMd.continuous).mul
      hg).integrable_of_hasCompactSupport ((hasCompactSupport_sq hFc).mul_right.mul_right)) fun x => ?_
    by_cases h : F x = 0
    · simp [h]
    · have hW := neg_poleFreeWeilOperator_ge hMd.continuous hLip hle hzero hR (hFx x h) (hFM x h)
      rw [hFM x h, mul_one]
      nlinarith [sq_nonneg (F x)]
  have hS := sq_oddPoleMoment_le hR0.le hR2 hF.continuous hFc hMd.continuous hMcs hnn hle hzero hFM
  have hE := sq_nonneg (evenPoleMoment F)
  have hW : windowFloor R * (∫ x, F x ^ 2) = V * (∫ x, F x ^ 2) - 4 * R ^ 3 * ∫ x, F x ^ 2 := by
    rw [hVdef]; unfold windowFloor; ring
  unfold fullZeroForm
  rw [hC12, hW]
  linarith

/-- The window floor for complex tests. -/
theorem zetaZeroConfig_re_W_ge_windowFloor {g : ℝ → ℂ} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hR : 2 * R < Real.log 2) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hzero : ∀ x, r < |x| → g x = 0) :
    windowFloor R * ∫ x, ‖g x‖ ^ 2 ≤ (zetaZeroConfig.W g g).re := by
  have hre : ContDiff ℝ 2 fun u => (g u).re := Complex.reCLM.contDiff.comp hg
  have him : ContDiff ℝ 2 fun u => (g u).im := Complex.imCLM.contDiff.comp hg
  have hrec : HasCompactSupport fun u => (g u).re := hgc.comp_left Complex.zero_re
  have himc : HasCompactSupport fun u => (g u).im := hgc.comp_left Complex.zero_im
  have h1 := fullZeroForm_ge_windowFloor hr hrR hR hre hrec fun x hx => by simp [hzero x hx]
  have h2 := fullZeroForm_ge_windowFloor hr hrR hR him himc fun x hx => by simp [hzero x hx]
  have hsplit := GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im
    hg hgc
  have i1 : Integrable fun x => (g x).re ^ 2 :=
    (hre.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hrec)
  have i2 : Integrable fun x => (g x).im ^ 2 :=
    (him.continuous.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq himc)
  have hnorm : (∫ x, ‖g x‖ ^ 2) = (∫ x, (g x).re ^ 2) + ∫ x, (g x).im ^ 2 := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hsplit, hnorm, mul_add]
  linarith

/-! ### The ground-energy floor -/

/-- `μ(A) ≥ w(R)` for every `R ∈ (A, (log 2)/2)`. -/
theorem windowFloor_le_ccmRestrictedWeilGroundEnergy {A : SuzukiPositiveAperture} {R : ℝ}
    (hAR : A.1 < R) (hR : 2 * R < Real.log 2) : windowFloor R ≤ ccmRestrictedWeilGroundEnergy A := by
  rw [← suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  refine (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).2 ?_
  rintro q ⟨u, hu, rfl⟩
  have hmass : suzukiWeilIntervalFormMass A u.toCCMFormVector = ∫ x, ‖u x‖ ^ 2 := by
    unfold suzukiWeilIntervalFormMass
    rw [norm_suzukiWeilIntervalFormEmbedding, norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector]
  have hpos : 0 < suzukiWeilIntervalFormMass A u.toCCMFormVector := pow_pos (norm_pos_iff.mpr hu) 2
  unfold suzukiWeilIntervalFormRayleigh
  rw [le_div_iff₀ hpos, ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil, hmass]
  have hzero : ∀ x, A.1 < |x| → u x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := u.tsupport_subset h
      exact absurd (abs_lt.mpr ⟨this.1, this.2⟩) (not_lt.mpr hx.le)
  exact zetaZeroConfig_re_W_ge_windowFloor A.2.le hAR hR
    (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) u.hasCompactSupport hzero

/-- **The ground-energy floor**: `μ(A) ≥ w(A)` for every aperture `2A < log 2`. -/
theorem windowFloor_le_ccmRestrictedWeilGroundEnergy_self {A : SuzukiPositiveAperture}
    (hA : 2 * A.1 < Real.log 2) : windowFloor A.1 ≤ ccmRestrictedWeilGroundEnergy A := by
  have hA0 := A.2
  have hlog : ContinuousAt (fun R : ℝ => Real.log (2 * R)) A.1 :=
    (Real.continuousAt_log (by positivity)).comp (continuous_const.mul continuous_id).continuousAt
  have hcont : ContinuousAt windowFloor A.1 := by
    show ContinuousAt (fun R => -Real.log (2 * R) - 3 / 2 * R - 2 * archConstantReal - 4 * R ^ 3) A.1
    exact ((hlog.neg.sub (continuousAt_const.mul continuousAt_id)).sub continuousAt_const).sub
      (continuousAt_const.mul (continuousAt_id.pow 3))
  refine le_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi A.1))) ?_
  filter_upwards [Ioo_mem_nhdsGT (show A.1 < Real.log 2 / 2 by linarith)] with R hR
  exact windowFloor_le_ccmRestrictedWeilGroundEnergy hR.1 (by linarith [hR.2])

/-! ### Comparison with Suzuki's asymptotic -/

/-- **Suzuki's main term**: `w(A) = log(1/A) − log(2π) + ψ(2) − 1 − (3/2)A − 4A³`, i.e. the
small-aperture main term without the limiting log ground energy. -/
theorem windowFloor_eq_suzukiMainTerm {A : ℝ} (hA : 0 < A) :
    windowFloor A = Real.log (1 / A) - Real.log (2 * Real.pi) + (Complex.digamma (2 : ℂ)).re - 1 -
      3 / 2 * A - 4 * A ^ 3 := by
  rw [GaloisForLFunctions.RHTower.digamma_two_re]
  unfold windowFloor archConstantReal
  rw [Real.log_mul two_ne_zero hA.ne', Real.log_mul two_ne_zero Real.pi_ne_zero, one_div,
    Real.log_inv]
  ring

/-- **The gap is the limiting log ground energy**: `0 ≤ μ(A) − w(A) ≤ μ₁ + C A` for small `A`. -/
theorem exists_ccmRestrictedWeilGroundEnergy_sub_windowFloor_le :
    ∃ δ C : ℝ, 0 < δ ∧ ∀ A : SuzukiPositiveAperture, A.1 < δ →
      0 ≤ ccmRestrictedWeilGroundEnergy A - windowFloor A.1 ∧
        ccmRestrictedWeilGroundEnergy A - windowFloor A.1 ≤
          suzukiLimitingLogGroundEnergy + C * A.1 := by
  obtain ⟨δ, hδ, hS⟩ := exists_suzukiSmallAperture_full_theorem_one_four
  refine ⟨min δ (min 1 (Real.log 2 / 2)), 2 * GaloisForLFunctions.RHTower.suzukiOriginCurvatureUnitBound + 3 / 2 + 4,
    lt_min hδ (lt_min one_pos (by have := Real.log_pos one_lt_two; positivity)), fun A hA => ?_⟩
  have hAδ : A.1 < δ := lt_of_lt_of_le hA (min_le_left _ _)
  have hA1 : A.1 < 1 := lt_of_lt_of_le hA ((min_le_right _ _).trans (min_le_left _ _))
  have hAl : A.1 < Real.log 2 / 2 := lt_of_lt_of_le hA ((min_le_right _ _).trans (min_le_right _ _))
  have hA0 := A.2
  obtain ⟨-, habs, -⟩ := hS A hAδ
  rw [suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy] at habs
  have hfl := windowFloor_le_ccmRestrictedWeilGroundEnergy_self (A := A) (by linarith)
  have hmain := windowFloor_eq_suzukiMainTerm hA0
  have hcube : A.1 ^ 3 ≤ A.1 := by
    have h2 : A.1 ^ 2 ≤ 1 := by nlinarith
    nlinarith
  refine ⟨by linarith, ?_⟩
  have := (abs_le.mp habs).2
  rw [hmain]
  nlinarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
