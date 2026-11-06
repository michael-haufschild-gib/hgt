import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.SquareRootThreshold.ZetaSingleHeightPositivityAboveArchimedeanHorizon
import GaloisForLFunctions.SquareRootThreshold.AnExplicitClusterDetectorConstant

/-!
# Every short interval at large height contains a zero

**Theorem** (`exists_zero_near_of_onLine`). Let `0 < σ ≤ 1`, `|t| ≥ gapHeight σ`, and suppose every zero within
`exp (gapScale σ)` of `t` lies on the critical line. Then a zero has ordinate within `σ` of `t`.

The test is `s(u) = w(u/Y)`, `w = (1 − u²)₊^{5/2}`, of width `Y = gapScale σ`. At height `t` its Weil form is at least
`(log(1 + |t|/8) − E − 2S) Y ∫w²`, by the archimedean symbol. On the zero side, a zero at distance `|x| ≥ σ` costs at most
`(1 + |x|)⁻³` times `8 (400 ∫w)²/(σ⁴Y²)`, since the transform of `s` is `Y ŵ(Yz)`; the local count bounds the sum by
`5760 log(|t|+3)` times this constant. The factor `Y³` decides.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower Zeta23 GaloisForLFunctions.SquareRootThreshold

noncomputable section

/-- The scaled test of width `Y`. -/
def gapTest (Y u : ℝ) : ℝ := sinhTestWeight 1 (u / Y)

theorem gapTest_contDiff (Y : ℝ) : ContDiff ℝ 2 (gapTest Y) :=
  (sinhTestWeight_contDiff 1).comp (contDiff_id.div_const Y)

theorem gapTest_supp {Y : ℝ} (hY : 0 < Y) : ∀ u, gapTest Y u ≠ 0 → |u| ≤ Y := fun u hu => by
  have h := sinhTestWeight_supp (by norm_num : (0 : ℝ) ≤ 1) _ hu
  rw [abs_div, abs_of_pos hY, div_le_one hY] at h
  exact h

/-- The complex test. -/
def gapTestC (Y u : ℝ) : ℂ := (gapTest Y u : ℂ)

theorem gapTestC_contDiff (Y : ℝ) : ContDiff ℝ 2 (gapTestC Y) :=
  Complex.ofRealCLM.contDiff.comp (gapTest_contDiff Y)

theorem tsupport_gapTestC {Y : ℝ} (hY : 0 < Y) : tsupport (gapTestC Y) ⊆ Icc (-Y) Y := by
  refine tsupport_subset_of_support_subset_abs fun u hu => ?_
  refine gapTest_supp hY u fun h => hu ?_
  simp [gapTestC, h]

/-- The mass `m₁ = ∫w`. -/
def gapMass : ℝ := kernelMass 1

theorem gapMass_pos : 0 < gapMass := kernelMass_pos one_pos le_rfl

/-- The energy `m₃ = ∫w²`. -/
def gapEnergy : ℝ := ∫ u, ‖((sinhTestWeight 1 u : ℝ) : ℂ)‖ ^ 2

theorem gapEnergy_pos : 0 < gapEnergy := by
  have hc : Continuous fun u => ‖((sinhTestWeight 1 u : ℝ) : ℂ)‖ ^ 2 :=
    (Complex.continuous_ofReal.comp (sinhTestWeight_contDiff 1).continuous).norm.pow 2
  have hsc : HasCompactSupport fun u => ‖((sinhTestWeight 1 u : ℝ) : ℂ)‖ ^ 2 := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun u hu => ?_
    have hne : sinhTestWeight 1 u ≠ 0 := fun h => hu (by simp [h])
    exact abs_le.mp (sinhTestWeight_supp (by norm_num) u hne)
  have hint : Integrable fun u => ‖((sinhTestWeight 1 u : ℝ) : ℂ)‖ ^ 2 := hc.integrable_of_hasCompactSupport hsc
  refine (integral_pos_iff_support_of_nonneg (fun _ => sq_nonneg _) hint).2 ?_
  have hopen : IsOpen (Function.support fun u => ‖((sinhTestWeight 1 u : ℝ) : ℂ)‖ ^ 2) := hc.isOpen_support
  refine hopen.measure_pos volume ⟨0, ?_⟩
  simp only [Function.mem_support]
  have h0 : sinhTestWeight 1 0 ≠ 0 := by
    simp [sinhTestWeight]
  simp [h0]

theorem integral_gapTestC_sq {Y : ℝ} (hY : 0 < Y) : ∫ u, ‖gapTestC Y u‖ ^ 2 = Y * gapEnergy := by
  have h := Measure.integral_comp_div
    (fun v : ℝ => ‖((sinhTestWeight 1 v : ℝ) : ℂ)‖ ^ 2) Y
  simp only [gapEnergy, gapTestC, gapTest] at h ⊢
  rw [h, abs_of_pos hY]
  rfl

/-- The transform of the scaled test is a dilate of the transform of `w`. -/
theorem paperFT_gapTestC {Y : ℝ} (hY : 0 < Y) (z : ℂ) :
    paperFT (gapTestC Y) z = Y * paperFT (fun u => ((sinhTestWeight 1 u : ℝ) : ℂ)) ((Y : ℂ) * z) := by
  rw [paperFT_def, paperFT_def]
  have h := Measure.integral_comp_div
    (fun v : ℝ => ((sinhTestWeight 1 v : ℝ) : ℂ) * cexp (I * ((Y : ℂ) * z) * v)) Y
  simp only [abs_of_pos hY, Complex.real_smul] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [gapTestC, gapTest]
  congr 2
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  push_cast
  field_simp

/-- Decay of the transform of the scaled test. -/
theorem norm_paperFT_gapTestC_le {Y : ℝ} (hY : 0 < Y) (z : ℂ) :
    ‖paperFT (gapTestC Y) z‖ ≤ Y * (400 * gapMass) * Real.exp (Y * |z.im|) / (1 + Y * |z.re|) ^ 2 := by
  have hm := gapMass_pos
  have hq := norm_kernelQ_le_decay (b := 1) one_pos le_rfl ((Y : ℂ) * z)
  have hre : ((Y : ℂ) * z).re = Y * z.re := by simp
  have him : ((Y : ℂ) * z).im = Y * z.im := by simp
  rw [hre, him, abs_mul, abs_mul, abs_of_pos hY, one_pow, one_mul, mul_one] at hq
  have hmC : ((gapMass : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hK : paperFT (fun u => ((sinhTestWeight 1 u : ℝ) : ℂ)) ((Y : ℂ) * z) =
      (gapMass : ℂ) * kernelQ 1 ((Y : ℂ) * z) := by
    rw [kernelQ]
    change _ = (gapMass : ℂ) * (_ / (gapMass : ℂ))
    field_simp
  rw [paperFT_gapTestC hY, hK, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hY, abs_of_pos hm]
  have hD : 0 < (1 + Y * |z.re|) ^ 2 := by positivity
  calc
    Y * (gapMass * ‖kernelQ 1 ((Y : ℂ) * z)‖)
        ≤ Y * (gapMass * (Real.exp (Y * |z.im|) * 400 / (1 + Y * |z.re|) ^ 2)) := by
      gcongr
    _ = _ := by ring

/-- The weight comparison of the summand of a zero at distance `x ≥ σ`. -/
theorem one_add_pow_mul_le {σ Y x : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hY : 0 < Y) (hx : σ ≤ x) :
    (1 + x) ^ 3 * (Y ^ 4 * σ ^ 4) ≤ 8 * (1 + Y * x) ^ 4 := by
  have hx0 : 0 < x := hσ.trans_le hx
  have h1 : (1 + x) * σ ≤ 2 * x := by nlinarith only [hσ1, hx, hx0, hσ]
  have h2 : ((1 + x) * σ) ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  have h3 : σ * Y ^ 4 ≤ x * Y ^ 4 := mul_le_mul_of_nonneg_right hx (by positivity)
  have h4 : (Y * x) ^ 4 ≤ (1 + Y * x) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith only) 4
  have h5 : ((1 + x) * σ) ^ 3 * (σ * Y ^ 4) ≤ (2 * x) ^ 3 * (x * Y ^ 4) :=
    mul_le_mul h2 h3 (by positivity) (by positivity)
  calc
    (1 + x) ^ 3 * (Y ^ 4 * σ ^ 4) = ((1 + x) * σ) ^ 3 * (σ * Y ^ 4) := by ring
    _ ≤ (2 * x) ^ 3 * (x * Y ^ 4) := h5
    _ = 8 * (Y * x) ^ 4 := by ring
    _ ≤ _ := by linarith only [h4]

theorem one_add_pow_mul_exp_le {σ Y x : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hY : 0 < Y) (hx : Real.exp Y ≤ x) :
    (1 + x) ^ 3 * (Y ^ 4 * σ ^ 4) * Real.exp Y ≤ 8 * (1 + Y * x) ^ 4 := by
  have hE1 : 1 ≤ Real.exp Y := Real.one_le_exp hY.le
  have hx1 : 1 ≤ x := hE1.trans hx
  have hx0 : 0 < x := by linarith only [hx1]
  have h1 : 1 + x ≤ 2 * x := by linarith only [hx1]
  have h2 : (1 + x) ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  have hσ4 : σ ^ 4 ≤ 1 := pow_le_one₀ hσ.le hσ1
  have h3 : σ ^ 4 * Real.exp Y ≤ x := by
    calc
      σ ^ 4 * Real.exp Y ≤ 1 * Real.exp Y := mul_le_mul_of_nonneg_right hσ4 (Real.exp_pos _).le
      _ ≤ x := by rw [one_mul]; exact hx
  have h4 : (Y * x) ^ 4 ≤ (1 + Y * x) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith only) 4
  calc
    (1 + x) ^ 3 * (Y ^ 4 * σ ^ 4) * Real.exp Y = (1 + x) ^ 3 * (Y ^ 4 * (σ ^ 4 * Real.exp Y)) := by ring
    _ ≤ (2 * x) ^ 3 * (Y ^ 4 * x) :=
      mul_le_mul h2 (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity) (by positivity)
    _ = 8 * (Y * x) ^ 4 := by ring
    _ ≤ _ := by linarith only [h4]

/-- The constant `8 G/(σ⁴ Y²)`. -/
def gapWeight (σ Y : ℝ) : ℝ := 8 * (400 * gapMass) ^ 2 / (σ ^ 4 * Y ^ 2)

/-- **The cost of one zero** at distance at least `σ`. -/
theorem norm_Wsummand_gapTest_le {σ Y t : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hY : 0 < Y)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hfar : σ ≤ |ρ.im - t|)
    (hon : |ρ.im - t| ≤ Real.exp Y → ρ.re = 1 / 2) :
    ‖zetaZeroConfig.Wsummand (modulatedTest t (gapTest Y)) (modulatedTest t (gapTest Y)) ρ‖ ≤
      gapWeight σ Y * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |ρ.im - t|) ^ 3) := by
  obtain ⟨x, hx⟩ : ∃ x, x = |ρ.im - t| := ⟨_, rfl⟩
  rw [← hx] at hfar hon ⊢
  have hx0 : 0 < x := hσ.trans_le hfar
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hst := zetaZeroConfig.strip ρ hρ
  have hδ : |1 / 2 - ρ.re| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith only [hst.1, hst.2]
  have h1 := norm_paperFT_gapTestC_le hY (gammaOf ρ - t)
  have h2 := norm_paperFT_gapTestC_le hY (conj (gammaOf ρ) - t)
  have e1 : (gammaOf ρ - t).re = ρ.im - t := by simp [WeilEF.gammaOf_re]
  have e2 : (gammaOf ρ - t).im = 1 / 2 - ρ.re := by simp [WeilEF.gammaOf_im]
  have e3 : (conj (gammaOf ρ) - t).re = ρ.im - t := by simp [WeilEF.gammaOf_re]
  have e4 : |(conj (gammaOf ρ) - t).im| = |1 / 2 - ρ.re| := by
    simp only [Complex.sub_im, Complex.conj_im, Complex.ofReal_im, sub_zero, WeilEF.gammaOf_im, abs_neg]
  rw [e1, e2, ← hx] at h1
  rw [e3, e4, ← hx] at h2
  have hsum := Wsummand_modulatedTest zetaZeroConfig t (gapTest Y) ρ
  change _ = (zetaZeroConfig.mult ρ : ℂ) * paperFT (gapTestC Y) (gammaOf ρ - t) *
    conj (paperFT (gapTestC Y) (conj (gammaOf ρ) - t)) at hsum
  rw [hsum, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_natCast]
  obtain ⟨G, hG⟩ : ∃ G, G = 400 * gapMass := ⟨_, rfl⟩
  have hG0 : 0 < G := by rw [hG]; exact mul_pos (by norm_num) gapMass_pos
  rw [← hG] at h1 h2
  have hD : 0 < 1 + Y * x := by positivity
  have hD4 : 0 < (1 + Y * x) ^ 4 := by positivity
  have hprod : ‖paperFT (gapTestC Y) (gammaOf ρ - t)‖ * ‖paperFT (gapTestC Y) (conj (gammaOf ρ) - t)‖ ≤
      Y ^ 2 * G ^ 2 * Real.exp (Y * |1 / 2 - ρ.re|) ^ 2 / (1 + Y * x) ^ 4 := by
    refine (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)).trans (le_of_eq ?_)
    field_simp
  have hbound : Y ^ 2 * G ^ 2 * Real.exp (Y * |1 / 2 - ρ.re|) ^ 2 / (1 + Y * x) ^ 4 ≤
      gapWeight σ Y * (1 / (1 + x) ^ 3) := by
    have hg : gapWeight σ Y = 8 * G ^ 2 / (σ ^ 4 * Y ^ 2) := by rw [gapWeight, hG]
    rw [hg, div_mul_div_comm, div_le_div_iff₀ hD4 (by positivity)]
    have hG2 : 0 ≤ G ^ 2 := sq_nonneg G
    have hA : 0 ≤ G ^ 2 * ((1 + x) ^ 3 * (Y ^ 4 * σ ^ 4)) := by positivity
    have e : Y ^ 2 * G ^ 2 * Real.exp (Y * |1 / 2 - ρ.re|) ^ 2 * (σ ^ 4 * Y ^ 2 * (1 + x) ^ 3) =
        G ^ 2 * ((1 + x) ^ 3 * (Y ^ 4 * σ ^ 4)) * Real.exp (Y * |1 / 2 - ρ.re|) ^ 2 := by ring
    rw [e, mul_one]
    rcases le_or_gt x (Real.exp Y) with hnear | hfar'
    · have hre := hon hnear
      rw [hre, sub_self, abs_zero, mul_zero, Real.exp_zero, one_pow, mul_one]
      have hw := mul_le_mul_of_nonneg_left (one_add_pow_mul_le hσ hσ1 hY hfar) hG2
      linarith only [hw]
    · have hw := mul_le_mul_of_nonneg_left (one_add_pow_mul_exp_le hσ hσ1 hY hfar'.le) hG2
      have hexp : Real.exp (Y * |1 / 2 - ρ.re|) ^ 2 ≤ Real.exp Y := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left hδ hY.le
        push_cast
        linarith only [this]
      have h3 := mul_le_mul_of_nonneg_left hexp hA
      linarith only [h3, hw]
  have hfinal := hbound
  calc
    (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (gapTestC Y) (gammaOf ρ - t)‖ *
        ‖paperFT (gapTestC Y) (conj (gammaOf ρ) - t)‖
        = (zetaZeroConfig.mult ρ : ℝ) * (‖paperFT (gapTestC Y) (gammaOf ρ - t)‖ *
          ‖paperFT (gapTestC Y) (conj (gammaOf ρ) - t)‖) := by ring
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (gapWeight σ Y * (1 / (1 + x) ^ 3)) :=
      mul_le_mul_of_nonneg_left (hprod.trans hfinal) hm
    _ = _ := by ring

/-- The scale `Y(σ)`, with `Y ≥ 1/σ` and `Y³ ≥ 32 G² · 5760/(σ⁴ m₃)`. -/
def gapScale (σ : ℝ) : ℝ :=
  max (1 / σ) ((32 * (400 * gapMass) ^ 2 * 5760 / (σ ^ 4 * gapEnergy)) ^ ((1 : ℝ) / 3))

theorem gapScale_pos {σ : ℝ} (hσ : 0 < σ) : 0 < gapScale σ :=
  lt_max_of_lt_left (by positivity)

theorem gapScale_cube {σ : ℝ} (hσ : 0 < σ) :
    32 * (400 * gapMass) ^ 2 * 5760 / (σ ^ 4 * gapEnergy) ≤ gapScale σ ^ 3 := by
  have hE := gapEnergy_pos
  have hm := gapMass_pos
  obtain ⟨c, hc⟩ : ∃ c, c = 32 * (400 * gapMass) ^ 2 * 5760 / (σ ^ 4 * gapEnergy) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  rw [← hc]
  have h1 : c ^ ((1 : ℝ) / 3) ≤ gapScale σ := by
    rw [gapScale, ← hc]
    exact le_max_right _ _
  have h2 := pow_le_pow_left₀ (Real.rpow_nonneg hc0 _) h1 3
  rwa [← Real.rpow_natCast, ← Real.rpow_mul hc0, show ((1 : ℝ) / 3 * ((3 : ℕ) : ℝ)) = 1 by norm_num,
    Real.rpow_one] at h2

/-- The size of the scaled test. -/
def gapTail (Y : ℝ) : ℝ :=
  (4 * ((∫ u, ‖gapTestC Y u‖) + ∫ u, ‖deriv (deriv (gapTestC Y)) u‖)) ^ 2

/-- The height above which `σ`-gaps are excluded. -/
def gapHeight (σ : ℝ) : ℝ :=
  max (128 * Real.exp (2 * (horizonExponent (Real.exp (2 * gapScale σ)) +
    2 * pairEnergy (1 / 2) (gapScale σ))))
    (gapTail (gapScale σ) / (gapScale σ * gapEnergy))

/-- **Short gaps.** If every zero within `exp (gapScale σ)` of `t` is on the line and `|t| ≥ gapHeight σ`, then some zero
has ordinate within `σ` of `t`. -/
theorem exists_zero_near_of_onLine {σ t : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ht : gapHeight σ ≤ |t|)
    (hon : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| ≤ Real.exp (gapScale σ) → ρ.re = 1 / 2) :
    ∃ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| < σ := by
  by_contra hno
  push Not at hno
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = gapScale σ := ⟨_, rfl⟩
  have hY : 0 < Y := by rw [hYdef]; exact gapScale_pos hσ
  have hEn := gapEnergy_pos
  -- The zero side.
  have hloc := zeta_unit_count_le_240
  obtain ⟨hwsum, hwle⟩ := window_tsum_le zetaZeroConfig (A₀ := 240) (by norm_num) hloc t
  have hbd : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand (modulatedTest t (gapTest Y)) (modulatedTest t (gapTest Y)) ρ‖ ≤
        gapWeight σ Y * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t|) ^ 3) := fun ρ =>
    norm_Wsummand_gapTest_le hσ hσ1 hY ρ.2 (hno ρ ρ.2) fun h => hon ρ ρ.2 (by rw [← hYdef]; exact h)
  have hw0 : 0 ≤ gapWeight σ Y := by unfold gapWeight; positivity
  have hsumN : Summable fun ρ : zetaZeroConfig.carrier =>
      ‖zetaZeroConfig.Wsummand (modulatedTest t (gapTest Y)) (modulatedTest t (gapTest Y)) ρ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd (hwsum.mul_left _)
  have hup : (zetaZeroConfig.W (modulatedTest t (gapTest Y)) (modulatedTest t (gapTest Y))).re ≤
      gapWeight σ Y * (24 * 240 * Real.log (|t| + 3)) := by
    rw [ZeroConfig.W]
    refine (Complex.re_le_norm _).trans ((norm_tsum_le_tsum_norm hsumN).trans ?_)
    refine (hsumN.tsum_le_tsum hbd (hwsum.mul_left _)).trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hwle hw0
  -- The symbol side.
  have hshift : heightShift (-t / (2 * π)) (gapTestC Y) = modulatedTest t (gapTest Y) := by
    funext u
    simp only [heightShift, modulatedTest, gapTestC]
    congr 2
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  have hlow := zetaZeroConfig_re_W_heightShift_ge hY.le (gapTestC_contDiff Y) (tsupport_gapTestC hY)
    (-t / (2 * π))
  rw [hshift, integral_gapTestC_sq hY] at hlow
  have habsξ : π * |(-t / (2 * π))| = |t| / 2 := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * π)]
    field_simp
  rw [habsξ] at hlow
  have hlogarg : (1 : ℝ) + |t| / 2 / 4 = 1 + |t| / 8 := by ring
  rw [hlogarg] at hlow
  -- Numerics.
  have hgap1 : 128 * Real.exp (2 * (horizonExponent (Real.exp (2 * Y)) + 2 * pairEnergy (1 / 2) Y)) ≤ |t| := by
    rw [hYdef]
    exact (le_max_left _ _).trans ht
  have hgap2 : gapTail Y / (Y * gapEnergy) ≤ |t| := by
    rw [hYdef]
    exact (le_max_right _ _).trans ht
  obtain ⟨E, hE⟩ : ∃ E, E = horizonExponent (Real.exp (2 * Y)) + 2 * pairEnergy (1 / 2) Y := ⟨_, rfl⟩
  rw [← hE] at hgap1
  have ht128 : 128 ≤ |t| := by
    have h1 : 1 ≤ Real.exp (2 * E) ∨ Real.exp (2 * E) < 1 := le_or_gt _ _
    have hS : 0 ≤ E := by
      have h2 := horizonExponent_pos (Real.exp (2 * Y))
      have h3 : 0 ≤ pairEnergy (1 / 2) Y := by
        unfold pairEnergy
        have := Real.self_le_sinh_iff.2 (by positivity : 0 ≤ 2 * (1 / 2) * Y)
        norm_num at this ⊢
        linarith only [this]
      rw [hE]
      linarith only [h2, h3]
    have h4 : 1 ≤ Real.exp (2 * E) := Real.one_le_exp (by positivity)
    nlinarith only [hgap1, h4]
  have ht0 : 0 < |t| := by linarith only [ht128]
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (|t| + 3) := ⟨_, rfl⟩
  have hL1 : 1 < L := by
    rw [hL, Real.lt_log_iff_exp_lt (by positivity)]
    have := Real.exp_one_lt_d9
    linarith only [this, ht128]
  have hlogmain : L / 2 + E ≤ Real.log (1 + |t| / 8) := by
    have h1 : Real.log (|t| / 8) ≤ Real.log (1 + |t| / 8) :=
      Real.log_le_log (by positivity) (by linarith only)
    have h2 : L ≤ Real.log (2 * |t|) := by
      rw [hL]
      exact Real.log_le_log (by positivity) (by linarith only [ht128])
    have h3 : Real.log (128 * Real.exp (2 * E)) ≤ Real.log |t| :=
      Real.log_le_log (by positivity) hgap1
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h3
    have e128 : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have e8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [Real.log_mul (by norm_num) ht0.ne'] at h2
    rw [Real.log_div ht0.ne' (by norm_num), e8] at h1
    rw [e128] at h3
    linarith only [h1, h2, h3]
  have hweight : gapWeight σ Y * (24 * 240 * L) ≤ Y * gapEnergy / 4 * L := by
    have hcube : 32 * (400 * gapMass) ^ 2 * 5760 / (σ ^ 4 * gapEnergy) ≤ Y ^ 3 := by
      rw [hYdef]
      exact gapScale_cube hσ
    rw [div_le_iff₀ (by positivity)] at hcube
    have hL0 : 0 ≤ L := by linarith only [hL1]
    have e : gapWeight σ Y * (24 * 240 * L) =
        (8 * (400 * gapMass) ^ 2 * 5760) / (σ ^ 4 * Y ^ 2) * L := by
      rw [gapWeight]
      field_simp
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ hL0
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [hcube, sq_nonneg Y, hY]
  have htail : gapTail Y / (8 * (1 + |t| / 2)) ≤ Y * gapEnergy / 4 := by
    rw [div_le_iff₀ (by positivity)] at hgap2 ⊢
    nlinarith only [hgap2, hY, hEn, mul_pos hY hEn, ht0]
  -- Comparison.
  rw [← hL] at hup
  have hlow' : (Real.log (1 + |t| / 8) - E) * (Y * gapEnergy) - gapTail Y / (8 * (1 + |t| / 2)) ≤
      (zetaZeroConfig.W (modulatedTest t (gapTest Y)) (modulatedTest t (gapTest Y))).re := by
    have e : (Real.log (1 + |t| / 8) - horizonExponent (Real.exp (2 * Y)) - 2 * pairEnergy (1 / 2) Y) =
        Real.log (1 + |t| / 8) - E := by rw [hE]; ring
    rw [e] at hlow
    exact hlow
  have hP : 0 < Y * gapEnergy := mul_pos hY hEn
  have h5 : L / 2 * (Y * gapEnergy) ≤ (Real.log (1 + |t| / 8) - E) * (Y * gapEnergy) :=
    mul_le_mul_of_nonneg_right (by linarith only [hlogmain]) hP.le
  nlinarith only [hlow', hup, hweight, htail, h5, hP, hL1]

end

end GaloisForLFunctions.VerifiedHeightRungs

#print axioms GaloisForLFunctions.VerifiedHeightRungs.exists_zero_near_of_onLine
