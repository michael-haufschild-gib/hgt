import GaloisForLFunctions.FrustratedArithmeticDirichletForms.EachEntryConfinesItsWeight
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomIsExactlyLogarithmic
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanPairingOfTwoAtoms

/-!
# The entry is logarithmically soft

When `n₀` enters the window (`2c ↓ log n₀`) the window confines its weight (`EachEntryConfinesItsWeight`).
This module measures the confinement as the collar sliver of width `δ = 2c − log n₀` opens:

  `|λ(n₀)| ≤ √n₀ (A log(1/δ) + B)`   for every `λ ∈ 𝒜(c)` once `δ` is below the gap of `log` at `n₀`

(`abs_calibration_coord_le_log`), with constants `A, B` depending only on `n₀`. The witnesses are the
two-site tests of radius `δ/2`: their archimedean–polar energy is `O(δ log(1/δ))`
(`archPolar_twoSite_le`, from the logarithmic self-energy of an atom), while the weight is read with
mass `δ`. Together with SWC's soft entry — a sector margin `η` admits every newest weight within
`ηΩ(δ) ≥ (η e^{−1/2}/2) log(1/δ)` — the tolerance of the newest weight is logarithmic in the sliver
width from both sides: soft entry is sharp in its order, and beyond the sliver (`δ` of order one) the
stage fibre is a bounded interval of bounded length.
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FrustratedArithmeticDirichletForms

open _root_.RHTower _root_.Zeta23

/-! ### The site bump is a dilation -/

theorem siteBump_eq_unit {r : ℝ} (hr : 0 < r) (x : ℝ) :
    siteBump r hr x = siteBump 1 one_pos (x / r) := by
  rw [ContDiffBump.apply, ContDiffBump.apply]
  simp only [siteBump, sub_zero, smul_eq_mul]
  congr 1
  · field_simp
  · field_simp

theorem siteBump_le_one {r : ℝ} (hr : 0 < r) (x : ℝ) : siteBump r hr x ≤ 1 := (siteBump r hr).le_one

theorem siteBump_nonneg {r : ℝ} (hr : 0 < r) (x : ℝ) : 0 ≤ siteBump r hr x := (siteBump r hr).nonneg

theorem siteBump_le_indicator {r : ℝ} (hr : 0 < r) (x : ℝ) :
    siteBump r hr x ≤ (Icc (-r) r).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ Icc (-r) r
  · rw [indicator_of_mem hx]; exact siteBump_le_one hr x
  · rw [indicator_of_notMem hx]
    refine (siteBump_eq_zero hr ?_).le
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

theorem integrable_siteBump {r : ℝ} (hr : 0 < r) : Integrable (siteBump r hr) :=
  (siteBump r hr).continuous.integrable_of_hasCompactSupport (siteBump r hr).hasCompactSupport

theorem integral_siteBump_le {r : ℝ} (hr : 0 < r) : ∫ x, siteBump r hr x ≤ 2 * r := by
  have hi : Integrable ((Icc (-r) r).indicator fun _ => (1 : ℝ)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  calc ∫ x, siteBump r hr x ≤ ∫ x, (Icc (-r) r).indicator (fun _ => (1 : ℝ)) x :=
        integral_mono (integrable_siteBump hr) hi (siteBump_le_indicator hr)
    _ = 2 * r := by
        rw [integral_indicator_const _ measurableSet_Icc]
        simp only [Measure.real, Real.volume_Icc, smul_eq_mul, mul_one]
        rw [ENNReal.toReal_ofReal (by linarith)]
        ring

theorem integral_siteBump_sq_le {r : ℝ} (hr : 0 < r) : ∫ x, siteBump r hr x ^ 2 ≤ 2 * r := by
  refine le_trans (integral_mono ?_ (integrable_siteBump hr) fun x => ?_) (integral_siteBump_le hr)
  · exact SpacingScaleHarmonicAnalysis.integrable_sq_of_continuous (siteBump r hr).continuous
      (siteBump r hr).hasCompactSupport
  · have h0 := siteBump_nonneg hr x
    have h1 := siteBump_le_one hr x
    nlinarith

/-- `∫ φ_r² = r ∫ φ_1²`. -/
theorem integral_siteBump_sq_eq {r : ℝ} (hr : 0 < r) :
    ∫ x, siteBump r hr x ^ 2 = r * ∫ x, siteBump 1 one_pos x ^ 2 := by
  simp_rw [siteBump_eq_unit hr]
  rw [Measure.integral_comp_div (fun y => siteBump 1 one_pos y ^ 2) r, abs_of_pos hr, smul_eq_mul]

/-! ### The archimedean–polar energy of a narrow two-site test -/

/-- The Lévy energy of a site bump is `O(r log(1/r))`. -/
theorem levyEnergy_siteBump_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, ∀ hr : 0 < r, r ≤ 1 / 2 →
      levyEnergy (siteBump r hr) ≤
        2 * r * (Real.log (1 / (2 * r)) + SpacingScaleHarmonicAnalysis.selfEnergyConstant) +
          4 * Real.exp (1 / 2) * K * r := by
  obtain ⟨C, hC⟩ := ((siteBump 1 one_pos).contDiff (n := 1)).lipschitzWith_of_hasCompactSupport
    (siteBump 1 one_pos).hasCompactSupport (by norm_num)
  refine ⟨C, C.2, fun r hr hr2 => ?_⟩
  set g : ℝ → ℝ := fun u => siteBump r hr (u - r)
  have hg : ContDiff ℝ 2 g := (siteBump r hr).contDiff.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport g := HasCompactSupport.intro (isCompact_Icc (a := 0) (b := 2 * r))
    fun u hu => siteBump_eq_zero hr (by
      simp only [mem_Icc, not_and_or, not_le] at hu
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  have hgsupp : ∀ u, u ∉ Icc 0 (2 * r) → g u = 0 := fun u hu => by
    have := hgc
    exact siteBump_eq_zero hr (by
      simp only [mem_Icc, not_and_or, not_le] at hu
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  have hlip : ∀ u v, |g u - g v| ≤ (C / r) * |u - v| := by
    intro u v
    simp only [g]
    rw [siteBump_eq_unit hr, siteBump_eq_unit hr]
    have h := hC.dist_le_mul ((u - r) / r) ((v - r) / r)
    rw [Real.dist_eq, Real.dist_eq] at h
    calc |siteBump 1 one_pos ((u - r) / r) - siteBump 1 one_pos ((v - r) / r)|
        ≤ C * |(u - r) / r - (v - r) / r| := h
      _ = (C / r) * |u - v| := by
          rw [show (u - r) / r - (v - r) / r = (u - v) / r by ring, abs_div, abs_of_pos hr]
          ring
  have hK0 : 0 ≤ (C : ℝ) / r := div_nonneg C.2 hr.le
  have h := SpacingScaleHarmonicAnalysis.levyEnergy_atom_le hg hgc hgsupp (by linarith)
    (by linarith) hK0 hlip
  have htr : levyEnergy g = levyEnergy (siteBump r hr) :=
    SpacingScaleHarmonicAnalysis.levyEnergy_translate (g := siteBump r hr) r
  have hsq : (∫ u, g u ^ 2) = ∫ u, siteBump r hr u ^ 2 :=
    integral_sub_right_eq_self (μ := volume) (fun u => siteBump r hr u ^ 2) r
  have habs : (∫ u, |g u|) = ∫ u, siteBump r hr u := by
    rw [integral_sub_right_eq_self (μ := volume) (fun u => |siteBump r hr u|) r]
    exact integral_congr_ae (Eventually.of_forall fun u => abs_of_nonneg (siteBump_nonneg hr u))
  rw [htr, hsq, habs] at h
  have hC0 : 0 ≤ SpacingScaleHarmonicAnalysis.selfEnergyConstant := by
    unfold SpacingScaleHarmonicAnalysis.selfEnergyConstant
    have : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have : 0 < 1 - Real.exp (-2) := by linarith
    positivity
  have hlog : 0 ≤ Real.log (1 / (2 * r)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have e1 := mul_le_mul_of_nonneg_left (integral_siteBump_sq_le hr)
    (show 0 ≤ Real.log (1 / (2 * r)) + SpacingScaleHarmonicAnalysis.selfEnergyConstant by linarith)
  have e2 : Real.exp (1 / 2) * (C / r) * (2 * r) * (∫ u, siteBump r hr u) ≤
      4 * Real.exp (1 / 2) * C * r := by
    have : Real.exp (1 / 2) * (C / r) * (2 * r) = 2 * Real.exp (1 / 2) * C := by field_simp
    rw [this]
    calc 2 * Real.exp (1 / 2) * C * (∫ u, siteBump r hr u) ≤ 2 * Real.exp (1 / 2) * C * (2 * r) :=
          mul_le_mul_of_nonneg_left (integral_siteBump_le hr) (by positivity)
      _ = 4 * Real.exp (1 / 2) * C * r := by ring
  linarith

theorem levyEnergy_const_mul (a : ℝ) (g : ℝ → ℝ) :
    levyEnergy (fun u => a * g u) = a ^ 2 * levyEnergy g := by
  unfold levyEnergy
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  have e : (fun u => (a * g u - a * g (u + x)) ^ 2) = fun u => a ^ 2 * (g u - g (u + x)) ^ 2 := by
    funext u; ring
  simp only [e, integral_const_mul]
  ring

/-- The Lévy energy of the two-site test is at most four times that of one site. -/
theorem levyEnergy_twoSite_le (ℓ : ℝ) {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : ε ^ 2 = 1) :
    levyEnergy (twoSiteTestAt ℓ r hr ε) ≤ 4 * levyEnergy (siteBump r hr) := by
  set g₁ : ℝ → ℝ := fun u => siteBump r hr (u - ℓ / 2)
  set g₂ : ℝ → ℝ := fun u => ε * siteBump r hr (u + ℓ / 2)
  have hg₁ : ContDiff ℝ 2 g₁ := (siteBump r hr).contDiff.comp (contDiff_id.sub contDiff_const)
  have hg₁c : HasCompactSupport g₁ :=
    (siteBump r hr).hasCompactSupport.comp_homeomorph (Homeomorph.subRight (ℓ / 2))
  have hg₂ : ContDiff ℝ 2 g₂ :=
    contDiff_const.mul ((siteBump r hr).contDiff.comp (contDiff_id.add contDiff_const))
  have hg₂c : HasCompactSupport g₂ :=
    ((siteBump r hr).hasCompactSupport.comp_homeomorph (Homeomorph.addRight (ℓ / 2))).mul_left
  have h := SpacingScaleHarmonicAnalysis.levyEnergy_add_le hg₁ hg₁c hg₂ hg₂c
  have e₁ : levyEnergy g₁ = levyEnergy (siteBump r hr) :=
    SpacingScaleHarmonicAnalysis.levyEnergy_translate (g := siteBump r hr) (ℓ / 2)
  have e₂ : levyEnergy g₂ = levyEnergy (siteBump r hr) := by
    rw [levyEnergy_const_mul, hε, one_mul]
    have := SpacingScaleHarmonicAnalysis.levyEnergy_translate (g := siteBump r hr) (-(ℓ / 2))
    simpa [sub_neg_eq_add] using this
  have hF : twoSiteTestAt ℓ r hr ε = fun u => g₁ u + g₂ u := rfl
  rw [hF]
  rw [e₁, e₂] at h
  have hL := SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' (siteBump r hr)
  have hsq : Real.sqrt (levyEnergy (siteBump r hr)) * Real.sqrt (levyEnergy (siteBump r hr)) =
      levyEnergy (siteBump r hr) := Real.mul_self_sqrt hL
  linarith

/-- The prime sum of the two-site test at distance `log n₀` is `2εw_{n₀}‖φ‖²`. -/
theorem primeSum_twoSiteAt {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {r g : ℝ} (hr : 0 < r)
    (hg : ∀ m : ℕ, 2 ≤ m → m ≠ n₀ → g ≤ |Real.log m - Real.log n₀|) (hrg : 2 * r ≤ g)
    (hr2 : 2 * r ≤ Real.log 2) (ε : ℝ) :
    primeSum (twoSiteTestAt (Real.log n₀) r hr ε) =
      2 * ε * vonMangoldtAtom n₀ * ∫ t, siteBump r hr t ^ 2 := by
  set ℓ := Real.log n₀
  set F := twoSiteTestAt ℓ r hr ε
  have hl2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by exact_mod_cast hn₀)
  have hlag : ∫ t, F t * F (t - ℓ) = ε * ∫ t, siteBump r hr t ^ 2 :=
    integral_twoSiteAt_mul_shift hr (by linarith) ε
  have hlag' : ∫ t, F t * F (t + ℓ) = ε * ∫ t, siteBump r hr t ^ 2 := by
    rw [← hlag, ← integral_mul_shift_neg F ℓ]
    simp_rw [sub_neg_eq_add]
  have hterm : ∀ m : ℕ, m ≠ n₀ → vonMangoldtAtom m *
      ((∫ t, F t * F (t - Real.log m)) + ∫ t, F t * F (t + Real.log m)) = 0 := by
    intro m hm
    by_cases h2 : 2 ≤ m
    · have hlm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast h2)
      have hgap := hg m h2 hm
      have z : ∀ y, 2 * r ≤ |y| → 2 * r ≤ |y - ℓ| → 2 * r ≤ |y + ℓ| →
          (∫ t, F t * F (t - y)) = 0 := fun y h0 h1 h2' =>
        integral_eq_zero_of_ae (Eventually.of_forall fun t => twoSiteAt_mul_shift_eq_zero hr ε h0 h1 h2' t)
      have z1 := z (Real.log m) (by rw [abs_of_pos (by linarith)]; linarith) (hrg.trans hgap)
        (by rw [abs_of_pos (by linarith)]; linarith)
      have z2 := z (-Real.log m) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
        (by rw [show -Real.log m - ℓ = -(Real.log m + ℓ) by ring, abs_neg,
          abs_of_pos (by linarith)]; linarith)
        (by rw [show -Real.log m + ℓ = -(Real.log m - ℓ) by ring, abs_neg]; exact hrg.trans hgap)
      simp only [sub_neg_eq_add] at z2
      rw [z1, z2, add_zero, mul_zero]
    · simp [vonMangoldtAtom, h2]
  unfold primeSum
  rw [tsum_eq_single n₀ hterm, hlag, hlag']
  ring

theorem hasCompactSupport_twoSiteTestAt (ℓ : ℝ) {r : ℝ} (hr : 0 < r) (ε : ℝ) :
    HasCompactSupport (twoSiteTestAt ℓ r hr ε) :=
  ((siteBump r hr).hasCompactSupport.comp_homeomorph (Homeomorph.subRight (ℓ / 2))).add
    ((siteBump r hr).hasCompactSupport.comp_homeomorph (Homeomorph.addRight (ℓ / 2))).mul_left

/-- **The archimedean–polar energy of the two-site test is the Weil energy without its prime part**:
`A_ε = 2θ′(0)‖F‖² + 𝒥(F) + 2C(F)² − 2S(F)²`. -/
theorem archPolar_twoSite_eq {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {r g : ℝ} (hr : 0 < r)
    (hg : ∀ m : ℕ, 2 ≤ m → m ≠ n₀ → g ≤ |Real.log m - Real.log n₀|) (hrg : 2 * r ≤ g)
    (hr2 : 2 * r ≤ Real.log 2) (ε : ℝ) :
    (weilFullFunctional (fun _ => 0)
        (EF.weilTest (fun u => (twoSiteTestAt (Real.log n₀) r hr ε u : ℂ))
          (fun u => (twoSiteTestAt (Real.log n₀) r hr ε u : ℂ)))).re =
      2 * gammaHardyPhaseRate 0 * (∫ u, twoSiteTestAt (Real.log n₀) r hr ε u ^ 2) +
        levyEnergy (twoSiteTestAt (Real.log n₀) r hr ε) +
        (2 * coshHalfMoment (twoSiteTestAt (Real.log n₀) r hr ε) ^ 2 -
          2 * sinhHalfMoment (twoSiteTestAt (Real.log n₀) r hr ε) ^ 2) := by
  set F := twoSiteTestAt (Real.log n₀) r hr ε
  have hF : ContDiff ℝ 2 F := contDiff_twoSiteTestAt _ hr ε
  have hFc : HasCompactSupport F := hasCompactSupport_twoSiteTestAt _ hr ε
  have hW := SpacingScaleHarmonicAnalysis.weilQuad_eq hF hFc
  have hsplit := weilFullFunctional_eq_sub_weightedPrimePart
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))
  have hP := weightedPrimePart_twoSiteAt hn₀ hr hg hrg hr2
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ε
  have hS := primeSum_twoSiteAt hn₀ hr hg hrg hr2 ε
  have hatom : vonMangoldtAtom n₀ = (ArithmeticFunction.vonMangoldt n₀ : ℝ) / Real.sqrt n₀ := by
    simp [vonMangoldtAtom, hn₀]
  have hQ : SpacingScaleHarmonicAnalysis.weilQuad F =
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re := rfl
  rw [hP] at hsplit
  have hre := congrArg Complex.re hsplit
  rw [Complex.sub_re, Complex.ofReal_re, ← hQ, hW, hS, hatom] at hre
  linarith

theorem integral_sq_twoSite_le (ℓ : ℝ) {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : ε ^ 2 = 1) :
    ∫ u, twoSiteTestAt ℓ r hr ε u ^ 2 ≤ 4 * ∫ u, siteBump r hr u ^ 2 := by
  have hsq : Integrable fun u => siteBump r hr u ^ 2 :=
    SpacingScaleHarmonicAnalysis.integrable_sq_of_continuous (siteBump r hr).continuous
      (siteBump r hr).hasCompactSupport
  have h1 : Integrable fun u => siteBump r hr (u - ℓ / 2) ^ 2 := hsq.comp_sub_right _
  have h2 : Integrable fun u => siteBump r hr (u + ℓ / 2) ^ 2 := hsq.comp_add_right _
  have hF : Integrable fun u => twoSiteTestAt ℓ r hr ε u ^ 2 :=
    SpacingScaleHarmonicAnalysis.integrable_sq_of_continuous (contDiff_twoSiteTestAt ℓ hr ε).continuous
      (hasCompactSupport_twoSiteTestAt ℓ hr ε)
  calc ∫ u, twoSiteTestAt ℓ r hr ε u ^ 2
      ≤ ∫ u, (2 * siteBump r hr (u - ℓ / 2) ^ 2 + 2 * siteBump r hr (u + ℓ / 2) ^ 2) := by
        refine integral_mono hF ((h1.const_mul 2).add (h2.const_mul 2)) fun u => ?_
        simp only [twoSiteTestAt]
        nlinarith [sq_nonneg (siteBump r hr (u - ℓ / 2) - ε * siteBump r hr (u + ℓ / 2))]
    _ = 4 * ∫ u, siteBump r hr u ^ 2 := by
        rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul, integral_const_mul,
          integral_sub_right_eq_self (μ := volume) (fun u => siteBump r hr u ^ 2) (ℓ / 2),
          integral_add_right_eq_self (μ := volume) (fun u => siteBump r hr u ^ 2) (ℓ / 2)]
        ring

theorem integral_abs_twoSite_le (ℓ : ℝ) {r : ℝ} (hr : 0 < r) {ε : ℝ} (hε : ε ^ 2 = 1) :
    ∫ u, |twoSiteTestAt ℓ r hr ε u| ≤ 4 * r := by
  have hε1 : |ε| = 1 := by
    have := abs_mul_abs_self ε
    nlinarith [abs_nonneg ε, sq_abs ε]
  have hi : Integrable (siteBump r hr) := integrable_siteBump hr
  have h1 : Integrable fun u => siteBump r hr (u - ℓ / 2) := hi.comp_sub_right _
  have h2 : Integrable fun u => siteBump r hr (u + ℓ / 2) := hi.comp_add_right _
  calc ∫ u, |twoSiteTestAt ℓ r hr ε u|
      ≤ ∫ u, (siteBump r hr (u - ℓ / 2) + siteBump r hr (u + ℓ / 2)) := by
        refine integral_mono ((contDiff_twoSiteTestAt ℓ hr ε).continuous.integrable_of_hasCompactSupport
          (hasCompactSupport_twoSiteTestAt ℓ hr ε)).abs (h1.add h2) fun u => ?_
        simp only [twoSiteTestAt]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, hε1, one_mul, abs_of_nonneg (siteBump_nonneg hr _),
          abs_of_nonneg (siteBump_nonneg hr _)]
    _ = 2 * ∫ u, siteBump r hr u := by
        rw [integral_add h1 h2, integral_sub_right_eq_self (μ := volume) (siteBump r hr) (ℓ / 2),
          integral_add_right_eq_self (μ := volume) (siteBump r hr) (ℓ / 2)]
        ring
    _ ≤ 4 * r := by linarith [integral_siteBump_le hr]

/-- **Reading the weight with a two-site test.** For `λ` in the calibration space, the two-site test
of radius `r` at distance `log n₀` gives `ελ(n₀)·2‖φ‖²/√n₀ ≤ A_ε`. -/
theorem twoSite_reading {c : ℝ} {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {r g : ℝ} (hr : 0 < r)
    (hg : ∀ m : ℕ, 2 ≤ m → m ≠ n₀ → g ≤ |Real.log m - Real.log n₀|) (hrg : 2 * r ≤ g)
    (hr2 : 2 * r ≤ Real.log 2) (hrc : Real.log n₀ / 2 + r ≤ c) {lam : ℕ → ℝ}
    (hlam : lam ∈ calibration c) (ε : ℝ) :
    ε * lam n₀ * (2 * (∫ t, siteBump r hr t ^ 2) / Real.sqrt n₀) ≤
      (weilFullFunctional (fun _ => 0)
        (EF.weilTest (fun u => (twoSiteTestAt (Real.log n₀) r hr ε u : ℂ))
          (fun u => (twoSiteTestAt (Real.log n₀) r hr ε u : ℂ)))).re := by
  have hℓ : 0 ≤ Real.log n₀ := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n₀))
  have h := hlam (fun u => (twoSiteTestAt (Real.log n₀) r hr ε u : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_twoSiteTestAt _ hr ε))
    (tsupport_twoSiteTestAt_subset hℓ hr ε hrc)
  rw [weilFullFunctional_eq_sub_weightedPrimePart, Complex.sub_re,
    weightedPrimePart_twoSiteAt hn₀ hr hg hrg hr2 lam ε, Complex.ofReal_re] at h
  have e : 2 * ε * (lam n₀ / Real.sqrt n₀) * ∫ t, siteBump r hr t ^ 2 =
      ε * lam n₀ * (2 * (∫ t, siteBump r hr t ^ 2) / Real.sqrt n₀) := by ring
  linarith

/-- **The entry is at most logarithmically soft.** There are constants `A, B` (depending on `n₀`)
such that, once the sliver `δ = 2c − log n₀` is below a threshold `δ₀ > 0`, every weight
sequence in the calibration space has `|λ(n₀)| ≤ √n₀ (A log(1/δ) + B)`. -/
theorem abs_calibration_coord_le_log {n₀ : ℕ} (hn₀ : 2 ≤ n₀) :
    ∃ δ₀ A B : ℝ, 0 < δ₀ ∧ ∀ c : ℝ, Real.log n₀ < 2 * c → 2 * c - Real.log n₀ ≤ δ₀ →
      ∀ lam ∈ calibration c,
        |lam n₀| ≤ Real.sqrt n₀ * (A * Real.log (1 / (2 * c - Real.log n₀)) + B) := by
  obtain ⟨g, hg0, hg⟩ := exists_log_gap n₀ hn₀
  obtain ⟨K, hK0, hK⟩ := levyEnergy_siteBump_le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set m₁ := ∫ x, siteBump 1 one_pos x ^ 2
  have hm₁ : 0 < m₁ := integral_siteBump_sq_pos one_pos
  set C₀ := SpacingScaleHarmonicAnalysis.selfEnergyConstant
  set Θ := |2 * gammaHardyPhaseRate 0|
  set Ch := Real.cosh ((Real.log n₀ + 1) / 4)
  refine ⟨min g (min (Real.log 2) 1), 4 / m₁,
    (4 * (2 * Θ) + 4 * (Real.log 2 + C₀) + 8 * Real.exp (1 / 2) * K + 8 * Ch ^ 2) / m₁,
    lt_min hg0 (lt_min hl2 one_pos), fun c hc hδ lam hlam => ?_⟩
  set δ := 2 * c - Real.log n₀ with hδdef
  have hδ0 : 0 < δ := by linarith
  have hδg : δ ≤ g := hδ.trans (min_le_left _ _)
  have hδ2 : δ ≤ Real.log 2 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  set r := δ / 4
  have hr : 0 < r := by positivity
  have hrg : 2 * r ≤ g := by simp only [r]; linarith
  have hr2 : 2 * r ≤ Real.log 2 := by simp only [r]; linarith
  have hrc : Real.log n₀ / 2 + r ≤ c := by simp only [r]; linarith
  have hrhalf : r ≤ 1 / 2 := by simp only [r]; linarith
  have hm : ∫ t, siteBump r hr t ^ 2 = r * m₁ := integral_siteBump_sq_eq hr
  have hsq : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))
  have hc0 : 0 < c := by
    have : 0 ≤ Real.log n₀ := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n₀))
    linarith
  -- the energy bound for both signs
  have hA : ∀ ε : ℝ, ε ^ 2 = 1 →
      (weilFullFunctional (fun _ => 0)
        (EF.weilTest (fun u => (twoSiteTestAt (Real.log n₀) r hr ε u : ℂ))
          (fun u => (twoSiteTestAt (Real.log n₀) r hr ε u : ℂ)))).re ≤
        r * (4 * (2 * Θ) + 8 * (Real.log (1 / (2 * r)) + C₀) + 16 * Real.exp (1 / 2) * K +
          32 * Ch ^ 2 * r) := by
    intro ε hε
    set F := twoSiteTestAt (Real.log n₀) r hr ε
    rw [archPolar_twoSite_eq hn₀ hr hg hrg hr2 ε]
    have hF2 := integral_sq_twoSite_le (Real.log n₀) hr hε
    have hF1 := integral_abs_twoSite_le (Real.log n₀) hr hε
    have hlev := (levyEnergy_twoSite_le (Real.log n₀) hr hε).trans
      (mul_le_mul_of_nonneg_left (hK r hr hrhalf) (by norm_num))
    have hsupp : SpacingScaleHarmonicAnalysis.SupportedIn c F := fun u hu => by
      have h := tsupport_twoSiteTestAt_subset (Real.log_nonneg (by exact_mod_cast
        (by omega : 1 ≤ n₀))) hr ε hrc
      by_contra hne
      have hmem : u ∈ tsupport (fun u => (F u : ℂ)) := subset_tsupport _ (by simpa using hne)
      have := h hmem
      exact absurd (abs_le.mpr ⟨this.1, this.2⟩) (not_le.mpr hu)
    have hC := SpacingScaleHarmonicAnalysis.abs_moment_le (contDiff_twoSiteTestAt _ hr ε).continuous
      (hasCompactSupport_twoSiteTestAt _ hr ε) hsupp (φ := fun u => Real.cosh (u / 2))
      (by fun_prop) fun u hu => SpacingScaleHarmonicAnalysis.abs_cosh_half_le hu
    have hCh : Real.cosh (c / 2) ≤ Ch := by
      rw [Real.cosh_le_cosh, abs_of_pos (by linarith), abs_of_pos (by
        have : 0 ≤ Real.log n₀ := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n₀))
        linarith)]
      linarith
    have hcosh : coshHalfMoment F ^ 2 ≤ (Ch * (4 * r)) ^ 2 := by
      have h1 : |coshHalfMoment F| ≤ Ch * (4 * r) := by
        refine (show |coshHalfMoment F| ≤ Real.cosh (c / 2) * ∫ u, |F u| from hC).trans ?_
        exact mul_le_mul hCh hF1 (integral_nonneg fun _ => abs_nonneg _) (by positivity)
      have h0 := abs_nonneg (coshHalfMoment F)
      nlinarith [sq_abs (coshHalfMoment F)]
    have hθ : 2 * gammaHardyPhaseRate 0 * (∫ u, F u ^ 2) ≤ Θ * (4 * (2 * r)) := by
      have hsq0 : 0 ≤ ∫ u, F u ^ 2 := integral_nonneg fun _ => sq_nonneg _
      have hθ1 : 2 * gammaHardyPhaseRate 0 ≤ Θ := le_abs_self _
      have hm2 := integral_siteBump_sq_le hr
      calc 2 * gammaHardyPhaseRate 0 * (∫ u, F u ^ 2) ≤ Θ * (∫ u, F u ^ 2) :=
            mul_le_mul_of_nonneg_right hθ1 hsq0
        _ ≤ Θ * (4 * (2 * r)) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    nlinarith [sq_nonneg (sinhHalfMoment F)]
  have hplus := twoSite_reading hn₀ hr hg hrg hr2 hrc hlam 1
  have hminus := twoSite_reading hn₀ hr hg hrg hr2 hrc hlam (-1)
  have hAplus := hA 1 (by norm_num)
  have hAminus := hA (-1) (by norm_num)
  rw [hm] at hplus hminus
  set L := Real.log (1 / δ)
  have hlog : Real.log (1 / (2 * r)) = Real.log 2 + L := by
    rw [show 1 / (2 * r) = 2 * (1 / δ) by simp only [r]; field_simp; ring,
      Real.log_mul (by norm_num) (by positivity)]
  set Q := 4 * (2 * Θ) + 8 * (Real.log (1 / (2 * r)) + C₀) + 16 * Real.exp (1 / 2) * K +
    32 * Ch ^ 2 * r
  have hpos : 0 < 2 * (r * m₁) / Real.sqrt n₀ := by positivity
  have hw : |lam n₀| * (2 * (r * m₁) / Real.sqrt n₀) ≤ r * Q := by
    rcases abs_cases (lam n₀) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
  have h1 : |lam n₀| ≤ r * Q / (2 * (r * m₁) / Real.sqrt n₀) := (le_div_iff₀ hpos).mpr hw
  have h2 : r * Q / (2 * (r * m₁) / Real.sqrt n₀) = Real.sqrt n₀ * (Q / (2 * m₁)) := by
    field_simp
  have hΘ : 0 ≤ Θ := abs_nonneg _
  have hr4 : 16 * Ch ^ 2 * r ≤ 8 * Ch ^ 2 := by nlinarith [sq_nonneg Ch]
  have h3 : Q / (2 * m₁) ≤ 4 / m₁ * L +
      (4 * (2 * Θ) + 4 * (Real.log 2 + C₀) + 8 * Real.exp (1 / 2) * K + 8 * Ch ^ 2) / m₁ := by
    rw [show Q / (2 * m₁) = (Q / 2) / m₁ by ring, show 4 / m₁ * L +
      (4 * (2 * Θ) + 4 * (Real.log 2 + C₀) + 8 * Real.exp (1 / 2) * K + 8 * Ch ^ 2) / m₁ =
      (4 * L + (4 * (2 * Θ) + 4 * (Real.log 2 + C₀) + 8 * Real.exp (1 / 2) * K + 8 * Ch ^ 2)) / m₁
      by ring]
    refine div_le_div_of_nonneg_right ?_ hm₁.le
    simp only [Q]
    rw [hlog]
    linarith
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left h3 hsq.le)

end GaloisForLFunctions.FrustratedArithmeticDirichletForms
