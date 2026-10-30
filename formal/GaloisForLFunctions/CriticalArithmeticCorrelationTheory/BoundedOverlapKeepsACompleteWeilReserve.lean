import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilFormKeepsADefectReserveAtEveryOverlap

import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapTiltedSplineReserve

/-!
# Bounded overlap keeps one complete Weil reserve

A single compact Fourier band gives the tilted spline a positive Gamma reserve throughout
`1 ≤ c ≤ K`. One ordered cutoff combines that reserve with separated prefix self-energy and
the prime-defect tail bound. The uniform signed arithmetic estimate then leaves a positive
complete defect coefficient, with one horizon and one square-mass cost for the whole interval.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology RHTower Zeta23
namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open ArithmeticElectrostatics RenormalizedArithmeticPotentialTheory ArithmeticCastelnuovoSeveri
  BiScaleUncertainty.ChebyshevGauge ArithmeticPositivityTheory

private theorem exists_tiltedUnitSpline_common_fourier_floor {K : ℝ} (hK : 1 ≤ K) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc (1 : ℝ) (101 * K),
      m ≤ ‖paperFT (cx tiltedUnitSpline) (t : ℂ)‖ ^ 2 := by
  have hd := EvenSector.differentiable_paperFT_of_compact
    (Complex.continuous_ofReal.comp contDiff_tiltedUnitSpline.continuous)
    (hasCompactSupport_tiltedUnitSpline.comp_left Complex.ofReal_zero)
  have hcont : Continuous (fun t : ℝ => ‖paperFT (cx tiltedUnitSpline) (t : ℂ)‖ ^ 2) :=
    (hd.continuous.comp Complex.continuous_ofReal).norm.pow 2
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (1 : ℝ) (101 * K)).Nonempty from ⟨1, le_rfl, by linarith only [hK]⟩)
    hcont.continuousOn
  refine ⟨_, ?_, fun r hr => hmin hr⟩
  exact sq_pos_of_pos (norm_pos_iff.mpr (paperFT_tiltedUnitSpline_real_ne_zero t))

private theorem tiltedUnitSpline_highBand_mass {c m : ℝ} (hc : 0 < c) (hm : 0 < m)
    (hfloor : ∀ t ∈ Set.Icc c (101 * c), m ≤ ‖paperFT (cx tiltedUnitSpline) (t : ℂ)‖ ^ 2)
    {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    (48 * (c / N) ^ 2 * m * N) * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      ∫ t in (N : ℝ)..101 * N,
        ‖paperFT (cx (atomicTest N x (atomDilate tiltedUnitSpline (c / N)))) (t : ℂ)‖ ^ 2 := by
  let w := c / (N : ℝ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < w := div_pos hc hNR
  have hwN : w * (N : ℝ) = c := by dsimp only [w]; field_simp [hNR.ne']
  have hg : ContDiff ℝ 2 (atomDilate tiltedUnitSpline w) :=
    contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest (tiltedUnitSpline_atom_support hw) N x
  have hhat := EvenSector.differentiable_paperFT_of_compact
    (Complex.continuous_ofReal.comp hf.continuous) (hfc.comp_left Complex.ofReal_zero)
  have hFcont : Continuous (fun t : ℝ =>
      ‖paperFT (cx (atomicTest N x (atomDilate tiltedUnitSpline w))) (t : ℂ)‖ ^ 2) :=
    (hhat.continuous.comp Complex.continuous_ofReal).norm.pow 2
  have hDcont : Continuous (fun t : ℝ => ‖dirichletPoly N x (t : ℂ)‖ ^ 2) := by
    unfold dirichletPoly
    fun_prop
  have hpoint : ∀ t ∈ Set.Icc (N : ℝ) (101 * N),
      (w ^ 2 * m) * ‖dirichletPoly N x (t : ℂ)‖ ^ 2 ≤
        ‖paperFT (cx (atomicTest N x (atomDilate tiltedUnitSpline w))) (t : ℂ)‖ ^ 2 := by
    intro t ht
    have hlow := mul_le_mul_of_nonneg_left ht.1 hw.le
    have hhigh := mul_le_mul_of_nonneg_left ht.2 hw.le
    have hmem : w * t ∈ Set.Icc c (101 * c) := by
      constructor <;> nlinarith only [hlow, hhigh, hwN]
    have hmval := hfloor (w * t) hmem
    rw [paperFT_atomicTest_atomDilate contDiff_tiltedUnitSpline.continuous
      hasCompactSupport_tiltedUnitSpline hw, ← Complex.ofReal_mul]
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hscaled := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hmval (sq_nonneg ‖dirichletPoly N x (t : ℂ)‖))
      (sq_nonneg w)
    simpa only [mul_assoc] using hscaled
  have hint := intervalIntegral.integral_mono_on (μ := volume)
    (show (N : ℝ) ≤ 101 * N by linarith only [hNR])
    ((hDcont.const_mul (w ^ 2 * m)).intervalIntegrable _ _)
    (hFcont.intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_const_mul] at hint
  have hMV := TransMetzlerWeilPositivity.BoundedOverlap.dirichletPoly_highBand_mass hN x
  calc
    _ = (w ^ 2 * m) * ((48 * N) * (∑ n ∈ Icc 1 N, x n ^ 2)) := by ring
    _ ≤ (w ^ 2 * m) * (∫ t in (N : ℝ)..101 * N, ‖dirichletPoly N x (t : ℂ)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hMV (mul_nonneg (sq_nonneg w) hm.le)
    _ ≤ _ := hint

/-- One Fourier band gives a uniform positive Gamma reserve on every bounded overlap interval. -/
theorem exists_tiltedUnitSpline_archForm_uniform_overlap_reserve {K : ℝ} (hK : 1 ≤ K) :
    ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, 0 ≤ b ∧ ∀ c : ℝ, 1 ≤ c → c ≤ K →
      ∀ N : ℕ, 1 ≤ N → ∀ x : ℕ → ℝ,
      (a * Real.log N - b) * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
        archForm (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) /
          ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) := by
  obtain ⟨m, hm, hfloor⟩ := exists_tiltedUnitSpline_common_fourier_floor hK
  let M := ∫ u, tiltedUnitSpline u ^ 2
  let a := 48 * m / (2 * Real.pi * M)
  let b := (factorialSpanGammaOffset + Real.log 2) * (1 + 2 * K * Real.exp K)
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hM : 0 < M := integral_tiltedUnitSpline_sq_pos
  have ha : 0 < a := by dsimp only [a]; positivity
  have hoffset : 0 ≤ factorialSpanGammaOffset + Real.log 2 :=
    add_nonneg factorialSpanGammaOffset_nonneg (Real.log_nonneg (by norm_num))
  refine ⟨a, ha, b, mul_nonneg hoffset (by positivity), ?_⟩
  intro c hc1 hcK N hN x
  have hc : 0 < c := zero_lt_one.trans_le hc1
  let w := c / (N : ℝ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < w := div_pos hc hNR
  have hg : ContDiff ℝ 2 (atomDilate tiltedUnitSpline w) :=
    contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc := hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hgsupp := tiltedUnitSpline_atom_support hw
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  have hgamma := archForm_ge_log_band_sub_mass hf hfc hNR
  have hband := tiltedUnitSpline_highBand_mass hc hm
    (fun t ht => hfloor t ⟨hc1.trans ht.1, ht.2.trans (mul_le_mul_of_nonneg_left hcK (by norm_num))⟩) hN x
  have hphysical0 := integral_atomicTest_sq_le_fixed_overlap hg.continuous hgc hc hN hgsupp x
  rw [integral_atomDilate_sq hw] at hphysical0
  have hQ : 1 + 2 * c * Real.exp c ≤ 1 + 2 * K * Real.exp K := by
    have he := mul_le_mul (mul_le_mul_of_nonneg_left hcK zero_le_two)
      (Real.exp_le_exp.mpr hcK) (Real.exp_pos c).le (by positivity : 0 ≤ 2 * K)
    linarith only [he]
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hphysical : (∫ u, atomicTest N x (atomDilate tiltedUnitSpline w) u ^ 2) ≤
      (w * M) * (1 + 2 * K * Real.exp K) * (∑ n ∈ Icc 1 N, x n ^ 2) :=
    hphysical0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ (mul_pos hw hM).le) hS)
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hbandCost := mul_le_mul_of_nonneg_left hband (div_nonneg hlog (by positivity : 0 ≤ 2 * Real.pi))
  have hmassCost := mul_le_mul_of_nonneg_left hphysical hoffset
  have hid : ((a * c * Real.log N - b) * (∑ n ∈ Icc 1 N, x n ^ 2)) * (w * M) =
      Real.log N / (2 * Real.pi) *
        ((48 * w ^ 2 * m * N) * (∑ n ∈ Icc 1 N, x n ^ 2)) -
      (factorialSpanGammaOffset + Real.log 2) *
        ((w * M) * (1 + 2 * K * Real.exp K) * (∑ n ∈ Icc 1 N, x n ^ 2)) := by
    dsimp only [a, b, w]
    field_simp [hM.ne', hNR.ne', Real.pi_ne_zero]
  have hscaled : (a * c * Real.log N - b) * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
      archForm (atomicTest N x (atomDilate tiltedUnitSpline w)) / (w * M) := by
    apply (le_div_iff₀ (mul_pos hw hM)).mpr
    rw [hid]
    linarith only [hgamma, hbandCost, hmassCost]
  have hcoef : a * Real.log N - b ≤ a * c * Real.log N - b := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc1 ha.le) hlog
    simp only [mul_one] at h
    linarith only [h]
  exact (mul_le_mul_of_nonneg_right hcoef hS).trans hscaled

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics ArithmeticEffectivityTheory

/-- One ordered cutoff pays the logarithmic counterterm at a strictly subunit defect cost
for every overlap in the bounded interval. -/
theorem exists_tiltedUnitSpline_gamma_uniform_overlap_payment {K : ℝ} (hK : 1 ≤ K) :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ x : ℕ → ℝ,
        Real.log N * (∑ n ∈ Icc 1 N, x n ^ 2) -
            (1 - a) * poleDefect N x - C * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
          archForm (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) /
            ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) := by
  obtain ⟨a₀, ha₀, b, hb, hband⟩ := exists_tiltedUnitSpline_archForm_uniform_overlap_reserve hK
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  let δ := min a₀ (1 / 2)
  have hδ : 0 < δ := lt_min ha₀ (by norm_num)
  have hδa : δ ≤ a₀ := min_le_left _ _
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  -- The cutoff separates low atoms and makes their defect cost smaller than the tail reserve.
  obtain ⟨L, hL⟩ := exists_nat_gt (max 1 (max (4 * K) (128 * Real.exp 2 * K / δ)))
  have hL1R : (1 : ℝ) < L := (le_max_left _ _).trans_lt hL
  have hL1 : 1 ≤ L := by exact_mod_cast hL1R.le
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL1
  have hLKc : 4 * K ≤ L :=
    (le_max_left (4 * K) _).trans ((le_max_right _ _).trans hL.le)
  have hLKδ : 128 * Real.exp 2 * K / δ ≤ L :=
    (le_max_right (4 * K) _).trans ((le_max_right _ _).trans hL.le)
  let A := separatedCrossMassCost
  let B := 1 + 2 * K * Real.exp K
  let C₀ := |Real.log K| + 2 * |gammaHardyPhaseRate 0| + 2 * K * A
  let R := Real.log (2 * (L : ℝ))
  let J := (Real.log 4 + 4) + (Real.log 8 + 4)
  let T := (1 + 4 / δ) * (R + J) + R
  let C := C₀ + b + 2 * Real.pi * B + (1 - δ) * T
  have hA : 0 ≤ A := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    dsimp only [A, separatedCrossMassCost]
    positivity
  have hB : 1 ≤ B := by
    have hp : 0 ≤ 2 * K * Real.exp K := by positivity
    dsimp only [B]
    linarith only [hp]
  have hB0 : 0 ≤ B := by linarith only [hB]
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hR : 0 ≤ R := Real.log_nonneg (by nlinarith only [hL1R])
  have hJ : 0 ≤ J := by
    have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    have h8 := Real.log_nonneg (show (1 : ℝ) ≤ 8 by norm_num)
    dsimp only [J]
    linarith only [h4, h8]
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hδle : 0 ≤ 1 - δ := by linarith only [hδ1]
  refine ⟨δ / 2, by positivity, C, by dsimp only [C]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop L] with N hLN
  intro c hc1 hcK x
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hLc : 4 * c ≤ (L : ℝ) := by linarith only [hcK, hLKc]
  have hLδ : 128 * Real.exp 2 * c / δ ≤ (L : ℝ) :=
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcK (by positivity : 0 ≤ 128 * Real.exp 2)) hδ.le).trans hLKδ
  have hBc : 1 + 2 * c * Real.exp c ≤ B := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hcK zero_le_two)
      (Real.exp_le_exp.mpr hcK) (Real.exp_pos c).le (by positivity : 0 ≤ 2 * K)
    dsimp only [B]
    linarith only [h]
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
      have habs : Real.log c - 2 * gammaHardyPhaseRate 0 ≤ |Real.log K| + 2 * |gammaHardyPhaseRate 0| := by
        have hlogc := Real.log_le_log hc hcK
        linarith only [hlogc, le_abs_self (Real.log K), neg_le_abs (gammaHardyPhaseRate 0)]
      have hcost := mul_le_mul_of_nonneg_right (hwMc.trans hcK) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)
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
    have hh := hband c hc1 hcK N hN y
    have ha := mul_le_mul_of_nonneg_right hδa (mul_nonneg hlog hS₁)
    have hbS := mul_le_mul_of_nonneg_left hS₁S hb
    change (a₀ * Real.log N - b) * S₁ ≤ archForm (atomicTest N y g) / G at hh
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
    have h := integral_atomicTest_sq_le_fixed_overlap hg.continuous hgc hc hN hsupp y
    rw [hmass] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hBc hG.le) hS₁)
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
  have htail : Real.log N * S₁ ≤ (1 + δ / 4) * poleDefect N x + T * S := by
    have ht := log_mul_tail_mass_le_defect hM hMN x (show 0 < 4 / δ by positivity)
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
  change Real.log N * S - (1 - δ / 2) * poleDefect N x - C * S ≤ _
  dsimp only [C]
  have hsplitLog := congrArg (fun z : ℝ => Real.log N * z) hsplit
  linarith only [hlo, hhi, hcombined, htpay, hgain, hsplitLog]

/-- The complete signed Weil form keeps one positive defect reserve over bounded overlap. -/
theorem exists_tiltedUnitSpline_complete_uniform_overlap_reserve {K : ℝ} (hK : 1 ≤ K) :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ x : ℕ → ℝ,
        a * poleDefect N x - C * (∑ n ∈ Icc 1 N, x n ^ 2) ≤
          weilQuad (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) /
            ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) := by
  obtain ⟨a, ha, C, hC, hgamma⟩ := exists_tiltedUnitSpline_gamma_uniform_overlap_payment hK
  let A := arithmeticRelativeCost K (a / 2)
  refine ⟨a / 2, by positivity, C + |A|, add_nonneg hC (abs_nonneg A), ?_⟩
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt K
  filter_upwards [hgamma, eventually_overlapArithmeticEnergy_ge_defect (zero_lt_one.trans_le hK)
    (show 0 < a / 2 by positivity), eventually_ge_atTop N₀, eventually_ge_atTop 1]
    with N hgam har hNN₀ hN
  intro c hc1 hcK x
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / (N : ℝ) := div_pos hc hNR
  have hw1 : c / (N : ℝ) ≤ 1 := by
    apply (div_le_one hNR).mpr
    exact hcK.trans (hN₀.le.trans (by exact_mod_cast hNN₀))
  let g := atomDilate tiltedUnitSpline (c / N)
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g := hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  have hmass : (∫ u, g u ^ 2) = (c / N) * ∫ u, tiltedUnitSpline u ^ 2 := integral_atomDilate_sq hw
  have hG : 0 < ∫ u, g u ^ 2 := by rw [hmass]; exact mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hs := har _ hw hw1 (div_le_div_of_nonneg_right hcK hNR.le) g hg.continuous hgc hsupp hG x
  have he := weilQuad_atomicTest_div_eq_arithmetic_add_gamma hg hsupp N x
  rw [hmass] at he
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  have hcost := mul_le_mul_of_nonneg_right (le_abs_self A) hS
  have hgamx := hgam c hc1 hcK x
  change (1 - a / 2) * poleDefect N x - A * _ ≤ overlapArithmeticEnergy g N x at hs
  change _ = overlapArithmeticEnergy g N x + _ - _ at he
  linarith only [hs, he, hgamx, hcost]

/-- The same common complete reserve in Euclidean matrix coordinates. -/
theorem exists_tiltedUnitSpline_completeWeilEnergy_uniform_overlap_reserve {K : ℝ} (hK : 1 ≤ K) :
    ∃ a : ℝ, ∃ β : ℝ, 0 < β ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K → ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a * ‖x‖ ^ 2 + β * poleDefect N (primeHorizonExtension x) ≤
        completeWeilEnergy tiltedUnitSpline c N x := by
  obtain ⟨β, hβ, C, -, hres⟩ := exists_tiltedUnitSpline_complete_uniform_overlap_reserve hK
  refine ⟨-C, β, hβ, ?_⟩
  filter_upwards [hres, eventually_ge_atTop 1] with N hN hN1
  intro c hc1 hcK x
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c / N := div_pos hc hNR
  have hmass : (∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2) =
      (c / N) * ∫ u, tiltedUnitSpline u ^ 2 := integral_atomDilate_sq hw
  have h := hN c hc1 hcK (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq] at h
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc hN1, hmass]
  linarith only [h]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.exists_tiltedUnitSpline_archForm_uniform_overlap_reserve
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_gamma_uniform_overlap_payment
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_complete_uniform_overlap_reserve
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_completeWeilEnergy_uniform_overlap_reserve
