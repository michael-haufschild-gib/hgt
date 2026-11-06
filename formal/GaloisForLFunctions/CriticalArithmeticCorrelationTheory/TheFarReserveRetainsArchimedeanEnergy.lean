import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTopCollarHasADyadicSeventhPowerReserve

/-!
# The far reserve retains archimedean energy

One quarter of the top archimedean form pays the dyadic aliasing reserve,
one half pays the high-frequency cross term, and one quarter remains.
After the window payment, one eighth of the aliasing reserve also remains.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology RHTower Zeta23 ArithmeticFunction
open scoped Classical BigOperators RealInnerProductSpace ArithmeticFunction Matrix CompactlySupported
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics ArithmeticEffectivityTheory
  ArithmeticPositivityTheory

/-- A quarter of the top archimedean form survives both the aliasing and Fourier allocations. -/
theorem top_block_ge_seventh_retaining_archForm {C_arch c : ℝ} (hc1 : 1 ≤ c) {N : ℕ}
    (hL2N : (linearDefectCutoff c : ℝ) ^ 2 ≤ N) (x : ℕ → ℝ)
    (harch_top : ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
      ((dyadicTopMassConstant / c ^ 7) * Real.log N *
          topCollarSeventhMass (N / linearDefectCutoff c) N x -
        C_arch * c * topCollarSeventhMass (N / linearDefectCutoff c) N x) ≤
      archForm (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
        (atomDilate tiltedUnitSpline (c / N))))
    {T : ℝ} (hT0 : 0 < T) :
    ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
        ((1 / 4 : ℝ) * ((dyadicTopMassConstant / c ^ 7) * Real.log N *
            topCollarSeventhMass (N / linearDefectCutoff c) N x -
          C_arch * c * topCollarSeventhMass (N / linearDefectCutoff c) N x) -
          topPrimeSeventhConstant * c *
            topCollarSeventhMass (N / linearDefectCutoff c) N x) +
      (1 / 2 : ℝ) * ((Real.log T - factorialSpanGammaOffset) *
          highFourierMass (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
            (atomDilate tiltedUnitSpline (c / N))) T -
        (factorialSpanGammaOffset + Real.log 2) *
          lowFourierMass (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
            (atomDilate tiltedUnitSpline (c / N))) T) +
      (1 / 4 : ℝ) * archForm (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
        (atomDilate tiltedUnitSpline (c / N))) ≤
      archForm (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
          (atomDilate tiltedUnitSpline (c / N))) -
        primeSum (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
          (atomDilate tiltedUnitSpline (c / N))) := by
  obtain ⟨hL3, -, -, -⟩ := linearDefectCutoff_bounds hc1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hLN : linearDefectCutoff c ≤ N := by
    have hLc_R : (3 : ℝ) ≤ linearDefectCutoff c := by exact_mod_cast hL3
    have : (linearDefectCutoff c : ℝ) ≤ N := by nlinarith only [hL2N, hLc_R]
    exact_mod_cast this
  have hNR : (0 : ℝ) < N := by
    have : 1 ≤ N := (by omega : 1 ≤ linearDefectCutoff c).trans hLN
    exact_mod_cast this
  have hw : 0 < c / (N : ℝ) := div_pos hc0 hNR
  set g := atomDilate tiltedUnitSpline (c / N)
  set y := atomicTailCoefficients (N / linearDefectCutoff c) x
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hsupp := tiltedUnitSpline_atom_support hw
  have hfy : ContDiff ℝ 2 (atomicTest N y g) := contDiff_atomicTest hg N y
  have hfyc : HasCompactSupport (atomicTest N y g) := hasCompactSupport_atomicTest hsupp N y
  have hband := archForm_ge_high_band hfy hfyc (T := T) (R := T) hT0 le_rfl
  rw [sub_self, zero_mul, add_zero] at hband
  have htop := (le_abs_self _).trans (abs_primeSum_top_le_seventh hc1 hLN x)
  linarith only [hband, htop, harch_top]


/-- The far window reserve preserves a positive fraction of the original top archimedean energy. -/
theorem exists_prefix_top_window_reserve_retaining_archForm :
    ∃ C_S C_P C_ψ c₀ t₀ : ℝ, 0 < C_S ∧ 0 < C_P ∧ 0 ≤ C_ψ ∧ 0 < c₀ ∧ 1 ≤ t₀ ∧
      ∀ {c : ℝ} {N : ℕ}, 1 ≤ c → (linearDefectCutoff c : ℝ) ^ 2 ≤ N →
      ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {h T : ℝ} {K' : ℕ}, 0 < h → h ≤ 1 → 0 < T →
        factorialSpanGammaOffset + 1 ≤ Real.log T → 1 ≤ K' → t₀ ≤ K' * Real.exp (-1) →
        (7 / 8 : ℝ) * poleDefect (N / linearDefectCutoff c) (primeHorizonExtension z) +
          (1 / 8 : ℝ) * (dyadicTopMassConstant / c ^ 7) * Real.log N *
            topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension z) -
          C_S * c *
            topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension z) -
          C_P * c * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) -
          16 * (1 + 2 * Real.exp 1 * c) / ((dyadicTopMassConstant / c ^ 7) * Real.log N) *
            (splineWindowConstant * ((c / N) / h ^ 2)) *
            windowSumBound C_ψ c₀ (((N / linearDefectCutoff c : ℕ) : ℝ) / 2)
              ⌊(N : ℝ) * Real.exp (c / N)⌋₊ (N / linearDefectCutoff c) K'
              (primeHorizonExtension z) h -
          (16 * (1 + 2 * Real.exp 1 * c) / ((dyadicTopMassConstant / c ^ 7) * Real.log N) *
              (T * h) ^ 2 + 8 / (Real.log T - factorialSpanGammaOffset)) *
            ((1 + 2 * Real.exp 1 * ((c / N) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊)) *
              (Real.log ⌊(N : ℝ) * Real.exp (c / N)⌋₊ *
                (Real.log (2 * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ /
                  (((N / linearDefectCutoff c : ℕ) : ℝ) / 2)) + 2 * (Real.log 4 + 4)))) *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) +
          ((1 / 4 : ℝ) * archForm (atomicTest N
            (atomicTailCoefficients (N / linearDefectCutoff c) (primeHorizonExtension z))
            (atomDilate tiltedUnitSpline (c / N)))) /
            ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) ≤
          completeWeilEnergy tiltedUnitSpline c N z := by
  obtain ⟨C_arch, hCarch, harch_top⟩ := exists_top_archForm_dyadic_seventh_reserve
  obtain ⟨C_ψ, c₀, t₀, hCψ, hc₀, ht₀1, hpnt⟩ := exists_vonMangoldtAtom_window_error
  have hG₀ : 0 ≤ factorialSpanGammaOffset := factorialSpanGammaOffset_nonneg
  have hC₄ : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith only [this]
  have hAsep : 0 ≤ separatedCrossMassCost := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    unfold separatedCrossMassCost; positivity
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hCtop7 : 0 < topPrimeSeventhConstant := topPrimeSeventhConstant_pos
  set E2 : ℝ := (factorialSpanGammaOffset + Real.log 2) / 2 + 2 * Real.pi
  have hE2 : 0 ≤ E2 := by
    have : 0 ≤ 2 * Real.pi := by positivity
    simp only [E2]; linarith
  let C_S := C_arch / 4 + E2 * (1 + 2 * Real.exp 1) + topPrimeSeventhConstant + 1
  let C_P := 1 + 2 * |gammaHardyPhaseRate 0| + 2 * separatedCrossMassCost + (Real.log 4 + 4) +
    2 * Real.pi
  have hCS : 0 < C_S := by
    have h1 : 0 ≤ E2 * (1 + 2 * Real.exp 1) := mul_nonneg hE2 (by positivity)
    simp only [C_S]; linarith
  have hCP : 0 < C_P := by
    have : 0 ≤ 2 * |gammaHardyPhaseRate 0| := by positivity
    have : 0 ≤ 2 * Real.pi := by positivity
    simp only [C_P]; linarith
  refine ⟨C_S, C_P, C_ψ, c₀, t₀, hCS, hCP, hCψ, hc₀, ht₀1, ?_⟩
  intro c N hc1 hL2N z hz h T K' hh hh1 hT0 hT hK' ht₀
  obtain ⟨hL3, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have h2LN : 2 * linearDefectCutoff c ≤ N := by
    have hLc_R : (3 : ℝ) ≤ linearDefectCutoff c := by exact_mod_cast hL3
    have : (2 * linearDefectCutoff c : ℝ) ≤ N := by nlinarith only [hL2N, hLc_R]
    exact_mod_cast this
  have hLN : linearDefectCutoff c ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hM : 1 ≤ N / linearDefectCutoff c :=
    (Nat.le_div_iff_mul_le (by omega : 0 < linearDefectCutoff c)).mpr (by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c / (N : ℝ) := div_pos hc0 hNR
  have hcN : c ≤ (N : ℝ) := by
    have hLNR : (linearDefectCutoff c : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hLNR, hc0]
  have hMN : N / linearDefectCutoff c ≤ N := Nat.div_le_self _ _
  have henergy := completeWeilEnergy_eq_arch_sub_primeSum hc0 hN2 hz
  rw [integral_atomDilate_sq hw] at henergy
  have hPb := prefix_block_ge hc1 hLN hM (primeHorizonExtension z)
  have hYb := top_block_ge_seventh_retaining_archForm hc1 hL2N (primeHorizonExtension z)
    (harch_top hc1 hL2N (primeHorizonExtension z)) hT0
  have hAb := archForm_prefix_top_split_ge hc1 hLN hM (primeHorizonExtension z)
  have hSb := primeSum_prefix_top_split hc1 h2LN (primeHorizonExtension z)
  obtain ⟨hFh, hF⟩ := translate_masses_le hCψ hc₀ hpnt hc1 h2LN (primeHorizonExtension z) hh hh1
    hK' ht₀
  set x := primeHorizonExtension z
  set M := N / linearDefectCutoff c
  set P := ∑ n ∈ Icc 1 M, x n ^ 2
  set S := ∑ n ∈ Ioc M N, x n ^ 2
  set S7 := topCollarSeventhMass M N x
  set w := c / (N : ℝ)
  set g := atomDilate tiltedUnitSpline w
  set G := w * ∫ u, tiltedUnitSpline u ^ 2
  set y := atomicTailCoefficients M x
  set δ := dyadicTopMassConstant / c ^ 7
  set Bn := ⌊(N : ℝ) * Real.exp w⌋₊
  set V : ℕ → ℝ := fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv (primeOrderCutoff N w) M x n
  set WSB := windowSumBound C_ψ c₀ ((M : ℝ) / 2) Bn M K' x h
  set Φ := (1 + 2 * Real.exp 1 * (w * Bn)) *
    (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4)))
  have hG : 0 < G := mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS7_0 : 0 ≤ S7 := topCollarSeventhMass_nonneg M N x
  have hS_le_S7 : S ≤ S7 := sum_sq_Ioc_le_topCollarSeventhMass M N x
  have hδ : 0 < δ := div_pos dyadicTopMassConstant_pos (by positivity)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hsupp := tiltedUnitSpline_atom_support hw
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hfy : ContDiff ℝ 2 (atomicTest N y g) := contDiff_atomicTest hg N y
  have hfyc : HasCompactSupport (atomicTest N y g) := hasCompactSupport_atomicTest hsupp N y
  set γc := 1 + 2 * Real.exp 1 * c
  have hγc : 0 < γc := by positivity
  have hfy2_S : (∫ u, atomicTest N y g u ^ 2) ≤ G * γc * S := by
    have h0 := integral_atomicTest_sq_le_of_le_horizon hg.continuous hgc hc0 hcN hsupp y
    rw [integral_atomDilate_sq hw, sum_atomicTailCoefficients_sq_eq_Ioc' hMN x] at h0
    exact h0
  have hfy2 : (∫ u, atomicTest N y g u ^ 2) ≤ G * γc * S7 :=
    hfy2_S.trans (mul_le_mul_of_nonneg_left hS_le_S7 (by positivity))
  have hAb' : archForm (atomicTest M x g) + archForm (atomicTest N y g) -
      2 * Real.pi * (G * P + G * γc * S7) ≤ archForm (atomicTest N x g) := by
    have hpiS : 2 * Real.pi * (G * γc * S) ≤ 2 * Real.pi * (G * γc * S7) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS_le_S7 (by positivity)) (by positivity)
    linarith only [hAb, hpiS]
  have hLMy := lowFourierMass_le_integral_sq hfy hfyc T
  set η := δ * Real.log N / (16 * γc)
  have hη : 0 < η := by positivity
  set lam := (Real.log T - factorialSpanGammaOffset) / 2
  have hlam : 0 < lam := by simp only [lam]; linarith only [hT]
  have hX := two_mul_abs_integral_mul_atomicTest_le (f := atomicTest N y g) hfy hfyc hg hsupp
    Bn V (T := T) hh hη hlam
  have hηinv : η⁻¹ = 16 * γc / (δ * Real.log N) := by simp only [η]; rw [inv_div]
  have hlaminv : lam⁻¹ * 4 = 8 / (Real.log T - factorialSpanGammaOffset) := by
    simp only [lam]; field_simp; ring
  have hfyη : η * (∫ u, atomicTest N y g u ^ 2) ≤ η * (G * γc * S7) :=
    mul_le_mul_of_nonneg_left hfy2 hη.le
  have hLMη : η * lowFourierMass (atomicTest N y g) T ≤ η * (G * γc * S7) :=
    mul_le_mul_of_nonneg_left (hLMy.trans hfy2) hη.le
  have hLME : (factorialSpanGammaOffset + Real.log 2) *
      lowFourierMass (atomicTest N y g) T ≤ (factorialSpanGammaOffset + Real.log 2) * (G * γc * S7) :=
    mul_le_mul_of_nonneg_left (hLMy.trans hfy2) (add_nonneg hG₀ hlog2)
  have hFhη : η⁻¹ * (∫ u, atomicTest Bn V (smoothedBump g h) u ^ 2) ≤
      η⁻¹ * (G * (splineWindowConstant * (w / h ^ 2)) * WSB) :=
    mul_le_mul_of_nonneg_left hFh (inv_nonneg.mpr hη.le)
  have hFη : η⁻¹ * ((T * h) ^ 2 * ∫ u, atomicTest Bn V g u ^ 2) ≤
      η⁻¹ * ((T * h) ^ 2 * (G * Φ * P)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF (sq_nonneg _)) (inv_nonneg.mpr hη.le)
  have hFlam : lam⁻¹ * (4 * ∫ u, atomicTest Bn V g u ^ 2) ≤ lam⁻¹ * (4 * (G * Φ * P)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF (by norm_num)) (inv_nonneg.mpr hlam.le)
  have hηG : 2 * (η * (G * γc * S7)) = G * ((δ / 8) * Real.log N * S7) := by
    simp only [η]; field_simp; ring
  have hlamHM : lam * highFourierMass (atomicTest N y g) T =
      (1 / 2 : ℝ) * ((Real.log T - factorialSpanGammaOffset) *
        highFourierMass (atomicTest N y g) T) := by simp only [lam]; ring
  have hXabs := le_abs_self (∫ u, atomicTest N y g u * atomicTest Bn V g u)
  have hcoefS : C_arch / 4 * c + topPrimeSeventhConstant * c + E2 * γc ≤ C_S * c := by
    have h2 : γc ≤ (1 + 2 * Real.exp 1) * c := by
      simp only [γc]; nlinarith only [hc1, Real.exp_pos 1]
    have h3 := mul_le_mul_of_nonneg_left h2 hE2
    simp only [C_S]
    nlinarith only [h3, hc0.le]
  have hcoefP : c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost +
      (Real.log 4 + 4) + 2 * Real.pi ≤ C_P * c := by
    have h1 : 2 * |gammaHardyPhaseRate 0| ≤ 2 * |gammaHardyPhaseRate 0| * c :=
      le_mul_of_one_le_right (by positivity) hc1
    have h2 : Real.log 4 + 4 ≤ (Real.log 4 + 4) * c := le_mul_of_one_le_right hC₄ hc1
    have h3 : 2 * Real.pi ≤ 2 * Real.pi * c := le_mul_of_one_le_right (by positivity) hc1
    simp only [C_P]
    nlinarith only [h1, h2, h3]
  have hSG : G * ((C_arch / 4 * c + topPrimeSeventhConstant * c + E2 * γc) * S7) ≤
      G * (C_S * c * S7) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoefS hS7_0) hG.le
  have hPG := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoefP hP0) hG.le
  rw [henergy, ← sub_div, le_div_iff₀ hG]
  rw [add_mul, div_mul_cancel₀ _ hG.ne']
  rw [hηinv] at hFhη hFη hX
  have hE2exp : G * (E2 * γc * S7) = (1 / 2 : ℝ) * ((factorialSpanGammaOffset + Real.log 2) *
      (G * γc * S7)) + 2 * Real.pi * (G * γc * S7) := by simp only [E2]; ring
  have hfinalF : (16 * γc / (δ * Real.log N) * (T * h) ^ 2 +
      8 / (Real.log T - factorialSpanGammaOffset)) * Φ * P * G =
      16 * γc / (δ * Real.log N) * ((T * h) ^ 2 * (G * Φ * P)) +
        lam⁻¹ * (4 * (G * Φ * P)) := by
    rw [← hlaminv]; ring
  have hfinalW : 16 * γc / (δ * Real.log N) * (splineWindowConstant * (w / h ^ 2)) * WSB * G =
      16 * γc / (δ * Real.log N) * (G * (splineWindowConstant * (w / h ^ 2)) * WSB) := by ring
  change ((7 / 8 : ℝ) * poleDefect M x + (1 / 8 : ℝ) * δ * Real.log N * S7 -
      C_S * c * S7 - C_P * c * P -
      16 * γc / (δ * Real.log N) * (splineWindowConstant * (w / h ^ 2)) * WSB -
      (16 * γc / (δ * Real.log N) * (T * h) ^ 2 +
        8 / (Real.log T - factorialSpanGammaOffset)) * Φ * P) * G +
      (1 / 4 : ℝ) * archForm (atomicTest N y g) ≤ _
  linarith only [hAb', hSb, hPb, hYb, hX, hXabs, hfyη, hLMη, hLME, hFhη, hFη, hFlam, hηG,
    hlamHM, hSG, hPG, hfinalF, hfinalW, hfy2, hE2exp]


private theorem mul_eq_quarter_mul {cp c th : ℝ} (hth : th ≠ 0) :
    cp * c = th / 4 * (4 * cp / th * c) := by
  field_simp [hth]

private theorem eta_num_eq {A g l c : ℝ} (hc : c ≠ 0) :
    A * (g * l) = (A * c ^ 7) * ((g / c ^ 7) * l) := by
  field_simp [hc]

private theorem window_mass_algebraic_eq {u c g0 l s w cb lm P' th : ℝ}
    (hg : g0 ≠ 0) (hl : l ≠ 0) (hth : th ≠ 0) :
    16 * u * c ^ 8 / (g0 * l) * s * ((c * w * (cb * lm)) * P') =
      th / 4 * l * P' * ((64 * u * s * w * cb / (g0 * th)) * (c ^ 9 * lm) / l ^ 2) := by
  field_simp [hg, hl, hth]; ring


/-- At every bounded critical ratio, the far reserve retains archimedean energy.
All remaining collar losses are a fixed multiple of `c` times seventh-power mass. -/
theorem exists_fixed_ratio_far_reserve_retaining_archForm :
    ∃ C_S : ℝ, 0 < C_S ∧ ∀ R : ℝ, 0 < R → ∀ B : ℕ, ∀ κ_P : ℝ, 0 < κ_P →
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
        c ≤ Real.log (N : ℝ) ^ (9 / 64 : ℝ) → c ^ 8 ≤ R * Real.log N →
        ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ∈ (conductorSubspace 1 N)ᗮ →
          (7 / 8 : ℝ) * poleDefect (N / linearDefectCutoff c) (primeHorizonExtension z) +
          (1 / 8 : ℝ) * (dyadicTopMassConstant / c ^ 7) * Real.log N *
            topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension z) -
          (C_S + 128 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 * R /
              dyadicTopMassConstant) * c *
            topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension z) -
          (κ_P * Real.log N / (1 + Real.log (Real.log N)) ^ B) *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) +
          ((1 / 4 : ℝ) * archForm (atomicTest N
            (atomicTailCoefficients (N / linearDefectCutoff c) (primeHorizonExtension z))
            (atomDilate tiltedUnitSpline (c / N)))) /
            ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) ≤
          completeWeilEnergy tiltedUnitSpline c N z := by
  obtain ⟨C_S, C_P, C_ψ, c₀, t₀, hCS, hCP, hCψ, hc₀, ht₀1, hres⟩ :=
    exists_prefix_top_window_reserve_retaining_archForm
  have hg₀ : 0 < dyadicTopMassConstant := dyadicTopMassConstant_pos
  have hκ_nn : 0 ≤ splineWindowConstant := splineWindowConstant_nonneg
  refine ⟨C_S, hCS, ?_⟩
  intro R hR B κ_P hκP
  let C_R : ℝ := 128 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 * R /
    dyadicTopMassConstant
  set α' : ℝ := 1 / 7
  have hα'0 : 0 < α' := by simp only [α']; norm_num
  set C_β := 1 + 25 / c₀ ^ 2 + |Real.log t₀|
  have hCβ : 0 ≤ C_β :=
    add_nonneg (add_nonneg zero_le_one (div_nonneg (by norm_num : (0 : ℝ) ≤ 25) (sq_nonneg c₀)))
      (abs_nonneg _)
  set C_B := C_β + 1 + (Real.log 4 + 4)
  set K₂ := Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) + 2 * (Real.log 4 + 4)
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev_ℓ : ∀ᶠ ℓ : ℝ in atTop,
      1 ≤ ℓ ∧
      8 * (256 * Real.exp 2 + 4) ≤ ℓ ∧
      2 * factorialSpanGammaOffset + 2 + Real.log (4 * C_ψ + 1) ≤ ℓ ^ α' ∧
      Real.log ℓ ≤ ℓ ^ α' ∧
      (4 * C_P / κ_P) * ℓ ^ (9 / 64 : ℝ) * (1 + Real.log ℓ) ^ B ≤ ℓ ^ (1 : ℝ) ∧
      (64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
        (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 /
        (dyadicTopMassConstant * κ_P)) * ℓ ^ (13 * α') * (1 + Real.log ℓ) ^ B ≤ ℓ ^ (2 : ℝ) ∧
      (256 * (1 + 2 * Real.exp 1) * (1 + 2 * Real.exp 2) * K₂ /
        (dyadicTopMassConstant * κ_P)) * ℓ ^ (9 * α' + 1) * (1 + Real.log ℓ) ^ (B + 1) ≤
        ℓ ^ (4 : ℝ) ∧
      (256 * (1 + 2 * Real.exp 2) * K₂ / κ_P) * ℓ ^ (9 / 64 + 1 : ℝ) *
        (1 + Real.log ℓ) ^ (B + 1) ≤ ℓ ^ (1 + α') ∧
      (|Real.log (2 * (Real.log 4 + 4))| + 4 + C_β) * ℓ ^ (2 * α') * (1 + Real.log ℓ) ^ 1 ≤
        ℓ ^ (1 : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (8 * (256 * Real.exp 2 + 4)),
      (tendsto_rpow_atTop hα'0).eventually_ge_atTop
        (2 * factorialSpanGammaOffset + 2 + Real.log (4 * C_ψ + 1)),
      eventually_mul_rpow_polylog_le_rpow hα'0 1 1,
      eventually_mul_rpow_polylog_le_rpow (by norm_num : (9 / 64 : ℝ) < 1) B _,
      eventually_mul_rpow_polylog_le_rpow (by simp only [α']; norm_num : 13 * α' < 2) B _,
      eventually_mul_rpow_polylog_le_rpow (by simp only [α']; norm_num : 9 * α' + 1 < 4) (B + 1) _,
      eventually_mul_rpow_polylog_le_rpow (by simp only [α']; norm_num : (9 / 64 + 1 : ℝ) < 1 + α')
        (B + 1) _,
      eventually_mul_rpow_polylog_le_rpow (by simp only [α']; norm_num : 2 * α' < 1) 1 _]
      with ℓ h1 h2 h3 h4 h5 h6 h7 h8 h9
    refine ⟨h1, h2, h3, ?_, h5, h6, h7, h8, h9⟩
    rw [Real.rpow_zero, mul_one, one_mul, pow_one] at h4
    linarith only [h4]
  filter_upwards [hlogN.eventually hev_ℓ, eventually_ge_atTop 2] with N hN hN2
  clear hev_ℓ
  intro c hc1 hc18 hc8_ub z hz
  obtain ⟨hℓ1, hℓ_L, hC0, hlogℓ, hQb, hQP, hQd, hQd', hQ5⟩ := hN
  set ℓ := Real.log (N : ℝ)
  have hℓpos : 0 < ℓ := zero_lt_one.trans_le hℓ1
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  have h1logℓ_pos : 0 < (1 + Real.log ℓ) ^ B := pow_pos (by linarith only [hlogℓ0]) B
  obtain ⟨θ, hθ_def⟩ : ∃ v, v = κ_P / (1 + Real.log ℓ) ^ B := ⟨_, rfl⟩
  have hθ : 0 < θ := hθ_def.symm ▸ div_pos hκP h1logℓ_pos
  have hθ_inv : ∀ X : ℝ, X / θ = (X / κ_P) * (1 + Real.log ℓ) ^ B := fun X => by
    rw [hθ_def, div_div_eq_mul_div, div_mul_eq_mul_div]
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNexp : Real.exp ℓ = N := Real.exp_log hNR
  have hcα' : c ≤ ℓ ^ α' :=
    hc18.trans (Real.rpow_le_rpow_of_exponent_le hℓ1 (by simp only [α']; norm_num))
  have hcℓ : c ≤ ℓ :=
    hc18.trans ((Real.rpow_le_rpow_of_exponent_le hℓ1 (by norm_num)).trans_eq (Real.rpow_one _))
  -- Verify `(linearDefectCutoff c : ℝ) ^ 2 ≤ N` from `Real.quadratic_le_exp_of_nonneg` at `ℓ / 2`
  have hL2N : (linearDefectCutoff c : ℝ) ^ 2 ≤ N := by
    obtain ⟨-, -, -, hLup⟩ := linearDefectCutoff_bounds hc1
    have hCL : 0 < 256 * Real.exp 2 + 4 := by positivity
    have hLc_ℓ : (linearDefectCutoff c : ℝ) ≤ (256 * Real.exp 2 + 4) * ℓ :=
      hLup.trans (mul_le_mul_of_nonneg_left hcℓ hCL.le)
    have hquad := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ ℓ / 2 by linarith only [hℓ1])
    have hℓ2_le : (256 * Real.exp 2 + 4) * ℓ ≤ Real.exp (ℓ / 2) := by
      have hm := mul_le_mul_of_nonneg_right hℓ_L hℓpos.le
      have h1 : (256 * Real.exp 2 + 4) * ℓ ≤ (ℓ / 2) ^ 2 / 2 := by
        linarith only [hm, (by ring : ℓ * ℓ = 8 * ((ℓ / 2) ^ 2 / 2))]
      linarith only [h1, hquad, hℓ1]
    calc (linearDefectCutoff c : ℝ) ^ 2
        ≤ ((256 * Real.exp 2 + 4) * ℓ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hLc_ℓ 2
      _ ≤ (Real.exp (ℓ / 2)) ^ 2 := pow_le_pow_left₀ (by positivity) hℓ2_le 2
      _ = Real.exp ℓ := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ = N := hNexp
  have h2LN : 2 * linearDefectCutoff c ≤ N := by
    obtain ⟨hL3, -, -, -⟩ := linearDefectCutoff_bounds hc1
    have hLc_R : (3 : ℝ) ≤ linearDefectCutoff c := by exact_mod_cast hL3
    have : (2 * linearDefectCutoff c : ℝ) ≤ N := by nlinarith only [hLc_R, hL2N]
    exact_mod_cast this
  obtain ⟨h, T, lam, β, K', hlam, hlam1, hhdef, hh0, hh1, hT0, hT, hlogT, hTh, hhℓ, hlamG, hK'1,
    ht₀', hpnt', hlogK', hK'le, hβ, hβ0⟩ := exists_far_parameters hCψ hc₀ ht₀1 hℓ1 hC0 hlogℓ
  have hexp := far_exp_le hNexp hc1 hcℓ hℓ1 hα'0 hlam hCβ hβ hQ5
  clear hQ5
  set M := N / linearDefectCutoff c
  set x := primeHorizonExtension z
  set P := ∑ n ∈ Icc 1 M, x n ^ 2
  set S7 := topCollarSeventhMass M N x
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS7_0 : 0 ≤ S7 := topCollarSeventhMass_nonneg M N x
  -- The prefix cost is negligible compared with its growing conductor reserve.
  have hb : C_P * c ≤ θ / 4 * ℓ := by
    rw [Real.rpow_one] at hQb
    have h1 : 4 * C_P / θ * c ≤ ℓ := by
      calc 4 * C_P / θ * c ≤ 4 * C_P / θ * ℓ ^ (9 / 64 : ℝ) :=
            mul_le_mul_of_nonneg_left hc18
              (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCP.le) hθ.le)
        _ = (4 * C_P / κ_P) * ℓ ^ (9 / 64 : ℝ) * (1 + Real.log ℓ) ^ B := by
            rw [hθ_inv]; ring
        _ ≤ ℓ := hQb
    calc C_P * c = θ / 4 * (4 * C_P / θ * c) := mul_eq_quarter_mul hθ.ne'
      _ ≤ θ / 4 * ℓ :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg hθ.le (by norm_num : (0 : ℝ) ≤ 4))
  clear hQb
  -- The pole window cost stays bounded at each fixed critical ratio.
  have hc_win : 16 * (1 + 2 * Real.exp 1 * c) / ((dyadicTopMassConstant / c ^ 7) * ℓ) *
        (splineWindowConstant * ((c / N) / h ^ 2)) *
        windowSumBound C_ψ c₀ ((M : ℝ) / 2) ⌊(N : ℝ) * Real.exp (c / N)⌋₊ M K' x h ≤
      C_R * c * S7 + θ / 4 * ℓ * P := by
    obtain ⟨hL3, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
    have hMN : M ≤ N := Nat.div_le_self _ _
    have hM1_nat : 1 ≤ M :=
      (Nat.le_div_iff_mul_le (by omega : 0 < linearDefectCutoff c)).mpr (by omega)
    have hσ_S7 : prefixPoleMoment M x ^ 2 ≤ S7 :=
      prefixPoleMoment_sq_le_topCollarSeventhMass hN2 hMN hz
    have hHM : prefixHarmonic M ≤ 1 + ℓ := by
      have h1 := RHTower.sum_Icc_one_div_le hM1_nat
      have h2 : Real.log (M : ℝ) ≤ ℓ :=
        Real.log_le_log (by exact_mod_cast hM1_nat) (by exact_mod_cast hMN)
      unfold prefixHarmonic; linarith only [h1, h2]
    have hH0 : 0 ≤ prefixHarmonic M :=
      sum_nonneg fun m _ => div_nonneg zero_le_one (Nat.cast_nonneg m)
    have hC₄ : 1 ≤ Real.log 4 + 4 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
    have hw0 : 0 < c / (N : ℝ) := div_pos hc0 hNR
    have hcN : c ≤ (N : ℝ) := by
      have hLNR : (linearDefectCutoff c : ℝ) ≤ N := by
        exact_mod_cast (show linearDefectCutoff c ≤ N by omega)
      linarith only [h4c, hLNR, hc0]
    have hw1 : c / (N : ℝ) ≤ 1 := (div_le_one hNR).mpr hcN
    have hwB : (c / (N : ℝ)) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ ≤ Real.exp 1 * c := by
      have hBn_le : (⌊(N : ℝ) * Real.exp (c / N)⌋₊ : ℝ) ≤ N * Real.exp (c / N) :=
        Nat.floor_le (by positivity)
      calc (c / (N : ℝ)) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊
          ≤ (c / (N : ℝ)) * (N * Real.exp (c / N)) := mul_le_mul_of_nonneg_left hBn_le hw0.le
        _ = c * Real.exp (c / N) := by rw [← mul_assoc, div_mul_cancel₀ _ hNR.ne']
        _ ≤ c * Real.exp 1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) hc0.le
        _ = Real.exp 1 * c := by ring
    have hAB : ((M : ℝ) / 2) ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := by
      have h1 : (N : ℝ) ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := by
        exact_mod_cast Nat.le_floor (le_mul_of_one_le_right hNR.le (Real.one_le_exp hw0.le))
      have h2 : (M : ℝ) ≤ N := by exact_mod_cast hMN
      linarith only [h1, h2]
    set ΛK := β + 1 + (Real.log 4 + 4)
    have hLK' : shortOrderWeight K' ≤ ΛK := by
      have := shortOrderWeight_le hK'1; simp only [ΛK]; linarith only [this, hlogK']
    have hΨK' : ∑ k ∈ range K', (Λ k : ℝ) ≤ (Real.log 4 + 4) * (2 * Real.exp β) :=
      (sum_vonMangoldt_range_le K').trans
        (mul_le_mul_of_nonneg_left hK'le (zero_le_one.trans hC₄))
    have hWS := windowSumBound_div_le (M := M) x hh0 hh1 hCψ hpnt' hw0.le hc0.le hwB
      (by positivity) hAB hLK' hΨK'
    have hwhΨ : ((c / (N : ℝ)) / h) * ((Real.log 4 + 4) * (2 * Real.exp β)) ≤ 1 := by
      rw [hhdef]; exact window_ratio_le hNR hℓpos hexp
    set ηi := 16 * (1 + 2 * Real.exp 1 * c) / ((dyadicTopMassConstant / c ^ 7) * ℓ)
    have hηi0 : 0 ≤ ηi := by simp only [ηi]; positivity
    have hηi : ηi ≤ 16 * (1 + 2 * Real.exp 1) * c ^ 8 / (dyadicTopMassConstant * ℓ) := by
      simp only [ηi]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hγ : 1 + 2 * Real.exp 1 * c ≤ (1 + 2 * Real.exp 1) * c := by
        nlinarith only [hc1, Real.exp_pos 1]
      rw [eta_num_eq hc0.ne']
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have := mul_le_mul_of_nonneg_left hγ (show (0 : ℝ) ≤ 16 * c ^ 7 by positivity)
      nlinarith only [this]
    have hX := mul_le_mul_of_nonneg_left hWS (mul_nonneg hηi0 hκ_nn)
    rw [show ηi * (splineWindowConstant * ((c / N) / h ^ 2)) *
        windowSumBound C_ψ c₀ ((M : ℝ) / 2) ⌊(N : ℝ) * Real.exp (c / N)⌋₊ M K' x h =
      (ηi * splineWindowConstant) * (((c / N) / h ^ 2) *
        windowSumBound C_ψ c₀ ((M : ℝ) / 2) ⌊(N : ℝ) * Real.exp (c / N)⌋₊ M K' x h) by ring]
    refine hX.trans ?_
    rw [mul_add]
    refine add_le_add ?_ ?_
    · have hηR : 16 * (1 + 2 * Real.exp 1) * c ^ 8 /
          (dyadicTopMassConstant * ℓ) ≤ 16 * (1 + 2 * Real.exp 1) * R / dyadicTopMassConstant := by
        have h := mul_le_mul_of_nonneg_left hc8_ub
          (show 0 ≤ 16 * (1 + 2 * Real.exp 1) by positivity)
        apply (div_le_div_iff₀ (mul_pos hg₀ hℓpos) hg₀).mpr
        nlinarith only [mul_le_mul_of_nonneg_right h hg₀.le]
      calc
        (ηi * splineWindowConstant) * (8 * Real.exp 2 * c * prefixPoleMoment M x ^ 2)
            ≤ (16 * (1 + 2 * Real.exp 1) * R / dyadicTopMassConstant * splineWindowConstant) *
                (8 * Real.exp 2 * c * S7) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hηi.trans hηR) hκ_nn)
            (mul_le_mul_of_nonneg_left hσ_S7 (by positivity)) (by positivity) (by positivity)
        _ = C_R * c * S7 := by dsimp only [C_R]; ring
    · -- Mass part `≤ θ / 4 * ℓ * P`
      have hL2K : Real.log (2 * K') ≤ ΛK + 1 := by
        have hK'R : (0 : ℝ) < K' := by exact_mod_cast hK'1
        rw [Real.log_mul (by norm_num) hK'R.ne']
        have := Real.log_two_lt_d9
        simp only [ΛK]; linarith only [hlogK', this, hC₄]
      have hΛK1 : 1 ≤ ΛK := by simp only [ΛK]; linarith only [hβ0, hC₄]
      have hΛKb : ΛK ≤ C_B * lam ^ 2 := by
        have hl2 : 1 ≤ lam ^ 2 := one_le_pow₀ hlam1
        simp only [ΛK, C_B]
        have := mul_le_mul_of_nonneg_left hl2
          (show (0 : ℝ) ≤ 1 + (Real.log 4 + 4) by linarith only [hC₄])
        linarith only [hβ, this]
      have hhH : h * prefixHarmonic M ≤ 2 := by
        have := mul_le_mul_of_nonneg_left hHM hh0.le; linarith only [this, hhℓ]
      have hh2H : h ^ 2 * prefixHarmonic M ≤ 2 := by
        calc h ^ 2 * prefixHarmonic M = h * (h * prefixHarmonic M) := by ring
          _ ≤ 1 * 2 := mul_le_mul hh1 hhH (mul_nonneg hh0.le hH0) zero_le_one
          _ = 2 := by ring
      have hΛ2 : ΛK ≤ ΛK ^ 2 := le_self_pow₀ hΛK1 two_ne_zero
      have hΛ1 : 1 ≤ ΛK ^ 2 := one_le_pow₀ hΛK1
      have hPc : 8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M) +
          48 * Real.exp 1 * c * h * prefixHarmonic M +
          2 * ΛK * (Real.exp 2 * c * ΛK +
            ((c / (N : ℝ)) / h) * ((Real.log 4 + 4) * (2 * Real.exp β))) ≤
          c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * ΛK ^ 2 := by
        have t1 : 1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M ≤ 11 * ΛK ^ 2 := by
          linarith only [hL2K, hh2H, hΛ2, hΛ1, hΛK1]
        have t1' := mul_le_mul_of_nonneg_left t1 (show 0 ≤ 8 * Real.exp 2 * c by positivity)
        have t2 : 48 * Real.exp 1 * c * h * prefixHarmonic M ≤ 96 * Real.exp 1 * c * ΛK ^ 2 := by
          have a1 := mul_le_mul_of_nonneg_left hhH (show 0 ≤ 48 * Real.exp 1 * c by positivity)
          have a2 := mul_le_mul_of_nonneg_left hΛ1 (show 0 ≤ 96 * Real.exp 1 * c by positivity)
          linarith only [a1, a2,
            (by ring : 48 * Real.exp 1 * c * h * prefixHarmonic M =
              48 * Real.exp 1 * c * (h * prefixHarmonic M))]
        have t3 : 2 * ΛK * (Real.exp 2 * c * ΛK +
            ((c / (N : ℝ)) / h) * ((Real.log 4 + 4) * (2 * Real.exp β))) ≤
            (2 * Real.exp 2 + 2) * c * ΛK ^ 2 := by
          have a1 := mul_le_mul_of_nonneg_left hwhΨ (show 0 ≤ 2 * ΛK by linarith only [hΛK1])
          have a2 : ΛK ^ 2 ≤ c * ΛK ^ 2 := le_mul_of_one_le_left (by positivity) hc1
          linarith only [a1, a2, hΛ2]
        have hcΛ : 0 ≤ (10 * Real.exp 2 + 4 * Real.exp 1 + 8) * (c * ΛK ^ 2) := by positivity
        linarith only [t1', t2, t3, hcΛ]
      have hΛsq : ΛK ^ 2 ≤ C_B ^ 2 * lam ^ 4 := by
        have := pow_le_pow_left₀ (by linarith) hΛKb 2
        rw [mul_pow, ← pow_mul] at this; exact this
      have hc9 : c ^ 9 ≤ ℓ ^ (9 * α') := pow_le_rpow_of_le_rpow hc1 hcα' hℓpos.le 9
      have hlam4 : lam ^ 4 = ℓ ^ (4 * α') := by
        rw [hlam, ← Real.rpow_natCast, ← Real.rpow_mul hℓpos.le]; ring_nf
      have hc13 : c ^ 9 * lam ^ 4 ≤ ℓ ^ (13 * α') := by
        rw [hlam4, show 13 * α' = 9 * α' + 4 * α' by ring, Real.rpow_add hℓpos]
        exact mul_le_mul_of_nonneg_right hc9 (by positivity)
      have hL2K0 : 0 ≤ 1 + Real.log (2 * K') := by
        have hK'R : (1 : ℝ) ≤ K' := by exact_mod_cast hK'1
        have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * K' by linarith only [hK'R])
        linarith only [this]
      have hwhΨ0 : 0 ≤ ((c / (N : ℝ)) / h) * ((Real.log 4 + 4) * (2 * Real.exp β)) := by
        have := zero_le_one.trans hC₄; positivity
      have hb1 : (ηi * splineWindowConstant) *
          ((8 * Real.exp 2 * c * (1 + Real.log (2 * K') + 4 * h ^ 2 * prefixHarmonic M) +
            48 * Real.exp 1 * c * h * prefixHarmonic M +
            2 * ΛK * (Real.exp 2 * c * ΛK +
              ((c / (N : ℝ)) / h) * ((Real.log 4 + 4) * (2 * Real.exp β)))) * P) ≤
          16 * (1 + 2 * Real.exp 1) * c ^ 8 / (dyadicTopMassConstant * ℓ) * splineWindowConstant *
            ((c * (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * (C_B ^ 2 * lam ^ 4)) * P) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hηi hκ_nn)
          (mul_le_mul_of_nonneg_right (hPc.trans (mul_le_mul_of_nonneg_left hΛsq (by positivity)))
            hP0) (by positivity) (by positivity)
      refine hb1.trans ?_
      rw [Real.rpow_two] at hQP
      have hAw_nn : 0 ≤ 64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
          (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 / (dyadicTopMassConstant * θ) :=
        div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64)
            (add_nonneg zero_le_one (mul_nonneg zero_le_two (Real.exp_pos 1).le))) hκ_nn)
          (add_nonneg (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) (Real.exp_pos 2).le)
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) (Real.exp_pos 1).le))
            (by norm_num : (0 : ℝ) ≤ 10)))
          (sq_nonneg C_B)) (mul_nonneg hg₀.le hθ.le)
      have hQP_θ : (64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
          (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 /
          (dyadicTopMassConstant * θ)) * (c ^ 9 * lam ^ 4) ≤ ℓ ^ 2 := by
        calc (64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
              (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 /
              (dyadicTopMassConstant * θ)) * (c ^ 9 * lam ^ 4)
            ≤ (64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
                (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 /
                (dyadicTopMassConstant * θ)) * ℓ ^ (13 * α') :=
              mul_le_mul_of_nonneg_left hc13 hAw_nn
          _ = (64 * (1 + 2 * Real.exp 1) * splineWindowConstant *
                (100 * Real.exp 2 + 100 * Real.exp 1 + 10) * C_B ^ 2 /
                (dyadicTopMassConstant * κ_P)) * ℓ ^ (13 * α') * (1 + Real.log ℓ) ^ B := by
              rw [← div_div, hθ_inv, div_div]; ring
          _ ≤ ℓ ^ 2 := hQP
      rw [window_mass_algebraic_eq hg₀.ne' hℓpos.ne' hθ.ne']
      calc _ ≤ θ / 4 * ℓ * P * 1 :=
            mul_le_mul_of_nonneg_left ((div_le_one (pow_pos hℓpos 2)).mpr hQP_θ)
              (mul_nonneg (mul_nonneg (div_nonneg hθ.le (by norm_num : (0 : ℝ) ≤ 4)) hℓpos.le) hP0)
        _ = θ / 4 * ℓ * P := mul_one _
  clear hQP
  -- 4. Translate cost `≤ (θ / 4) ℓ` via `far_cost_translate`
  have hd : (16 * (1 + 2 * Real.exp 1 * c) / ((dyadicTopMassConstant / c ^ 7) * ℓ) * (T * h) ^ 2 +
        8 / (Real.log T - factorialSpanGammaOffset)) *
      ((1 + 2 * Real.exp 1 * ((c / N) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊)) *
        (Real.log ⌊(N : ℝ) * Real.exp (c / N)⌋₊ *
          (Real.log (2 * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ / ((M : ℝ) / 2)) +
            2 * (Real.log 4 + 4)))) ≤ θ / 4 * ℓ := by
    have hK₂ : 0 ≤ K₂ := by
      have he1 := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
      have he2 := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
      have h1 : 0 ≤ Real.log (8 * Real.exp 1 * (256 * Real.exp 2 + 4)) :=
        Real.log_nonneg (by nlinarith only [he1, he2])
      have hl4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      simp only [K₂]; linarith only [h1, hl4]
    have hΦ := translate_factor_le hc1 h2LN
    set Φ := (1 + 2 * Real.exp 1 * ((c / N) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊)) *
      (Real.log ⌊(N : ℝ) * Real.exp (c / N)⌋₊ *
        (Real.log (2 * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4)))
    have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
    have hΦ' : Φ ≤ (1 + 2 * Real.exp 2) * K₂ * c * (2 * ℓ) * (1 + Real.log c) := by
      refine hΦ.trans ?_
      have h1 : 1 + ℓ ≤ 2 * ℓ := by linarith only [hℓ1]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h1
          (mul_nonneg (mul_nonneg
            (add_nonneg zero_le_one (mul_nonneg zero_le_two (Real.exp_pos 2).le)) hK₂) hc0.le))
        (by linarith only [hlogc0])
    have hΦ0 : 0 ≤ Φ := by
      have hN1 : 1 ≤ N := by omega
      have hBn1 : (1 : ℝ) ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := by
        have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        have : 1 ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := Nat.le_floor (by
          push_cast
          exact hN1R.trans (le_mul_of_one_le_right hNR.le
            (Real.one_le_exp (div_nonneg hc0.le hNR.le))))
        exact_mod_cast this
      have hlogBn := Real.log_nonneg hBn1
      have hM1_nat : 1 ≤ M :=
        (Nat.le_div_iff_mul_le (by have := (linearDefectCutoff_bounds hc1).1; omega)).mpr (by omega)
      have hMN : M ≤ N := Nat.div_le_self _ _
      have hrat : 1 ≤ 2 * (⌊(N : ℝ) * Real.exp (c / N)⌋₊ : ℝ) / ((M : ℝ) / 2) := by
        have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1_nat
        rw [le_div_iff₀ (by linarith only [hM1R])]
        have h1 : (M : ℝ) ≤ N := by exact_mod_cast hMN
        have h2 : (N : ℝ) ≤ ⌊(N : ℝ) * Real.exp (c / N)⌋₊ := by
          exact_mod_cast Nat.le_floor (le_mul_of_one_le_right hNR.le
            (Real.one_le_exp (div_nonneg hc0.le hNR.le)))
        linarith only [h1, h2]
      have h3 := Real.log_nonneg hrat
      have hl4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      refine mul_nonneg (add_nonneg zero_le_one (mul_nonneg
        (mul_nonneg zero_le_two (Real.exp_pos 1).le)
        (mul_nonneg (div_nonneg hc0.le hNR.le) (Nat.cast_nonneg _))))
        (mul_nonneg hlogBn (by linarith only [h3, hl4]))
    have hηi : 16 * (1 + 2 * Real.exp 1 * c) / ((dyadicTopMassConstant / c ^ 7) * ℓ) ≤
        16 * (1 + 2 * Real.exp 1) * c ^ 8 / (dyadicTopMassConstant * ℓ) := by
      rw [div_le_div_iff₀ (mul_pos (div_pos hg₀ (pow_pos hc0 7)) hℓpos) (mul_pos hg₀ hℓpos)]
      have hγ : 1 + 2 * Real.exp 1 * c ≤ (1 + 2 * Real.exp 1) * c := by
        nlinarith only [hc1, Real.exp_pos 1]
      rw [eta_num_eq hc0.ne']
      refine mul_le_mul_of_nonneg_right ?_ (mul_pos (div_pos hg₀ (pow_pos hc0 7)) hℓpos).le
      have := mul_le_mul_of_nonneg_left hγ
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) (pow_nonneg hc0.le 7))
      nlinarith only [this]
    have h9 := pow_le_rpow_of_le_rpow hc1 hcα' hℓpos.le 9
    push_cast at h9
    have hQd_θ : 256 * (1 + 2 * Real.exp 1) * (1 + 2 * Real.exp 2) * K₂ /
        (dyadicTopMassConstant * θ) * ℓ ^ (9 * α' + 1) * (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (4 : ℝ) := by
      refine le_trans (le_of_eq ?_) hQd
      rw [← div_div, hθ_inv, div_div, pow_one, pow_succ]
      ring
    have hQd'_θ : 256 * (1 + 2 * Real.exp 2) * K₂ / θ * ℓ ^ (9 / 64 + 1 : ℝ) *
        (1 + Real.log ℓ) ^ 1 ≤ ℓ ^ (1 + α') := by
      refine le_trans (le_of_eq ?_) hQd'
      rw [hθ_inv, pow_one, pow_succ]
      ring
    rw [hTh, hlogT]
    exact far_cost_translate hℓ1 hc1 hθ hg₀ hK₂ hηi hΦ' hΦ0 h9 hc18
      (Real.log_le_log hc0 hcℓ) hlogc0 hQd_θ hQd'_θ hlam hlamG (zero_lt_one.trans_le hlam1)
  clear hQd hQd'
  -- Assemble all four budgets
  have hE := hres hc1 hL2N hz hh0 hh1 hT0 hT hK'1 ht₀'
  clear hres
  have hbP := mul_le_mul_of_nonneg_right hb hP0
  have hdP := mul_le_mul_of_nonneg_right hd hP0
  have hθP_nn : 0 ≤ θ * ℓ * P := mul_nonneg (mul_nonneg hθ.le hℓpos.le) hP0
  have hid_θ : (κ_P * ℓ / (1 + Real.log ℓ) ^ B) * P = θ * ℓ * P := by
    rw [hθ_def]; ring
  have hcost : (C_S + C_R) * c * S7 = C_S * c * S7 + C_R * c * S7 := by ring
  change (7 / 8 : ℝ) * poleDefect M x +
      (1 / 8 : ℝ) * (dyadicTopMassConstant / c ^ 7) * ℓ * S7 -
      (C_S + C_R) * c * S7 - (κ_P * ℓ / (1 + Real.log ℓ) ^ B) * P +
      ((1 / 4 : ℝ) * archForm (atomicTest N (atomicTailCoefficients M x)
        (atomDilate tiltedUnitSpline (c / N)))) /
        ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) ≤ _
  linarith only [hE, hbP, hc_win, hdP, hθP_nn, hid_θ, hcost]


#print axioms top_block_ge_seventh_retaining_archForm
#print axioms exists_prefix_top_window_reserve_retaining_archForm
#print axioms exists_fixed_ratio_far_reserve_retaining_archForm
end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
