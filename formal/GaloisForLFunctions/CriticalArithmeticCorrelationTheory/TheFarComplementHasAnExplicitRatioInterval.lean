import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheDyadicReserveHasAnExplicitConstant
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFarReserveRetainsArchimedeanEnergy
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalFarComplementRetainsTheCollarWeight
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis

/-!
# The far complement on an explicit interval of critical ratios

With `C_arch = dyadicArchConstant` explicit, the far reserve holds with explicit collar constants: every
loss of the top collar is `(C + C′R) c` per unit of seventh-power mass, and the reserve is
`(3/8) (D/c⁷) log N`, one eighth of the aliasing reserve plus the retained quarter of the top archimedean
energy.

At `c⁸ ≤ R log N` the balance is `c · farMargin R` with

`farMargin R = 3D/(8R) − C − C′R`,

which is positive exactly for `R < farRatioRoot`, the positive root of `C′R² + CR − 3D/8 = 0`
(`farMargin_pos_iff`). This is the size-only optimum of the far band, and on `0 < R < farRatioRoot` the
complete Weil form is coercive on the far complement (`far_complement_coercive_below_root`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology RHTower Zeta23 ArithmeticFunction
open scoped Classical BigOperators RealInnerProductSpace ArithmeticFunction Matrix CompactlySupported
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ExplicitShell
open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics ArithmeticEffectivityTheory
  ArithmeticPositivityTheory

/-- The explicit collar constant of the far reserve. -/
def farCollarConstant : ℝ :=
  dyadicArchConstant / 4 +
    ((factorialSpanGammaOffset + Real.log 2) / 2 + 2 * Real.pi) * (1 + 2 * Real.exp 1) +
    topPrimeSeventhConstant + 1

/-- The explicit ratio coefficient of the far reserve: the pole window cost per unit of `R`. -/
def farRatioConstant : ℝ :=
  128 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 / dyadicTopMassConstant

/-- The explicit cost of the terminal leak of the prefix defect. -/
def farLeakConstant : ℝ :=
  7 * (5 + Real.log (2 * (256 * Real.exp 2 + 4))) / (2 * explicitConductorCutoffConstant)

/-- All linear collar losses of the far complement. -/
def farLinearConstant : ℝ :=
  farCollarConstant + dyadicArchConstant / 4 + farLeakConstant

/-- The balance of the far band at critical ratio `R`, per unit of `c` and of collar mass. -/
def farMargin (R : ℝ) : ℝ :=
  3 * dyadicTopMassConstant / (8 * R) - farLinearConstant - farRatioConstant * R

/-- The positive root of `C′R² + CR − 3D/8 = 0`. -/
def farRatioRoot : ℝ :=
  (-farLinearConstant + Real.sqrt (farLinearConstant ^ 2 +
    4 * farRatioConstant * (3 * dyadicTopMassConstant / 8))) / (2 * farRatioConstant)

/-- The far window reserve preserves a positive fraction of the original top archimedean energy. -/
theorem exists_prefix_top_window_reserve_retaining_archForm :
    ∃ C_S C_P C_ψ c₀ t₀ : ℝ, C_S = farCollarConstant ∧ 0 < C_S ∧ 0 < C_P ∧ 0 ≤ C_ψ ∧ 0 < c₀ ∧ 1 ≤ t₀ ∧
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
  obtain ⟨C_arch, hCd, hCarch, harch_top⟩ := exists_top_archForm_dyadic_seventh_reserve
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
  refine ⟨C_S, C_P, C_ψ, c₀, t₀, (by dsimp only [C_S, E2]; rw [hCd]; rfl), hCS, hCP, hCψ, hc₀, ht₀1, ?_⟩
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
    ∃ C_S : ℝ, C_S = farCollarConstant ∧ 0 < C_S ∧ ∀ R : ℝ, 0 < R → ∀ B : ℕ, ∀ κ_P : ℝ, 0 < κ_P →
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
  obtain ⟨C_S, C_P, C_ψ, c₀, t₀, hCSd, hCS, hCP, hCψ, hc₀, ht₀1, hres⟩ :=
    exists_prefix_top_window_reserve_retaining_archForm
  have hg₀ : 0 < dyadicTopMassConstant := dyadicTopMassConstant_pos
  have hκ_nn : 0 ≤ splineWindowConstant := splineWindowConstant_nonneg
  refine ⟨C_S, hCSd, hCS, ?_⟩
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



/-! ### The ratio root -/

theorem farLinearConstant_pos : 0 < farLinearConstant := by
  have hD := explicitConductorCutoffConstant_pos
  have hH : (1 : ℝ) ≤ 2 * (256 * Real.exp 2 + 4) := by nlinarith only [Real.exp_pos 2]
  have hlog := Real.log_nonneg hH
  have hgap : 0 ≤ factorialSpanGammaOffset + Real.log 2 :=
    add_nonneg factorialSpanGammaOffset_nonneg (Real.log_nonneg one_le_two)
  have hA : 0 ≤ dyadicArchConstant := by
    obtain ⟨_, hd, h0, -⟩ := exists_top_archForm_dyadic_seventh_reserve
    exact hd ▸ h0
  have hE : 0 ≤ ((factorialSpanGammaOffset + Real.log 2) / 2 + 2 * Real.pi) * (1 + 2 * Real.exp 1) := by
    positivity
  have hT := topPrimeSeventhConstant_pos
  have hL : 0 ≤ farLeakConstant := by unfold farLeakConstant; positivity
  unfold farLinearConstant farCollarConstant
  linarith only [hA, hE, hT, hL]

theorem farRatioConstant_pos : 0 < farRatioConstant := by
  have hg := dyadicTopMassConstant_pos
  have hw : 0 < splineWindowConstant := by
    unfold splineWindowConstant
    have hm : (∫ u, tiltedUnitSpline u) ≠ 0 := integral_tiltedUnitSpline_ne_zero
    have h2 : 0 < (∫ u, tiltedUnitSpline u) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hm).symm
    exact div_pos h2 integral_tiltedUnitSpline_sq_pos
  unfold farRatioConstant
  positivity

private theorem quadratic_root_spec {C B D : ℝ} (hC : 0 < C) (hB : 0 < B) (hD : 0 < D) :
    0 < (-B + Real.sqrt (B ^ 2 + 4 * C * D)) / (2 * C) ∧
      C * ((-B + Real.sqrt (B ^ 2 + 4 * C * D)) / (2 * C)) ^ 2 +
        B * ((-B + Real.sqrt (B ^ 2 + 4 * C * D)) / (2 * C)) = D := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (B ^ 2 + 4 * C * D) := ⟨_, rfl⟩
  rw [← hs]
  have hrad : 0 ≤ B ^ 2 + 4 * C * D := by positivity
  have hs2 : s ^ 2 = B ^ 2 + 4 * C * D := by rw [hs, Real.sq_sqrt hrad]
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hsB : B < s := by
    have hlt : B ^ 2 < s ^ 2 := by rw [hs2]; nlinarith only [mul_pos hC hD]
    exact lt_of_pow_lt_pow_left₀ 2 hs0 hlt
  have hC2 : 0 < 2 * C := by positivity
  refine ⟨div_pos (by linarith only [hsB]) hC2, ?_⟩
  obtain ⟨r, hr⟩ : ∃ r, r = (-B + s) / (2 * C) := ⟨_, rfl⟩
  rw [← hr]
  have hrC : 2 * C * r = s - B := by
    rw [hr]
    field_simp
    ring
  have h0 : 4 * C * (C * r ^ 2 + B * r - D) = 0 := by
    linear_combination (2 * C * r + B + s) * hrC + hs2
  have hne : 4 * C ≠ 0 := by positivity
  have h1 := (mul_eq_zero.mp h0).resolve_left hne
  linarith only [h1]

/-- **The root is positive and it annihilates the far balance.** -/
theorem farRatioRoot_spec :
    0 < farRatioRoot ∧ farRatioConstant * farRatioRoot ^ 2 + farLinearConstant * farRatioRoot =
      3 * dyadicTopMassConstant / 8 :=
  quadratic_root_spec farRatioConstant_pos farLinearConstant_pos
    (by have := dyadicTopMassConstant_pos; positivity)

/-- **The far balance is positive exactly below the root.** -/
theorem farMargin_pos_iff {R : ℝ} (hR : 0 < R) : 0 < farMargin R ↔ R < farRatioRoot := by
  obtain ⟨hr, hroot⟩ := farRatioRoot_spec
  have hC := farRatioConstant_pos
  have hB := farLinearConstant_pos
  have hfactor : 0 < farRatioConstant * (R + farRatioRoot) + farLinearConstant := by positivity
  have hid : farMargin R * R =
      (farRatioRoot - R) * (farRatioConstant * (R + farRatioRoot) + farLinearConstant) := by
    unfold farMargin
    field_simp
    nlinarith only [hroot]
  constructor
  · intro h
    have hpos : 0 < farMargin R * R := mul_pos h hR
    rw [hid] at hpos
    have := (pos_iff_pos_of_mul_pos hpos).mpr hfactor
    linarith only [this]
  · intro h
    have hpos : 0 < farMargin R * R := by
      rw [hid]
      exact mul_pos (by linarith only [h]) hfactor
    exact (pos_iff_pos_of_mul_pos hpos).mpr hR

/-! ### The far complement at a fixed ratio -/

private theorem le_rpow_nine_of_ratio {c L R : ℝ} (hc0 : 0 < c) (hL0 : 0 < L)
    (hRL : R ≤ L ^ (1 / 8 : ℝ)) (hc8 : c ^ 8 ≤ R * L) : c ≤ L ^ (9 / 64 : ℝ) := by
  have hpow : c ^ 8 ≤ (L ^ (9 / 64 : ℝ)) ^ 8 := by
    have e : (L ^ (9 / 64 : ℝ)) ^ 8 = L ^ (1 / 8 : ℝ) * L := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_add_one hL0.ne']
      norm_num
    rw [e]
    exact hc8.trans (mul_le_mul_of_nonneg_right hRL hL0.le)
  exact (pow_le_pow_iff_left₀ hc0.le (Real.rpow_nonneg hL0.le _) (by norm_num)).mp hpow

/-- **The far complement at a fixed critical ratio.** The conductor gap pays the prefix. The collar
keeps three eighths of its aliasing reserve against linear losses `(C + C′R) c`. -/
theorem eventually_far_complement_at_ratio {R : ℝ} (hR : 0 < R) :
    ∀ᶠ N : ℕ in atTop, ∀ c θ : ℝ, 1 ≤ c → c ^ 8 ≤ R * Real.log N →
      1 / (1 + Real.log (Real.log (N : ℝ))) ^ 5 ≤ θ → θ ≤ 1 / 4096 →
      ∀ z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N)ᗮ,
        (θ * Real.log N / (8 * explicitConductorCutoffConstant)) *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) +
          ((3 / 8 : ℝ) * (dyadicTopMassConstant / c ^ 7) * Real.log N -
              (farLinearConstant + farRatioConstant * R) * c) *
            topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension z) ≤
          completeWeilEnergy tiltedUnitSpline c N z := by
  obtain ⟨C_S, hCSd, -, hfixed⟩ := exists_fixed_ratio_far_reserve_retaining_archForm
  obtain ⟨C_arch, hCad, -, harch⟩ := exists_top_archForm_dyadic_seventh_reserve
  let D := explicitConductorCutoffConstant
  let g := dyadicTopMassConstant
  let H := 256 * Real.exp 2 + 4
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  have hg : 0 < g := dyadicTopMassConstant_pos
  have hH1 : 1 ≤ H := by
    dsimp only [H]
    linarith only [Real.exp_pos 2]
  have hlogH : 0 ≤ Real.log (2 * H) := Real.log_nonneg (by linarith only [hH1])
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hfixed R hR 5 (1 / (16 * D)) (by positivity),
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually_ge_atTop (2000 + H),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 1) (4 * D + 4)),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hLlim).eventually_ge_atTop R]
    with N hfixN hLX hlarge hpoly hRL
  intro c θ hc1 hc8 hθlo hθhi z hz
  let L := Real.log (N : ℝ)
  let T := linearDefectCutoff c
  let M := N / T
  let Rc := ⌊(N : ℝ) ^ θ⌋₊
  have hL2000 : 2000 ≤ L := by linarith only [hlarge, hH1]
  have hL1 : 1 ≤ L := by linarith only [hL2000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have ht : 0 < (1 + Real.log L) ^ 5 := by
    have := Real.log_nonneg hL1
    positivity
  have hθ : 0 < θ := (one_div_pos.mpr ht).trans_le hθlo
  have hθ36 : θ ≤ 1 / 36 := hθhi.trans (by norm_num)
  have hθ1 : θ ≤ 1 := hθhi.trans (by norm_num)
  have hθL : 4 * D + 4 ≤ θ * L := by
    have hpoly' : (4 * D + 4) * (1 + Real.log L) ^ 5 ≤ L := by
      simpa only [Real.rpow_one] using hpoly
    have h₁ := (le_div_iff₀ ht).mpr hpoly'
    have h₂ := mul_le_mul_of_nonneg_right hθlo hL0.le
    change 1 / (1 + Real.log L) ^ 5 * L ≤ θ * L at h₂
    calc
      _ ≤ L / (1 + Real.log L) ^ 5 := h₁
      _ ≤ θ * L := (by ring : L / (1 + Real.log L) ^ 5 =
        1 / (1 + Real.log L) ^ 5 * L).trans_le h₂
  have h2θ : 2 / θ ≤ L := by
    rw [div_le_iff₀ hθ]
    linarith only [hθL, hD]
  have h4Dθ : 4 * D / θ ≤ L := by
    rw [div_le_iff₀ hθ]
    linarith only [hθL]
  have hN1 : 1 ≤ N := by
    by_contra hn
    have : N = 0 := by omega
    subst this
    simp [L] at hL0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNθ4 : 4 ≤ (N : ℝ) ^ θ := by
    rw [Real.rpow_def_of_pos hN0]
    have h := Real.add_one_le_exp (L * θ)
    change 4 ≤ Real.exp (L * θ)
    linarith only [h, hθL, hD]
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc18 : c ≤ L ^ (9 / 64 : ℝ) := le_rpow_nine_of_ratio hc0 hL0 hRL hc8
  have hcL : c ≤ L := hc18.trans ((Real.rpow_le_rpow_of_exponent_le hL1
    (by norm_num : (9 / 64 : ℝ) ≤ 1)).trans_eq (Real.rpow_one L))
  obtain ⟨hR2, hTN, hRM, hM2, hhalf, hlogM, hgap, hlogR⟩ :=
    critical_prefix_cutoff_geometry hθ hθ36 hc1 hcL hL2000
      (by linarith only [hlarge]) h2θ h4Dθ hLX hNθ4
  change Real.log (Rc : ℝ) ≤ θ * L at hlogR
  have hlogM0 : 0 < Real.log (M : ℝ) := (by positivity : 0 < L / 2).trans_le hhalf
  have hk : 0 < Real.log (Rc : ℝ) / D - 1 := (by positivity : 0 < θ / (4 * D) * L).trans_le hgap
  have hscale : D ≤ Real.log (Rc : ℝ) := by
    have h := (lt_div_iff₀ hD).mp (show 1 < Real.log (Rc : ℝ) / D by linarith only [hk])
    linarith only [h]
  have hpre := poleDefect_prefix_ge_of_conductor_orthogonal hR2 hM2
    (Nat.div_le_self N T) hRM hlogM hscale hz
  have hz1 : z ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hz v (conductorSubspace_mono (by omega : 1 ≤ Rc) N hv)
  have hf := hfixN c hc1 hc18 hc8 hz1
  obtain ⟨hT3, -, -, hTup⟩ := linearDefectCutoff_bounds hc1
  have hTB := terminalPacketCost_nat_div_le (Q := Rc) (by omega) hTN hRM
  have hlog2T : Real.log (2 * (T : ℝ)) ≤ Real.log (2 * H) + c := by
    have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
    have h := Real.log_le_log (show 0 < 2 * (T : ℝ) by positivity)
      (mul_le_mul_of_nonneg_left hTup zero_le_two)
    rw [show 2 * (H * c) = (2 * H) * c by ring,
      Real.log_mul (by positivity) hc0.ne'] at h
    linarith only [h, Real.log_le_sub_one_of_pos hc0]
  let B := terminalPacketCost Rc M N / Real.log (M : ℝ)
  let k := Real.log (Rc : ℝ) / D - 1
  have hB0 : 0 ≤ B := div_nonneg (terminalPacketCost_nonneg Rc (Nat.div_le_self N T)) hlogM0.le
  have hB : B ≤ 2 * (4 + Real.log (2 * H) + c) / L := by
    apply (div_le_div_iff₀ hlogM0 hL0).mpr
    have hcost : terminalPacketCost Rc M N ≤ 4 + Real.log (2 * H) + c := by
      linarith only [hTB, hlog2T]
    have hnum : 0 ≤ 4 + Real.log (2 * H) + c := by positivity
    change L / 2 ≤ Real.log (M : ℝ) at hhalf
    have h₁ := mul_le_mul_of_nonneg_right hcost hL0.le
    have h₂ := mul_le_mul_of_nonneg_left hhalf hnum
    nlinarith only [h₁, h₂]
  have hkL : k ≤ L / D := by
    have h₁ := div_le_div_of_nonneg_right hlogR hD.le
    have h₂ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hθ1 hL0.le) hD.le
    simp only [one_mul] at h₂
    exact (sub_le_self _ zero_le_one).trans (h₁.trans h₂)
  have hleak : (7 / 4 : ℝ) * k * B ≤ farLeakConstant * c := by
    calc
      _ ≤ (7 / 4 : ℝ) * (L / D) * (2 * (4 + Real.log (2 * H) + c) / L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hkL (by norm_num)) hB hB0 (by positivity)
      _ = 7 * (4 + Real.log (2 * H) + c) / (2 * D) := by field_simp; ring
      _ ≤ farLeakConstant * c := by
        have h := mul_nonneg (show 0 ≤ 4 + Real.log (2 * H) by positivity) (sub_nonneg.mpr hc1)
        have hnum : 7 * (4 + Real.log (2 * H) + c) ≤
            7 * (5 + Real.log (2 * H)) * c := by nlinarith only [h]
        refine (div_le_div_of_nonneg_right hnum (show 0 ≤ 2 * D by positivity)).trans_eq ?_
        unfold farLeakConstant
        ring
  let P := ∑ n ∈ Icc 1 M, primeHorizonExtension z n ^ 2
  let S := ∑ n ∈ Ioc M N, primeHorizonExtension z n ^ 2
  let S7 := topCollarSeventhMass M N (primeHorizonExtension z)
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hS7 : S ≤ S7 := sum_sq_Ioc_le_topCollarSeventhMass M N _
  have hleakS : (7 / 4 : ℝ) * k * B * S ≤ farLeakConstant * c * S7 := by
    refine (mul_le_mul_of_nonneg_right hleak hS).trans ?_
    have hleak0 : 0 ≤ farLeakConstant * c := by
      unfold farLeakConstant
      positivity
    exact mul_le_mul_of_nonneg_left hS7 hleak0
  have hprefixCost : (1 / (16 * D) * L / (1 + Real.log L) ^ 5) * P ≤
      (θ * L / (16 * D)) * P := by
    apply mul_le_mul_of_nonneg_right _ hP
    have h := mul_le_mul_of_nonneg_right hθlo (show 0 ≤ L / (16 * D) by positivity)
    convert h using 1 <;> ring
  have hgapP := mul_le_mul_of_nonneg_right hgap hP
  change θ / (4 * D) * L * P ≤ k * P at hgapP
  let A := θ * L / D * P
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hgapA : A / 4 ≤ k * P := by
    convert hgapP using 1 <;> dsimp only [A] <;> ring
  have hcostA : (1 / (16 * D) * L / (1 + Real.log L) ^ 5) * P ≤ A / 16 :=
    hprefixCost.trans_eq (by dsimp only [A]; ring)
  -- the retained archimedean quarter is at least a quarter of the top reserve
  have hLN2 : (linearDefectCutoff c : ℝ) ^ 2 ≤ N := by
    have hTL : (T : ℝ) ≤ L * L :=
      hTup.trans (mul_le_mul (by linarith only [hlarge]) hcL hc0.le hL0.le)
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have hp : (N : ℝ) ^ (1 / 36 : ℝ) ^ 1 = (N : ℝ) ^ (1 / 36 : ℝ) := by norm_num
    have hX : L ≤ (N : ℝ) ^ (1 / 36 : ℝ) := hLX
    have hX0 : 0 ≤ (N : ℝ) ^ (1 / 36 : ℝ) := Real.rpow_nonneg hN0.le _
    have hX36 : ((N : ℝ) ^ (1 / 36 : ℝ)) ^ 36 = N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      norm_num
    have hX1 : 1 ≤ (N : ℝ) ^ (1 / 36 : ℝ) := hL1.trans hX
    calc (linearDefectCutoff c : ℝ) ^ 2 ≤ (L * L) ^ 2 := pow_le_pow_left₀ hT0 hTL 2
      _ ≤ ((N : ℝ) ^ (1 / 36 : ℝ) * (N : ℝ) ^ (1 / 36 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul hX hX hL0.le hX0) 2
      _ = ((N : ℝ) ^ (1 / 36 : ℝ)) ^ 4 := by ring
      _ ≤ ((N : ℝ) ^ (1 / 36 : ℝ)) ^ 36 := pow_le_pow_right₀ hX1 (by norm_num)
      _ = N := hX36
  have htop := harch hc1 hLN2 (primeHorizonExtension z)
  have hG : 0 < (c / N) * ∫ u, tiltedUnitSpline u ^ 2 :=
    mul_pos (div_pos hc0 hN0) integral_tiltedUnitSpline_sq_pos
  have hquarter : (1 / 4 : ℝ) * ((g / c ^ 7) * L * S7 - C_arch * c * S7) ≤
      ((1 / 4 : ℝ) * archForm (atomicTest N (atomicTailCoefficients M (primeHorizonExtension z))
        (atomDilate tiltedUnitSpline (c / N)))) / ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) := by
    rw [le_div_iff₀ hG]
    have h := mul_le_mul_of_nonneg_left htop (by norm_num : (0 : ℝ) ≤ 1 / 4)
    change (1 / 4 : ℝ) * (((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
      ((g / c ^ 7) * L * S7 - C_arch * c * S7)) ≤ _ at h
    refine le_trans (le_of_eq ?_) h
    ring
  change (7 / 8 : ℝ) * poleDefect M (primeHorizonExtension z) +
    (1 / 8 : ℝ) * (g / c ^ 7) * L * S7 -
    (C_S + 128 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 * R / g) * c * S7 -
    (1 / (16 * D) * L / (1 + Real.log L) ^ 5) * P +
    ((1 / 4 : ℝ) * archForm (atomicTest N (atomicTailCoefficients M (primeHorizonExtension z))
      (atomDilate tiltedUnitSpline (c / N)))) / ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) ≤ _ at hf
  simp only [mul_div_assoc] at hpre
  change k * ((15 / 16 : ℝ) * P - 2 * B * S) ≤ poleDefect M (primeHorizonExtension z) at hpre
  have hRcoef : 128 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 * R / g =
      farRatioConstant * R := by
    change _ = 128 * (1 + 2 * Real.exp 1) * splineWindowConstant * Real.exp 2 / g * R
    ring
  rw [hRcoef, hCSd] at hf
  rw [hCad] at hquarter
  change (θ * L / (8 * D)) * P +
    ((3 / 8 : ℝ) * (g / c ^ 7) * L - (farLinearConstant + farRatioConstant * R) * c) * S7 ≤ _
  have hAeq : (θ * L / (8 * D)) * P = A / 8 := by dsimp only [A]; ring
  rw [hAeq]
  have hlin : farLinearConstant = farCollarConstant + dyadicArchConstant / 4 + farLeakConstant := rfl
  rw [hlin]
  have hpre' : (7 / 8 : ℝ) * (k * ((15 / 16 : ℝ) * P - 2 * B * S)) ≤
      (7 / 8 : ℝ) * poleDefect M (primeHorizonExtension z) :=
    mul_le_mul_of_nonneg_left hpre (by norm_num)
  nlinarith only [hf, hquarter, hpre', hleakS, hgapA, hcostA, hA]

/-- **The size-only balance.** Above the far conductor cutoff the collar keeps `c · farMargin R`. -/
theorem eventually_far_complement_margin {R : ℝ} (hR : 0 < R) :
    ∀ᶠ N : ℕ in atTop, ∀ c θ : ℝ, 1 ≤ c → c ^ 8 ≤ R * Real.log N →
      1 / (1 + Real.log (Real.log (N : ℝ))) ^ 5 ≤ θ → θ ≤ 1 / 4096 →
      ∀ z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N)ᗮ,
        (θ * Real.log N / (8 * explicitConductorCutoffConstant)) *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) +
          (c * farMargin R) *
            topCollarSeventhMass (N / linearDefectCutoff c) N (primeHorizonExtension z) ≤
          completeWeilEnergy tiltedUnitSpline c N z := by
  filter_upwards [eventually_far_complement_at_ratio hR] with N hN
  intro c θ hc1 hc8 hθlo hθhi z hz
  refine le_trans ?_ (hN c θ hc1 hc8 hθlo hθhi z hz)
  refine add_le_add (le_refl _) (mul_le_mul_of_nonneg_right ?_ (topCollarSeventhMass_nonneg _ _ _))
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hg := dyadicTopMassConstant_pos
  have hratio : c * (3 * dyadicTopMassConstant / (8 * R)) ≤
      (3 / 8 : ℝ) * (dyadicTopMassConstant / c ^ 7) * Real.log N := by
    have e : c * (3 * dyadicTopMassConstant / (8 * R)) = (3 / 8 : ℝ) * dyadicTopMassConstant * (c ^ 8 / R) / c ^ 7 := by
      field_simp
    rw [e]
    have h1 : c ^ 8 / R ≤ Real.log N := by
      rw [div_le_iff₀ hR]
      linarith only [hc8]
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (3 / 8 : ℝ) * dyadicTopMassConstant)
    have h3 := div_le_div_of_nonneg_right h2 (by positivity : 0 ≤ c ^ 7)
    refine h3.trans_eq ?_
    field_simp
  unfold farMargin
  nlinarith only [hratio]

/-- **The certified ratio interval.** For every ratio below the explicit root, the complete Weil form
is coercive on the far complement, with floor `min 1 (farMargin R)`. -/
theorem far_complement_coercive_below_root {R : ℝ} (hR : 0 < R) (hRr : R < farRatioRoot) :
    ∀ᶠ N : ℕ in atTop, ∀ c θ : ℝ, 1 ≤ c → c ^ 8 ≤ R * Real.log N →
      1 / (1 + Real.log (Real.log (N : ℝ))) ^ 5 ≤ θ → θ ≤ 1 / 4096 →
      ∀ z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N)ᗮ,
        min 1 (farMargin R) * ‖z‖ ^ 2 ≤ completeWeilEnergy tiltedUnitSpline c N z := by
  have hm : 0 < farMargin R := (farMargin_pos_iff hR).mpr hRr
  have hD := explicitConductorCutoffConstant_pos
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_far_complement_margin hR,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 1) (8 * explicitConductorCutoffConstant)),
    hLlim.eventually_ge_atTop 1] with N hN hpoly hL1
  intro c θ hc1 hc8 hθlo hθhi z hz
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  obtain ⟨M, hMd⟩ : ∃ M, M = N / linearDefectCutoff c := ⟨_, rfl⟩
  have hMN : M ≤ N := by rw [hMd]; exact Nat.div_le_self _ _
  have hE := hN c θ hc1 hc8 hθlo hθhi z hz
  rw [← hMd] at hE
  obtain ⟨P, hPd⟩ : ∃ P, P = ∑ n ∈ Icc 1 M, primeHorizonExtension z n ^ 2 := ⟨_, rfl⟩
  obtain ⟨S7, hS7d⟩ : ∃ S7, S7 = topCollarSeventhMass M N (primeHorizonExtension z) := ⟨_, rfl⟩
  rw [← hPd, ← hS7d] at hE
  have hP : 0 ≤ P := by rw [hPd]; exact sum_nonneg fun _ _ => sq_nonneg _
  have hS7 : 0 ≤ S7 := by rw [hS7d]; exact topCollarSeventhMass_nonneg _ _ _
  have hnorm : ‖z‖ ^ 2 ≤ P + S7 := by
    have hS := sum_sq_Ioc_le_topCollarSeventhMass M N (primeHorizonExtension z)
    have hsplit : ‖z‖ ^ 2 = (∑ n ∈ Icc 1 M, primeHorizonExtension z n ^ 2) +
        ∑ n ∈ Ioc M N, primeHorizonExtension z n ^ 2 := by
      rw [← sum_primeHorizonExtension_sq z, Ioc_eq_Icc_sdiff_Icc_telescoped M N, add_comm]
      exact (sum_sdiff (Icc_subset_Icc le_rfl hMN)).symm
    rw [hsplit, hPd, hS7d]
    linarith only [hS]
  -- the prefix coefficient is at least one
  have ht : 0 < (1 + Real.log (Real.log (N : ℝ))) ^ 5 := by
    have := Real.log_nonneg hL1
    positivity
  have hpre1 : 1 ≤ θ * Real.log N / (8 * explicitConductorCutoffConstant) := by
    have hpoly' : (8 * explicitConductorCutoffConstant) *
        (1 + Real.log (Real.log (N : ℝ))) ^ 5 ≤ Real.log N := by
      simpa only [Real.rpow_one] using hpoly
    have h₁ := (le_div_iff₀ ht).mpr hpoly'
    have h₂ := mul_le_mul_of_nonneg_right hθlo hL0.le
    rw [one_le_div (by positivity)]
    refine h₁.trans (le_trans (le_of_eq ?_) h₂)
    ring
  have hmin : 0 ≤ min 1 (farMargin R) := le_min zero_le_one hm.le
  have h1 : min 1 (farMargin R) * P ≤ (θ * Real.log N / (8 * explicitConductorCutoffConstant)) * P :=
    mul_le_mul_of_nonneg_right ((min_le_left _ _).trans hpre1) hP
  have h2 : min 1 (farMargin R) * S7 ≤ (c * farMargin R) * S7 := by
    refine mul_le_mul_of_nonneg_right ((min_le_right _ _).trans ?_) hS7
    exact le_mul_of_one_le_left hm.le hc1
  have h3 := mul_le_mul_of_nonneg_left hnorm hmin
  nlinarith only [h1, h2, h3, hE]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ExplicitShell
