import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTopPrimeSelfFormCostsOnlyALogarithm
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheWindowSumsOfThePrimeTranslateCancelOffThePole
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheHodgeIndexAtGrowingOverlap
import GaloisForLFunctions.SuccessorShellArithmetic.TheNonRatioFormIsAFiniteSumOfShells

/-!
# The far reserve through the window average

On `(V_1)ᗮ`, split a horizon vector `x` at `M = N / linearDefectCutoff c` into a separated prefix
and a top `y`. Then:

* the prefix keeps `(7/8) D_M` against an `O(c)` mass cost (`prefix_block_ge`);
* the top keeps the growing reserve `δ log N` per unit mass on half of its Gamma form, the other
  half pays its frequencies above `T`, and its prime self-form costs `O(c(1 + log c))`
  (`top_block_ge`);
* the archimedean cross of prefix and top is ordered and costs `2π` per unit mass
  (`archForm_prefix_top_split_ge`);
* the prime cross is the pairing of the top with the prime translate of the prefix on the top
  window (`primeSum_prefix_top_split`). Its window average is bounded through the window sums of
  the translate (`translate_masses_le`), its frequencies above `T` by the Gamma form, and its
  frequencies below `T` by `(T h)²` (`two_mul_abs_integral_mul_atomicTest_le`).

Assembled, `exists_completeWeilEnergy_prefix_top_window_reserve` bounds the complete Weil energy
below by `(7/8) D_M + (3/8) δ log N · S` minus explicit costs in the smoothing length `h`, the
Gamma threshold `T` and the short-row cutoff `K'`. The pole moment of the prefix enters through
`windowSumBound`; on `(V_1)ᗮ` it is bounded by the top (`prefixPoleMoment_sq_le`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology RHTower Zeta23 ArithmeticFunction
open scoped Classical BigOperators RealInnerProductSpace ArithmeticFunction Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics ArithmeticEffectivityTheory
  ArithmeticPositivityTheory

/-- The complete Weil energy of a pole-orthogonal vector is the archimedean form minus the prime
form of its atomic test, per unit atom mass. -/
theorem completeWeilEnergy_eq_arch_sub_primeSum {c : ℝ} (hc0 : 0 < c) {N : ℕ} (hN2 : 2 ≤ N)
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hz : z ∈ (conductorSubspace 1 N)ᗮ) :
    completeWeilEnergy tiltedUnitSpline c N z =
      archForm (atomicTest N (primeHorizonExtension z) (atomDilate tiltedUnitSpline (c / N))) /
          (∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2) -
        primeSum (atomicTest N (primeHorizonExtension z) (atomDilate tiltedUnitSpline (c / N))) /
          (∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2) := by
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  set x := primeHorizonExtension z
  set w := c / (N : ℝ)
  set g := atomDilate tiltedUnitSpline w
  have hw : 0 < w := div_pos hc0 hNR
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  have hpole_zero :
      (∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
        (∫ u, atomicTest N x g u * Real.exp (u / 2)) = 0 := by
    rw [integral_atomicTest_mul_exp_neg_half hg.continuous hsupp N x,
      poleFunctional_eq_zero_of_mem_conductorSubspace_one_orthogonal hN2 hz, mul_zero, zero_mul]
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc0 hN1]
  have he := weilQuad_atomicTest_div_eq_arithmetic_add_gamma hg hsupp N x
  rw [he]
  unfold overlapArithmeticEnergy overlapPrimeEnergy
  rw [hpole_zero]
  ring

/-- Restricting the coefficients to `[1, M]` gives the prefix atomic test. -/
theorem atomicTest_restrict_prefix {M N : ℕ} (hMN : M ≤ N) (x : ℕ → ℝ) (g : ℝ → ℝ) :
    atomicTest N (fun n => if n ≤ M then x n else 0) g = atomicTest M x g := by
  funext u
  unfold atomicTest
  have : ∑ n ∈ Icc 1 N, (if n ≤ M then x n else 0) * g (u - Real.log n) =
      ∑ n ∈ (Icc 1 N).filter (· ≤ M), x n * g (u - Real.log n) := by
    rw [sum_filter]; exact sum_congr rfl fun n _ => by split_ifs <;> ring
  rw [this]
  congr 1
  ext n; simp only [mem_filter, mem_Icc]; omega

/-- Coefficients vanishing above `B` give the same atomic test at every larger horizon. -/
theorem atomicTest_eq_of_vanish_above {B N' : ℕ} (hBN : B ≤ N') {x : ℕ → ℝ}
    (hx : ∀ n, B < n → x n = 0) (g : ℝ → ℝ) : atomicTest N' x g = atomicTest B x g := by
  funext u
  unfold atomicTest
  refine (sum_subset (Icc_subset_Icc le_rfl hBN) fun n hn hnB => ?_).symm
  have : B < n := by
    by_contra h; exact hnB (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, not_lt.mp h⟩)
  rw [hx n this, zero_mul]

theorem primeConv_congr {K M : ℕ} {x x' : ℕ → ℝ} (h : ∀ m ∈ Icc 1 M, x m = x' m) (n : ℕ) :
    primeConv K M x n = primeConv K M x' n := by
  unfold primeConv
  exact sum_congr rfl fun k _ => sum_congr rfl fun m hm => by rw [h m hm]

/-- `2|∫ f h| ≤ η ∫ f² + η⁻¹ ∫ h²`. -/
theorem two_mul_abs_integral_mul_le_whole {f k : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {η : ℝ}
    (hη : 0 < η) : 2 * |∫ u, f u * k u| ≤ η * (∫ u, f u ^ 2) + η⁻¹ * ∫ u, k u ^ 2 := by
  have h := two_mul_abs_integral_mul_le hf hfc hk hkc 0 hη hη
  have h1 := lowFourierMass_add_highFourierMass hf hfc 0
  have h2 := lowFourierMass_add_highFourierMass hk hkc 0
  have e1 : η * lowFourierMass f 0 + η * highFourierMass f 0 = η * (∫ u, f u ^ 2) := by
    rw [← mul_add, h1]
  have e2 : η⁻¹ * lowFourierMass k 0 + η⁻¹ * highFourierMass k 0 = η⁻¹ * ∫ u, k u ^ 2 := by
    rw [← mul_add, h2]
  calc 2 * |∫ u, f u * k u|
      ≤ η * lowFourierMass f 0 + η⁻¹ * lowFourierMass k 0 + η * highFourierMass f 0 +
          η⁻¹ * highFourierMass k 0 := h
    _ = (η * lowFourierMass f 0 + η * highFourierMass f 0) +
          (η⁻¹ * lowFourierMass k 0 + η⁻¹ * highFourierMass k 0) := by ring
    _ = η * (∫ u, f u ^ 2) + η⁻¹ * ∫ u, k u ^ 2 := by rw [e1, e2]

/-- The prefix pairing with the pole is the negative of the top pairing, so
`σ² ≤ (Σ_{M < n ≤ N} 1/n) · S` on `(V_1)ᗮ`. -/
theorem prefixPoleMoment_sq_le {N M : ℕ} (hN2 : 2 ≤ N) (hMN : M ≤ N)
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hz : z ∈ (conductorSubspace 1 N)ᗮ) :
    prefixPoleMoment M (primeHorizonExtension z) ^ 2 ≤
      (∑ n ∈ Ioc M N, (1 : ℝ) / n) * ∑ n ∈ Ioc M N, primeHorizonExtension z n ^ 2 := by
  set x := primeHorizonExtension z
  have hpole := poleFunctional_eq_zero_of_mem_conductorSubspace_one_orthogonal hN2 hz
  change ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 at hpole
  have hsplit : ∑ n ∈ Icc 1 N, x n / Real.sqrt n =
      ∑ n ∈ Icc 1 M, x n / Real.sqrt n + ∑ n ∈ Ioc M N, x n / Real.sqrt n := by
    have hdisj : Icc 1 N = Icc 1 M ∪ Ioc M N := by
      ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
    rw [hdisj, sum_union]
    exact disjoint_left.mpr fun n h1 h2 => by
      simp only [mem_Icc] at h1; simp only [mem_Ioc] at h2; omega
  have hσ : prefixPoleMoment M x = -∑ n ∈ Ioc M N, x n / Real.sqrt n := by
    unfold prefixPoleMoment; linarith
  rw [hσ, neg_sq]
  have hcs := sum_mul_sq_le_sq_mul_sq (Ioc M N) (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) x
  have e1 : ∀ n : ℕ, 1 / Real.sqrt (n : ℝ) * x n = x n / Real.sqrt n := fun n => by ring
  have e2 : ∀ n : ℕ, (1 / Real.sqrt n) ^ 2 = (1 : ℝ) / n := fun n => by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_pow]
  simp only [e1, e2] at hcs
  exact hcs

theorem sum_atomicTailCoefficients_sq_eq_Ioc' {M N : ℕ} (hMN : M ≤ N) (x : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, atomicTailCoefficients M x n ^ 2) = ∑ n ∈ Ioc M N, x n ^ 2 := by
  have h1 := sum_sq_prefix_add_tail hMN x
  have hIoc : (Ioc M N : Finset ℕ) = Icc 1 N \ Icc 1 M := by
    ext n; rw [mem_Ioc, Finset.mem_sdiff, mem_Icc, mem_Icc]; omega
  have h2 : (∑ n ∈ Icc 1 M, x n ^ 2) + (∑ n ∈ Ioc M N, x n ^ 2) = ∑ n ∈ Icc 1 N, x n ^ 2 := by
    rw [hIoc, add_comm]
    exact sum_sdiff (Icc_subset_Icc le_rfl hMN)
  linarith only [h1, h2]

/-- The window constant `(∫ φ)² / ∫ φ²` of the tilted spline. -/
def splineWindowConstant : ℝ := (∫ u, tiltedUnitSpline u) ^ 2 / ∫ u, tiltedUnitSpline u ^ 2

/-- **The separated prefix block.** With `M = N / linearDefectCutoff c`, the prefix atomic test
keeps `(7/8) D_M` against an `O(c)` mass cost:
`G ((7/8) D_M − (c + 2|γ₀| + 2c A_sep + log 4 + 4) P) ≤ arch(f_P) − P(f_P)`. -/
theorem prefix_block_ge {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ} (hLN : linearDefectCutoff c ≤ N)
    (hM : 1 ≤ N / linearDefectCutoff c) (x : ℕ → ℝ) :
    ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
        ((7 / 8 : ℝ) * poleDefect (N / linearDefectCutoff c) x -
          (c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost + (Real.log 4 + 4)) *
            ∑ n ∈ Icc 1 (N / linearDefectCutoff c), x n ^ 2) ≤
      archForm (atomicTest (N / linearDefectCutoff c) x (atomDilate tiltedUnitSpline (c / N))) -
        primeSum (atomicTest (N / linearDefectCutoff c) x (atomDilate tiltedUnitSpline (c / N))) := by
  obtain ⟨hL3, h4c, h256, -⟩ := linearDefectCutoff_bounds hc1
  set L := linearDefectCutoff c with hL_def
  set M := N / L with hM_def
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL1 : 1 ≤ L := by omega
  have hN1 : 1 ≤ N := hL1.trans hLN
  have hMN : M ≤ N := Nat.div_le_self N L
  have hML : (M : ℝ) * L ≤ N := by exact_mod_cast Nat.div_mul_le_self N L
  have hlogMN : Real.log M ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast hMN)
  clear_value L M
  set P := ∑ n ∈ Icc 1 M, x n ^ 2
  set w := c / (N : ℝ)
  set g := atomDilate tiltedUnitSpline w
  set G := w * ∫ u, tiltedUnitSpline u ^ 2
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL1
  have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hcN : c ≤ (N : ℝ) := by
    have hLNR : (L : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hLNR, hc0]
  have hw : 0 < w := div_pos hc0 hNR
  have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
  have hwN : w * N = c := by simp only [w]; field_simp [hNR.ne']
  have hwM : w * M ≤ c / L := by
    apply (le_div_iff₀ hLR).mpr
    calc w * M * L = w * ((M : ℝ) * L) := by ring
      _ ≤ w * N := mul_le_mul_of_nonneg_left hML hw.le
      _ = c := hwN
  have hwMc : w * M ≤ c :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hMN) hw.le).trans_eq hwN
  have hsep : w ≤ atomSpacing M / 2 := by
    have hfour : 4 * w * M ≤ 1 := by
      have hl : 4 * (c / (L : ℝ)) ≤ 1 := by
        rw [← mul_div_assoc, div_le_one hLR]; exact h4c
      nlinarith only [hwM, hl]
    have hbound : w ≤ (1 / ((M : ℝ) + 1)) / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < M + 1)).mpr
      nlinarith only [hfour, mul_nonneg hw.le (sub_nonneg.mpr hM1R)]
    exact hbound.trans (div_le_div_of_nonneg_right (atomSpacing_bounds hM).1 (by norm_num))
  have hsmall_pre : 32 * Real.exp 2 * w * M ≤ 1 / 8 := by
    have hcost : 32 * Real.exp 2 * (c / (L : ℝ)) ≤ 1 / 8 := by
      rw [← mul_div_assoc, div_le_iff₀ hLR]
      linarith only [h256]
    calc 32 * Real.exp 2 * w * M = (32 * Real.exp 2) * (w * M) := by ring
      _ ≤ (32 * Real.exp 2) * (c / (L : ℝ)) := mul_le_mul_of_nonneg_left hwM (by positivity)
      _ ≤ 1 / 8 := hcost
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hG : 0 < G := mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  have hmass : (∫ u, g u ^ 2) = G := integral_atomDilate_sq hw
  have hAsep : 0 ≤ separatedCrossMassCost := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    unfold separatedCrossMassCost; positivity
  have hlogc_le : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc0
  -- archimedean side
  have hraw := archForm_atomicTest_ge_separated_defect hg hgc hsupp hM hw hw1 hsep x
  rw [hmass] at hraw
  have hlogw : Real.log (1 / w) = Real.log N - Real.log c := by
    simp only [w]; rw [one_div_div, Real.log_div hNR.ne' hc0.ne']
  have hcoef : Real.log N - (c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost) ≤
      2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - 2 * w * M * separatedCrossMassCost := by
    have habs : Real.log c - 2 * gammaHardyPhaseRate 0 ≤ c + 2 * |gammaHardyPhaseRate 0| := by
      linarith only [hlogc_le, neg_le_abs (gammaHardyPhaseRate 0)]
    have hcost := mul_le_mul_of_nonneg_right hwMc
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hAsep)
    rw [hlogw]
    linarith only [habs, hcost]
  have hpay := mul_le_mul_of_nonneg_right hsmall_pre (poleDefect_nonneg M x)
  have hleft := mul_le_mul_of_nonneg_right hcoef hP
  have harch : G * (Real.log N * P -
      (c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost) * P -
      (1 / 8 : ℝ) * poleDefect M x) ≤ archForm (atomicTest M x g) := by
    refine (mul_le_mul_of_nonneg_left ?_ hG.le).trans hraw
    linarith only [hleft, hpay]
  -- prime side: no non-ratio lags among separated atoms
  have hnr0 : nonRatioForm g M x = 0 := by
    apply SuccessorShellArithmetic.nonRatioForm_eq_zero_of_shellRange_eq_zero hsupp
    unfold SuccessorShellArithmetic.shellRange
    apply Nat.floor_eq_zero.mpr
    have he1 : Real.exp w - 1 ≤ w * Real.exp w := by
      have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-w)) (Real.exp_pos w).le
      have h2 : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
      linarith only [h, h2]
    have hew : Real.exp w ≤ Real.exp 1 := Real.exp_le_exp.mpr hw1
    have hcL : c / (L : ℝ) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hLR (by norm_num)]; linarith only [h4c]
    have he3 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith only [this]
    have hMw : (M : ℝ) * (Real.exp w - 1) ≤ (w * M) * Real.exp 1 := by
      calc (M : ℝ) * (Real.exp w - 1) ≤ M * (w * Real.exp w) :=
            mul_le_mul_of_nonneg_left he1 hMR.le
        _ = (w * M) * Real.exp w := by ring
        _ ≤ (w * M) * Real.exp 1 := mul_le_mul_of_nonneg_left hew (mul_nonneg hw.le hMR.le)
    have h5 : (w * M) * Real.exp 1 ≤ (1 / 4) * 3 :=
      mul_le_mul (hwM.trans hcL) he3.le (Real.exp_pos 1).le (by norm_num)
    linarith only [hMw, h5]
  have hprime : primeSum (atomicTest M x g) = G * atomicWeilForm M x := by
    have h1 := primeSum_atomicTest_eq_ratio_add hg.continuous hgc hsupp hw.le M x
    rw [hnr0, add_zero, hmass] at h1
    exact h1
  have hawf := atomicWeilForm_add_full_poleDefect_le M x
  rw [hprime]
  have hD := poleDefect_nonneg M x
  have key : G * ((7 / 8 : ℝ) * poleDefect M x -
      (c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost + (Real.log 4 + 4)) * P) ≤
      G * (Real.log N * P -
        (c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost) * P -
        (1 / 8 : ℝ) * poleDefect M x) - G * atomicWeilForm M x := by
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ hG.le
    have hlogP := mul_le_mul_of_nonneg_right hlogMN hP
    linarith only [hawf, hlogP]
  linarith only [key, harch]

/-- **The top block.** Half of the Gamma form keeps the growing reserve `δ log N` per unit mass,
half pays the frequencies above `T`, and the prime self-form costs `O(c(1 + log c))`. -/
theorem top_block_ge {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ} (hLN : linearDefectCutoff c ≤ N) (x : ℕ → ℝ)
    {T : ℝ} (hT0 : 0 < T) :
    ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
        ((1 / 2 : ℝ) * (growingMassConstant / c ^ 7 * Real.log N - growingReserveCost * c) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, x n ^ 2) -
          topPrimeConstant * c * (1 + Real.log c) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, x n ^ 2)) +
      (1 / 2 : ℝ) * ((Real.log T - factorialSpanGammaOffset) *
          highFourierMass (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
            (atomDilate tiltedUnitSpline (c / N))) T -
        (factorialSpanGammaOffset + Real.log 2) *
          lowFourierMass (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
            (atomDilate tiltedUnitSpline (c / N))) T) ≤
      archForm (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
          (atomDilate tiltedUnitSpline (c / N))) -
        primeSum (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
          (atomDilate tiltedUnitSpline (c / N))) := by
  obtain ⟨hL3, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hrow := topPrimeRow_le hc1 hLN
  set L := linearDefectCutoff c with hL_def
  set M := N / L with hM_def
  have hL1 : 1 ≤ L := by omega
  have hN1 : 1 ≤ N := hL1.trans hLN
  have hMN : M ≤ N := Nat.div_le_self N L
  have hMltN : M < N := Nat.div_lt_self (by omega) (by omega)
  clear_value L M
  set y := atomicTailCoefficients M x
  set S := ∑ n ∈ Ioc M N, x n ^ 2
  set w := c / (N : ℝ)
  set g := atomDilate tiltedUnitSpline w
  set G := w * ∫ u, tiltedUnitSpline u ^ 2
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcN : c ≤ (N : ℝ) := by
    have hLNR : (L : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hLNR, hc0]
  have hw : 0 < w := div_pos hc0 hNR
  have hG : 0 < G := mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  have hmass : (∫ u, g u ^ 2) = G := integral_atomDilate_sq hw
  have hy_eq : (∑ n ∈ Icc 1 N, y n ^ 2) = S := sum_atomicTailCoefficients_sq_eq_Ioc' hMN x
  have hy0 : ∀ n ∈ Icc 1 M, y n = 0 := fun n hn =>
    if_neg (Nat.not_lt.mpr (mem_Icc.mp hn).2)
  have hfy : ContDiff ℝ 2 (atomicTest N y g) := contDiff_atomicTest hg N y
  have hfyc : HasCompactSupport (atomicTest N y g) := hasCompactSupport_atomicTest hsupp N y
  have hgrowA : (growingMassConstant / c ^ 7 * Real.log N - growingReserveCost * c) * G * S ≤
      archForm (atomicTest N y g) := by
    have hh0 := archForm_atomicTest_ge_growing hc1 hcN y
    rw [hy_eq] at hh0
    exact hh0
  have hband := archForm_ge_high_band hfy hfyc (T := T) (R := T) hT0 le_rfl
  rw [sub_self, zero_mul, add_zero] at hband
  have htop := abs_primeSum_top_le hg.continuous hgc hsupp hw.le hMltN y hy0
  rw [hmass, hy_eq] at htop
  have htop' : primeSum (atomicTest N y g) ≤
      G * (topPrimeConstant * c * (1 + Real.log c)) * S := by
    have h1 := (le_abs_self _).trans htop
    have h2 : G * topPrimeRow w M N * S ≤ G * (topPrimeConstant * c * (1 + Real.log c)) * S :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrow hG.le) hS
    linarith only [h1, h2]
  have e : G * ((1 / 2 : ℝ) * (growingMassConstant / c ^ 7 * Real.log N - growingReserveCost * c) *
      S - topPrimeConstant * c * (1 + Real.log c) * S) =
      (1 / 2 : ℝ) * ((growingMassConstant / c ^ 7 * Real.log N - growingReserveCost * c) * G * S) -
        G * (topPrimeConstant * c * (1 + Real.log c)) * S := by ring
  rw [e]
  linarith only [hgrowA, hband, htop']

/-- **The prime cross through the window average.** For a test `f` and the atomic test
`F = f_V`, `2|∫ f F| ≤ η ∫ f² + η⁻¹ ∫ (f_V^{(h)})² + η LM_T(f) + η⁻¹ (T h)² ∫ F²
  + λ HM_T(f) + 4 λ⁻¹ ∫ F²`. -/
theorem two_mul_abs_integral_mul_atomicTest_le {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) {w : ℝ}
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (B : ℕ) (V : ℕ → ℝ) {h T η lam : ℝ}
    (hh : 0 < h) (hη : 0 < η) (hlam : 0 < lam) :
    2 * |∫ u, f u * atomicTest B V g u| ≤
      η * (∫ u, f u ^ 2) + η⁻¹ * (∫ u, atomicTest B V (smoothedBump g h) u ^ 2) +
        η * lowFourierMass f T + η⁻¹ * ((T * h) ^ 2 * ∫ u, atomicTest B V g u ^ 2) +
        lam * highFourierMass f T + lam⁻¹ * (4 * ∫ u, atomicTest B V g u ^ 2) := by
  have hgc := hasCompactSupport_of_support_Icc hgsupp
  set F := atomicTest B V g
  set Fh := atomicTest B V (smoothedBump g h)
  have hF : ContDiff ℝ 2 F := contDiff_atomicTest hg B V
  have hFc : HasCompactSupport F := hasCompactSupport_atomicTest hgsupp B V
  have hFh : ContDiff ℝ 2 Fh := contDiff_atomicTest (contDiff_smoothedBump hg hgc h) B V
  have hFhc : HasCompactSupport Fh :=
    hasCompactSupport_atomicTest (w := w + h) (fun v hv => smoothedBump_eq_zero hgsupp hv) B V
  have hD : ContDiff ℝ 2 (fun u => F u - Fh u) := hF.sub hFh
  have hDc : HasCompactSupport (fun u => F u - Fh u) := hFc.sub hFhc
  have i1 : Integrable fun u => f u * Fh u :=
    (hf.continuous.mul hFh.continuous).integrable_of_hasCompactSupport (hfc.mul_right)
  have i2 : Integrable fun u => f u * (F u - Fh u) :=
    (hf.continuous.mul hD.continuous).integrable_of_hasCompactSupport (hfc.mul_right)
  have hsplit : ∫ u, f u * F u = (∫ u, f u * Fh u) + ∫ u, f u * (F u - Fh u) := by
    rw [← integral_add i1 i2]
    congr 1; funext u; ring
  have h1 := two_mul_abs_integral_mul_le_whole hf hfc hFh hFhc hη
  have h2 := two_mul_abs_integral_mul_le hf hfc hD hDc T hη hlam
  have hlowD := lowFourierMass_atomicTest_sub_smoothedBump_le hg hgsupp hh B V T
  have hhighD := highFourierMass_atomicTest_sub_smoothedBump_le hg hgsupp hh B V T
  have hl := mul_le_mul_of_nonneg_left hlowD (inv_nonneg.mpr hη.le)
  have hh' := mul_le_mul_of_nonneg_left hhighD (inv_nonneg.mpr hlam.le)
  have habs : |∫ u, f u * F u| ≤ |∫ u, f u * Fh u| + |∫ u, f u * (F u - Fh u)| := by
    rw [hsplit]; exact abs_add_le _ _
  linarith only [habs, h1, h2, hl, hh']

/-- **The masses of the prime translate and of its window average.** -/
theorem translate_masses_le {C_ψ c₀ t₀ : ℝ} (hCψ : 0 ≤ C_ψ) (hc₀ : 0 < c₀)
    (hpnt : ∀ ⦃h X Y : ℝ⦄, 0 < h → h ≤ 1 → Y = X * Real.exp (-h) → t₀ ≤ Y →
      |∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, vonMangoldtAtom k - Real.sqrt X * (1 - Real.exp (-h))| ≤
        Real.sqrt X * (4 * C_ψ * Real.exp (-c₀ * Real.sqrt (Real.log Y)) + h ^ 2))
    {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ} (h2LN : 2 * linearDefectCutoff c ≤ N) (x : ℕ → ℝ) {h : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) {K' : ℕ} (hK' : 1 ≤ K') (ht₀ : t₀ ≤ K' * Real.exp (-1)) :
    (∫ u, atomicTest ⌊(N : ℝ) * Real.exp (c / N)⌋₊
        (fun n => topWeight (((N / linearDefectCutoff c : ℕ) : ℝ) / 2) ⌊(N : ℝ) * Real.exp (c / N)⌋₊ n *
          primeConv (primeOrderCutoff N (c / N)) (N / linearDefectCutoff c) x n)
        (smoothedBump (atomDilate tiltedUnitSpline (c / N)) h) u ^ 2) ≤
      ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * (splineWindowConstant * ((c / N) / h ^ 2)) *
        windowSumBound C_ψ c₀ (((N / linearDefectCutoff c : ℕ) : ℝ) / 2)
          ⌊(N : ℝ) * Real.exp (c / N)⌋₊ (N / linearDefectCutoff c) K' x h ∧
    (∫ u, atomicTest ⌊(N : ℝ) * Real.exp (c / N)⌋₊
        (fun n => topWeight (((N / linearDefectCutoff c : ℕ) : ℝ) / 2) ⌊(N : ℝ) * Real.exp (c / N)⌋₊ n *
          primeConv (primeOrderCutoff N (c / N)) (N / linearDefectCutoff c) x n)
        (atomDilate tiltedUnitSpline (c / N)) u ^ 2) ≤
      ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
        ((1 + 2 * Real.exp 1 * ((c / N) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊)) *
          (Real.log ⌊(N : ℝ) * Real.exp (c / N)⌋₊ *
            (Real.log (2 * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ /
              (((N / linearDefectCutoff c : ℕ) : ℝ) / 2)) + 2 * (Real.log 4 + 4)))) *
        ∑ n ∈ Icc 1 (N / linearDefectCutoff c), x n ^ 2 := by
  obtain ⟨hL3, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
  set L := linearDefectCutoff c with hL_def
  set M := N / L with hM_def
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL1 : 1 ≤ L := by omega
  have hLN : L ≤ N := by omega
  have hN1 : 1 ≤ N := hL1.trans hLN
  have hM2 : 2 ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < L)).mpr (by omega)
  have hMN : M ≤ N := Nat.div_le_self N L
  clear_value L M
  set w := c / (N : ℝ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcN : c ≤ (N : ℝ) := by
    have hLNR : (L : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hLNR, hc0]
  have hw : 0 < w := div_pos hc0 hNR
  have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
  have hNle : (N : ℝ) ≤ N * Real.exp w := le_mul_of_one_le_right hNR.le (Real.one_le_exp hw.le)
  have hNBn : N ≤ ⌊(N : ℝ) * Real.exp w⌋₊ := Nat.le_floor hNle
  have hBnK : ⌊(N : ℝ) * Real.exp w⌋₊ < primeOrderCutoff N w :=
    Nat.lt_succ_of_le (Nat.floor_le_ceil _)
  set Bn := ⌊(N : ℝ) * Real.exp w⌋₊ with hBn_def
  set K := primeOrderCutoff N w with hK_def
  clear_value Bn K
  set A : ℝ := (M : ℝ) / 2
  set g := atomDilate tiltedUnitSpline w
  set G := w * ∫ u, tiltedUnitSpline u ^ 2
  have hM2R : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hA1 : 1 ≤ A := by simp only [A]; linarith only [hM2R]
  have hMA : (M : ℝ) ≤ 2 * A := by simp only [A]; linarith only []
  have hBnR : (N : ℝ) ≤ Bn := by exact_mod_cast hNBn
  have hMNR : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hAB : A ≤ Bn := by simp only [A]; linarith only [hBnR, hMNR, hM2R]
  have hBn1 : (1 : ℝ) ≤ Bn := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    linarith only [this, hBnR]
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  have hg0 : ∀ u, 0 ≤ g u := fun u => RenormalizedIntersectionTheory.tiltedUnitSpline_nonneg _
  have hmass : (∫ u, g u ^ 2) = G := integral_atomDilate_sq hw
  have hφ2 : 0 < ∫ u, tiltedUnitSpline u ^ 2 := integral_tiltedUnitSpline_sq_pos
  have hint : (∫ u, g u) = w * ∫ u, tiltedUnitSpline u := by
    have h := Measure.integral_comp_div (fun u => tiltedUnitSpline u) w
    simp only [smul_eq_mul, abs_of_pos hw] at h
    exact h
  constructor
  · have h1 := integral_sq_atomicTest_smoothedBump_le hg hsupp hg0 hh Bn
      (fun n => topWeight A Bn n * primeConv K M x n)
    have h2 := integral_windowSum_primeConv_sq_le hCψ hc₀ hpnt hh hh1 hA1 (by omega) hMA hAB hBnK
      hK' ht₀ x
    have hc : (∫ t, g t) ^ 2 / h ^ 2 = G * (splineWindowConstant * (w / h ^ 2)) := by
      rw [hint]
      simp only [G, splineWindowConstant]
      field_simp
    rw [hc] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left h2 ?_)
    rw [← hc]; positivity
  · have hcB : 0 < w * Bn := mul_pos hw (by linarith only [hBn1])
    have hcBN : w * Bn ≤ Bn := by
      have := mul_le_mul_of_nonneg_right hw1 (by linarith only [hBn1] : (0 : ℝ) ≤ Bn)
      linarith only [this]
    have hsuppB : ∀ u, u ∉ Set.Icc 0 (w * Bn / Bn) → g u = 0 := by
      rw [mul_div_assoc, div_self (by linarith only [hBn1]), mul_one]; exact hsupp
    have h1 := integral_atomicTest_sq_le_of_le_horizon hg.continuous hgc hcB hcBN hsuppB
      (fun n => topWeight A Bn n * primeConv K M x n)
    have h2 := sum_sq_topWeight_primeConv_le hA1 hAB K M x
    rw [hmass] at h1
    have hG0 : 0 ≤ G * (1 + 2 * Real.exp 1 * (w * Bn)) := by positivity
    calc _ ≤ G * (1 + 2 * Real.exp 1 * (w * Bn)) *
          ∑ n ∈ Icc 1 Bn, (topWeight A Bn n * primeConv K M x n) ^ 2 := h1
      _ ≤ G * (1 + 2 * Real.exp 1 * (w * Bn)) * (Real.log Bn * (Real.log (2 * Bn / A) +
          2 * (Real.log 4 + 4)) * prefixMass M x) := mul_le_mul_of_nonneg_left h2 hG0
      _ = _ := by simp only [prefixMass]; ring

/-- **The prime form of the split test** is the two self-forms plus the cross with the prime
translate of the prefix on the top window. -/
theorem primeSum_prefix_top_split {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ}
    (h2LN : 2 * linearDefectCutoff c ≤ N) (x : ℕ → ℝ) :
    primeSum (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) =
      primeSum (atomicTest (N / linearDefectCutoff c) x (atomDilate tiltedUnitSpline (c / N))) +
      primeSum (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
        (atomDilate tiltedUnitSpline (c / N))) +
      2 * ∫ u, atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
          (atomDilate tiltedUnitSpline (c / N)) u *
        atomicTest ⌊(N : ℝ) * Real.exp (c / N)⌋₊
          (fun n => topWeight (((N / linearDefectCutoff c : ℕ) : ℝ) / 2)
            ⌊(N : ℝ) * Real.exp (c / N)⌋₊ n *
            primeConv (primeOrderCutoff N (c / N)) (N / linearDefectCutoff c) x n)
          (atomDilate tiltedUnitSpline (c / N)) u := by
  obtain ⟨hL3, h4c, h256, -⟩ := linearDefectCutoff_bounds hc1
  set L := linearDefectCutoff c with hL_def
  set M := N / L with hM_def
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL1 : 1 ≤ L := by omega
  have hLN : L ≤ N := by omega
  have hN1 : 1 ≤ N := hL1.trans hLN
  have hM2 : 2 ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < L)).mpr (by omega)
  have hMN : M ≤ N := Nat.div_le_self N L
  clear_value L M
  set w := c / (N : ℝ)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < w := div_pos hc0 hNR
  have hwN : w * N = c := by simp only [w]; field_simp [hNR.ne']
  have hw_log2 : w < Real.log 2 := by
    have hLNR : (L : ℝ) ≤ N := by exact_mod_cast hLN
    have h1 : w * (256 * Real.exp 2 * c) ≤ c := by
      have := mul_le_mul_of_nonneg_left (h256.trans hLNR) hw.le
      linarith only [this, hwN]
    have he2 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    have h2 : w * 256 * Real.exp 2 ≤ 1 := by
      have h3 : (w * 256 * Real.exp 2) * c ≤ 1 * c := by
        rw [one_mul]; linarith only [h1]
      exact le_of_mul_le_mul_right h3 hc0
    have hw256 : w * 256 ≤ 1 :=
      le_trans (le_mul_of_one_le_right (by positivity) he2) h2
    have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith only [this]
    linarith only [hw256, hl2]
  have hNle : (N : ℝ) ≤ N * Real.exp w := le_mul_of_one_le_right hNR.le (Real.one_le_exp hw.le)
  have hBn_floor : ∀ n' : ℕ, (n' : ℝ) ≤ N * Real.exp w → n' ≤ ⌊(N : ℝ) * Real.exp w⌋₊ :=
    fun n' h => Nat.le_floor h
  have hBnK : ⌊(N : ℝ) * Real.exp w⌋₊ < primeOrderCutoff N w :=
    Nat.lt_succ_of_le (Nat.floor_le_ceil _)
  set g := atomDilate tiltedUnitSpline w
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  set xP : ℕ → ℝ := fun n => if n ≤ M then x n else 0
  set y := atomicTailCoefficients M x
  have hxP : ∀ n, M < n → xP n = 0 := fun n hn => if_neg (Nat.not_le.mpr hn)
  have hy0 : ∀ n, n ≤ M → y n = 0 := fun n hn => if_neg (Nat.not_lt.mpr hn)
  have hsum_xy : (fun n => xP n + y n) = x := by
    funext n
    change (if n ≤ M then x n else 0) + (if M < n then x n else 0) = x n
    by_cases hn : n ≤ M
    · rw [if_pos hn, if_neg (Nat.not_lt.mpr hn), add_zero]
    · rw [if_neg hn, if_pos (Nat.lt_of_not_le hn), zero_add]
  have hhalf : (1 : ℝ) / 2 ≤ Real.exp (-w) := by
    calc (1 : ℝ) / 2 = (Real.exp (Real.log 2))⁻¹ := by
          rw [Real.exp_log (by norm_num)]; norm_num
      _ = Real.exp (-Real.log 2) := (Real.exp_neg _).symm
      _ ≤ Real.exp (-w) := Real.exp_le_exp.mpr (neg_le_neg hw_log2.le)
  have hMR : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hρ : ∀ n' : ℕ, (M : ℝ) * Real.exp (-w) ≤ n' → (n' : ℝ) ≤ N * Real.exp w →
      topWeight ((M : ℝ) / 2) ⌊(N : ℝ) * Real.exp w⌋₊ n' = 1 := by
    intro n' h1 h2
    unfold topWeight
    rw [if_pos]
    refine ⟨?_, hBn_floor n' h2⟩
    have h3 : (M : ℝ) / 2 ≤ (M : ℝ) * Real.exp (-w) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hhalf hMR
    exact h3.trans h1
  have hcross := primeSum_atomicTest_prefix_add_top hg.continuous hgc hsupp hw.le hw_log2 hMN hN1
    xP y hxP hy0 (topWeight ((M : ℝ) / 2) ⌊(N : ℝ) * Real.exp w⌋₊) hρ
  rw [hsum_xy, atomicTest_restrict_prefix hMN x g] at hcross
  have hBnKM : ⌊(N : ℝ) * Real.exp w⌋₊ ≤ primeOrderCutoff N w * M :=
    hBnK.le.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hVeq : (fun n => topWeight ((M : ℝ) / 2) ⌊(N : ℝ) * Real.exp w⌋₊ n *
      primeConv (primeOrderCutoff N w) M xP n) =
      fun n => topWeight ((M : ℝ) / 2) ⌊(N : ℝ) * Real.exp w⌋₊ n *
        primeConv (primeOrderCutoff N w) M x n := by
    funext n
    rw [primeConv_congr (x' := x) (fun m hm => if_pos (mem_Icc.mp hm).2)]
  have hVvan : ∀ n, ⌊(N : ℝ) * Real.exp w⌋₊ < n →
      topWeight ((M : ℝ) / 2) ⌊(N : ℝ) * Real.exp w⌋₊ n *
        primeConv (primeOrderCutoff N w) M x n = 0 := fun n hn => by
    unfold topWeight
    rw [if_neg (fun h => absurd h.2 (Nat.not_le.mpr hn)), zero_mul]
  rw [hVeq, atomicTest_eq_of_vanish_above hBnKM hVvan] at hcross
  exact hcross

/-- **The ordered archimedean split** of the prefix and the top. -/
theorem archForm_prefix_top_split_ge {c : ℝ} (hc1 : 1 ≤ c) {N : ℕ}
    (hLN : linearDefectCutoff c ≤ N) (hM : 1 ≤ N / linearDefectCutoff c) (x : ℕ → ℝ) :
    archForm (atomicTest (N / linearDefectCutoff c) x (atomDilate tiltedUnitSpline (c / N))) +
        archForm (atomicTest N (atomicTailCoefficients (N / linearDefectCutoff c) x)
          (atomDilate tiltedUnitSpline (c / N))) -
        2 * Real.pi * (((c / N) * ∫ u, tiltedUnitSpline u ^ 2) *
          (∑ n ∈ Icc 1 (N / linearDefectCutoff c), x n ^ 2) +
          ((c / N) * ∫ u, tiltedUnitSpline u ^ 2) * (1 + 2 * Real.exp 1 * c) *
            ∑ n ∈ Ioc (N / linearDefectCutoff c) N, x n ^ 2) ≤
      archForm (atomicTest N x (atomDilate tiltedUnitSpline (c / N))) := by
  obtain ⟨hL3, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
  set L := linearDefectCutoff c with hL_def
  set M := N / L with hM_def
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL1 : 1 ≤ L := by omega
  have hN1 : 1 ≤ N := hL1.trans hLN
  have hMN : M ≤ N := Nat.div_le_self N L
  have hML : (M : ℝ) * L ≤ N := by exact_mod_cast Nat.div_mul_le_self N L
  clear_value L M
  set w := c / (N : ℝ)
  set g := atomDilate tiltedUnitSpline w
  set G := w * ∫ u, tiltedUnitSpline u ^ 2
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL1
  have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hcN : c ≤ (N : ℝ) := by
    have hLNR : (L : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hLNR, hc0]
  have hw : 0 < w := div_pos hc0 hNR
  have hwN : w * N = c := by simp only [w]; field_simp [hNR.ne']
  have hwM : w * M ≤ c / L := by
    apply (le_div_iff₀ hLR).mpr
    calc w * M * L = w * ((M : ℝ) * L) := by ring
      _ ≤ w * N := mul_le_mul_of_nonneg_left hML hw.le
      _ = c := hwN
  have hsep : w < atomSpacing M := by
    have hfour : 4 * w * M ≤ 1 := by
      have hl : 4 * (c / (L : ℝ)) ≤ 1 := by
        rw [← mul_div_assoc, div_le_one hLR]; exact h4c
      nlinarith only [hwM, hl]
    have hbound : w ≤ (1 / ((M : ℝ) + 1)) / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < M + 1)).mpr
      nlinarith only [hfour, mul_nonneg hw.le (sub_nonneg.mpr hM1R)]
    have h1 := (atomSpacing_bounds hM).1
    have hp := atomSpacing_pos hM
    linarith only [hbound, h1, hp]
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  have hmass : (∫ u, g u ^ 2) = G := integral_atomDilate_sq hw
  obtain ⟨boundary, hleft, hright⟩ := atomicTest_prefix_tail_ordered hsupp hM hsep N x
  have hcrossA := archForm_add_ge_of_ordered
    (contDiff_atomicTest hg M x) (hasCompactSupport_atomicTest hsupp M x)
    (contDiff_atomicTest hg N (atomicTailCoefficients M x))
    (hasCompactSupport_atomicTest hsupp N _) hleft hright
  rw [← atomicTest_eq_prefix_add_tail hMN x g] at hcrossA
  have hloMass : (∫ u, atomicTest M x g u ^ 2) = G * ∑ n ∈ Icc 1 M, x n ^ 2 := by
    rw [integral_atomicTest_sq hg hgc hsupp hsep, hmass, mul_comm]
  have hhiMass : (∫ u, atomicTest N (atomicTailCoefficients M x) g u ^ 2) ≤
      G * (1 + 2 * Real.exp 1 * c) * ∑ n ∈ Ioc M N, x n ^ 2 := by
    have h := integral_atomicTest_sq_le_of_le_horizon hg.continuous hgc hc0 hcN hsupp
      (atomicTailCoefficients M x)
    rw [hmass, sum_atomicTailCoefficients_sq_eq_Ioc' hMN x] at h
    exact h
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have := mul_le_mul_of_nonneg_left hhiMass hpi
  rw [hloMass] at hcrossA
  nlinarith only [hcrossA, this]

/-- **The far reserve through the window average.** On `(V_1)ᗮ`, split at
`M = N / linearDefectCutoff c` into a separated prefix and a top. The prefix keeps `(7/8) D_M`
up to `O(c) P`; the top keeps `(3/8) δ log N` per unit mass (`δ = κ/c⁷`), its Gamma form pays
its frequencies above `T`, and its prime self-form costs `O(c (1 + log c))`. The prime cross
pairs the top with the prime translate of the prefix (`primeSum_prefix_top_split`); its window
average is paid through the window sums (`translate_masses_le`), its high frequencies by the Gamma
form at `T`, and its low frequencies by `(T h)²`. -/
theorem exists_completeWeilEnergy_prefix_top_window_reserve :
    ∃ C_S C_P C_ψ c₀ t₀ : ℝ, 0 < C_S ∧ 0 < C_P ∧ 0 ≤ C_ψ ∧ 0 < c₀ ∧ 1 ≤ t₀ ∧
      ∀ {c : ℝ} {N : ℕ}, 1 ≤ c → 2 * linearDefectCutoff c ≤ N →
      ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {h T : ℝ} {K' : ℕ}, 0 < h → h ≤ 1 → 0 < T →
        factorialSpanGammaOffset + 1 ≤ Real.log T → 1 ≤ K' → t₀ ≤ K' * Real.exp (-1) →
        (7 / 8 : ℝ) * poleDefect (N / linearDefectCutoff c) (primeHorizonExtension z) +
          (3 / 8 : ℝ) * (growingMassConstant / c ^ 7) * Real.log N *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension z n ^ 2) -
          C_S * c * (1 + Real.log c) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension z n ^ 2) -
          C_P * c * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) -
          16 * (1 + 2 * Real.exp 1 * c) / ((growingMassConstant / c ^ 7) * Real.log N) *
            (splineWindowConstant * ((c / N) / h ^ 2)) *
            windowSumBound C_ψ c₀ (((N / linearDefectCutoff c : ℕ) : ℝ) / 2)
              ⌊(N : ℝ) * Real.exp (c / N)⌋₊ (N / linearDefectCutoff c) K'
              (primeHorizonExtension z) h -
          (16 * (1 + 2 * Real.exp 1 * c) / ((growingMassConstant / c ^ 7) * Real.log N) *
              (T * h) ^ 2 + 8 / (Real.log T - factorialSpanGammaOffset)) *
            ((1 + 2 * Real.exp 1 * ((c / N) * ⌊(N : ℝ) * Real.exp (c / N)⌋₊)) *
              (Real.log ⌊(N : ℝ) * Real.exp (c / N)⌋₊ *
                (Real.log (2 * ⌊(N : ℝ) * Real.exp (c / N)⌋₊ /
                  (((N / linearDefectCutoff c : ℕ) : ℝ) / 2)) + 2 * (Real.log 4 + 4)))) *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) ≤
          completeWeilEnergy tiltedUnitSpline c N z := by
  obtain ⟨C_ψ, c₀, t₀, hCψ, hc₀, ht₀1, hpnt⟩ := exists_vonMangoldtAtom_window_error
  have hG₀ : 0 ≤ factorialSpanGammaOffset := factorialSpanGammaOffset_nonneg
  have hC₄ : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith only [this]
  have hAsep : 0 ≤ separatedCrossMassCost := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    unfold separatedCrossMassCost; positivity
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hCtop : 0 ≤ topPrimeConstant := by
    unfold topPrimeConstant
    have he1 := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
    have he2 := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
    have hl : 0 ≤ Real.log (Real.exp 1 * (256 * Real.exp 2 + 4)) :=
      Real.log_nonneg (by nlinarith)
    have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    refine mul_nonneg (Real.exp_pos _).le ?_
    have t1 : 0 ≤ 2 * (Real.log 4 + 4) * Real.exp 1 ^ 2 := by positivity
    have t2 : 0 ≤ 2 * Real.exp 1 * (Real.log (Real.exp 1 * (256 * Real.exp 2 + 4)) +
      (Real.log 4 + 4) + 1) := by positivity
    have t3 : 0 ≤ (Real.log 4 + 4) * Real.exp 1 * (256 * Real.exp 2 + 4) := by positivity
    linarith
  have hgrow := growingReserveCost_nonneg
  set E2 : ℝ := (factorialSpanGammaOffset + Real.log 2) / 2 + 2 * Real.pi
  have hE2 : 0 ≤ E2 := by have : 0 ≤ 2 * Real.pi := by positivity
                          simp only [E2]; linarith
  let C_S := growingReserveCost / 2 + E2 * (1 + 2 * Real.exp 1) + topPrimeConstant + 1
  let C_P := 1 + 2 * |gammaHardyPhaseRate 0| + 2 * separatedCrossMassCost + (Real.log 4 + 4) +
    2 * Real.pi
  have hCS : 0 < C_S := by
    have h1 : 0 ≤ E2 * (1 + 2 * Real.exp 1) := mul_nonneg hE2 (by positivity)
    have h2 : 0 ≤ growingReserveCost / 2 := by positivity
    simp only [C_S]; linarith
  have hCP : 0 < C_P := by
    have : 0 ≤ 2 * |gammaHardyPhaseRate 0| := by positivity
    have : 0 ≤ 2 * Real.pi := by positivity
    simp only [C_P]; linarith
  refine ⟨C_S, C_P, C_ψ, c₀, t₀, hCS, hCP, hCψ, hc₀, ht₀1, ?_⟩
  intro c N hc1 h2LN z hz h T K' hh hh1 hT0 hT hK' ht₀
  obtain ⟨hL3, h4c, -, -⟩ := linearDefectCutoff_bounds hc1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
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
  -- the blocks
  have henergy := completeWeilEnergy_eq_arch_sub_primeSum hc0 hN2 hz
  rw [integral_atomDilate_sq hw] at henergy
  have hPb := prefix_block_ge hc1 hLN hM (primeHorizonExtension z)
  have hYb := top_block_ge hc1 hLN (primeHorizonExtension z) hT0
  have hAb := archForm_prefix_top_split_ge hc1 hLN hM (primeHorizonExtension z)
  have hSb := primeSum_prefix_top_split hc1 h2LN (primeHorizonExtension z)
  obtain ⟨hFh, hF⟩ := translate_masses_le hCψ hc₀ hpnt hc1 h2LN (primeHorizonExtension z) hh hh1
    hK' ht₀
  set x := primeHorizonExtension z
  set M := N / linearDefectCutoff c
  set P := ∑ n ∈ Icc 1 M, x n ^ 2
  set S := ∑ n ∈ Ioc M N, x n ^ 2
  set w := c / (N : ℝ)
  set g := atomDilate tiltedUnitSpline w
  set G := w * ∫ u, tiltedUnitSpline u ^ 2
  set y := atomicTailCoefficients M x
  set δ := growingMassConstant / c ^ 7
  set Bn := ⌊(N : ℝ) * Real.exp w⌋₊
  set V : ℕ → ℝ := fun n => topWeight ((M : ℝ) / 2) Bn n * primeConv (primeOrderCutoff N w) M x n
  set WSB := windowSumBound C_ψ c₀ ((M : ℝ) / 2) Bn M K' x h
  set Φ := (1 + 2 * Real.exp 1 * (w * Bn)) *
    (Real.log Bn * (Real.log (2 * Bn / ((M : ℝ) / 2)) + 2 * (Real.log 4 + 4)))
  have hG : 0 < G := mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hδ : 0 < δ := div_pos growingMassConstant_pos (by positivity)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hsupp := tiltedUnitSpline_atom_support hw
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hfy : ContDiff ℝ 2 (atomicTest N y g) := contDiff_atomicTest hg N y
  have hfyc : HasCompactSupport (atomicTest N y g) := hasCompactSupport_atomicTest hsupp N y
  have hfy2 : (∫ u, atomicTest N y g u ^ 2) ≤ G * (1 + 2 * Real.exp 1 * c) * S := by
    have h0 := integral_atomicTest_sq_le_of_le_horizon hg.continuous hgc hc0 hcN hsupp y
    rw [integral_atomDilate_sq hw, sum_atomicTailCoefficients_sq_eq_Ioc' hMN x] at h0
    exact h0
  have hLMy := lowFourierMass_le_integral_sq hfy hfyc T
  -- the cross with `η = δ log N / (16 (1 + 2ec))` and `λ = (log T − G₀)/2`
  set γc := 1 + 2 * Real.exp 1 * c
  have hγc : 0 < γc := by positivity
  set η := δ * Real.log N / (16 * γc)
  have hη : 0 < η := by positivity
  set lam := (Real.log T - factorialSpanGammaOffset) / 2
  have hlam : 0 < lam := by simp only [lam]; linarith only [hT]
  have hX := two_mul_abs_integral_mul_atomicTest_le (f := atomicTest N y g) hfy hfyc hg hsupp
    Bn V (T := T) hh hη hlam
  have hηinv : η⁻¹ = 16 * γc / (δ * Real.log N) := by simp only [η]; rw [inv_div]
  have hlaminv : lam⁻¹ * 4 = 8 / (Real.log T - factorialSpanGammaOffset) := by
    simp only [lam]; field_simp; ring
  -- product inequalities
  have hfyη : η * (∫ u, atomicTest N y g u ^ 2) ≤ η * (G * γc * S) :=
    mul_le_mul_of_nonneg_left hfy2 hη.le
  have hLMη : η * lowFourierMass (atomicTest N y g) T ≤ η * (G * γc * S) :=
    mul_le_mul_of_nonneg_left (hLMy.trans hfy2) hη.le
  have hLME : (factorialSpanGammaOffset + Real.log 2) *
      lowFourierMass (atomicTest N y g) T ≤ (factorialSpanGammaOffset + Real.log 2) * (G * γc * S) :=
    mul_le_mul_of_nonneg_left (hLMy.trans hfy2) (add_nonneg hG₀ hlog2)
  have hFhη : η⁻¹ * (∫ u, atomicTest Bn V (smoothedBump g h) u ^ 2) ≤
      η⁻¹ * (G * (splineWindowConstant * (w / h ^ 2)) * WSB) :=
    mul_le_mul_of_nonneg_left hFh (inv_nonneg.mpr hη.le)
  have hFη : η⁻¹ * ((T * h) ^ 2 * ∫ u, atomicTest Bn V g u ^ 2) ≤
      η⁻¹ * ((T * h) ^ 2 * (G * Φ * P)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF (sq_nonneg _)) (inv_nonneg.mpr hη.le)
  have hFlam : lam⁻¹ * (4 * ∫ u, atomicTest Bn V g u ^ 2) ≤ lam⁻¹ * (4 * (G * Φ * P)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF (by norm_num)) (inv_nonneg.mpr hlam.le)
  have hηG : 2 * (η * (G * γc * S)) = G * ((δ / 8) * Real.log N * S) := by
    simp only [η]; field_simp; ring
  have hlamHM : lam * highFourierMass (atomicTest N y g) T =
      (1 / 2 : ℝ) * ((Real.log T - factorialSpanGammaOffset) *
        highFourierMass (atomicTest N y g) T) := by simp only [lam]; ring
  have hXabs := le_abs_self (∫ u, atomicTest N y g u * atomicTest Bn V g u)
  -- the mass coefficients
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hcl : c ≤ c * (1 + Real.log c) := le_mul_of_one_le_right hc0.le (by linarith only [hlogc0])
  have hcoefS : growingReserveCost / 2 * c + topPrimeConstant * c * (1 + Real.log c) +
      E2 * γc ≤ C_S * c * (1 + Real.log c) := by
    have h1 : growingReserveCost / 2 * c ≤ growingReserveCost / 2 * (c * (1 + Real.log c)) :=
      mul_le_mul_of_nonneg_left hcl (by positivity)
    have h2 : γc ≤ (1 + 2 * Real.exp 1) * (c * (1 + Real.log c)) := by
      simp only [γc]
      have : (1 : ℝ) ≤ c * (1 + Real.log c) := hc1.trans hcl
      nlinarith only [this, hcl, Real.exp_pos 1]
    have h3 := mul_le_mul_of_nonneg_left h2 hE2
    have h4 : (0 : ℝ) ≤ c * (1 + Real.log c) := by positivity
    simp only [C_S]
    nlinarith only [h1, h3, h4]
  have hcoefP : c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost +
      (Real.log 4 + 4) + 2 * Real.pi ≤ C_P * c := by
    have h1 : 2 * |gammaHardyPhaseRate 0| ≤ 2 * |gammaHardyPhaseRate 0| * c :=
      le_mul_of_one_le_right (by positivity) hc1
    have h2 : Real.log 4 + 4 ≤ (Real.log 4 + 4) * c := le_mul_of_one_le_right hC₄ hc1
    have h3 : 2 * Real.pi ≤ 2 * Real.pi * c := le_mul_of_one_le_right (by positivity) hc1
    simp only [C_P]
    nlinarith only [h1, h2, h3]
  have hSG := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoefS hS0) hG.le
  have hPG := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoefP hP0) hG.le
  -- assemble
  rw [henergy, ← sub_div, le_div_iff₀ hG]
  rw [hηinv] at hFhη hFη hX
  have hE2exp : G * (E2 * γc * S) = (1 / 2 : ℝ) * ((factorialSpanGammaOffset + Real.log 2) *
      (G * γc * S)) + 2 * Real.pi * (G * γc * S) := by simp only [E2]; ring
  have hfinalF : (16 * γc / (δ * Real.log N) * (T * h) ^ 2 +
      8 / (Real.log T - factorialSpanGammaOffset)) * Φ * P * G =
      16 * γc / (δ * Real.log N) * ((T * h) ^ 2 * (G * Φ * P)) +
        lam⁻¹ * (4 * (G * Φ * P)) := by
    rw [← hlaminv]; ring
  have hfinalW : 16 * γc / (δ * Real.log N) * (splineWindowConstant * (w / h ^ 2)) * WSB * G =
      16 * γc / (δ * Real.log N) * (G * (splineWindowConstant * (w / h ^ 2)) * WSB) := by ring
  change ((7 / 8 : ℝ) * poleDefect M x + (3 / 8 : ℝ) * δ * Real.log N * S -
      C_S * c * (1 + Real.log c) * S - C_P * c * P -
      16 * γc / (δ * Real.log N) * (splineWindowConstant * (w / h ^ 2)) * WSB -
      (16 * γc / (δ * Real.log N) * (T * h) ^ 2 +
        8 / (Real.log T - factorialSpanGammaOffset)) * Φ * P) * G ≤ _
  linarith only [hAb, hSb, hPb, hYb, hX, hXabs, hfyη, hLMη, hLME, hFhη, hFη, hFlam, hηG, hlamHM,
    hSG, hPG, hfinalF, hfinalW, hfy2, hE2exp]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
