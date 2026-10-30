import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleProjectionIsTheEuclideanGroundProjection
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePrimeFormHasASpectralGapBelowItsPole
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedSplineKeepsAGammaReserveAtEveryOverlap

/-!
# The defect correction for overlap Gram smoothing

The prime defect has the reciprocal-square-root pole as its exact kernel.
Smoothing one argument by the physical mass Gram need not preserve positivity:
the Gram does not preserve this ground line. A quarter of the defect of the
smoothing error completes the form to a square. The corrected kernel is the
inverse image of the arithmetic ground line under identity plus Gram.
-/

noncomputable section

set_option autoImplicit false

open Finset MeasureTheory Filter Topology
open scoped RealInnerProductSpace Convolution

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis ArithmeticFunction
  BiScaleUncertainty.ChebyshevGauge RHTower.WeilDeletion

/-- The bilinear prime-power edge energy on the positive integer horizon. -/
def primeDefectPairing (N : ℕ) (x y : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m),
    vonMangoldt t * (x (m * t) - x m / Real.sqrt t) *
      (y (m * t) - y m / Real.sqrt t)

theorem primeDefectPairing_self (N : ℕ) (x : ℕ → ℝ) :
    primeDefectPairing N x x = poleDefect N x := by
  unfold primeDefectPairing poleDefect
  exact sum_congr rfl fun m _ => sum_congr rfl fun t _ => by ring

/-- A quarter of the difference energy completes the polarized defect to a square. -/
theorem primeDefectPairing_add_quarter_difference (N : ℕ) (x y : ℕ → ℝ) :
    primeDefectPairing N x y + (1 / 4) * poleDefect N (x - y) =
      (1 / 4) * poleDefect N (x + y) := by
  unfold primeDefectPairing poleDefect
  simp only [mul_sum, ← sum_add_distrib, Pi.sub_apply, Pi.add_apply]
  exact sum_congr rfl fun m _ => sum_congr rfl fun t _ => by ring

private theorem primeHorizonExtension_add {N : ℕ}
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeHorizonExtension (x + y) = primeHorizonExtension x + primeHorizonExtension y := by
  funext n
  simp only [primeHorizonExtension, Pi.add_apply]
  split_ifs
  · rfl
  · exact (zero_add (0 : ℝ)).symm

private theorem primeHorizonExtension_sub {N : ℕ}
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeHorizonExtension (x - y) = primeHorizonExtension x - primeHorizonExtension y := by
  funext n
  simp only [primeHorizonExtension, Pi.sub_apply]
  split_ifs
  · rfl
  · exact (sub_self (0 : ℝ)).symm

private theorem primeHorizonExtension_smul {N : ℕ}
    (a : ℝ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeHorizonExtension (a • x) = a • primeHorizonExtension x := by
  funext n
  simp only [primeHorizonExtension, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rfl
  · exact (mul_zero a).symm

private theorem poleDefect_smul (N : ℕ) (a : ℝ) (x : ℕ → ℝ) :
    poleDefect N (a • x) = a ^ 2 * poleDefect N x := by
  unfold poleDefect
  simp only [mul_sum, Pi.smul_apply, smul_eq_mul]
  exact sum_congr rfl fun m _ => sum_congr rfl fun t _ => by ring

private theorem horizonPoleVector_defect_zero (N : ℕ) :
    poleDefect N (primeHorizonExtension (horizonPoleVector N)) = 0 := by
  unfold poleDefect
  refine sum_eq_zero fun m hm => sum_eq_zero fun t ht => ?_
  have hm1 := (mem_Icc.mp hm).1
  have ht1 := (mem_Icc.mp ht).1
  have hmt : m * t ∈ Icc 1 N := mem_Icc.mpr ⟨Nat.mul_pos hm1 ht1,
    by simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le hm1).mp (mem_Icc.mp ht).2⟩
  simp only [primeHorizonExtension, dif_pos hmt, dif_pos hm]
  change vonMangoldt t * (1 / Real.sqrt (m * t : ℕ) -
    (1 / Real.sqrt m) / Real.sqrt t) ^ 2 = 0
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m), div_mul_eq_div_div, sub_self]
  ring

/-- Zero prime defect is exactly the arithmetic pole line, at every positive horizon. -/
theorem poleDefect_eq_zero_iff_horizonPoleVector {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    poleDefect N (primeHorizonExtension x) = 0 ↔
      ∃ a : ℝ, x = a • horizonPoleVector N := by
  constructor
  · intro hx
    obtain ⟨g, hg, hgap⟩ := exists_poleDefect_ge
    have h := hgap N (primeHorizonExtension (horizonPoleProjection x))
      (harmonicSum_horizonPoleProjection hN x)
    rw [sum_primeHorizonExtension_sq, poleDefect_horizonPoleProjection hN, hx] at h
    have hn : ‖horizonPoleProjection x‖ = 0 := by
      have hs : ‖horizonPoleProjection x‖ ^ 2 = 0 :=
        (mul_eq_zero.mp (le_antisymm h (mul_nonneg hg.le (sq_nonneg _)))).resolve_left hg.ne'
      nlinarith only [hs, norm_nonneg (horizonPoleProjection x)]
    have he := norm_eq_zero.mp hn
    refine ⟨⟪x, normalizedHorizonPoleVector N⟫ *
      (Real.sqrt (SelectiveMultiscaleArithmeticPositivity.harmonicMass N))⁻¹, ?_⟩
    have hx' := sub_eq_zero.mp he
    simpa only [normalizedHorizonPoleVector, smul_smul] using hx'
  · rintro ⟨a, rfl⟩
    rw [primeHorizonExtension_smul, poleDefect_smul, horizonPoleVector_defect_zero, mul_zero]

/-- The physical mass Gram normalized by the mass of one atom. -/
def normalizedOverlapGram (g : ℝ → ℝ) (N : ℕ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) →ₗ[ℝ]
      EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  Matrix.toEuclideanLin (horizonKernelMatrix
    (fun m n => bumpCorr g (-(Real.log n - Real.log m)) / (∫ u, g u ^ 2)) N)

/-- The Gram quadratic form is the actual physical mass, with its normalization. -/
theorem normalizedOverlapGram_inner (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (N : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪normalizedOverlapGram g N x, x⟫ =
      (∫ u, atomicTest N (primeHorizonExtension x) g u ^ 2) / (∫ u, g u ^ 2) := by
  rw [normalizedOverlapGram, horizonKernelMatrix_inner,
    integral_atomicTest_sq_eq_gram hg hgc]
  simp only [sum_div, mul_div_assoc]

theorem normalizedOverlapGram_inner_nonneg (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (N : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    0 ≤ ⟪normalizedOverlapGram g N x, x⟫ := by
  rw [normalizedOverlapGram_inner g hg hgc]
  exact div_nonneg (integral_nonneg fun u => sq_nonneg _)
    (integral_nonneg fun u => sq_nonneg _)

/-- Identity plus the physical Gram is invertible, including horizons with overlapping atoms. -/
theorem id_add_normalizedOverlapGram_bijective (g : ℝ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (N : ℕ) :
    Function.Bijective ((LinearMap.id : EuclideanSpace ℝ (PrimeHorizonIndex N) →ₗ[ℝ]
      EuclideanSpace ℝ (PrimeHorizonIndex N)) + normalizedOverlapGram g N) := by
  have hi : Function.Injective ((LinearMap.id : EuclideanSpace ℝ (PrimeHorizonIndex N) →ₗ[ℝ]
      EuclideanSpace ℝ (PrimeHorizonIndex N)) + normalizedOverlapGram g N) := by
    apply (LinearMap.ker_eq_bot).mp
    apply (LinearMap.ker_eq_bot').mpr
    intro x hx
    have hi := congrArg (fun y => ⟪y, x⟫) hx
    change ⟪x + normalizedOverlapGram g N x, x⟫ = ⟪0, x⟫ at hi
    rw [inner_add_left, inner_zero_left, real_inner_self_eq_norm_sq] at hi
    have hg0 := normalizedOverlapGram_inner_nonneg g hg hgc N x
    have hn : ‖x‖ = 0 := by nlinarith only [hi, hg0, norm_nonneg x]
    exact norm_eq_zero.mp hn
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- The Gram-smoothed prime defect with a multiple of its smoothing-error energy. -/
def correctedOverlapDefect (g : ℝ → ℝ) (N : ℕ) (τ : ℝ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) : ℝ :=
  primeDefectPairing N (primeHorizonExtension x)
      (primeHorizonExtension (normalizedOverlapGram g N x)) +
    τ * poleDefect N (primeHorizonExtension (x - normalizedOverlapGram g N x))

/-- The exact signed decomposition separates the positive square from its correction deficit. -/
theorem correctedOverlapDefect_eq (g : ℝ → ℝ) (N : ℕ) (τ : ℝ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    correctedOverlapDefect g N τ x =
      (1 / 4) * poleDefect N (primeHorizonExtension (x + normalizedOverlapGram g N x)) +
        (τ - 1 / 4) * poleDefect N (primeHorizonExtension (x - normalizedOverlapGram g N x)) := by
  have h := primeDefectPairing_add_quarter_difference N (primeHorizonExtension x)
    (primeHorizonExtension (normalizedOverlapGram g N x))
  rw [← primeHorizonExtension_sub, ← primeHorizonExtension_add] at h
  unfold correctedOverlapDefect
  nlinarith only [h]

/-- A quarter correction always restores nonnegativity of the arithmetic form. -/
theorem correctedOverlapDefect_nonneg (g : ℝ → ℝ) (N : ℕ) {τ : ℝ}
    (hτ : 1 / 4 ≤ τ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    0 ≤ correctedOverlapDefect g N τ x := by
  rw [correctedOverlapDefect_eq]
  exact add_nonneg (mul_nonneg (by norm_num) (poleDefect_nonneg _ _))
    (mul_nonneg (sub_nonneg.mpr hτ) (poleDefect_nonneg _ _))

/-- The corrected nullspace is the preimage of the pole line under identity plus Gram. -/
theorem correctedOverlapDefect_quarter_eq_zero_iff {N : ℕ} (hN : 1 ≤ N)
    (g : ℝ → ℝ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    correctedOverlapDefect g N (1 / 4) x = 0 ↔
      ∃ a : ℝ, x + normalizedOverlapGram g N x = a • horizonPoleVector N := by
  rw [correctedOverlapDefect_eq]
  have h := poleDefect_eq_zero_iff_horizonPoleVector hN
    (x + normalizedOverlapGram g N x)
  constructor
  · intro hz
    apply h.mp
    nlinarith only [hz]
  · intro hx
    rw [h.mpr hx]
    ring

/-- Identity plus Gram transports the one-dimensional arithmetic ground space bijectively. -/
theorem exists_correctedOverlapDefect_ground_line {N : ℕ} (hN : 1 ≤ N)
    (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ u : EuclideanSpace ℝ (PrimeHorizonIndex N),
      u + normalizedOverlapGram g N u = horizonPoleVector N ∧
      ∀ x, correctedOverlapDefect g N (1 / 4) x = 0 ↔ ∃ a : ℝ, x = a • u := by
  obtain ⟨hi, hs⟩ := id_add_normalizedOverlapGram_bijective g hg hgc N
  obtain ⟨u, hu⟩ := hs (horizonPoleVector N)
  change u + normalizedOverlapGram g N u = horizonPoleVector N at hu
  refine ⟨u, hu, fun x => ?_⟩
  rw [correctedOverlapDefect_quarter_eq_zero_iff hN]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, hi ?_⟩
    change x + normalizedOverlapGram g N x = a • u + normalizedOverlapGram g N (a • u)
    rw [map_smul, ← smul_add, hu]
    exact ha
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    rw [map_smul, ← smul_add, hu]

private theorem horizonPoleVector_ne_zero {N : ℕ} (hN : 1 ≤ N) : horizonPoleVector N ≠ 0 := by
  intro h
  have hs := horizonPoleVector_norm_sq N
  rw [h, norm_zero, zero_pow two_ne_zero] at hs
  have hmass := one_le_harmonicMass hN
  linarith only [hs, hmass]

private theorem preimage_not_pole {N : ℕ} (hN : 1 ≤ N)
    (G : EuclideanSpace ℝ (PrimeHorizonIndex N) →ₗ[ℝ]
      EuclideanSpace ℝ (PrimeHorizonIndex N))
    (hG : ¬ ∃ a : ℝ, G (horizonPoleVector N) = a • horizonPoleVector N)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu : u + G u = horizonPoleVector N) : ¬ ∃ a : ℝ, u = a • horizonPoleVector N := by
  rintro ⟨a, ha⟩
  have ha0 : a ≠ 0 := by
    intro hz
    rw [ha, hz, zero_smul, _root_.map_zero, add_zero] at hu
    exact horizonPoleVector_ne_zero hN hu.symm
  have hGu : G (a • horizonPoleVector N) = horizonPoleVector N - a • horizonPoleVector N := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [ha, add_comm] using hu
  apply hG
  refine ⟨a⁻¹ - 1, ?_⟩
  calc
    G (horizonPoleVector N) = a⁻¹ • G (a • horizonPoleVector N) := by
      rw [map_smul, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    _ = a⁻¹ • (horizonPoleVector N - a • horizonPoleVector N) := by rw [hGu]
    _ = (a⁻¹ - 1) • horizonPoleVector N := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ ha0, sub_smul, one_smul]

private theorem sharp_correction_of_ground_line_failure {N : ℕ} (hN : 1 ≤ N)
    (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hG : ¬ ∃ a : ℝ, normalizedOverlapGram g N (horizonPoleVector N) =
      a • horizonPoleVector N) :
    ∀ τ : ℝ, (∀ x, 0 ≤ correctedOverlapDefect g N τ x) ↔ 1 / 4 ≤ τ := by
  obtain ⟨u, hu, -⟩ := exists_correctedOverlapDefect_ground_line hN g hg hgc
  have hnot := preimage_not_pole hN (normalizedOverlapGram g N) hG hu
  have hd : 0 < poleDefect N (primeHorizonExtension (u - normalizedOverlapGram g N u)) := by
    apply lt_of_le_of_ne (poleDefect_nonneg _ _)
    intro hz
    obtain ⟨a, ha⟩ := (poleDefect_eq_zero_iff_horizonPoleVector hN _).mp hz.symm
    apply hnot
    refine ⟨(a + 1) / 2, ?_⟩
    ext i
    have hi := congrArg (fun x : EuclideanSpace ℝ (PrimeHorizonIndex N) => x i) hu
    have hi' := congrArg (fun x : EuclideanSpace ℝ (PrimeHorizonIndex N) => x i) ha
    change u i + normalizedOverlapGram g N u i = horizonPoleVector N i at hi
    change u i - normalizedOverlapGram g N u i = a * horizonPoleVector N i at hi'
    change u i = ((a + 1) / 2) * horizonPoleVector N i
    linarith only [hi, hi']
  intro τ
  constructor
  · intro hτ
    have h := hτ u
    rw [correctedOverlapDefect_eq, hu, horizonPoleVector_defect_zero, mul_zero, zero_add] at h
    by_contra hquarter
    exact (not_lt_of_ge h) (mul_neg_of_neg_of_pos
      (sub_neg.mpr (lt_of_not_ge hquarter)) hd)
  · exact fun hτ x => correctedOverlapDefect_nonneg g N hτ x


private theorem unit_uniform_bound (t : ℝ) : ‖unif 1 t‖ ≤ (1 / 2 : ℝ) := by
  unfold unif
  by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem ht]
    norm_num
  · rw [Set.indicator_of_notMem ht]
    norm_num

private theorem upow_unit_pos (n : ℕ) {x : ℝ} (hx : |x| < n + 1) :
    0 < upow 1 n x := by
  induction n generalizing x with
  | zero =>
      have hx' : -1 < x ∧ x < 1 := by simpa using abs_lt.mp hx
      change 0 < (Set.Icc (-1 : ℝ) 1).indicator (fun _ => 1 / (2 * 1 : ℝ)) x
      rw [Set.indicator_of_mem (show x ∈ Set.Icc (-1 : ℝ) 1 from ⟨hx'.1.le, hx'.2.le⟩)]
      norm_num
  | succ n ih =>
      have hx' := abs_lt.mp hx
      push_cast at hx'
      let a : ℝ := max (-1) (x - (n + 1))
      let b : ℝ := min 1 (x + (n + 1))
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hab : a < b := by
        dsimp only [a, b]
        exact max_lt (lt_min (by norm_num) (by linarith only [hx'.1]))
          (lt_min (by linarith only [hx'.2]) (by linarith only [hn]))
      have hi : Integrable (fun t : ℝ => unif 1 t * upow 1 n (x - t)) :=
        ((integrable_upow 1 n).comp_sub_left x).bdd_mul
          (integrable_unif 1).aestronglyMeasurable
          (Eventually.of_forall unit_uniform_bound)
      have hsub : Set.Ioo a b ⊆ Function.support (fun t => unif 1 t * upow 1 n (x - t)) := by
        intro t ht
        have ht0 : -1 < t := lt_of_le_of_lt (le_max_left _ _) ht.1
        have ht1 : t < 1 := lt_of_lt_of_le ht.2 (min_le_left _ _)
        have htx0 : x - (n + 1) < t := lt_of_le_of_lt (le_max_right _ _) ht.1
        have htx1 : t < x + (n + 1) := lt_of_lt_of_le ht.2 (min_le_right _ _)
        have hp : 0 < upow 1 n (x - t) := ih (abs_lt.mpr
          ⟨by linarith only [htx1], by linarith only [htx0]⟩)
        have hu : unif 1 t = (1 / 2 : ℝ) := by
          unfold unif
          rw [Set.indicator_of_mem (show t ∈ Set.Icc (-1 : ℝ) 1 from ⟨ht0.le, ht1.le⟩)]
          norm_num
        exact (mul_pos (by rw [hu]; norm_num) hp).ne'
      have hv : 0 < volume (Set.Ioo a b) := by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
      have hp := (integral_pos_iff_support_of_nonneg
        (fun t => mul_nonneg (unif_nonneg one_pos t) (upow_nonneg one_pos n (x - t))) hi).mpr
          (lt_of_lt_of_le hv (measure_mono hsub))
      simpa only [upow, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hp

private theorem tiltedUnitSpline_nonneg (u : ℝ) : 0 ≤ tiltedUnitSpline u := by
  change 0 ≤ Real.exp (1 * ((u - 1 / 2) / (1 / 8))) *
    upow 1 3 ((u - 1 / 2) / (1 / 8))
  exact mul_nonneg (Real.exp_pos _).le (upow_nonneg one_pos 3 _)

private theorem tiltedUnitSpline_pos {u : ℝ} (hu : u ∈ Set.Ioo 0 1) :
    0 < tiltedUnitSpline u := by
  change 0 < Real.exp (1 * ((u - 1 / 2) / (1 / 8))) *
    upow 1 3 ((u - 1 / 2) / (1 / 8))
  apply mul_pos (Real.exp_pos _)
  apply upow_unit_pos
  norm_num
  exact abs_lt.mpr ⟨by linarith only [hu.1], by linarith only [hu.2]⟩


private theorem positive_bumpCorr {g : ℝ → ℝ} {w s : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u)
    (hgp : ∀ u ∈ Set.Ioo 0 w, 0 < g u) (hs : |s| < w) : 0 < bumpCorr g s := by
  have hs' := abs_lt.mp hs
  have hp : 0 < g ((w - s) / 2) * g ((w - s) / 2 + s) :=
    mul_pos (hgp _ ⟨by linarith only [hs'.2], by linarith only [hs'.1]⟩)
      (hgp _ ⟨by linarith only [hs'.1], by linarith only [hs'.2]⟩)
  have hcont : Continuous (fun u => g u * g (u + s)) :=
    hg.mul (hg.comp (continuous_id.add continuous_const))
  exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hgc.mul_right
    (fun u => mul_nonneg (hg0 u) (hg0 (u + s))) hp.ne'

private theorem overlapGram_does_not_preserve_pole {N : ℕ} (hN : 3 ≤ N)
    {g : ℝ → ℝ} {w : ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hg0 : ∀ u, 0 ≤ g u) (hgp : ∀ u ∈ Set.Ioo 0 w, 0 < g u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hM : 0 < ∫ u, g u ^ 2) (hw2 : w < Real.log 2)
    (hgap : Real.log (N : ℝ) - Real.log ((N - 1 : ℕ) : ℝ) < w) :
    ¬ ∃ a : ℝ, normalizedOverlapGram g N (horizonPoleVector N) =
      a • horizonPoleVector N := by
  let i₁ : PrimeHorizonIndex N := ⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  let iN : PrimeHorizonIndex N := ⟨N, mem_Icc.mpr ⟨by omega, le_rfl⟩⟩
  let K : ℕ → ℕ → ℝ := fun m n =>
    bumpCorr g (-(Real.log n - Real.log m)) / (∫ u, g u ^ 2)
  have hK0 : ∀ m n, 0 ≤ K m n := fun m n =>
    div_nonneg (integral_nonneg fun u => mul_nonneg (hg0 u) (hg0 _)) hM.le
  have hdiag : ∀ n, K n n = 1 := fun n => by
    simp only [K, sub_self, neg_zero, bumpCorr_zero, div_self hM.ne']
  have hfirst : normalizedOverlapGram g N (horizonPoleVector N) i₁ = 1 := by
    rw [normalizedOverlapGram, horizonPoleVector, horizonKernelMatrix_apply_profile]
    change (∑ n ∈ Icc 1 N, K 1 n * (1 / Real.sqrt n)) = 1
    rw [sum_eq_single 1]
    · rw [hdiag]
      norm_num
    · intro n hn hn1
      have hn2 : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
      have hlog : Real.log 2 ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
      have hlog0 : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (mem_Icc.mp hn).1)
      have hsep : w < |-(Real.log (n : ℝ) - Real.log (1 : ℝ))| := by
        rw [Real.log_one, sub_zero, abs_neg, abs_of_nonneg hlog0]
        exact hw2.trans_le hlog
      simp only [K, Nat.cast_one, bumpCorr_eq_zero hsupp hsep, zero_div, zero_mul]
    · intro hn
      exact False.elim (hn (mem_Icc.mpr ⟨le_rfl, by omega⟩))
  have hpred : N - 1 ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, by omega⟩
  have hNp : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (mem_Icc.mp hpred).1
  have hlogN : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hNp (by exact_mod_cast (mem_Icc.mp hpred).2)
  have hclose : |-(Real.log ((N - 1 : ℕ) : ℝ) - Real.log (N : ℝ))| < w := by
    rw [abs_of_nonneg (by linarith only [hlogN])]
    linarith only [hgap]
  have hKp : 0 < K N (N - 1) := div_pos (positive_bumpCorr hg hgc hg0 hgp hclose) hM
  have hlast : 1 / Real.sqrt (N : ℝ) <
      normalizedOverlapGram g N (horizonPoleVector N) iN := by
    rw [normalizedOverlapGram, horizonPoleVector, horizonKernelMatrix_apply_profile]
    change 1 / Real.sqrt (N : ℝ) < ∑ n ∈ Icc 1 N, K N n * (1 / Real.sqrt n)
    have hs : ({N, N - 1} : Finset ℕ) ⊆ Icc 1 N := by
      intro n hn
      rcases mem_insert.mp hn with rfl | hn
      · exact mem_Icc.mpr ⟨by omega, le_rfl⟩
      · rw [mem_singleton] at hn
        subst n
        exact hpred
    have hsum := sum_le_sum_of_subset_of_nonneg (f := fun n => K N n * (1 / Real.sqrt n))
      hs (fun n _ _ => mul_nonneg (hK0 N n) (by positivity))
    rw [sum_insert (by simp only [mem_singleton]; omega), sum_singleton,
      hdiag, one_mul] at hsum
    have hp : 0 < K N (N - 1) * (1 / Real.sqrt ((N - 1 : ℕ) : ℝ)) :=
      mul_pos hKp (one_div_pos.mpr (Real.sqrt_pos.mpr hNp))
    linarith only [hsum, hp]
  rintro ⟨a, ha⟩
  have h₁ := congrArg (fun x : EuclideanSpace ℝ (PrimeHorizonIndex N) => x i₁) ha
  simp only [PiLp.smul_apply, smul_eq_mul] at h₁
  have hb₁ : horizonPoleVector N i₁ = 1 := by
    change 1 / Real.sqrt ((1 : ℕ) : ℝ) = 1
    norm_num
  rw [hfirst, hb₁, mul_one] at h₁
  have hN' := congrArg (fun x : EuclideanSpace ℝ (PrimeHorizonIndex N) => x iN) ha
  simp only [PiLp.smul_apply, smul_eq_mul] at hN'
  have hbN : horizonPoleVector N iN = 1 / Real.sqrt (N : ℝ) := rfl
  rw [hbN, ← h₁, one_mul] at hN'
  exact hlast.ne hN'.symm

private theorem eventually_overlap_endpoints {c : ℝ} (hc : 1 < c) :
    ∀ᶠ N : ℕ in atTop, 3 ≤ N ∧ c / N < Real.log 2 ∧
      Real.log (N : ℝ) - Real.log ((N - 1 : ℕ) : ℝ) < c / N := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨K, hK⟩ := exists_nat_gt (max 3 (max (c / Real.log 2) (c / (c - 1))))
  filter_upwards [eventually_ge_atTop K] with N hN
  have hKN : (K : ℝ) ≤ N := by exact_mod_cast hN
  have hNb : max 3 (max (c / Real.log 2) (c / (c - 1))) < (N : ℝ) := hK.trans_le hKN
  have hN3 : 3 < (N : ℝ) := (le_max_left _ _).trans_lt hNb
  have hN0 : (0 : ℝ) < N := by linarith only [hN3]
  have hN3' : 3 ≤ N := by exact_mod_cast hN3.le
  have hNp : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ N - 1 by omega)
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hwidth : c / N < Real.log 2 := by
    have h : c / Real.log 2 < (N : ℝ) :=
      (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hNb
    have h' := (div_lt_iff₀ hl2).mp h
    exact (div_lt_iff₀ hN0).mpr (by linarith only [h'])
  have hrat : 1 / ((N - 1 : ℕ) : ℝ) < c / N := by
    have h : c / (c - 1) < (N : ℝ) :=
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hNb
    have h' := (div_lt_iff₀ (sub_pos.mpr hc)).mp h
    rw [div_lt_div_iff₀ hNp hN0, one_mul, hcast]
    nlinarith only [h']
  have hlog : Real.log (N : ℝ) - Real.log ((N - 1 : ℕ) : ℝ) ≤
      1 / ((N - 1 : ℕ) : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hN0 hNp)
    rw [Real.log_div hN0.ne' hNp.ne'] at h
    have he : (N : ℝ) / ((N - 1 : ℕ) : ℝ) - 1 = 1 / ((N - 1 : ℕ) : ℝ) := by
      field_simp
      linarith only [hcast]
    rwa [he] at h
  exact ⟨hN3', hwidth, hlog.trans_lt hrat⟩

/-- Genuine fixed overlap changes the arithmetic ground line of the literal spline mass Gram. -/
theorem eventually_normalizedTiltedGram_does_not_preserve_pole {c : ℝ} (hc : 1 < c) :
    ∀ᶠ N : ℕ in atTop, ¬ ∃ a : ℝ,
      normalizedOverlapGram (atomDilate tiltedUnitSpline (c / N)) N (horizonPoleVector N) =
        a • horizonPoleVector N := by
  filter_upwards [eventually_overlap_endpoints hc] with N hN
  have hw : 0 < c / (N : ℝ) := div_pos (lt_trans zero_lt_one hc)
    (by exact_mod_cast (show 0 < N by omega))
  apply overlapGram_does_not_preserve_pole
    (g := atomDilate tiltedUnitSpline (c / N)) (w := c / N) hN.1
    (contDiff_tiltedUnitSpline.continuous.comp (continuous_id.div_const _))
    (hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline)
    (fun u => tiltedUnitSpline_nonneg _)
    (fun u hu => tiltedUnitSpline_pos ⟨div_pos hu.1 hw, (div_lt_one hw).mpr hu.2⟩)
    (tiltedUnitSpline_atom_support hw)
  · rw [integral_atomDilate_sq hw]
    exact mul_pos hw integral_tiltedUnitSpline_sq_pos
  · exact hN.2.1
  · exact hN.2.2

/-- For every genuine fixed overlap, one quarter is the exact correction threshold. -/
theorem eventually_correctedTiltedOverlapDefect_nonneg_iff {c : ℝ} (hc : 1 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ τ : ℝ,
      (∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        0 ≤ correctedOverlapDefect (atomDilate tiltedUnitSpline (c / N)) N τ x) ↔
          1 / 4 ≤ τ := by
  filter_upwards [eventually_normalizedTiltedGram_does_not_preserve_pole hc,
    eventually_ge_atTop 1] with N hG hN
  have hw : 0 < c / (N : ℝ) := div_pos (lt_trans zero_lt_one hc) (by exact_mod_cast hN)
  exact sharp_correction_of_ground_line_failure hN _
    (contDiff_tiltedUnitSpline.continuous.comp (continuous_id.div_const _))
    (hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline) hG

/-- The corrected spline reserve has one ground direction, with strictly positive unsmoothed defect. -/
theorem eventually_correctedTiltedOverlapDefect_ground_line {c : ℝ} (hc : 1 < c) :
    ∀ᶠ N : ℕ in atTop, ∃ u : EuclideanSpace ℝ (PrimeHorizonIndex N),
      u + normalizedOverlapGram (atomDilate tiltedUnitSpline (c / N)) N u = horizonPoleVector N ∧
      0 < poleDefect N (primeHorizonExtension u) ∧
      ∀ x, correctedOverlapDefect (atomDilate tiltedUnitSpline (c / N)) N (1 / 4) x = 0 ↔
        ∃ a : ℝ, x = a • u := by
  filter_upwards [eventually_normalizedTiltedGram_does_not_preserve_pole hc,
    eventually_ge_atTop 1] with N hG hN
  have hw : 0 < c / (N : ℝ) := div_pos (lt_trans zero_lt_one hc) (by exact_mod_cast hN)
  obtain ⟨u, hu, hkernel⟩ := exists_correctedOverlapDefect_ground_line hN
    (atomDilate tiltedUnitSpline (c / N))
    (contDiff_tiltedUnitSpline.continuous.comp (continuous_id.div_const _))
    (hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline)
  refine ⟨u, hu, ?_, hkernel⟩
  apply lt_of_le_of_ne (poleDefect_nonneg _ _)
  intro hz
  exact preimage_not_pole hN _ hG hu
    ((poleDefect_eq_zero_iff_horizonPoleVector hN u).mp hz.symm)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.poleDefect_eq_zero_iff_horizonPoleVector
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.correctedOverlapDefect_eq
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.exists_correctedOverlapDefect_ground_line
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.eventually_normalizedTiltedGram_does_not_preserve_pole
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.eventually_correctedTiltedOverlapDefect_nonneg_iff
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.eventually_correctedTiltedOverlapDefect_ground_line
