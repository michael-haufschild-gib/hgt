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
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis ArithmeticFunction
  BiScaleUncertainty.ChebyshevGauge

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

private theorem poleDefect_zero (N : ℕ) : poleDefect N 0 = 0 := by
  simp only [poleDefect, Pi.zero_apply, zero_div, sub_self, zero_pow two_ne_zero,
    mul_zero, sum_const_zero]

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
  have he := congrArg (fun x : EuclideanSpace ℝ (PrimeHorizonIndex N) =>
    x ⟨1, mem_Icc.mpr ⟨le_rfl, hN⟩⟩) h
  change 1 / Real.sqrt (1 : ℝ) = 0 at he
  norm_num at he

private theorem preimage_not_pole {N : ℕ} (hN : 1 ≤ N)
    (G : EuclideanSpace ℝ (PrimeHorizonIndex N) →ₗ[ℝ]
      EuclideanSpace ℝ (PrimeHorizonIndex N))
    (hG : ¬ ∃ a : ℝ, G (horizonPoleVector N) = a • horizonPoleVector N)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu : u + G u = horizonPoleVector N) : ¬ ∃ a : ℝ, u = a • horizonPoleVector N := by
  rintro ⟨a, ha⟩
  have ha0 : a ≠ 0 := by
    intro hz
    rw [ha, hz, zero_smul, map_zero, add_zero] at hu
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

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
