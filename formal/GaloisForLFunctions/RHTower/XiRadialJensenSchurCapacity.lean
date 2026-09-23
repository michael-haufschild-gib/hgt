import GaloisForLFunctions.RHTower.XiGlobalReflectionDefectEnergy
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.RHTower.XiOffLineQuartetThermalOrientationBound
import GaloisForLFunctions.RHTower.XiHeatShellMinimum
import GaloisForLFunctions.HTGeometry.SchwarzPickEstimate

/-!
# The disk-Schur norm of the Xi moment functional is the central curvature

Every reciprocal-square Xi atom lies inside the disk of radius `2/41` and inside a narrow positive
sector, so the divisor family satisfies the small-sector balance.  The narrow-sector Schur lemma
then makes the weighted evaluation functional attain its norm at the constant function: its Schur
norm is exactly the central prime--Gamma curvature.

The missing trace-norm mass is precisely half the global reflection-defect energy, so saturation of
the Schur bound by the radial Jensen mass is the Riemann hypothesis.
-/

open Complex Metric

namespace RHTower

noncomputable section

theorem norm_xiZeroCopyReciprocalSquare_eq (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ = ‖xiReciprocalCoordinate q‖ ^ (2 : ℕ) := by
  rw [xiZeroCopyReciprocalSquare, xiReciprocalCoordinate, norm_pow]

private theorem norm_xiZeroCopyReciprocalSquare_le (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ ≤ 2 / 41 := by
  have hgap := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hnorm : ‖xiSpectralPoint q‖ = ‖(q.1 : ℂ) - 1 / 2‖ := norm_xiSpectralPoint q
  have hsq : ‖(q.1 : ℂ) - 1 / 2‖ ^ (2 : ℕ) =
      ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + ((q.1 : ℂ).im) ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    norm_num
    ring
  have hlarge : 41 / 2 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
    rw [hnorm, hsq]
    nlinarith [sq_nonneg ((q.1 : ℂ).re - 1 / 2)]
  have hpos : (0 : ℝ) < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by linarith
  rw [norm_xiZeroCopyReciprocalSquare_eq, xiReciprocalCoordinate, norm_inv, inv_pow]
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

private theorem summable_norm_xiZeroCopyReciprocalSquare :
    Summable (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖) := by
  apply summable_norm_xiSpectralPoint_inv_sq.congr
  intro q
  rw [norm_xiZeroCopyReciprocalSquare_eq, xiReciprocalCoordinate]

theorem tsum_norm_xiZeroCopyReciprocalSquare :
    (∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖) = xiReciprocalHermitianMass := by
  rw [xiReciprocalHermitianMass]
  exact tsum_congr fun q => norm_xiZeroCopyReciprocalSquare_eq q

theorem tsum_xiZeroCopyReciprocalSquare_eq_curvature :
    (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q) =
      ((primeArchCentralCurvature : ℝ) : ℂ) := by
  have h := tsum_xiZeroCopyReciprocalSquare_pow 0
  simp only [zero_add, pow_one] at h
  rw [h, primeArchCentralCurvature_eq_moment_re]
  exact (Complex.conj_eq_iff_re.mp (xiCentralReciprocalMoment_conj 0)).symm

theorem tsum_re_xiZeroCopyReciprocalSquare :
    (∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q).re) = primeArchCentralCurvature := by
  rw [← Complex.re_tsum summable_xiZeroCopyReciprocalSquare,
    tsum_xiZeroCopyReciprocalSquare_eq_curvature, Complex.ofReal_re]

theorem primeArchCentralCurvature_pos : 0 < primeArchCentralCurvature := by
  rw [← tsum_re_xiZeroCopyReciprocalSquare]
  have hsum : Summable (fun q : XiZeroCopy => (xiZeroCopyReciprocalSquare q).re) :=
    Complex.reCLM.summable summable_xiZeroCopyReciprocalSquare
  obtain ⟨q₀⟩ := nonempty_xiZeroCopy
  exact hsum.tsum_pos (fun q => (xiThermalNode_pos q).le) q₀ (xiThermalNode_pos q₀)

/-- **Narrow positive sector.**  Every reciprocal-square atom is within a fixed factor of its
positive real part. -/
theorem norm_le_elevenTenths_re (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ ≤ (11 / 10) * (xiZeroCopyReciprocalSquare q).re := by
  have hre : 0 < (xiZeroCopyReciprocalSquare q).re := xiThermalNode_pos q
  have him := xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  have hnormsq : ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ) =
      (xiZeroCopyReciprocalSquare q).re ^ (2 : ℕ) + (xiZeroCopyReciprocalSquare q).im ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hbound : ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ) ≤
      ((11 / 10) * (xiZeroCopyReciprocalSquare q).re) ^ (2 : ℕ) := by
    rw [hnormsq]
    rw [xiThermalNode] at him
    nlinarith
  nlinarith [norm_nonneg (xiZeroCopyReciprocalSquare q), hre]

theorem xiReciprocalHermitianMass_le :
    xiReciprocalHermitianMass ≤ (11 / 10) * primeArchCentralCurvature := by
  rw [← tsum_norm_xiZeroCopyReciprocalSquare, ← tsum_re_xiZeroCopyReciprocalSquare,
    ← tsum_mul_left]
  exact summable_norm_xiZeroCopyReciprocalSquare.tsum_mono
    ((Complex.reCLM.summable summable_xiZeroCopyReciprocalSquare).mul_left _)
    norm_le_elevenTenths_re

theorem summable_norm_sq_xiZeroCopyReciprocalSquare :
    Summable (fun q : XiZeroCopy => ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ)) := by
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    (summable_norm_xiZeroCopyReciprocalSquare.mul_left (2 / 41))
  show ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ) ≤ 2 / 41 * ‖xiZeroCopyReciprocalSquare q‖
  have h1 : ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ) =
      ‖xiZeroCopyReciprocalSquare q‖ * ‖xiZeroCopyReciprocalSquare q‖ := by ring
  rw [h1, mul_comm (2 / 41 : ℝ)]
  exact mul_le_mul_of_nonneg_left (norm_xiZeroCopyReciprocalSquare_le q) (norm_nonneg _)

theorem tsum_norm_sq_le :
    (∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ)) ≤
      (2 / 41) * xiReciprocalHermitianMass := by
  rw [← tsum_norm_xiZeroCopyReciprocalSquare, ← tsum_mul_left]
  refine summable_norm_sq_xiZeroCopyReciprocalSquare.tsum_mono
    (summable_norm_xiZeroCopyReciprocalSquare.mul_left _) (fun q => ?_)
  show ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ) ≤ 2 / 41 * ‖xiZeroCopyReciprocalSquare q‖
  have h1 : ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ) =
      ‖xiZeroCopyReciprocalSquare q‖ * ‖xiZeroCopyReciprocalSquare q‖ := by ring
  rw [h1, mul_comm (2 / 41 : ℝ)]
  exact mul_le_mul_of_nonneg_left (norm_xiZeroCopyReciprocalSquare_le q) (norm_nonneg _)

/-- **The small-sector balance for the Xi divisor.** -/
theorem xi_narrowSector_balance :
    2 * (∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ ^ (2 : ℕ)) ≤
      (1 - 2 / 41) * primeArchCentralCurvature := by
  have h1 := tsum_norm_sq_le
  have h2 := xiReciprocalHermitianMass_le
  have h3 : (0 : ℝ) ≤ primeArchCentralCurvature := primeArchCentralCurvature_pos.le
  nlinarith

/-- **The disk-Schur norm of the Xi moment functional is the central curvature.** -/
theorem norm_xiSchurFunctional_le
    {f : ℂ → ℂ} (hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hf : ∀ w ∈ ball (0 : ℂ) 1, ‖f w‖ ≤ 1) :
    ‖∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q * f (xiZeroCopyReciprocalSquare q)‖ ≤
      primeArchCentralCurvature :=
  GaloisForLFunctions.HTGeometry.narrowSectorSchur_norm_le
    summable_norm_xiZeroCopyReciprocalSquare (by norm_num) (by norm_num)
    norm_xiZeroCopyReciprocalSquare_le tsum_xiZeroCopyReciprocalSquare_eq_curvature
    primeArchCentralCurvature_pos rfl xi_narrowSector_balance hdiff hf

/-- The constant function attains the bound, so the norm is exactly the central curvature. -/
theorem xiSchurFunctional_const_one :
    (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q * (1 : ℂ)) =
      ((primeArchCentralCurvature : ℝ) : ℂ) := by
  simpa using tsum_xiZeroCopyReciprocalSquare_eq_curvature

/-- **Exact reflection-energy norm gap.**  The radial Jensen mass exceeds the Schur norm by
exactly half the global reflection-defect energy. -/
theorem xiReciprocalHermitianMass_sub_curvature :
    xiReciprocalHermitianMass - primeArchCentralCurvature =
      xiGlobalReflectionDefectEnergy / 2 := by
  have h := xiGlobalReflectionDefectEnergy_eq_mass_sub_source
  linarith

end

end RHTower
