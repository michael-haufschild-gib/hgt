import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedHigherPointSpectrum
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPowerSharpGrowth

/-! Concrete unit data attain the full exponential growth along every ray at derivative orders at least three. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPowerGrowthLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalPowerGrowthChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalPowerGrowthChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalPowerGrowthChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalPowerGrowthEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalPowerGrowthEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalPowerGrowthEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalPowerGrowthEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalPowerGrowthEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


open ComplexConjugate

private theorem power_exp_eigenvector (m : ℕ) (z q : ℂ) (u : causalBoundedChain)
    (he : (causalBoundedChainShift^m) u = q • u) :
    causalBoundedPowerExponential m z u = Complex.exp (z*q) • u := by
  have hp (k : ℕ) : ((causalBoundedChainShift^m)^k) u = q^k • u := by
    induction k with
    | zero => simp only [pow_zero, one_smul]; rfl
    | succ k ih =>
      have ha := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u)
        (pow_succ' (causalBoundedChainShift^m) k)
      have hb := congrArg (fun v : causalBoundedChain => (causalBoundedChainShift^m) v) ih
      have hc := (causalBoundedChainShift^m).map_smul (q^k) u
      have hd := congrArg (fun v : causalBoundedChain => q^k • v) he
      have hf := smul_smul (q^k) q u
      have hg := congrArg (fun c : ℂ => c • u) (pow_succ q k).symm
      exact ha.trans (hb.trans (hc.trans (hd.trans (hf.trans hg))))
  have hc : HasSum (fun k : ℕ => ((k.factorial : ℂ))⁻¹ * (z*q)^k) (Complex.exp (z*q)) := by
    simpa only [smul_eq_mul, Complex.exp_eq_exp_ℂ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z*q)
  calc
    _ = ∑' k : ℕ, (((k.factorial : ℂ))⁻¹*z^k) • (((causalBoundedChainShift^m)^k) u) :=
      causalBoundedPowerExponential_series m z u
    _ = ∑' k : ℕ, (((k.factorial : ℂ))⁻¹*(z*q)^k) • u := by
      apply tsum_congr
      intro k
      have ha := congrArg (fun v : causalBoundedChain => (((k.factorial : ℂ))⁻¹*z^k) • v) (hp k)
      have hb := smul_smul (((k.factorial : ℂ))⁻¹*z^k) (q^k) u
      have he' : (((k.factorial : ℂ))⁻¹*z^k) * q^k = ((k.factorial : ℂ))⁻¹*(z*q)^k := by
        rw [mul_pow, mul_assoc]
      exact ha.trans (hb.trans (congrArg (fun c : ℂ => c • u) he'))
    _ = _ := (hc.smul_const u).tsum_eq

/-- Every disk eigenchain carries the exact scalar character of every derivative-order evolution. -/
theorem causalBoundedPowerExponential_diskEigenchain (m : ℕ) (z : ℂ) (q : causalBoundedDiskRate) :
    causalBoundedPowerExponential m z (causalBoundedDiskEigenchain q) =
      Complex.exp (z*q.val^m) • causalBoundedDiskEigenchain q :=
  power_exp_eigenvector m z (q.val^m) (causalBoundedDiskEigenchain q)
    (causalBoundedChainShift_pow_diskEigenchain m q)

/-- The higher-order producer realizes every nonzero unit-disk exponential character. -/
theorem causalBoundedPowerExponential_higherEigenchain (n : ℕ) (z : ℂ) (q : causalPuncturedUnitDisk) :
    causalBoundedPowerExponential (n+3) z (causalBoundedHigherEigenchain n q) =
      Complex.exp (z*q.val) • causalBoundedHigherEigenchain n q :=
  power_exp_eigenvector (n+3) z q.val (causalBoundedHigherEigenchain n q)
    (causalBoundedChainShift_higher_eigenchain n q)

/-- Each constructed higher-order chain has the exact exponential norm of its scalar character. -/
theorem norm_causalBoundedPowerExponential_higherEigenchain (n : ℕ) (z : ℂ) (q : causalPuncturedUnitDisk) :
    ‖causalBoundedPowerExponential (n+3) z (causalBoundedHigherEigenchain n q)‖ =
      Real.exp ((z*q.val).re) := by
  have he := congrArg (fun u : causalBoundedChain => ‖u‖)
    (causalBoundedPowerExponential_higherEigenchain n z q)
  have hs := norm_smul (Complex.exp (z*q.val)) (causalBoundedHigherEigenchain n q)
  have hn := congrArg (fun r : ℝ => ‖Complex.exp (z*q.val)‖*r) (norm_causalBoundedHigherEigenchain n q)
  exact he.trans (hs.trans (hn.trans ((mul_one _).trans (Complex.norm_exp _))))

private theorem growth_rate_norm (z : ℂ) (hz : z ≠ 0) : ‖conj z / (‖z‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.mpr hz)]

/-- A nonzero disk rate aligned with the maximal real growth direction, including a fixed choice at zero. -/
def causalBoundedPowerGrowthRate (z : ℂ) : causalPuncturedUnitDisk :=
  if hz : z = 0 then ⟨1, one_ne_zero, (norm_one : ‖(1 : ℂ)‖ = 1).le⟩
  else ⟨conj z / (‖z‖ : ℂ),
    by intro h; have hn := growth_rate_norm z hz; rw [h, norm_zero] at hn; exact zero_ne_one hn,
    (growth_rate_norm z hz).le⟩

/-- The maximizing rate lies on the actual unit circle. -/
theorem norm_causalBoundedPowerGrowthRate (z : ℂ) : ‖(causalBoundedPowerGrowthRate z).val‖ = 1 := by
  by_cases hz : z = 0
  · simp only [causalBoundedPowerGrowthRate, dif_pos hz, norm_one]
  · exact (by simpa only [causalBoundedPowerGrowthRate, dif_neg hz] using growth_rate_norm z hz)

/-- The actual aligned rate attains the full real growth `norm z`. -/
theorem causalBoundedPowerGrowthRate_character (z : ℂ) :
    (z*(causalBoundedPowerGrowthRate z).val).re = ‖z‖ := by
  by_cases hz : z = 0
  · simp only [hz, zero_mul, Complex.zero_re, norm_zero]
  · have hn := norm_ne_zero_iff.mpr hz
    simp only [causalBoundedPowerGrowthRate, dif_neg hz]
    calc
      _ = (z*conj z).re / ‖z‖ := by rw [← mul_div_assoc, Complex.div_ofReal_re]
      _ = ‖z‖^2 / ‖z‖ := by rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      _ = ‖z‖ * (‖z‖/‖z‖) := by rw [pow_two, mul_div_assoc]
      _ = ‖z‖ := by rw [div_self hn, mul_one]

/-- One actual unit chain selected for the whole positive ray in complex time. -/
def causalBoundedPowerGrowthVector (n : ℕ) (z : ℂ) : causalBoundedChain :=
  causalBoundedHigherEigenchain n (causalBoundedPowerGrowthRate z)

/-- Every selected maximizing datum has genuine unit chain norm. -/
theorem norm_causalBoundedPowerGrowthVector (n : ℕ) (z : ℂ) :
    ‖causalBoundedPowerGrowthVector n z‖ = 1 := norm_causalBoundedHigherEigenchain n _

/-- One concrete datum realizes maximal exponential growth at every positive time on the chosen ray. -/
theorem causalBoundedPowerGrowthVector_ray_norm (n : ℕ) (z : ℂ) (t : ℝ≥0) :
    ‖causalBoundedPowerExponential (n+3) ((t : ℂ)*z) (causalBoundedPowerGrowthVector n z)‖ =
      Real.exp ((t : ℝ)*‖z‖) := by
  have hr : (((t : ℂ)*z)*(causalBoundedPowerGrowthRate z).val).re = (t : ℝ)*‖z‖ := by
    calc
      _ = ((t : ℂ)*(z*(causalBoundedPowerGrowthRate z).val)).re := congrArg Complex.re (mul_assoc _ _ _)
      _ = (t : ℝ)*(z*(causalBoundedPowerGrowthRate z).val).re := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      _ = _ := congrArg (fun r : ℝ => (t : ℝ)*r) (causalBoundedPowerGrowthRate_character z)
  exact (norm_causalBoundedPowerExponential_higherEigenchain n ((t : ℂ)*z) (causalBoundedPowerGrowthRate z)).trans
    (congrArg Real.exp hr)

end
end RHTower.FokasLenells
