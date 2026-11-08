import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedProbeSpace
import GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Compact inclusions between conductor-weighted probe spaces

Decreasing the conductor exponent changes normalized Hilbert coordinates by
`n^((β−δ)/2)` and preserves the original arithmetic coefficient sequence.
For a strict decrease this multiplier tends to zero, giving compactness.
The real inclusion is the restriction of the existing complex diagonal operator.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open HTGeometry.LpDiagonal

/-- Embed real Hilbert coordinates into complex coordinates. -/
def probeComplexify : WeightedProbe 0 →L[ℝ] LpTwo ℕ :=
  lp.mapCLM 2 (fun _ : ℕ => Complex.ofRealCLM) zero_le_one
    (fun _ => Complex.ofRealCLM_norm.le)

/-- Recover the real coordinates of a complex Hilbert probe. -/
def probeRealPart : LpTwo ℕ →L[ℝ] WeightedProbe 0 :=
  lp.mapCLM 2 (fun _ : ℕ => Complex.reCLM) zero_le_one
    (fun _ => Complex.reCLM_norm.le)

/-- Decreasing the conductor weight multiplies normalized coordinates by this factor. -/
def probeWeightFactor (δ β : ℝ) (n : ℕ) : ℝ :=
  ((n+1:ℕ):ℝ)^((β-δ)/2)

theorem probeWeightFactor_norm_le (δ β : ℝ) (h : β ≤ δ) (n : ℕ) :
    ‖(probeWeightFactor δ β n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  change |((n+1:ℕ):ℝ)^((β-δ)/2)| ≤ 1
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    (by linarith)

/-- The natural conductor inclusion preserves the original arithmetic coefficient sequence. -/
def weightedProbeInclusion (δ β : ℝ) (h : β ≤ δ) : WeightedProbe δ →L[ℝ] WeightedProbe β :=
  probeRealPart.comp
    (((lpDiag (fun n => (probeWeightFactor δ β n : ℂ)) 1 zero_le_one
      (probeWeightFactor_norm_le δ β h)).restrictScalars ℝ).comp probeComplexify)

theorem weightedProbeInclusion_apply (δ β : ℝ) (h : β ≤ δ) (u : WeightedProbe δ) (n : ℕ) :
    weightedProbeInclusion δ β h u n=probeWeightFactor δ β n*u n := by
  change ((probeWeightFactor δ β n : ℂ)*(u n : ℂ)).re = _
  simp only [← Complex.ofReal_mul,Complex.ofReal_re]

/-- Changing the Hilbert normalization leaves every arithmetic coefficient unchanged. -/
theorem weightedProbeInclusion_coefficients (δ β : ℝ) (h : β ≤ δ) (u : WeightedProbe δ) :
    probeCoefficients β (weightedProbeInclusion δ β h u)=probeCoefficients δ u := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    rw [probeCoefficients_succ,probeCoefficients_succ,weightedProbeInclusion_apply]
    have hn : (0:ℝ)<(n+1:ℕ) := by positivity
    change (((n+1:ℕ):ℝ)^((β-δ)/2)*u n)*((n+1:ℕ):ℝ)^(-β/2)=
      u n*((n+1:ℕ):ℝ)^(-δ/2)
    calc _ = u n*(((n+1:ℕ):ℝ)^((β-δ)/2)*((n+1:ℕ):ℝ)^(-β/2)) := by ring
         _ = _ := by
          rw [← Real.rpow_add hn,show (β-δ)/2 + -β/2 = -δ/2 by ring]

/-- Strictly decreasing the conductor weight gives a compact inclusion. -/
theorem weightedProbeInclusion_compact (δ β : ℝ) (h : β < δ) :
    IsCompactOperator (weightedProbeInclusion δ β h.le) := by
  have ht : Tendsto (fun n : ℕ => ‖(probeWeightFactor δ β n : ℂ)‖) cofinite (𝓝 0) := by
    have he : (β-δ)/2 = -((δ-β)/2) := by ring
    have hr := tendsto_rpow_neg_atTop (show 0 < (δ-β)/2 by linarith)
    have hn : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hh := hr.comp hn
    rw [Nat.cofinite_eq_atTop]
    convert hh using 1
    funext n
    rw [Complex.norm_real,Real.norm_eq_abs]
    change |((n+1:ℕ):ℝ)^((β-δ)/2)| = ((n+1:ℕ):ℝ)^(-((δ-β)/2))
    rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _),he]
  have hc := isCompactOperator_lpDiag (fun n => (probeWeightFactor δ β n : ℂ)) 1 zero_le_one
    (probeWeightFactor_norm_le δ β h.le) ht
  exact (hc.comp_clm probeComplexify).clm_comp probeRealPart

#print axioms weightedProbeInclusion_coefficients
#print axioms weightedProbeInclusion_compact
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
