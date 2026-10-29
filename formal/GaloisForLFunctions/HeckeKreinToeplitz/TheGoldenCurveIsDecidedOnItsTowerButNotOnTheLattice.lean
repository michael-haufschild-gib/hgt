import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep
import GaloisForLFunctions.HeckeKreinToeplitz.WeilsIndexIsCountedByTheOuterFrobeniusEigenvalues
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSelectivityBatteryOfOrientation

/-!
# The golden curve is decided on its tower but not on the lattice

The golden datum `1 − 5X + 5X²` is a fake curve over `𝔽₅`: integral counts, rational zeta,
functional equation, but normalized eigenvalues `φ, φ⁻¹` off the unit circle. Its zeros
`ρ_{i,k} = ½ + log|β_i|/log 5 + i(arg β_i + 2πk)/log 5` repeat with the vertical period `2π/log 5`.

* **On its own tower** the trace kernel has index exactly one (`negIndex_golden_traceKernel`): all
  the right zeros `ρ_{0,k}` have the same value `5^{ρ−1/2} = φ` and alias into one hyperbolic pair.
* **On the Hecke lattice** the orbit kernel of the golden configuration has infinite index
  (`negIndex_orbitKernel_golden`), already on any two primes (`negIndex_orbitKernel_golden_twoPrime`):
  the right zeros are infinitely many (`rightZeros_golden_infinite`) and two primes never alias them.

So a configuration that is periodic in the ordinate is a single pair on the tower of its own
characteristic and infinitely many pairs on `ℚ_{>0}`: the Hecke lattice is not a tower, and the
calibration over `𝔽_q` is the restriction of the theory to one cyclic sublattice
(`golden_tower_vs_lattice`).
-/

open Complex Finset
open Zeta23
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (goldenDatum CurveDatum rightZeros)
open GaloisForLFunctions.ArithmeticOrientationGeometry (goldenConfig temperedConfig_goldenConfig
  seenRightZeros_cubicSpline)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- **The golden curve has infinitely many zeros right of the line.** -/
theorem rightZeros_golden_infinite :
    {ρ ∈ goldenConfig.carrier | 1 / 2 < ρ.re}.Infinite := by
  have hφ : 1 < ‖goldenDatum.β 0‖ := by
    show 1 < ‖((Real.goldenRatio : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.goldenRatio_pos]
    exact Real.one_lt_goldenRatio
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => goldenDatum.zetaZero 0 k)
    (fun k k' h => ?_) fun k => ⟨⟨(0, k), rfl⟩, (goldenDatum.re_zetaZero_gt_iff 0 k).mpr hφ⟩
  have him := congrArg Complex.im h
  simp only [CurveDatum.im_zetaZero, add_right_inj] at him
  exact_mod_cast mul_right_cancel₀ goldenDatum.period_pos.ne' him

/-- **The golden orbit kernel has infinite index on the Hecke lattice.** -/
theorem negIndex_orbitKernel_golden : negIndex (orbitKernel goldenConfig cubicSpline) = ⊤ := by
  rw [negIndex_orbitKernel _ temperedConfig_goldenConfig cubicSpline_mem_realTests,
    seenRightZeros_cubicSpline]
  exact Set.encard_eq_top_iff.mpr rightZeros_golden_infinite

/-- **Already two primes see infinitely many golden pairs.** -/
theorem negIndex_orbitKernel_golden_twoPrime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    negIndex (orbitKernel goldenConfig cubicSpline ∘ (twoPrimeLattice hp hq).subtype) = ⊤ := by
  rw [negIndex_orbitKernel_twoPrime _ temperedConfig_goldenConfig cubicSpline_mem_realTests hp hq
    hpq, seenRightZeros_cubicSpline]
  exact Set.encard_eq_top_iff.mpr rightZeros_golden_infinite

/-- **Index one on the tower, infinite index on the lattice.** -/
theorem golden_tower_vs_lattice :
    negIndex (traceKernel goldenDatum) = 1 ∧
      negIndex (orbitKernel goldenConfig cubicSpline) = ⊤ :=
  ⟨negIndex_golden_traceKernel, negIndex_orbitKernel_golden⟩

end GaloisForLFunctions.HeckeKreinToeplitz
