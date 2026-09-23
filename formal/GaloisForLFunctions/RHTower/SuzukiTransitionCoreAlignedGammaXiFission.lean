import GaloisForLFunctions.RHTower.SuzukiTransitionCoreAlignedGammaCompletion
import GaloisForLFunctions.RHTower.FrankensteinWoldCubicJuliaOrbitBudget
import GaloisForLFunctions.RHTower.SourceHorizontalEulerWoldJordanConormalCoShortAdmission

/-!
# Aligned completed Suzuki transition core on each Xi fibre

Gamma completion is inserted before residue selection by one global real source factor.  The
resulting carrier preserves every ordered transition pair, analytic multiplicity copy, both
residue orientations, same-fibre star covariance, and the four-orientation non-spectral short.
Its total Xi-fibre energy is exactly the aligned completed transition-core energy, rather than a
post-selected scalar surrogate.
-/

open Complex Filter Matrix Set Topology
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

/-- Global source alignment: complete the coherent atomic amplitude before forming pair energy. -/
def suzukiTransitionCoreGammaAlignmentFactor (N : ℕ) : ℝ :=
  if _hA : unitRieszCoherentPrimeOutgoingCharge N = 0 then 0
  else suzukiNaturalApertureCompletedLowerHardyAmplitude N /
    unitRieszCoherentPrimeOutgoingCharge N

theorem suzukiTransitionCoreAlignedGammaCompletedEnergy_eq (N : ℕ) :
    suzukiTransitionCoreAlignedGammaCompletedEnergy N =
      suzukiNaturalApertureTransitionCoreCauchyEnergy N *
        suzukiTransitionCoreGammaAlignmentFactor N ^ (2 : ℕ) := by
  rw [suzukiTransitionCoreAlignedGammaCompletedEnergy,
    suzukiTransitionCoreGammaAlignmentFactor]
  split_ifs <;> simp

def suzukiTransitionCoreAlignedXiCopyReflectedCoordinate
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) : ℂ :=
  (suzukiTransitionCoreGammaAlignmentFactor N : ℂ) *
    suzukiTransitionCoreXiCopyReflectedCoordinate N ij rho r j

def suzukiTransitionCoreAlignedXiCopyForwardCoordinate
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) : ℂ :=
  (suzukiTransitionCoreGammaAlignmentFactor N : ℂ) *
    suzukiTransitionCoreXiCopyForwardCoordinate N ij rho r j

def suzukiTransitionCoreAlignedXiReflectedCopySourceCoordinate
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport)
    (z : ℂ) (r : ℝ) (j : Fin (xiSupportMultiplicity rho)) : ℂ :=
  (suzukiTransitionCoreGammaAlignmentFactor N : ℂ) *
    suzukiTransitionCoreXiReflectedCopySourceCoordinate N ij rho z r j

def suzukiTransitionCoreAlignedXiForwardCopySourceCoordinate
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport)
    (z : ℂ) (r : ℝ) (j : Fin (xiSupportMultiplicity rho)) : ℂ :=
  (suzukiTransitionCoreGammaAlignmentFactor N : ℂ) *
    suzukiTransitionCoreXiForwardCopySourceCoordinate N ij rho z r j

theorem tendsto_suzukiTransitionCoreAlignedXiReflectedCopySourceCoordinate
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    Tendsto
      (fun z => suzukiTransitionCoreAlignedXiReflectedCopySourceCoordinate
        N ij rho z r j)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (suzukiTransitionCoreAlignedXiCopyReflectedCoordinate N ij rho r j)) := by
  simpa [suzukiTransitionCoreAlignedXiReflectedCopySourceCoordinate,
    suzukiTransitionCoreAlignedXiCopyReflectedCoordinate] using
    (tendsto_suzukiTransitionCoreXiReflectedCopySourceCoordinate
      N ij rho r j).const_mul (suzukiTransitionCoreGammaAlignmentFactor N : ℂ)

theorem tendsto_suzukiTransitionCoreAlignedXiForwardCopySourceCoordinate
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    Tendsto
      (fun z => suzukiTransitionCoreAlignedXiForwardCopySourceCoordinate
        N ij rho z r j)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (suzukiTransitionCoreAlignedXiCopyForwardCoordinate N ij rho r j)) := by
  simpa [suzukiTransitionCoreAlignedXiForwardCopySourceCoordinate,
    suzukiTransitionCoreAlignedXiCopyForwardCoordinate] using
    (tendsto_suzukiTransitionCoreXiForwardCopySourceCoordinate
      N ij rho r j).const_mul (suzukiTransitionCoreGammaAlignmentFactor N : ℂ)

theorem suzukiTransitionCoreAlignedXiCopyReflectedCoordinate_eq_star_forward
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    suzukiTransitionCoreAlignedXiCopyReflectedCoordinate N ij rho r j =
      star (suzukiTransitionCoreAlignedXiCopyForwardCoordinate N ij rho r j) := by
  rw [suzukiTransitionCoreAlignedXiCopyReflectedCoordinate,
    suzukiTransitionCoreAlignedXiCopyForwardCoordinate,
    suzukiTransitionCoreXiCopyReflectedCoordinate_eq,
    suzukiTransitionCoreXiCopyForwardCoordinate_eq,
    xiWardCubicReflectedConormalMateFeature_eq_star]
  simp [suzukiTransitionCoreStokesAmplitude]

def suzukiTransitionCoreAlignedXiCopySharedOrientationBlock
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) : Matrix (Fin 2) (Fin 2) ℂ :=
  routePJuliaSharedOrientationOrbitBlock
    (suzukiTransitionCoreAlignedXiCopyForwardCoordinate N ij rho r j)

theorem suzukiTransitionCoreAlignedXiCopySharedOrientationBlock_posSemidef
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    (suzukiTransitionCoreAlignedXiCopySharedOrientationBlock
      N ij rho r j).PosSemidef := by
  exact routePJuliaSharedOrientationOrbitBlock_posSemidef _

theorem suzukiTransitionCoreAlignedXiCopySharedOrientationBlock_short
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    let B := suzukiTransitionCoreAlignedXiCopySharedOrientationBlock N ij rho r j
    B 0 0 - B 0 1 * (B 1 1)⁻¹ * B 1 0 =
      (((4 : ℝ) * Complex.normSq
        (suzukiTransitionCoreAlignedXiCopyForwardCoordinate N ij rho r j) : ℝ) : ℂ) := by
  exact routePJuliaSharedOrientationOrbitBlock_short _

def suzukiTransitionCoreAlignedXiFibreCornerEnergy
    (N : ℕ) (rho : XiDivisorSupport) (r : ℝ) : ℝ :=
  ∑ ij ∈ suzukiTransitionCorePairSet N,
    ∑ j, Complex.normSq
      (suzukiTransitionCoreAlignedXiCopyForwardCoordinate N ij rho r j)

theorem suzukiTransitionCoreAlignedXiFibreCornerEnergy_eq
    (N : ℕ) (rho : XiDivisorSupport) (r : ℝ) :
    suzukiTransitionCoreAlignedXiFibreCornerEnergy N rho r =
      suzukiTransitionCoreGammaAlignmentFactor N ^ (2 : ℕ) *
        suzukiTransitionCoreXiFibreCornerEnergy N rho r := by
  classical
  rw [suzukiTransitionCoreAlignedXiFibreCornerEnergy,
    suzukiTransitionCoreXiFibreCornerEnergy]
  simp only [suzukiTransitionCoreAlignedXiCopyForwardCoordinate,
    Complex.normSq_mul, Complex.normSq_ofReal]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem two_mul_suzukiTransitionCoreAlignedXiFibreCornerEnergy_eq
    (N : ℕ) (rho : XiDivisorSupport) (r : ℝ) :
    2 * suzukiTransitionCoreAlignedXiFibreCornerEnergy N rho r =
      (xiSupportMultiplicity rho : ℝ) *
        suzukiTransitionCoreAlignedGammaCompletedEnergy N *
          Complex.normSq (routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  rw [suzukiTransitionCoreAlignedXiFibreCornerEnergy_eq]
  have h := two_mul_suzukiTransitionCoreXiFibreCornerEnergy_eq N rho r
  rw [suzukiTransitionCoreAlignedGammaCompletedEnergy_eq]
  nlinarith

def suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy
    (N : ℕ) (rho : XiDivisorSupport) (r : ℝ) : ℝ :=
  ∑ ij ∈ suzukiTransitionCorePairSet N,
    ∑ j, sourceHorizontalLiteralConormalShort
      (suzukiTransitionCoreAlignedXiCopyForwardCoordinate N ij rho r j)

/-- Exact multi-gate weld: one pre-residue alignment survives Xi selection, multiplicity fission,
both reflection orientations, and the four-orientation non-spectral short. -/
theorem suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy_eq
    (N : ℕ) (rho : XiDivisorSupport) (r : ℝ) :
    suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy N rho r =
      2 * (xiSupportMultiplicity rho : ℝ) *
        suzukiTransitionCoreAlignedGammaCompletedEnergy N *
          Complex.normSq (routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  calc
    suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy N rho r =
        4 * suzukiTransitionCoreAlignedXiFibreCornerEnergy N rho r := by
      rw [suzukiTransitionCoreAlignedXiSharedOrientationShortEnergy,
        suzukiTransitionCoreAlignedXiFibreCornerEnergy]
      simp only [sourceHorizontalLiteralConormalShort, Finset.mul_sum]
    _ = 2 * (xiSupportMultiplicity rho : ℝ) *
        suzukiTransitionCoreAlignedGammaCompletedEnergy N *
          Complex.normSq (routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
      have h := two_mul_suzukiTransitionCoreAlignedXiFibreCornerEnergy_eq N rho r
      nlinarith

end
end GaloisForLFunctions.RHTower
