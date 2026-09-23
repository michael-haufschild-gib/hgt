import GaloisForLFunctions.RHTower.SuzukiTransitionCoreGrowingRankCartanFission
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaCompletedXiDivisorShorting

/-!
# Suzuki transition-core descent through completed Xi residues

Every retained ordered pair in the positive Suzuki reporter-secant transition core is transported
through the existing pre-divisor completed Gamma/polar quadratic source current.  Its Cartan
amplitude is inserted before either pole limit, analytic multiplicity is split on the source side,
and only then are the two reflected divisor residues taken.

On a common Xi fibre the resulting block is Hermitian positive rank one and has zero Schur short.
More importantly, summing its positive source corner over all ordered transition pairs and every
analytic-multiplicity copy recovers exactly the literal transition-core Cauchy energy times the
multiplicity and Route-P conormal energy.  Thus prime-pair labels, reporter-secant coefficients,
both residue orientations, and divisor multiplicity survive one coefficient-faithful carrier.

This is an occurrence and transport theorem, not an order theorem.  Zero short does not annihilate
the nonzero Xi coordinate.  The remaining producer must supply a signed completed-source budget
or relational order that controls this exact corner before scalar domination.
-/

open Complex Filter Matrix Set Topology
open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

noncomputable section

def suzukiTransitionCoreXiReflectedResidueGauge
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport)
    (z : ℂ) (r : ℝ) : ℂ :=
  suzukiTransitionCoreStokesAmplitude N ij *
    ((z - criticalMellinXiPole rho) *
      frankensteinKreinCCMRoutePReflectedSourceColumn z r)

def suzukiTransitionCoreXiForwardResidueGauge
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport)
    (z : ℂ) (r : ℝ) : ℂ :=
  suzukiTransitionCoreStokesAmplitude N ij *
    ((z - criticalMellinXiPole rho) *
      frankensteinKreinCCMRoutePForwardSourceColumn z r)

def suzukiTransitionCoreCompletedSourceEnvironmentBlock
    (N : ℕ) (ij : ℕ × ℕ) (rho tau : XiDivisorSupport)
    (z w : ℂ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  routePJuliaEnvironmentBilinearBlock
    (suzukiTransitionCoreXiReflectedResidueGauge N ij rho z r)
    (suzukiTransitionCoreXiForwardResidueGauge N ij tau w r)

@[simp] theorem suzukiTransitionCoreCompletedSourceEnvironmentBlock_short_eq_zero
    (N : ℕ) (ij : ℕ × ℕ) (rho tau : XiDivisorSupport)
    (z w : ℂ) (r : ℝ) :
    routePJuliaEnvironmentBilinearShort
      (suzukiTransitionCoreXiReflectedResidueGauge N ij rho z r)
      (suzukiTransitionCoreXiForwardResidueGauge N ij tau w r) = 0 := by
  exact routePJuliaEnvironmentBilinearShort_eq_zero _ _

theorem suzukiTransitionCoreCompletedSourceEnvironmentBlock_sourceCorner
    (N : ℕ) (ij : ℕ × ℕ) (rho tau : XiDivisorSupport)
    (z w : ℂ) (r : ℝ) :
    suzukiTransitionCoreCompletedSourceEnvironmentBlock
        N ij rho tau z w r 0 0 =
      (z - criticalMellinXiPole rho) * (w - criticalMellinXiPole tau) *
        suzukiTransitionCoreStokesAmplitude N ij ^ (2 : ℕ) *
          frankensteinKreinCCMRoutePQuadraticSourceCurrent z w r := by
  change
    (suzukiTransitionCoreStokesAmplitude N ij *
        ((z - criticalMellinXiPole rho) *
          frankensteinKreinCCMRoutePReflectedSourceColumn z r)) *
      (suzukiTransitionCoreStokesAmplitude N ij *
        ((w - criticalMellinXiPole tau) *
          frankensteinKreinCCMRoutePForwardSourceColumn w r)) = _
  rw [frankensteinKreinCCMRoutePQuadraticSourceCurrent]
  ring

theorem tendsto_suzukiTransitionCoreXiReflectedResidueGauge
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun z => suzukiTransitionCoreXiReflectedResidueGauge N ij rho z r)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (suzukiTransitionCoreStokesAmplitude N ij *
        ((inverseTiltedXiMultiplicity rho : ℂ) *
          xiWardCubicReflectedConormalMateFeature (rho : ℂ) r))) := by
  simpa [suzukiTransitionCoreXiReflectedResidueGauge] using
    (frankensteinKreinCCMRoutePReflectedSourceColumn_residue rho r).const_mul
      (suzukiTransitionCoreStokesAmplitude N ij)

theorem tendsto_suzukiTransitionCoreXiForwardResidueGauge
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun z => suzukiTransitionCoreXiForwardResidueGauge N ij rho z r)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (suzukiTransitionCoreStokesAmplitude N ij *
        ((inverseTiltedXiMultiplicity rho : ℂ) *
          routePXiBaseConormalResidueFeature (rho : ℂ) r))) := by
  simpa [suzukiTransitionCoreXiForwardResidueGauge] using
    (frankensteinKreinCCMRoutePForwardSourceColumn_residue rho r).const_mul
      (suzukiTransitionCoreStokesAmplitude N ij)

def suzukiTransitionCoreXiCopyReflectedCoordinate
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) : ℂ :=
  routePXiConormalMultiplicitySplit rho
    ((xiSupportMultiplicity rho : ℂ) *
      (suzukiTransitionCoreStokesAmplitude N ij *
        xiWardCubicReflectedConormalMateFeature (rho : ℂ) r)) j

def suzukiTransitionCoreXiCopyForwardCoordinate
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) : ℂ :=
  routePXiConormalMultiplicitySplit rho
    ((xiSupportMultiplicity rho : ℂ) *
      (suzukiTransitionCoreStokesAmplitude N ij *
        routePXiBaseConormalResidueFeature (rho : ℂ) r)) j

@[simp] theorem suzukiTransitionCoreXiCopyReflectedCoordinate_eq
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    suzukiTransitionCoreXiCopyReflectedCoordinate N ij rho r j =
      suzukiTransitionCoreStokesAmplitude N ij *
        xiWardCubicReflectedConormalMateFeature (rho : ℂ) r := by
  exact routePXiConormalMultiplicitySplit_raw_apply rho _ j

@[simp] theorem suzukiTransitionCoreXiCopyForwardCoordinate_eq
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    suzukiTransitionCoreXiCopyForwardCoordinate N ij rho r j =
      suzukiTransitionCoreStokesAmplitude N ij *
        routePXiBaseConormalResidueFeature (rho : ℂ) r := by
  exact routePXiConormalMultiplicitySplit_raw_apply rho _ j

def suzukiTransitionCoreXiReflectedCopySourceCoordinate
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport)
    (z : ℂ) (r : ℝ) (j : Fin (xiSupportMultiplicity rho)) : ℂ :=
  routePXiConormalMultiplicitySplit rho
    (suzukiTransitionCoreXiReflectedResidueGauge N ij rho z r) j

def suzukiTransitionCoreXiForwardCopySourceCoordinate
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport)
    (z : ℂ) (r : ℝ) (j : Fin (xiSupportMultiplicity rho)) : ℂ :=
  routePXiConormalMultiplicitySplit rho
    (suzukiTransitionCoreXiForwardResidueGauge N ij rho z r) j

theorem tendsto_suzukiTransitionCoreXiReflectedCopySourceCoordinate
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    Tendsto
      (fun z => suzukiTransitionCoreXiReflectedCopySourceCoordinate
        N ij rho z r j)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (suzukiTransitionCoreXiCopyReflectedCoordinate N ij rho r j)) := by
  change Tendsto
    (fun z => suzukiTransitionCoreXiReflectedResidueGauge N ij rho z r /
      (xiSupportMultiplicity rho : ℂ)) _ _
  rw [suzukiTransitionCoreXiCopyReflectedCoordinate_eq]
  have h := (tendsto_suzukiTransitionCoreXiReflectedResidueGauge
    N ij rho r).div_const (xiSupportMultiplicity rho : ℂ)
  convert h using 1
  rw [inverseTiltedXiMultiplicity_eq_xiSupportMultiplicity]
  have hm : (xiSupportMultiplicity rho : ℂ) ≠ 0 := by
    exact_mod_cast (xiSupportMultiplicity_pos rho).ne'
  field_simp [hm]

theorem tendsto_suzukiTransitionCoreXiForwardCopySourceCoordinate
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    Tendsto
      (fun z => suzukiTransitionCoreXiForwardCopySourceCoordinate
        N ij rho z r j)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (suzukiTransitionCoreXiCopyForwardCoordinate N ij rho r j)) := by
  change Tendsto
    (fun z => suzukiTransitionCoreXiForwardResidueGauge N ij rho z r /
      (xiSupportMultiplicity rho : ℂ)) _ _
  rw [suzukiTransitionCoreXiCopyForwardCoordinate_eq]
  have h := (tendsto_suzukiTransitionCoreXiForwardResidueGauge
    N ij rho r).div_const (xiSupportMultiplicity rho : ℂ)
  convert h using 1
  rw [inverseTiltedXiMultiplicity_eq_xiSupportMultiplicity]
  have hm : (xiSupportMultiplicity rho : ℂ) ≠ 0 := by
    exact_mod_cast (xiSupportMultiplicity_pos rho).ne'
  field_simp [hm]

def suzukiTransitionCoreXiCopySourceEnvironmentBlock
    (N : ℕ) (ij : ℕ × ℕ) (rho tau : XiDivisorSupport)
    (z w : ℂ) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho))
    (k : Fin (xiSupportMultiplicity tau)) : Matrix (Fin 2) (Fin 2) ℂ :=
  routePJuliaEnvironmentBilinearBlock
    (suzukiTransitionCoreXiReflectedCopySourceCoordinate N ij rho z r j)
    (suzukiTransitionCoreXiForwardCopySourceCoordinate N ij tau w r k)

theorem tendsto_suzukiTransitionCoreXiCopySourceEnvironmentBlock_right
    (N : ℕ) (ij : ℕ × ℕ) (rho tau : XiDivisorSupport)
    (z : ℂ) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho))
    (k : Fin (xiSupportMultiplicity tau)) :
    Tendsto
      (fun w => suzukiTransitionCoreXiCopySourceEnvironmentBlock
        N ij rho tau z w r j k)
      (nhdsWithin (criticalMellinXiPole tau) ({criticalMellinXiPole tau}ᶜ))
      (nhds (routePJuliaEnvironmentBilinearBlock
        (suzukiTransitionCoreXiReflectedCopySourceCoordinate N ij rho z r j)
        (suzukiTransitionCoreXiCopyForwardCoordinate N ij tau r k))) := by
  exact tendsto_routePJuliaEnvironmentBilinearBlock tendsto_const_nhds
    (tendsto_suzukiTransitionCoreXiForwardCopySourceCoordinate
      N ij tau r k)

theorem tendsto_suzukiTransitionCoreXiCopySourceEnvironmentBlock_iterated
    (N : ℕ) (ij : ℕ × ℕ) (rho tau : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho))
    (k : Fin (xiSupportMultiplicity tau)) :
    Tendsto
      (fun z => routePJuliaEnvironmentBilinearBlock
        (suzukiTransitionCoreXiReflectedCopySourceCoordinate N ij rho z r j)
        (suzukiTransitionCoreXiCopyForwardCoordinate N ij tau r k))
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (routePJuliaEnvironmentBilinearBlock
        (suzukiTransitionCoreXiCopyReflectedCoordinate N ij rho r j)
        (suzukiTransitionCoreXiCopyForwardCoordinate N ij tau r k))) := by
  exact tendsto_routePJuliaEnvironmentBilinearBlock
    (tendsto_suzukiTransitionCoreXiReflectedCopySourceCoordinate
      N ij rho r j) tendsto_const_nhds

def suzukiTransitionCoreXiCopyEnvironmentBlock
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) : Matrix (Fin 2) (Fin 2) ℂ :=
  routePJuliaEnvironmentBilinearBlock
    (suzukiTransitionCoreXiCopyReflectedCoordinate N ij rho r j)
    (suzukiTransitionCoreXiCopyForwardCoordinate N ij rho r j)

theorem suzukiTransitionCoreXiCopyEnvironmentBlock_eq_hermitian
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    suzukiTransitionCoreXiCopyEnvironmentBlock N ij rho r j =
      routePJuliaEnvironmentHermitianBlock
        (suzukiTransitionCoreStokesAmplitude N ij *
          routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  rw [suzukiTransitionCoreXiCopyEnvironmentBlock,
    suzukiTransitionCoreXiCopyReflectedCoordinate_eq,
    suzukiTransitionCoreXiCopyForwardCoordinate_eq,
    routePJuliaEnvironmentHermitianBlock,
    xiWardCubicReflectedConormalMateFeature_eq_star]
  congr 1
  simp [suzukiTransitionCoreStokesAmplitude]

theorem suzukiTransitionCoreXiCopyEnvironmentBlock_posSemidef
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    (suzukiTransitionCoreXiCopyEnvironmentBlock N ij rho r j).PosSemidef := by
  rw [suzukiTransitionCoreXiCopyEnvironmentBlock_eq_hermitian]
  exact routePJuliaEnvironmentHermitianBlock_posSemidef _

theorem suzukiTransitionCoreXiCopyEnvironmentBlock_short_eq_zero
    (N : ℕ) (ij : ℕ × ℕ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    let B := suzukiTransitionCoreXiCopyEnvironmentBlock N ij rho r j
    B 0 0 - B 0 1 * (B 1 1)⁻¹ * B 1 0 = 0 := by
  simp [suzukiTransitionCoreXiCopyEnvironmentBlock,
    routePJuliaEnvironmentBilinearBlock]

theorem normSq_suzukiTransitionCoreStokesAmplitude
    {N : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ suzukiTransitionCorePairSet N) :
    Complex.normSq (suzukiTransitionCoreStokesAmplitude N ij) =
      suzukiTransitionCoreCartanCell N ij := by
  rw [suzukiTransitionCoreStokesAmplitude, Complex.normSq_ofReal]
  simpa [pow_two] using
    Real.sq_sqrt (suzukiTransitionCoreCartanCell_nonneg hij)

theorem suzukiTransitionCoreXiCopyForwardCoordinate_energy
    {N : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ suzukiTransitionCorePairSet N)
    (rho : XiDivisorSupport) (r : ℝ) :
    ∑ j, Complex.normSq
        (suzukiTransitionCoreXiCopyForwardCoordinate N ij rho r j) =
      (xiSupportMultiplicity rho : ℝ) *
        suzukiTransitionCoreCartanCell N ij *
          Complex.normSq (routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  change (∑ j, Complex.normSq
    (routePXiConormalMultiplicitySplit rho
      ((xiSupportMultiplicity rho : ℂ) *
        (suzukiTransitionCoreStokesAmplitude N ij *
          routePXiBaseConormalResidueFeature (rho : ℂ) r)) j)) = _
  rw [routePXiConormalMultiplicitySplit_raw_energy, Complex.normSq_mul,
    normSq_suzukiTransitionCoreStokesAmplitude hij]
  ring

def suzukiTransitionCoreXiFibreCornerEnergy
    (N : ℕ) (rho : XiDivisorSupport) (r : ℝ) : ℝ :=
  ∑ ij ∈ suzukiTransitionCorePairSet N,
    ∑ j, Complex.normSq
      (suzukiTransitionCoreXiCopyForwardCoordinate N ij rho r j)

theorem two_mul_suzukiTransitionCoreXiFibreCornerEnergy_eq
    (N : ℕ) (rho : XiDivisorSupport) (r : ℝ) :
    2 * suzukiTransitionCoreXiFibreCornerEnergy N rho r =
      (xiSupportMultiplicity rho : ℝ) *
        suzukiNaturalApertureTransitionCoreCauchyEnergy N *
          Complex.normSq (routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  classical
  rw [suzukiTransitionCoreXiFibreCornerEnergy]
  calc
    2 * ∑ ij ∈ suzukiTransitionCorePairSet N,
        ∑ j, Complex.normSq
          (suzukiTransitionCoreXiCopyForwardCoordinate N ij rho r j) =
      2 * ∑ ij ∈ suzukiTransitionCorePairSet N,
        ((xiSupportMultiplicity rho : ℝ) *
          suzukiTransitionCoreCartanCell N ij *
            Complex.normSq (routePXiBaseConormalResidueFeature (rho : ℂ) r)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      exact suzukiTransitionCoreXiCopyForwardCoordinate_energy hij rho r
    _ = (xiSupportMultiplicity rho : ℝ) *
        (2 * suzukiTransitionCoreStokesLinearMass N) *
          Complex.normSq (routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
      rw [suzukiTransitionCoreStokesLinearMass]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = _ := by
      rw [suzukiTransitionCoreStokesLinearMass_two_mul_eq]

end

end GaloisForLFunctions.RHTower

