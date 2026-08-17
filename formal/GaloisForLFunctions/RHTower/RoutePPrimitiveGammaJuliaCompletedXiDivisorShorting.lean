import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaWardPrecompressionShorting
import GaloisForLFunctions.RHTower.FrankensteinKreinCCMRoutePQuadraticSourceBridge
import GaloisForLFunctions.RHTower.RoutePCompletedXiConormalMultiplicitySplit
import GaloisForLFunctions.RHTower.XiWardCubicKreinOppositeRadialPairIncidence

/-!
# Gamma--Julia environment short descent to the completed Xi divisor

P-G206 constructs a literal nonlocal Gamma--Julia coupling `kappa` before two-prime compression
and proves that its resolved environment block is rank one with Schur short zero. A target-side
rank-one wrapper around a Xi residue would not transport that construction. This module instead
puts the same `kappa` into both legs of the already source-defined completed Gamma/polar quadratic
current, gauges the two pole variables separately, and takes the divisor residues only afterward.

The universal block `B(a,b)=[[ab,a],[b,1]]` leaves the environment pivot unscaled. Its upper-left
source entry is exactly the two-sided pole gauge of the completed quadratic current, multiplied by
`kappa^2`. Iterated residues retain the complete coefficient and analytic-multiplicity product.
Canonical leg-by-leg multiplicity splitting is then performed before the limits; every actual
divisor copy receives one exact Julia-weighted conormal coordinate. On a common support the
reflection law makes both raw and split landings Hermitian positive rank-one blocks. Their short is
still zero, their codiagonals recover the raw residue legs, and split corner energy is linear in
multiplicity.

This is unconditional and closes the requested transport. It is not an RH proof: a nonzero Xi
coordinate can coexist with zero short, so an independent completed-source budget or order law is
still required to annihilate an off-line landing.
-/

open Complex Filter Matrix Set Topology
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Universal two-leg environment block that retains pivot `1` during separate residue gauges. -/
def routePJuliaEnvironmentBilinearBlock (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a * b, a; b, 1]

/-- Scalar Schur short of the source corner through the retained environment pivot. -/
def routePJuliaEnvironmentBilinearShort (a b : ℂ) : ℂ :=
  let B := routePJuliaEnvironmentBilinearBlock a b
  B 0 0 - B 0 1 * (B 1 1)⁻¹ * B 1 0

@[simp] theorem routePJuliaEnvironmentBilinearShort_eq_zero (a b : ℂ) :
    routePJuliaEnvironmentBilinearShort a b = 0 := by
  simp [routePJuliaEnvironmentBilinearShort, routePJuliaEnvironmentBilinearBlock]

theorem routePJuliaEnvironmentBilinearBlock_det (a b : ℂ) :
    (routePJuliaEnvironmentBilinearBlock a b).det = 0 := by
  rw [Matrix.det_fin_two]
  simp [routePJuliaEnvironmentBilinearBlock]

theorem tendsto_routePJuliaEnvironmentBilinearBlock
    {α : Type*} {l : Filter α} {a b : α → ℂ} {a0 b0 : ℂ}
    (ha : Tendsto a l (nhds a0)) (hb : Tendsto b l (nhds b0)) :
    Tendsto (fun t => routePJuliaEnvironmentBilinearBlock (a t) (b t)) l
      (nhds (routePJuliaEnvironmentBilinearBlock a0 b0)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  fin_cases i <;> fin_cases j
  · simpa [routePJuliaEnvironmentBilinearBlock] using ha.mul hb
  · simpa [routePJuliaEnvironmentBilinearBlock] using ha
  · simpa [routePJuliaEnvironmentBilinearBlock] using hb
  · simpa [routePJuliaEnvironmentBilinearBlock] using
      (tendsto_const_nhds : Tendsto (fun _ : α => (1 : ℂ)) l (nhds 1))

/-- Same block on a reflected pair; it is the Gram of the row `[c,1]`. -/
def routePJuliaEnvironmentHermitianBlock (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  routePJuliaEnvironmentBilinearBlock (star c) c

theorem routePJuliaEnvironmentHermitianBlock_posSemidef (c : ℂ) :
    (routePJuliaEnvironmentHermitianBlock c).PosSemidef := by
  let R : Matrix (Fin 1) (Fin 2) ℂ := !![c, 1]
  have hGram : routePJuliaEnvironmentHermitianBlock c = Rᴴ * R := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [routePJuliaEnvironmentHermitianBlock,
        routePJuliaEnvironmentBilinearBlock, R, Matrix.mul_apply]
  rw [hGram]
  exact Matrix.posSemidef_conjTranspose_mul_self R

/-- Coefficient extension of P-G206's literal real precompression block. -/
def routePTwoPrimeJuliaWardPrecompressionComplexBlock (x u : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (routePTwoPrimeJuliaWardPrecompressionBlock x u i j : ℂ)

theorem routePTwoPrimeJuliaWardPrecompressionComplexBlock_eq_bilinear
    (x u : ℝ) :
    routePTwoPrimeJuliaWardPrecompressionComplexBlock x u =
      routePJuliaEnvironmentBilinearBlock
        (routePTwoPrimeJuliaWardNonlocalCoupling x u : ℂ)
        (routePTwoPrimeJuliaWardNonlocalCoupling x u : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (routePTwoPrimeJuliaWardCompressedEnergy x u : ℂ) =
      (routePTwoPrimeJuliaWardNonlocalCoupling x u : ℂ) *
        (routePTwoPrimeJuliaWardNonlocalCoupling x u : ℂ)
    have h := congrArg (fun t : ℝ => (t : ℂ))
      (routePTwoPrimeJuliaWardNonlocalCoupling_sq x u).symm
    simpa [pow_two] using h
  · simp [routePTwoPrimeJuliaWardPrecompressionComplexBlock,
      routePTwoPrimeJuliaWardPrecompressionBlock,
      routePJuliaEnvironmentBilinearBlock]
  · simp [routePTwoPrimeJuliaWardPrecompressionComplexBlock,
      routePTwoPrimeJuliaWardPrecompressionBlock,
      routePJuliaEnvironmentBilinearBlock]
  · simp [routePTwoPrimeJuliaWardPrecompressionComplexBlock,
      routePTwoPrimeJuliaWardPrecompressionBlock,
      routePJuliaEnvironmentBilinearBlock]

/-- Exact P-G206 Julia exterior coupling, retained as a complex source coefficient. -/
def routePPrimitiveGammaJuliaXiDescentCoefficient (x u : ℝ) : ℂ :=
  (routePTwoPrimeJuliaWardNonlocalCoupling x u : ℂ)

def routePPrimitiveGammaJuliaXiReflectedResidueGauge
    (x u : ℝ) (rho : XiDivisorSupport) (z : ℂ) (r : ℝ) : ℂ :=
  routePPrimitiveGammaJuliaXiDescentCoefficient x u *
    ((z - criticalMellinXiPole rho) *
      frankensteinKreinCCMRoutePReflectedSourceColumn z r)

def routePPrimitiveGammaJuliaXiForwardResidueGauge
    (x u : ℝ) (tau : XiDivisorSupport) (w : ℂ) (r : ℝ) : ℂ :=
  routePPrimitiveGammaJuliaXiDescentCoefficient x u *
    ((w - criticalMellinXiPole tau) *
      frankensteinKreinCCMRoutePForwardSourceColumn w r)

/-- Pre-divisor completed source block with a separate pole gauge on each source leg. -/
def routePPrimitiveGammaJuliaCompletedSourceEnvironmentBlock
    (x u : ℝ) (rho tau : XiDivisorSupport) (z w : ℂ) (r : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  routePJuliaEnvironmentBilinearBlock
    (routePPrimitiveGammaJuliaXiReflectedResidueGauge x u rho z r)
    (routePPrimitiveGammaJuliaXiForwardResidueGauge x u tau w r)

@[simp] theorem routePPrimitiveGammaJuliaCompletedSourceEnvironmentBlock_short_eq_zero
    (x u : ℝ) (rho tau : XiDivisorSupport) (z w : ℂ) (r : ℝ) :
    routePJuliaEnvironmentBilinearShort
      (routePPrimitiveGammaJuliaXiReflectedResidueGauge x u rho z r)
      (routePPrimitiveGammaJuliaXiForwardResidueGauge x u tau w r) = 0 := by
  exact routePJuliaEnvironmentBilinearShort_eq_zero _ _

theorem routePPrimitiveGammaJuliaCompletedSourceEnvironmentBlock_sourceCorner
    (x u : ℝ) (rho tau : XiDivisorSupport) (z w : ℂ) (r : ℝ) :
    routePPrimitiveGammaJuliaCompletedSourceEnvironmentBlock x u rho tau z w r 0 0 =
      (z - criticalMellinXiPole rho) * (w - criticalMellinXiPole tau) *
        routePPrimitiveGammaJuliaXiDescentCoefficient x u ^ 2 *
          frankensteinKreinCCMRoutePQuadraticSourceCurrent z w r := by
  change
    (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
        ((z - criticalMellinXiPole rho) *
          frankensteinKreinCCMRoutePReflectedSourceColumn z r)) *
      (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
        ((w - criticalMellinXiPole tau) *
          frankensteinKreinCCMRoutePForwardSourceColumn w r)) = _
  rw [frankensteinKreinCCMRoutePQuadraticSourceCurrent]
  ring

theorem tendsto_routePPrimitiveGammaJuliaXiReflectedResidueGauge
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun z => routePPrimitiveGammaJuliaXiReflectedResidueGauge x u rho z r)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
        ((inverseTiltedXiMultiplicity rho : ℂ) *
          xiWardCubicReflectedConormalMateFeature (rho : ℂ) r))) := by
  simpa [routePPrimitiveGammaJuliaXiReflectedResidueGauge] using
    (frankensteinKreinCCMRoutePReflectedSourceColumn_residue rho r).const_mul
      (routePPrimitiveGammaJuliaXiDescentCoefficient x u)

theorem tendsto_routePPrimitiveGammaJuliaXiForwardResidueGauge
    (x u : ℝ) (tau : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun w => routePPrimitiveGammaJuliaXiForwardResidueGauge x u tau w r)
      (nhdsWithin (criticalMellinXiPole tau) ({criticalMellinXiPole tau}ᶜ))
      (nhds (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
        ((inverseTiltedXiMultiplicity tau : ℂ) *
          routePXiBaseConormalResidueFeature (tau : ℂ) r))) := by
  simpa [routePPrimitiveGammaJuliaXiForwardResidueGauge] using
    (frankensteinKreinCCMRoutePForwardSourceColumn_residue tau r).const_mul
      (routePPrimitiveGammaJuliaXiDescentCoefficient x u)

/-- Full-multiplicity iterated-residue landing of the completed source block. -/
def routePPrimitiveGammaJuliaXiRawEnvironmentBlock
    (x u : ℝ) (rho tau : XiDivisorSupport) (r : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  routePJuliaEnvironmentBilinearBlock
    (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
      ((inverseTiltedXiMultiplicity rho : ℂ) *
        xiWardCubicReflectedConormalMateFeature (rho : ℂ) r))
    (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
      ((inverseTiltedXiMultiplicity tau : ℂ) *
        routePXiBaseConormalResidueFeature (tau : ℂ) r))

theorem tendsto_routePPrimitiveGammaJuliaCompletedSourceEnvironmentBlock_right
    (x u : ℝ) (rho tau : XiDivisorSupport) (z : ℂ) (r : ℝ) :
    Tendsto
      (fun w => routePPrimitiveGammaJuliaCompletedSourceEnvironmentBlock
        x u rho tau z w r)
      (nhdsWithin (criticalMellinXiPole tau) ({criticalMellinXiPole tau}ᶜ))
      (nhds (routePJuliaEnvironmentBilinearBlock
        (routePPrimitiveGammaJuliaXiReflectedResidueGauge x u rho z r)
        (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
          ((inverseTiltedXiMultiplicity tau : ℂ) *
            routePXiBaseConormalResidueFeature (tau : ℂ) r)))) := by
  exact tendsto_routePJuliaEnvironmentBilinearBlock tendsto_const_nhds
    (tendsto_routePPrimitiveGammaJuliaXiForwardResidueGauge x u tau r)

theorem tendsto_routePPrimitiveGammaJuliaCompletedSourceEnvironmentBlock_iterated
    (x u : ℝ) (rho tau : XiDivisorSupport) (r : ℝ) :
    Tendsto
      (fun z => routePJuliaEnvironmentBilinearBlock
        (routePPrimitiveGammaJuliaXiReflectedResidueGauge x u rho z r)
        (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
          ((inverseTiltedXiMultiplicity tau : ℂ) *
            routePXiBaseConormalResidueFeature (tau : ℂ) r)))
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (routePPrimitiveGammaJuliaXiRawEnvironmentBlock x u rho tau r)) := by
  exact tendsto_routePJuliaEnvironmentBilinearBlock
    (tendsto_routePPrimitiveGammaJuliaXiReflectedResidueGauge x u rho r)
    tendsto_const_nhds

def routePPrimitiveGammaJuliaXiCopyReflectedCoordinate
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) : ℂ :=
  routePXiConormalMultiplicitySplit rho
    ((xiSupportMultiplicity rho : ℂ) *
      (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
        xiWardCubicReflectedConormalMateFeature (rho : ℂ) r)) j

def routePPrimitiveGammaJuliaXiCopyForwardCoordinate
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) : ℂ :=
  routePXiConormalMultiplicitySplit rho
    ((xiSupportMultiplicity rho : ℂ) *
      (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
        routePXiBaseConormalResidueFeature (rho : ℂ) r)) j

@[simp] theorem routePPrimitiveGammaJuliaXiCopyReflectedCoordinate_eq
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    routePPrimitiveGammaJuliaXiCopyReflectedCoordinate x u rho r j =
      routePPrimitiveGammaJuliaXiDescentCoefficient x u *
        xiWardCubicReflectedConormalMateFeature (rho : ℂ) r := by
  exact routePXiConormalMultiplicitySplit_raw_apply rho _ j

@[simp] theorem routePPrimitiveGammaJuliaXiCopyForwardCoordinate_eq
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    routePPrimitiveGammaJuliaXiCopyForwardCoordinate x u rho r j =
      routePPrimitiveGammaJuliaXiDescentCoefficient x u *
        routePXiBaseConormalResidueFeature (rho : ℂ) r := by
  exact routePXiConormalMultiplicitySplit_raw_apply rho _ j

/-- One coefficient-faithful block on one analytic-multiplicity copy of a Xi support. -/
def routePPrimitiveGammaJuliaXiCopyEnvironmentBlock
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) : Matrix (Fin 2) (Fin 2) ℂ :=
  routePJuliaEnvironmentBilinearBlock
    (routePPrimitiveGammaJuliaXiCopyReflectedCoordinate x u rho r j)
    (routePPrimitiveGammaJuliaXiCopyForwardCoordinate x u rho r j)

theorem routePPrimitiveGammaJuliaXiCopyEnvironmentBlock_eq_hermitian
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    routePPrimitiveGammaJuliaXiCopyEnvironmentBlock x u rho r j =
      routePJuliaEnvironmentHermitianBlock
        (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
          routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  rw [routePPrimitiveGammaJuliaXiCopyEnvironmentBlock,
    routePPrimitiveGammaJuliaXiCopyReflectedCoordinate_eq,
    routePPrimitiveGammaJuliaXiCopyForwardCoordinate_eq,
    routePJuliaEnvironmentHermitianBlock,
    xiWardCubicReflectedConormalMateFeature_eq_star]
  congr 1
  simp [routePPrimitiveGammaJuliaXiDescentCoefficient]

theorem routePPrimitiveGammaJuliaXiCopyEnvironmentBlock_posSemidef
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    (routePPrimitiveGammaJuliaXiCopyEnvironmentBlock x u rho r j).PosSemidef := by
  rw [routePPrimitiveGammaJuliaXiCopyEnvironmentBlock_eq_hermitian]
  exact routePJuliaEnvironmentHermitianBlock_posSemidef _

theorem routePPrimitiveGammaJuliaXiCopyEnvironmentBlock_short_eq_zero
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    let B := routePPrimitiveGammaJuliaXiCopyEnvironmentBlock x u rho r j
    B 0 0 - B 0 1 * (B 1 1)⁻¹ * B 1 0 = 0 := by
  simp [routePPrimitiveGammaJuliaXiCopyEnvironmentBlock,
    routePJuliaEnvironmentBilinearBlock]

theorem routePPrimitiveGammaJuliaXiCopyForwardCoordinate_sum
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ) :
    ∑ j, routePPrimitiveGammaJuliaXiCopyForwardCoordinate x u rho r j =
      (xiSupportMultiplicity rho : ℂ) *
        (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
          routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  exact routePXiConormalMultiplicitySplit_sum rho _

theorem routePPrimitiveGammaJuliaXiCopyCornerEnergy_sum
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ) :
    ∑ j, Complex.normSq
      (routePPrimitiveGammaJuliaXiCopyForwardCoordinate x u rho r j) =
      (xiSupportMultiplicity rho : ℝ) * Complex.normSq
        (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
          routePXiBaseConormalResidueFeature (rho : ℂ) r) := by
  simpa [routePPrimitiveGammaJuliaXiCopyForwardCoordinate] using
    routePXiConormalMultiplicitySplit_raw_energy rho
      (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
        routePXiBaseConormalResidueFeature (rho : ℂ) r)

def routePPrimitiveGammaJuliaXiReflectedCopySourceCoordinate
    (x u : ℝ) (rho : XiDivisorSupport) (z : ℂ) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) : ℂ :=
  routePXiConormalMultiplicitySplit rho
    (routePPrimitiveGammaJuliaXiReflectedResidueGauge x u rho z r) j

def routePPrimitiveGammaJuliaXiForwardCopySourceCoordinate
    (x u : ℝ) (rho : XiDivisorSupport) (w : ℂ) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) : ℂ :=
  routePXiConormalMultiplicitySplit rho
    (routePPrimitiveGammaJuliaXiForwardResidueGauge x u rho w r) j

theorem tendsto_routePPrimitiveGammaJuliaXiReflectedCopySourceCoordinate
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    Tendsto
      (fun z => routePPrimitiveGammaJuliaXiReflectedCopySourceCoordinate
        x u rho z r j)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (routePPrimitiveGammaJuliaXiCopyReflectedCoordinate x u rho r j)) := by
  change Tendsto
    (fun z => routePPrimitiveGammaJuliaXiReflectedResidueGauge x u rho z r /
      (xiSupportMultiplicity rho : ℂ)) _ _
  rw [routePPrimitiveGammaJuliaXiCopyReflectedCoordinate_eq]
  have h := (tendsto_routePPrimitiveGammaJuliaXiReflectedResidueGauge
    x u rho r).div_const (xiSupportMultiplicity rho : ℂ)
  convert h using 1
  rw [inverseTiltedXiMultiplicity_eq_xiSupportMultiplicity]
  have hm : (xiSupportMultiplicity rho : ℂ) ≠ 0 := by
    exact_mod_cast (xiSupportMultiplicity_pos rho).ne'
  field_simp [hm]

theorem tendsto_routePPrimitiveGammaJuliaXiForwardCopySourceCoordinate
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho)) :
    Tendsto
      (fun w => routePPrimitiveGammaJuliaXiForwardCopySourceCoordinate
        x u rho w r j)
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (routePPrimitiveGammaJuliaXiCopyForwardCoordinate x u rho r j)) := by
  change Tendsto
    (fun w => routePPrimitiveGammaJuliaXiForwardResidueGauge x u rho w r /
      (xiSupportMultiplicity rho : ℂ)) _ _
  rw [routePPrimitiveGammaJuliaXiCopyForwardCoordinate_eq]
  have h := (tendsto_routePPrimitiveGammaJuliaXiForwardResidueGauge
    x u rho r).div_const (xiSupportMultiplicity rho : ℂ)
  convert h using 1
  rw [inverseTiltedXiMultiplicity_eq_xiSupportMultiplicity]
  have hm : (xiSupportMultiplicity rho : ℂ) ≠ 0 := by
    exact_mod_cast (xiSupportMultiplicity_pos rho).ne'
  field_simp [hm]

/-- Multiplicity-split block formed on the completed source before either divisor limit. -/
def routePPrimitiveGammaJuliaXiCopySourceEnvironmentBlock
    (x u : ℝ) (rho tau : XiDivisorSupport) (z w : ℂ) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho))
    (k : Fin (xiSupportMultiplicity tau)) : Matrix (Fin 2) (Fin 2) ℂ :=
  routePJuliaEnvironmentBilinearBlock
    (routePPrimitiveGammaJuliaXiReflectedCopySourceCoordinate x u rho z r j)
    (routePPrimitiveGammaJuliaXiForwardCopySourceCoordinate x u tau w r k)

theorem tendsto_routePPrimitiveGammaJuliaXiCopySourceEnvironmentBlock_right
    (x u : ℝ) (rho tau : XiDivisorSupport) (z : ℂ) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho))
    (k : Fin (xiSupportMultiplicity tau)) :
    Tendsto
      (fun w => routePPrimitiveGammaJuliaXiCopySourceEnvironmentBlock
        x u rho tau z w r j k)
      (nhdsWithin (criticalMellinXiPole tau) ({criticalMellinXiPole tau}ᶜ))
      (nhds (routePJuliaEnvironmentBilinearBlock
        (routePPrimitiveGammaJuliaXiReflectedCopySourceCoordinate x u rho z r j)
        (routePPrimitiveGammaJuliaXiCopyForwardCoordinate x u tau r k))) := by
  exact tendsto_routePJuliaEnvironmentBilinearBlock tendsto_const_nhds
    (tendsto_routePPrimitiveGammaJuliaXiForwardCopySourceCoordinate x u tau r k)

theorem tendsto_routePPrimitiveGammaJuliaXiCopySourceEnvironmentBlock_iterated
    (x u : ℝ) (rho tau : XiDivisorSupport) (r : ℝ)
    (j : Fin (xiSupportMultiplicity rho))
    (k : Fin (xiSupportMultiplicity tau)) :
    Tendsto
      (fun z => routePJuliaEnvironmentBilinearBlock
        (routePPrimitiveGammaJuliaXiReflectedCopySourceCoordinate x u rho z r j)
        (routePPrimitiveGammaJuliaXiCopyForwardCoordinate x u tau r k))
      (nhdsWithin (criticalMellinXiPole rho) ({criticalMellinXiPole rho}ᶜ))
      (nhds (routePJuliaEnvironmentBilinearBlock
        (routePPrimitiveGammaJuliaXiCopyReflectedCoordinate x u rho r j)
        (routePPrimitiveGammaJuliaXiCopyForwardCoordinate x u tau r k))) := by
  exact tendsto_routePJuliaEnvironmentBilinearBlock
    (tendsto_routePPrimitiveGammaJuliaXiReflectedCopySourceCoordinate x u rho r j)
    tendsto_const_nhds

theorem routePPrimitiveGammaJuliaXiRawEnvironmentBlock_eq_hermitian
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ) :
    routePPrimitiveGammaJuliaXiRawEnvironmentBlock x u rho rho r =
      routePJuliaEnvironmentHermitianBlock
        ((inverseTiltedXiMultiplicity rho : ℂ) *
          (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
            routePXiBaseConormalResidueFeature (rho : ℂ) r)) := by
  rw [routePPrimitiveGammaJuliaXiRawEnvironmentBlock,
    routePJuliaEnvironmentHermitianBlock,
    xiWardCubicReflectedConormalMateFeature_eq_star]
  congr 1
  · simp [routePPrimitiveGammaJuliaXiDescentCoefficient]
    ring
  · ring

theorem routePPrimitiveGammaJuliaXiRawEnvironmentBlock_posSemidef
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ) :
    (routePPrimitiveGammaJuliaXiRawEnvironmentBlock x u rho rho r).PosSemidef := by
  rw [routePPrimitiveGammaJuliaXiRawEnvironmentBlock_eq_hermitian]
  exact routePJuliaEnvironmentHermitianBlock_posSemidef _

/-- Even the full-multiplicity raw divisor landing retains the source-side zero short. -/
theorem routePPrimitiveGammaJuliaXiRawEnvironmentBlock_short_eq_zero
    (x u : ℝ) (rho tau : XiDivisorSupport) (r : ℝ) :
    let B := routePPrimitiveGammaJuliaXiRawEnvironmentBlock x u rho tau r
    B 0 0 - B 0 1 * (B 1 1)⁻¹ * B 1 0 = 0 := by
  simp [routePPrimitiveGammaJuliaXiRawEnvironmentBlock,
    routePJuliaEnvironmentBilinearBlock]

theorem routePPrimitiveGammaJuliaXiCopyReflectedCoordinate_sum
    (x u : ℝ) (rho : XiDivisorSupport) (r : ℝ) :
    ∑ j, routePPrimitiveGammaJuliaXiCopyReflectedCoordinate x u rho r j =
      (xiSupportMultiplicity rho : ℂ) *
        (routePPrimitiveGammaJuliaXiDescentCoefficient x u *
          xiWardCubicReflectedConormalMateFeature (rho : ℂ) r) := by
  exact routePXiConormalMultiplicitySplit_sum rho _

/-- The index used by the split block has exactly the cardinality of the actual Xi support fibre. -/
theorem routePPrimitiveGammaJuliaXiActualSupportFiber_card
    (q : XiRightZeroCopy) :
    Fintype.card (XiRightSupportFiber q) = xiSupportMultiplicity q.1.1 := by
  rw [card_xiRightSupportFiber, xiRightMultiplicity,
    xiSupportMultiplicity_eq_analyticOrderAt_toNat]

/-- Hostile boundary: zero short does not annihilate its Xi coordinate when the Julia coupling
and radial coordinate are nonzero. -/
theorem routePPrimitiveGammaJuliaXiCopyForwardCoordinate_ne_zero
    {x u r : ℝ} (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho))
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0)
    (hr : r ≠ 0) :
    routePPrimitiveGammaJuliaXiCopyForwardCoordinate x u rho r j ≠ 0 := by
  rw [routePPrimitiveGammaJuliaXiCopyForwardCoordinate_eq]
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr hkappa
  · rw [routePXiBaseConormalResidueFeature]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) (Complex.exp_ne_zero _)

end

end RHTower
