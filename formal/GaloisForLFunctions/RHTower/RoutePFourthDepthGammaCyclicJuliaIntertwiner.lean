import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolJuliaKreinMatrixCompletion
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPoleUnitPrimeCellGammaPythagoreanBudget

/-!
# Route P fourth-depth Gamma-cyclic Julia intertwiner

P-G105C reduced full finite matrix completion to provenance of one universal Julia channel.  The
existing prime-cell Gamma budget has a source-defined Cayley coordinate, but at a general thermal
ratio that coordinate varies with the prime cell.  This file solves the source gauge exactly.

For running prime odds `a`, set

```text
T = (8 + a) / 7.
```

Then `T > 1`, the co-Poisson Cayley coordinate is exactly `1 / 8`, the boundary child has energy
`a / 64`, and the Gamma cyclic complement has energy `63 a / 64`.  More strongly, the square of
the actual archimedean cyclic characteristic at rapidity `artanh(1 / 8)` is exactly the Julia
defect amplitude `sqrt 63 / 8`.  Hence the Gamma-defined defect operator and co-graph pivots are
definitionally typed on the existing carriers and proved equal to the P-G105/P-G105B/P-G105C
Julia channels.

This closes Gamma-cyclic coefficient and operator provenance.  It does not yet identify the
negative coordinate with the oriented Stokes incidence, prove compatibility of this cellwise
thermal gauge with cofinal sewing, or land the completed determinant in the Xi divisor.
-/

open Complex MeasureTheory Set
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Literal running odds of a prime at source displacement `sigma`. -/
def routePPrimitiveFourthDepthGammaRunningOdds
    (p : Nat.Primes) (sigma : ℝ) : ℝ :=
  HedenmalmThetaSource.thermalBernoulliRunningOdds
    ((p : ℝ) ^ (-1 : ℝ)) (sigma * Real.log (p : ℝ))

/-- Unique positive thermal ratio forcing the co-Poisson Cayley coordinate to `1 / 8`. -/
def routePPrimitiveFourthDepthGammaThermalRatio
    (p : Nat.Primes) (sigma : ℝ) : ℝ :=
  (8 + routePPrimitiveFourthDepthGammaRunningOdds p sigma) / 7

theorem routePPrimitiveFourthDepthGammaRunningOdds_pos
    (p : Nat.Primes) (sigma : ℝ) :
    0 < routePPrimitiveFourthDepthGammaRunningOdds p sigma := by
  apply HedenmalmThetaSource.thermalBernoulliRunningOdds_pos
  exact Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _

/-- The forced thermal gauge is always a genuine finite source cell. -/
theorem routePPrimitiveFourthDepthGammaThermalRatio_one_lt
    (p : Nat.Primes) (sigma : ℝ) :
    1 < routePPrimitiveFourthDepthGammaThermalRatio p sigma := by
  have ha := routePPrimitiveFourthDepthGammaRunningOdds_pos p sigma
  rw [routePPrimitiveFourthDepthGammaThermalRatio]
  linarith

/-- Source gauge calibration: the literal prime-cell Cayley coordinate is the Route-P contraction. -/
theorem routePPrimitiveFourthDepthGammaCayley_eq_contraction
    (p : Nat.Primes) (sigma : ℝ) :
    HedenmalmThetaSource.thermalBernoulliCoPoissonCayley
        ((p : ℝ) ^ (-1 : ℝ))
        (sigma * Real.log (p : ℝ))
        (routePPrimitiveFourthDepthGammaThermalRatio p sigma) =
      routeEPCubicFourthDepthNormalizedContraction := by
  have ha := routePPrimitiveFourthDepthGammaRunningOdds_pos p sigma
  rw [HedenmalmThetaSource.thermalBernoulliCoPoissonCayley,
    ← routePPrimitiveFourthDepthGammaRunningOdds,
    routePPrimitiveFourthDepthGammaThermalRatio,
    routeEPCubicFourthDepthNormalizedContraction]
  field_simp
  ring

/-- The finite boundary-layer child has exactly fourth-depth energy `a / 64`. -/
theorem routePPrimitiveFourthDepthGammaBoundaryDefect_eq
    (p : Nat.Primes) (sigma : ℝ) :
    HedenmalmThetaSource.thermalBernoulliMidpointDefectOdds
        ((p : ℝ) ^ (-1 : ℝ))
        (HedenmalmThetaSource.thermalBernoulliBoundaryLayerEccentricity
          (sigma * Real.log (p : ℝ))
          (routePPrimitiveFourthDepthGammaThermalRatio p sigma))
        (routePPrimitiveFourthDepthGammaThermalRatio p sigma) =
      (1 / 64 : ℝ) *
        routePPrimitiveFourthDepthGammaRunningOdds p sigma := by
  rw [HedenmalmThetaSource.thermalBernoulliBoundaryLayerDefectOdds_eq_runningOdds_mul_cayley_sq
      (routePPrimitiveFourthDepthGammaThermalRatio_one_lt p sigma),
    routePPrimitiveFourthDepthGammaCayley_eq_contraction,
    routeEPCubicFourthDepthNormalizedContraction,
    routePPrimitiveFourthDepthGammaRunningOdds]
  ring

/-- The literal Gamma cyclic complement pays exactly the `63 / 64` Julia energy debt. -/
theorem routePPrimitiveFourthDepthGammaComplement_eq
    (p : Nat.Primes) (sigma : ℝ) :
    HedenmalmThetaSource.thermalBernoulliCoPoissonComplement
        ((p : ℝ) ^ (-1 : ℝ))
        (sigma * Real.log (p : ℝ))
        (routePPrimitiveFourthDepthGammaThermalRatio p sigma) =
      (63 / 64 : ℝ) *
        routePPrimitiveFourthDepthGammaRunningOdds p sigma := by
  rw [HedenmalmThetaSource.thermalBernoulliCoPoissonComplement_eq_runningOdds_mul_one_sub_cayley_sq
      (routePPrimitiveFourthDepthGammaThermalRatio_one_lt p sigma),
    routePPrimitiveFourthDepthGammaCayley_eq_contraction,
    routeEPCubicFourthDepthNormalizedContraction,
    routePPrimitiveFourthDepthGammaRunningOdds]
  ring

/-- Gamma-cyclic Hilbert amplitude at the universal fourth-depth scattering rapidity. -/
def routePPrimitiveFourthDepthGammaCyclicAmplitude : ℝ :=
  semilocalArchimedeanCharacteristic (Real.artanh (1 / 8 : ℝ)) ^ 2

theorem routePPrimitiveFourthDepthGammaCyclicAmplitude_sq :
    routePPrimitiveFourthDepthGammaCyclicAmplitude ^ 2 = 63 / 64 := by
  have h := semilocalArchimedeanCharacteristic_pow_four_add_tanh_sq
    (Real.artanh (1 / 8 : ℝ))
  rw [Real.tanh_artanh (by norm_num : (1 / 8 : ℝ) ∈ Set.Ioo (-1) 1)] at h
  rw [routePPrimitiveFourthDepthGammaCyclicAmplitude]
  nlinarith

/-- **Gamma--Julia coefficient identity.** The actual cyclic characteristic squared is the
fourth-depth Julia defect, with positive branch fixed by source positivity. -/
theorem routePPrimitiveFourthDepthGammaCyclicAmplitude_eq_juliaDefect :
    routePPrimitiveFourthDepthGammaCyclicAmplitude =
      routeEPCubicFourthDepthJuliaDefect := by
  have hsq := routePPrimitiveFourthDepthGammaCyclicAmplitude_sq
  have hdsq := routeEPCubicFourthDepthJuliaDefect_sq
  have hgamma : 0 ≤ routePPrimitiveFourthDepthGammaCyclicAmplitude := by
    exact sq_nonneg _
  have hd : 0 ≤ routeEPCubicFourthDepthJuliaDefect := Real.sqrt_nonneg _
  nlinarith

/-- Every forced prime cell evaluates the same universal Gamma cyclic complement coefficient. -/
theorem routePPrimitiveFourthDepthGammaCharacteristic_pow_four
    (p : Nat.Primes) (sigma : ℝ) :
    semilocalArchimedeanCharacteristic
        (Real.artanh
          (HedenmalmThetaSource.thermalBernoulliCoPoissonCayley
            ((p : ℝ) ^ (-1 : ℝ))
            (sigma * Real.log (p : ℝ))
            (routePPrimitiveFourthDepthGammaThermalRatio p sigma))) ^ 4 =
      63 / 64 := by
  rw [routePPrimitiveFourthDepthGammaCayley_eq_contraction,
    routeEPCubicFourthDepthNormalizedContraction]
  have h := routePPrimitiveFourthDepthGammaCyclicAmplitude_sq
  rw [routePPrimitiveFourthDepthGammaCyclicAmplitude] at h
  nlinarith

/-- Gamma-cyclic defect operator on Burnol's physical even co-Poisson carrier. -/
def routePPrimitiveFourthDepthGammaCyclicDefect :
    evenSubspace →L[ℂ] evenSubspace :=
  (routePPrimitiveFourthDepthGammaCyclicAmplitude : ℂ) • 1

/-- **Gamma--Julia operator intertwiner.** The Gamma cyclic source operator is exactly Julia defect. -/
theorem routePPrimitiveFourthDepthGammaCyclicDefect_eq_juliaDefect :
    routePPrimitiveFourthDepthGammaCyclicDefect =
      routePPrimitiveFourthDepthCoPoissonJuliaDefect := by
  ext f
  simp [routePPrimitiveFourthDepthGammaCyclicDefect,
    routePPrimitiveFourthDepthCoPoissonJuliaDefect,
    routePPrimitiveFourthDepthGammaCyclicAmplitude_eq_juliaDefect]

/-- Gamma-cyclic co-graph pivot on the physical even co-Poisson carrier. -/
def routePPrimitiveFourthDepthCoPoissonGammaCyclicKreinPivot
    (f : evenSubspace) : evenSubspace × evenSubspace :=
  let c : ℂ := routeEPCubicFourthDepthNormalizedContraction
  let gamma : ℂ := routePPrimitiveFourthDepthGammaCyclicAmplitude
  ((gamma / c ^ 2) • routePPrimitiveFourthDepthCoPoissonContraction f,
    (1 / c) • f)

/-- Gamma-cyclic co-graph is exactly P-G105B's Julia--Krein pivot. -/
theorem routePPrimitiveFourthDepthCoPoissonGammaCyclicKreinPivot_eq_juliaPivot
    (f : evenSubspace) :
    routePPrimitiveFourthDepthCoPoissonGammaCyclicKreinPivot f =
      routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f := by
  simp [routePPrimitiveFourthDepthCoPoissonGammaCyclicKreinPivot,
    routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot,
    routePPrimitiveFourthDepthGammaCyclicAmplitude_eq_juliaDefect]

/-- Gamma-cyclic co-graph on P-G186's actual half-line feature carrier. -/
def routePPrimitiveBurnolGammaCyclicKreinPivot
    (f : routePBurnolHalfLineL2) : routePPrimitiveBurnolJuliaKreinCarrier :=
  let c : ℂ := routeEPCubicFourthDepthNormalizedContraction
  let gamma : ℂ := routePPrimitiveFourthDepthGammaCyclicAmplitude
  ((gamma / c) • f, (1 / c) • f)

/-- Gamma-cyclic co-graph is exactly P-G105C's universal half-line Julia--Krein channel. -/
theorem routePPrimitiveBurnolGammaCyclicKreinPivot_eq_juliaPivot
    (f : routePBurnolHalfLineL2) :
    routePPrimitiveBurnolGammaCyclicKreinPivot f =
      routePPrimitiveBurnolJuliaKreinPivot f := by
  have hcoef :
      (routePPrimitiveFourthDepthGammaCyclicAmplitude : ℂ) /
          (routeEPCubicFourthDepthNormalizedContraction : ℂ) =
        (Real.sqrt 63 : ℂ) := by
    rw [routePPrimitiveFourthDepthGammaCyclicAmplitude_eq_juliaDefect,
      routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
    push_cast
    norm_num [routeEPCubicFourthDepthNormalizedContraction]
    ring
  rw [routePPrimitiveBurnolGammaCyclicKreinPivot,
    routePPrimitiveBurnolJuliaKreinPivot, hcoef]
  norm_num [routeEPCubicFourthDepthNormalizedContraction]

/-- Literal finite-cell Ward identity in fourth-depth coordinates. -/
theorem routePPrimitiveFourthDepthGammaCyclicWard
    (p : Nat.Primes) (sigma : ℝ) :
    eulerGammaCoPoissonPrimitiveTerm p (((1 + sigma : ℝ) : ℂ)) +
        ((1 / 64 : ℝ) *
          routePPrimitiveFourthDepthGammaRunningOdds p sigma : ℝ) +
        ((routePPrimitiveFourthDepthGammaCyclicAmplitude ^ 2 *
          routePPrimitiveFourthDepthGammaRunningOdds p sigma : ℝ) : ℂ) = 0 := by
  rw [routePPrimitiveFourthDepthGammaCyclicAmplitude_sq]
  have h := HedenmalmThetaSource.eulerGammaCoPoissonPrimitiveTerm_prime_runningOdds
    p sigma 1
  norm_num at h
  have h' : eulerGammaCoPoissonPrimitiveTerm p (((1 + sigma : ℝ) : ℂ)) =
      -(routePPrimitiveFourthDepthGammaRunningOdds p sigma : ℝ) := by
    simpa [routePPrimitiveFourthDepthGammaRunningOdds, map_add] using h
  rw [h']
  push_cast
  ring

/-- P-G105D capstone: source gauge, Gamma coefficient/operator provenance, both carrier pivots,
and the exact prime-cell Ward identity, all without premises. -/
theorem routePPrimitiveFourthDepth_GammaCyclicJuliaIntertwiner
    (p : Nat.Primes) (sigma : ℝ) (f : evenSubspace)
    (g : routePBurnolHalfLineL2) :
    1 < routePPrimitiveFourthDepthGammaThermalRatio p sigma ∧
      HedenmalmThetaSource.thermalBernoulliCoPoissonCayley
          ((p : ℝ) ^ (-1 : ℝ))
          (sigma * Real.log (p : ℝ))
          (routePPrimitiveFourthDepthGammaThermalRatio p sigma) =
        routeEPCubicFourthDepthNormalizedContraction ∧
      routePPrimitiveFourthDepthGammaCyclicAmplitude =
        routeEPCubicFourthDepthJuliaDefect ∧
      routePPrimitiveFourthDepthGammaCyclicDefect =
        routePPrimitiveFourthDepthCoPoissonJuliaDefect ∧
      routePPrimitiveFourthDepthCoPoissonGammaCyclicKreinPivot f =
        routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f ∧
      routePPrimitiveBurnolGammaCyclicKreinPivot g =
        routePPrimitiveBurnolJuliaKreinPivot g ∧
      eulerGammaCoPoissonPrimitiveTerm p (((1 + sigma : ℝ) : ℂ)) +
          ((1 / 64 : ℝ) *
            routePPrimitiveFourthDepthGammaRunningOdds p sigma : ℝ) +
          ((routePPrimitiveFourthDepthGammaCyclicAmplitude ^ 2 *
            routePPrimitiveFourthDepthGammaRunningOdds p sigma : ℝ) : ℂ) = 0 :=
  ⟨routePPrimitiveFourthDepthGammaThermalRatio_one_lt p sigma,
    routePPrimitiveFourthDepthGammaCayley_eq_contraction p sigma,
    routePPrimitiveFourthDepthGammaCyclicAmplitude_eq_juliaDefect,
    routePPrimitiveFourthDepthGammaCyclicDefect_eq_juliaDefect,
    routePPrimitiveFourthDepthCoPoissonGammaCyclicKreinPivot_eq_juliaPivot f,
    routePPrimitiveBurnolGammaCyclicKreinPivot_eq_juliaPivot g,
    routePPrimitiveFourthDepthGammaCyclicWard p sigma⟩

end
end RHTower
