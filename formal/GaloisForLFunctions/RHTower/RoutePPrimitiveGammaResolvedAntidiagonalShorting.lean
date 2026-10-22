import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaSewnCriticalGreenThreshold
import GaloisForLFunctions.RHTower.FrankensteinTailFluxGammaCoorientedShortingNoGo
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittResolvedCrossEffectBoundary

/-!
# Route P Gamma-resolved antidiagonal shorting

The physically cooriented Gamma exterior is symmetric under exchange of its
two prime-power cells.  Consequently its resolved two-channel reporter factors
through the codiagonal.  Away from the balanced section and off the cell
diagonal, its kernel is exactly the universal antidiagonal, so the sign pattern
needed to evade the positive-cone obstruction is forced rather than chosen.

The square root of the trace-finite double-Green flux supplies a canonical
nonzero antidiagonal Wold vector.  It shorts the cooriented reporter while
retaining twice the pair flux as positive energy; before coorientation the same
vector doubles, rather than kills, the reflection-odd exterior.

No Xi divisor, zero-location statement, target positivity assumption, or
Riemann-hypothesis premise occurs.
-/

open Complex Set MeasureTheory Filter Topology
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Physical coorientation turns the reflection-odd exterior into a symmetric
two-cell reporter. -/
theorem xiGammaEulerPrimitiveCoorientedReflectionOddExterior_swap
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveCoorientedReflectionOddExterior a j i =
      xiGammaEulerPrimitiveCoorientedReflectionOddExterior a i j := by
  rw [xiGammaEulerPrimitiveCoorientedReflectionOddExterior,
    xiGammaEulerPrimitiveCoorientedReflectionOddExterior,
    xiGammaEulerPrimitiveReflectionOddExterior_swap]
  ring

/-- Off the balanced section, physical coorientation detects every pair of
distinct labelled prime-power cells. -/
theorem xiGammaEulerPrimitiveCoorientedReflectionOddExterior_ne_zero
    {a : ℝ} (ha : a ≠ 0) (i j : Nat.Primes × ℕ) (hij : i ≠ j) :
    xiGammaEulerPrimitiveCoorientedReflectionOddExterior a i j ≠ 0 := by
  have hheight : xiGammaEulerBoundaryHalfHeight i.1 i.2 ≠
      xiGammaEulerBoundaryHalfHeight j.1 j.2 := by
    intro h
    exact hij
      (PrimitivePromotedCellHodgeRigidity.xiGammaEulerBoundaryHalfHeight_cell_injective h)
  apply mul_ne_zero
  · exact sub_ne_zero.mpr (Ne.symm hheight)
  · exact xiGammaEulerPrimitiveReflectionOddExterior_ne_zero ha i j hheight

/-- The resolved physical Gamma reporter on an ordered cell pair. -/
def routePPrimitiveGammaCoorientedResolvedReporter
    (a : ℝ) (i j : Nat.Primes × ℕ) : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun z :=
    z.1 * xiGammaEulerPrimitiveCoorientedReflectionOddExterior a i j +
      z.2 * xiGammaEulerPrimitiveCoorientedReflectionOddExterior a j i
  map_add' x y := by simp; ring
  map_smul' c x := by simp; ring

/-- The resolved physical reporter is exactly the ordinary codiagonal followed
by multiplication by one nonzero pair exterior. -/
theorem routePPrimitiveGammaCoorientedResolvedReporter_eq_codiagonal
    (a : ℝ) (i j : Nat.Primes × ℕ) (z : ℝ × ℝ) :
    routePPrimitiveGammaCoorientedResolvedReporter a i j z =
      xiGammaEulerPrimitiveCoorientedReflectionOddExterior a i j *
        resolvedDefectCodiagonal (R := ℝ) z := by
  change z.1 * xiGammaEulerPrimitiveCoorientedReflectionOddExterior a i j +
      z.2 * xiGammaEulerPrimitiveCoorientedReflectionOddExterior a j i =
    xiGammaEulerPrimitiveCoorientedReflectionOddExterior a i j * (z.1 + z.2)
  rw [
    xiGammaEulerPrimitiveCoorientedReflectionOddExterior_swap]
  ring

/-- **Forced-sign classification.**  Away from the balanced section and the
cell diagonal, the physical two-channel shorting kernel is exactly the
codiagonal kernel. -/
theorem ker_routePPrimitiveGammaCoorientedResolvedReporter_eq_codiagonal
    {a : ℝ} (ha : a ≠ 0) (i j : Nat.Primes × ℕ) (hij : i ≠ j) :
    LinearMap.ker (routePPrimitiveGammaCoorientedResolvedReporter a i j) =
      LinearMap.ker (resolvedDefectCodiagonal (R := ℝ) (Z := ℝ)) := by
  have hE :=
    xiGammaEulerPrimitiveCoorientedReflectionOddExterior_ne_zero ha i j hij
  ext z
  rw [LinearMap.mem_ker, LinearMap.mem_ker,
    routePPrimitiveGammaCoorientedResolvedReporter_eq_codiagonal]
  simp [hE]

/-- Hence the universal antidiagonal is not merely a possible signed repair:
it is the complete physical shorting sector. -/
theorem ker_routePPrimitiveGammaCoorientedResolvedReporter_eq_range_antidiagonal
    {a : ℝ} (ha : a ≠ 0) (i j : Nat.Primes × ℕ) (hij : i ≠ j) :
    LinearMap.ker (routePPrimitiveGammaCoorientedResolvedReporter a i j) =
      LinearMap.range (resolvedDefectAntidiagonal (R := ℝ) (Z := ℝ)) := by
  rw [ker_routePPrimitiveGammaCoorientedResolvedReporter_eq_codiagonal ha i j hij,
    ker_resolvedDefectCodiagonal_eq_range_antidiagonal]

/-- Canonical square-root amplitude of the trace-finite double-Green flux on a
cell pair. -/
def routePPrimitiveGammaResolvedWoldAmplitude
    (i j : Nat.Primes × ℕ) : ℝ :=
  Real.sqrt
    (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux i *
      routePPrimitiveGammaSewnCriticalQuadraticGreenFlux j)

theorem routePPrimitiveGammaResolvedWoldAmplitude_pos
    (i j : Nat.Primes × ℕ) :
    0 < routePPrimitiveGammaResolvedWoldAmplitude i j := by
  rw [routePPrimitiveGammaResolvedWoldAmplitude, Real.sqrt_pos]
  exact mul_pos
    (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_pos i)
    (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_pos j)

theorem routePPrimitiveGammaResolvedWoldAmplitude_sq
    (i j : Nat.Primes × ℕ) :
    routePPrimitiveGammaResolvedWoldAmplitude i j ^ (2 : ℕ) =
      routePPrimitiveGammaSewnCriticalQuadraticGreenFlux i *
        routePPrimitiveGammaSewnCriticalQuadraticGreenFlux j := by
  rw [routePPrimitiveGammaResolvedWoldAmplitude, Real.sq_sqrt]
  exact mul_nonneg
    (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_pos i).le
    (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_pos j).le

/-- The canonical two-channel Wold current forced by the shorting
classification. -/
def routePPrimitiveGammaResolvedWoldCurrent
    (i j : Nat.Primes × ℕ) : ℝ × ℝ :=
  resolvedDefectAntidiagonal (R := ℝ)
    (routePPrimitiveGammaResolvedWoldAmplitude i j)

theorem routePPrimitiveGammaResolvedWoldCurrent_ne_zero
    (i j : Nat.Primes × ℕ) :
    routePPrimitiveGammaResolvedWoldCurrent i j ≠ 0 := by
  intro hzero
  have hfirst := congrArg Prod.fst hzero
  simp [routePPrimitiveGammaResolvedWoldCurrent] at hfirst
  exact (routePPrimitiveGammaResolvedWoldAmplitude_pos i j).ne' hfirst

/-- The canonical Wold current physically shorts every cooriented pair
reporter. -/
@[simp] theorem routePPrimitiveGammaCoorientedResolvedReporter_woldCurrent
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    routePPrimitiveGammaCoorientedResolvedReporter a i j
      (routePPrimitiveGammaResolvedWoldCurrent i j) = 0 := by
  rw [routePPrimitiveGammaCoorientedResolvedReporter_eq_codiagonal]
  simp [routePPrimitiveGammaResolvedWoldCurrent]

/-- Despite exact shorting, the hidden two-channel current retains exactly
twice the pairwise quadratic-Green flux as Euclidean energy. -/
theorem routePPrimitiveGammaResolvedWoldCurrent_energy
    (i j : Nat.Primes × ℕ) :
    (routePPrimitiveGammaResolvedWoldCurrent i j).1 ^ (2 : ℕ) +
        (routePPrimitiveGammaResolvedWoldCurrent i j).2 ^ (2 : ℕ) =
      2 * routePPrimitiveGammaSewnCriticalQuadraticGreenFlux i *
        routePPrimitiveGammaSewnCriticalQuadraticGreenFlux j := by
  rw [routePPrimitiveGammaResolvedWoldCurrent,
    resolvedDefectAntidiagonal_apply]
  simp only [neg_sq]
  rw [routePPrimitiveGammaResolvedWoldAmplitude_sq]
  ring

/-- Before physical coorientation, the same antidiagonal current doubles the
reflection-odd orientation signal instead of annihilating it. -/
theorem routePPrimitiveGammaResolvedWoldCurrent_uncooriented_eq
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    (routePPrimitiveGammaResolvedWoldCurrent i j).1 *
        xiGammaEulerPrimitiveReflectionOddExterior a i j +
      (routePPrimitiveGammaResolvedWoldCurrent i j).2 *
        xiGammaEulerPrimitiveReflectionOddExterior a j i =
      2 * routePPrimitiveGammaResolvedWoldAmplitude i j *
        xiGammaEulerPrimitiveReflectionOddExterior a i j := by
  rw [routePPrimitiveGammaResolvedWoldCurrent,
    resolvedDefectAntidiagonal_apply,
    xiGammaEulerPrimitiveReflectionOddExterior_swap]
  ring

theorem routePPrimitiveGammaResolvedWoldCurrent_uncooriented_ne_zero
    {a : ℝ} (ha : a ≠ 0) (i j : Nat.Primes × ℕ) (hij : i ≠ j) :
    (routePPrimitiveGammaResolvedWoldCurrent i j).1 *
        xiGammaEulerPrimitiveReflectionOddExterior a i j +
      (routePPrimitiveGammaResolvedWoldCurrent i j).2 *
        xiGammaEulerPrimitiveReflectionOddExterior a j i ≠ 0 := by
  rw [routePPrimitiveGammaResolvedWoldCurrent_uncooriented_eq]
  have hheight : xiGammaEulerBoundaryHalfHeight i.1 i.2 ≠
      xiGammaEulerBoundaryHalfHeight j.1 j.2 := by
    intro h
    exact hij
      (PrimitivePromotedCellHodgeRigidity.xiGammaEulerBoundaryHalfHeight_cell_injective h)
  exact mul_ne_zero
    (mul_ne_zero (by norm_num)
      (routePPrimitiveGammaResolvedWoldAmplitude_pos i j).ne')
    (xiGammaEulerPrimitiveReflectionOddExterior_ne_zero ha i j hheight)

/-- The retained pair-energy family is globally summable. -/
theorem summable_routePPrimitiveGammaResolvedWoldCurrent_energy :
    Summable (fun ij :
        (Nat.Primes × ℕ) × (Nat.Primes × ℕ) =>
      (routePPrimitiveGammaResolvedWoldCurrent ij.1 ij.2).1 ^ (2 : ℕ) +
        (routePPrimitiveGammaResolvedWoldCurrent ij.1 ij.2).2 ^ (2 : ℕ)) := by
  have hsum : Summable
      (fun ij : (Nat.Primes × ℕ) × (Nat.Primes × ℕ) =>
      2 * routePPrimitiveGammaSewnCriticalQuadraticGreenFlux ij.1 *
        routePPrimitiveGammaSewnCriticalQuadraticGreenFlux ij.2) := by
    rw [summable_prod_of_nonneg (fun ij =>
        mul_nonneg
          (mul_nonneg (by norm_num)
            (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_pos ij.1).le)
          (routePPrimitiveGammaSewnCriticalQuadraticGreenFlux_pos ij.2).le)]
    constructor
    · intro i
      exact summable_routePPrimitiveGammaSewnCriticalQuadraticGreenFlux.mul_left
        (2 * routePPrimitiveGammaSewnCriticalQuadraticGreenFlux i)
    · apply
        (summable_routePPrimitiveGammaSewnCriticalQuadraticGreenFlux.mul_left
          (2 * ∑' j, routePPrimitiveGammaSewnCriticalQuadraticGreenFlux j)).congr
      intro i
      calc
        (2 * ∑' j, routePPrimitiveGammaSewnCriticalQuadraticGreenFlux j) *
              routePPrimitiveGammaSewnCriticalQuadraticGreenFlux i =
            (2 * routePPrimitiveGammaSewnCriticalQuadraticGreenFlux i) *
              ∑' j, routePPrimitiveGammaSewnCriticalQuadraticGreenFlux j := by ring
        _ = ∑' j, (2 * routePPrimitiveGammaSewnCriticalQuadraticGreenFlux i) *
              routePPrimitiveGammaSewnCriticalQuadraticGreenFlux j := by
            rw [tsum_mul_left]
        _ = ∑' j,
              2 * routePPrimitiveGammaSewnCriticalQuadraticGreenFlux (i, j).1 *
                routePPrimitiveGammaSewnCriticalQuadraticGreenFlux (i, j).2 := by
            apply tsum_congr
            intro j
            ring
  exact hsum.congr fun ij =>
    (routePPrimitiveGammaResolvedWoldCurrent_energy ij.1 ij.2).symm

end

end RHTower
