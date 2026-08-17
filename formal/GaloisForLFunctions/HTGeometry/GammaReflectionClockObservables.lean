import GaloisForLFunctions.HTGeometry.MeromorphicGammaReflection
import GaloisForLFunctions.HTGeometry.MeromorphicReflection
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# The two reflection readings of the Gamma clock

The clock involution `z ↦ 1 − z` acts on the pair of Gamma readings `Γ(z)`, `Γ(1 − z)`.  Passing to
multiplicative invariant and anti-invariant coordinates

`P = Γ(z)·Γ(1 − z)`,  `R = Γ(z)/Γ(1 − z)`

separates what the reflection constraint fixes from what it leaves observable.  Euler reflection
identifies `P` with the elementary gauge `π / sin(π z)`, so `P` is differentially algebraic, while
`R = Γ²/P` is hypertranscendental: an algebraic differential equation for `R` would give one for
`Γ²`, which Hölder's theorem in its signed-Gamma-product form forbids.  The two readings recover
the squared Gamma values, so the anti-invariant channel carries the whole differential
transcendence content and the invariant channel carries none.
-/

namespace GaloisForLFunctions

open Filter Set Topology Function Complex
open scoped Differential

open Bottcher

noncomputable section

open scoped UnivMeroFieldInstances

/-- The reflection-invariant multiplicative clock reading `Γ(z)·Γ(1−z)`. -/
def gammaClockInvariantMero : meroField Set.univ :=
  gammaShiftMero 0 * gammaNegativeShiftMero 1

/-- The reflection-anti-invariant multiplicative clock reading `Γ(z)/Γ(1−z)`. -/
def gammaClockAntiInvariantMero : meroField Set.univ :=
  gammaShiftMero 0 / gammaNegativeShiftMero 1

theorem gammaNegativeShiftMero_one_ne_zero : gammaNegativeShiftMero 1 ≠ 0 := by
  rw [gammaNegativeShiftMero_reflection 1]
  simp only [sub_self]
  exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero 1)
    (inv_ne_zero (gammaShiftMero_ne_zero 0))

/-- **Euler reflection for the clock product.**  The invariant reading is the elementary gauge
`π / sin(π z)`. -/
theorem gammaClockInvariantMero_eq_gauge :
    gammaClockInvariantMero = gammaReflectionGaugeMero 1 := by
  rw [gammaClockInvariantMero, gammaNegativeShiftMero_reflection 1]
  simp only [sub_self]
  field_simp [gammaShiftMero_ne_zero 0]

/-- The anti-invariant reading is the squared Gamma element divided by the gauge. -/
theorem gammaClockAntiInvariantMero_eq :
    gammaClockAntiInvariantMero
      = gammaShiftMero 0 ^ 2 / gammaReflectionGaugeMero 1 := by
  rw [gammaClockAntiInvariantMero, gammaNegativeShiftMero_reflection 1]
  simp only [sub_self]
  field_simp

/-- The two clock readings recover the squared Gamma value. -/
theorem gammaShiftMero_sq_eq_product_mul_quotient :
    gammaShiftMero 0 ^ 2 = gammaClockInvariantMero * gammaClockAntiInvariantMero := by
  rw [gammaClockInvariantMero, gammaClockAntiInvariantMero]
  field_simp [gammaNegativeShiftMero_one_ne_zero]

/-- The reflected squared Gamma value is the quotient of the two readings. -/
theorem gammaNegativeShiftMero_sq_eq_product_div_quotient :
    gammaNegativeShiftMero 1 ^ 2
      = gammaClockInvariantMero / gammaClockAntiInvariantMero := by
  rw [gammaClockInvariantMero, gammaClockAntiInvariantMero]
  field_simp [gammaShiftMero_ne_zero 0, gammaNegativeShiftMero_one_ne_zero]

/-- **The invariant channel is differentially algebraic.** -/
theorem differentialAlgebraicOver_gammaClockInvariantMero :
    DifferentialAlgebraicOver (RatFunc ℂ) gammaClockInvariantMero := by
  rw [gammaClockInvariantMero_eq_gauge]
  exact differentialAlgebraicOver_gammaReflectionGaugeMero 1

theorem gammaOrbitProductMero_zero_two :
    gammaOrbitProductMero ![0] ![(2 : ℤ)] = gammaShiftMero 0 ^ 2 := by
  rw [gammaOrbitProductMero, Fin.prod_univ_one]
  simp only [Matrix.cons_val_zero]
  rw [zpow_two, sq]

/-- **The anti-invariant channel is hypertranscendental.**  Hölder's theorem in its
signed-Gamma-product form forbids an algebraic differential equation for `Γ²`, and the invariant
gauge is differentially algebraic. -/
theorem hypertranscendentalOver_gammaClockAntiInvariantMero :
    HypertranscendentalOver (RatFunc ℂ) gammaClockAntiInvariantMero := by
  intro hDA
  have hsq : DifferentialAlgebraicOver (RatFunc ℂ) (gammaShiftMero 0 ^ 2) := by
    have hmul : gammaShiftMero 0 ^ 2
        = gammaClockAntiInvariantMero * gammaReflectionGaugeMero 1 := by
      rw [gammaClockAntiInvariantMero_eq]
      field_simp [gammaReflectionGaugeMero_ne_zero 1]
    rw [hmul]
    exact HTGeometry.differentialAlgebraicOver_mul hDA
      (differentialAlgebraicOver_gammaReflectionGaugeMero 1)
  have hHT := hypertranscendentalOver_gammaOrbitProductMero ![0] ![(2 : ℤ)] 0
    (by norm_num) (fun c hc => absurd (Subsingleton.elim c 0) hc)
  rw [gammaOrbitProductMero_zero_two] at hHT
  exact hHT hsq

end

end GaloisForLFunctions

namespace GaloisForLFunctions

open Filter Set Topology Function Complex
open scoped Differential

open Bottcher

noncomputable section

open scoped UnivMeroFieldInstances

theorem complexReflectionAnalyticEquiv_reciprocalGammaShiftAnalytic_zero :
    complexReflectionAnalyticEquiv 1 (reciprocalGammaShiftAnalytic 0)
      = reciprocalGammaNegativeShiftAnalytic 1 := by
  apply Subtype.ext
  show ((precompAnalytic (analyticOnNhd_complexReflection 1 _) (Set.mapsTo_univ _ _)
      (reciprocalGammaShiftAnalytic 0) : analyticSubring (Set.univ : Set ℂ)) :
      Germ (𝓟 (Set.univ : Set ℂ)) ℂ) = _
  rw [precompAnalytic_coe]
  change (Germ.ofFun (l := 𝓟 (Set.univ : Set ℂ))
      (fun z => reciprocalGammaEntire (z + 0))).compTendsto (complexReflection 1) _ = _
  rw [Germ.coe_compTendsto]
  refine Germ.coe_eq.mpr (eventually_principal.mpr fun z _ => ?_)
  simp only [Function.comp_apply, complexReflection]
  congr 1
  ring

theorem complexReflectionAnalyticEquiv_reciprocalGammaNegativeShiftAnalytic_one :
    complexReflectionAnalyticEquiv 1 (reciprocalGammaNegativeShiftAnalytic 1)
      = reciprocalGammaShiftAnalytic 0 := by
  apply Subtype.ext
  show ((precompAnalytic (analyticOnNhd_complexReflection 1 _) (Set.mapsTo_univ _ _)
      (reciprocalGammaNegativeShiftAnalytic 1) : analyticSubring (Set.univ : Set ℂ)) :
      Germ (𝓟 (Set.univ : Set ℂ)) ℂ) = _
  rw [precompAnalytic_coe]
  change (Germ.ofFun (l := 𝓟 (Set.univ : Set ℂ))
      (fun z => reciprocalGammaEntire (-z + 1))).compTendsto (complexReflection 1) _ = _
  rw [Germ.coe_compTendsto]
  refine Germ.coe_eq.mpr (eventually_principal.mpr fun z _ => ?_)
  simp only [Function.comp_apply, complexReflection]
  congr 1
  ring

/-- The clock involution exchanges the two Gamma readings. -/
theorem complexReflectionMeroEquiv_gammaShiftMero_zero :
    complexReflectionMeroEquiv 1 (gammaShiftMero 0) = gammaNegativeShiftMero 1 := by
  rw [gammaShiftMero, gammaNegativeShiftMero, map_inv₀,
    complexReflectionMeroEquiv_algebraMap,
    complexReflectionAnalyticEquiv_reciprocalGammaShiftAnalytic_zero]

theorem complexReflectionMeroEquiv_gammaNegativeShiftMero_one :
    complexReflectionMeroEquiv 1 (gammaNegativeShiftMero 1) = gammaShiftMero 0 := by
  rw [gammaShiftMero, gammaNegativeShiftMero, map_inv₀,
    complexReflectionMeroEquiv_algebraMap,
    complexReflectionAnalyticEquiv_reciprocalGammaNegativeShiftAnalytic_one]

/-- **The product reading is reflection invariant.** -/
theorem complexReflectionMeroEquiv_gammaClockInvariantMero :
    complexReflectionMeroEquiv 1 gammaClockInvariantMero = gammaClockInvariantMero := by
  rw [gammaClockInvariantMero, map_mul,
    complexReflectionMeroEquiv_gammaShiftMero_zero,
    complexReflectionMeroEquiv_gammaNegativeShiftMero_one, mul_comm]

/-- **The quotient reading is reflection anti-invariant.** -/
theorem complexReflectionMeroEquiv_gammaClockAntiInvariantMero :
    complexReflectionMeroEquiv 1 gammaClockAntiInvariantMero
      = gammaClockAntiInvariantMero⁻¹ := by
  rw [gammaClockAntiInvariantMero, map_div₀,
    complexReflectionMeroEquiv_gammaShiftMero_zero,
    complexReflectionMeroEquiv_gammaNegativeShiftMero_one, inv_div]

end

end GaloisForLFunctions
