import GaloisForLFunctions.AdelicKreinGeometry.TheArchimedeanGluingFormula
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeEnergyHasFiniteRamanujanCoordinates
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanPlacePaysTheArithmeticPoint

/-!
# The pole class is the ground conductor

Two readings of the scaling surface meet on the integer slopes `1, …, N`.

* The archimedean gluing of Weil's correlation (`AdelicKreinGeometry`) constrains coefficient
  vectors by the boost functional `ℓ(w) = Σ_i w_i u_i^{−1/2}`; on `ℓ = 0` the glued state has the
  index of the zeros.
* The complete Weil matrix at horizon `N` (`CriticalArithmeticCorrelationTheory`) has its ground state
  on the normalized pole-conductor vector `v_1 = (log N)^{−1/2} (n^{−1/2})_{n ≤ N}`.

**Pole-class identity** (`boostMassU_integerSlopes_eq_inner`): on the integer slopes
`ℓ(x) = √(log N) ⟪x, v_1⟫`. Hence (`boostMassU_integerSlopes_eq_zero_iff`) the boost hyperplane of
the archimedean gluing is the orthogonal complement of the complete-Weil ground conductor. The
index-one problem of the archimedean Weil state and the sign problem of the complete Weil matrix
are positivity on the same hyperplane `v_1^⊥`.
-/

open Finset
open scoped RealInnerProductSpace
open GaloisForLFunctions.AdelicKreinGeometry GaloisForLFunctions.ArithmeticPositiveDuality
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- The integer slope `i + 1` as a positive rational. -/
def integerSlopes (N : ℕ) (i : Fin N) : posUnits :=
  ⟨Units.mk0 ((i + 1 : ℕ) : ℚ) (by positivity), by show (0 : ℚ) < ((i + 1 : ℕ) : ℚ); positivity⟩

/-- The horizon `{1, …, N}` indexed by `Fin N`. -/
def finHorizon (N : ℕ) : Fin N ≃ PrimeHorizonIndex N where
  toFun i := ⟨i + 1, mem_Icc.mpr ⟨by omega, by omega⟩⟩
  invFun n := ⟨n.1 - 1, by have := mem_Icc.mp n.2; omega⟩
  left_inv i := by ext; simp
  right_inv n := by ext; have := mem_Icc.mp n.2; simp; omega

theorem ramanujanPoleProfile_one (n : ℕ) : ramanujanPoleProfile 1 n = (Real.sqrt n)⁻¹ := by
  simp [ramanujanPoleProfile, normalizedRamanujanMode, ramanujanMode_one]

/-- The boost functional on the integer slopes. -/
theorem boostMassU_integerSlopes (N : ℕ) (w : Fin N → ℂ) :
    boostMassU (integerSlopes N) w = ∑ i, w i * (((Real.sqrt ((i + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) := by
  simp only [boostMassU, LinearMap.coe_mk, AddHom.coe_mk, integerSlopes, Units.val_mk0]
  refine sum_congr rfl fun i _ => ?_
  rw [Rat.cast_natCast, Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow]

/-- **Pole-class identity**: on the integer slopes the boost functional is `√(log N)` times the
pairing with the complete-Weil pole conductor `v_1`. -/
theorem boostMassU_integerSlopes_eq_inner {N : ℕ} (hN : 2 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    boostMassU (integerSlopes N) (fun i => (x (finHorizon N i) : ℂ)) =
      ((Real.sqrt (Real.log N) * ⟪x, normalizedRamanujanHorizonVector 1 N⟫ : ℝ) : ℂ) := by
  have hL : 0 < Real.sqrt (Real.log N) :=
    Real.sqrt_pos.mpr (Real.log_pos (by exact_mod_cast hN))
  rw [boostMassU_integerSlopes, normalizedRamanujanHorizonVector, real_inner_smul_right,
    ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  change ∑ i, x (finHorizon N i) * (Real.sqrt ((i + 1 : ℕ) : ℝ))⁻¹ =
    ∑ n : PrimeHorizonIndex N, ramanujanPoleProfile 1 n * x n
  rw [← (finHorizon N).sum_comp]
  refine sum_congr rfl fun i _ => ?_
  rw [ramanujanPoleProfile_one, mul_comm]
  rfl

/-- **The boost hyperplane is the orthogonal complement of the ground conductor.** -/
theorem boostMassU_integerSlopes_eq_zero_iff {N : ℕ} (hN : 2 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    boostMassU (integerSlopes N) (fun i => (x (finHorizon N i) : ℂ)) = 0 ↔
      ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 := by
  have hL : Real.sqrt (Real.log N) ≠ 0 :=
    (Real.sqrt_pos.mpr (Real.log_pos (by exact_mod_cast hN))).ne'
  rw [boostMassU_integerSlopes_eq_inner hN, Complex.ofReal_eq_zero, mul_eq_zero, or_iff_right hL]

end GaloisForLFunctions.RenormalizedIntersectionTheory
