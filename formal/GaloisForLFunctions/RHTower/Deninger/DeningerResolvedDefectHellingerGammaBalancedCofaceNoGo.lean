import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittCompletedXiHellingerGammaPureHodgeCoface
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittResolvedCrossEffectBoundary

/-!
# Balanced Hellinger--Gamma coface is transverse to the Deninger resolved defect

The completed Hellinger--Gamma coend has two channels, but they are Hodge-reflection channels,
not the two internal factor-defect channels of the Deninger Green factorization.  Both balanced
Gamma coefficients are strictly positive.  Consequently the codiagonal of a balanced primitive
vanishes only when its completed Xi input is zero.

Thus the balanced finite-grade range is disjoint from the entire antidiagonal kernel carrying the
Deninger resolved Green defect.  No nonzero resolved defect can be represented by merely reusing
one balanced coend grade.  A factor-provenance graph lift is a genuinely additional map.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open PrimitivePromotedHellingerGammaPureHodgeCoface
open CompletedXiHellingerGammaPureHodgeCoface

/-- Linear version of one completed balanced Hellinger--Gamma primitive. -/
def hellingerGammaCompletedBalancedPrimitiveLM
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ) :
    DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq →ₗ[ℂ]
      HellingerGammaPureHodgeXiCofaceCompletion p q hpq where
  toFun := fun x =>
    ((hellingerGammaGaugedModularCoefficient (-a) p q n : ℂ) • x,
      (hellingerGammaGaugedModularCoefficient a p q n : ℂ) • x)
  map_add' := by
    intro x y
    apply Prod.ext <;> simp
  map_smul' := by
    intro c x
    apply Prod.ext
    · dsimp
      exact smul_comm _ _ _
    · dsimp
      exact smul_comm _ _ _

@[simp]
theorem hellingerGammaCompletedBalancedPrimitiveLM_apply
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    hellingerGammaCompletedBalancedPrimitiveLM hpq a n x =
      hellingerGammaCompletedBalancedPrimitive hpq a n x :=
  rfl

/-- Every real Gamma-gauged modular coefficient is strictly positive. -/
theorem deninger_hellingerGammaGaugedModularCoefficient_pos
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    0 < hellingerGammaGaugedModularCoefficient a p q n := by
  unfold hellingerGammaGaugedModularCoefficient
    hellingerEvenGammaResidueGauge
  positivity

/-- Codiagonal of a balanced primitive is multiplication by the sum of its two positive gauges. -/
theorem resolvedDefectCodiagonal_hellingerGammaCompletedBalancedPrimitive
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    resolvedDefectCodiagonal (R := ℂ)
        (hellingerGammaCompletedBalancedPrimitive hpq a n x) =
      (((hellingerGammaGaugedModularCoefficient (-a) p q n +
          hellingerGammaGaugedModularCoefficient a p q n : ℝ) : ℂ) • x) := by
  simp [resolvedDefectCodiagonal,
    hellingerGammaCompletedBalancedPrimitive, add_smul]

/-- A balanced completed coface grade meets the codiagonal kernel only at zero input. -/
theorem resolvedDefectCodiagonal_hellingerGammaCompletedBalancedPrimitive_eq_zero_iff
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    resolvedDefectCodiagonal (R := ℂ)
        (hellingerGammaCompletedBalancedPrimitive hpq a n x) = 0 ↔
      x = 0 := by
  rw [resolvedDefectCodiagonal_hellingerGammaCompletedBalancedPrimitive]
  have hsumReal :
      0 < hellingerGammaGaugedModularCoefficient (-a) p q n +
        hellingerGammaGaugedModularCoefficient a p q n :=
    add_pos
      (deninger_hellingerGammaGaugedModularCoefficient_pos (-a) p q n)
      (deninger_hellingerGammaGaugedModularCoefficient_pos a p q n)
  have hsum :
      ((hellingerGammaGaugedModularCoefficient (-a) p q n +
          hellingerGammaGaugedModularCoefficient a p q n : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsumReal.ne'
  constructor
  · intro hzero
    exact (smul_eq_zero.mp hzero).resolve_left hsum
  · rintro rfl
    simp

/-- **Exact transversality.**  The range of every finite balanced coface grade is disjoint from
the antidiagonal/codiagonal-kernel sector containing the Deninger resolved Green defect. -/
theorem hellingerGammaCompletedBalancedPrimitive_range_disjoint_codiagonalKernel
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ) :
    Disjoint
      (LinearMap.range (hellingerGammaCompletedBalancedPrimitiveLM hpq a n))
      (LinearMap.ker
        (resolvedDefectCodiagonal
          (R := ℂ)
          (Z := DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq))) := by
  rw [Submodule.disjoint_def]
  intro z hzRange hzKernel
  obtain ⟨x, rfl⟩ := hzRange
  change
    resolvedDefectCodiagonal (R := ℂ)
        (hellingerGammaCompletedBalancedPrimitive hpq a n x) = 0 at hzKernel
  have hx :=
    (resolvedDefectCodiagonal_hellingerGammaCompletedBalancedPrimitive_eq_zero_iff
      hpq a n x).mp hzKernel
  subst x
  simp [hellingerGammaCompletedBalancedPrimitive]

/-- No nonzero antidiagonal resolved defect can be one finite balanced Hellinger--Gamma grade. -/
theorem hellingerGammaCompletedBalancedPrimitive_ne_resolvedDefectAntidiagonal
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (x z : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq)
    (hz : z ≠ 0) :
    hellingerGammaCompletedBalancedPrimitive hpq a n x ≠
      resolvedDefectAntidiagonal (R := ℂ) z := by
  intro heq
  have hzero :
      resolvedDefectCodiagonal (R := ℂ)
          (hellingerGammaCompletedBalancedPrimitive hpq a n x) = 0 := by
    rw [heq]
    simp [resolvedDefectCodiagonal, resolvedDefectAntidiagonal]
  have hx :=
    (resolvedDefectCodiagonal_hellingerGammaCompletedBalancedPrimitive_eq_zero_iff
      hpq a n x).mp hzero
  subst x
  have hfirst := congrArg Prod.fst heq
  simp [hellingerGammaCompletedBalancedPrimitive,
    resolvedDefectAntidiagonal] at hfirst
  exact hz hfirst.symm

end

end RHTower
