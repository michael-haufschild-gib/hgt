import GaloisForLFunctions.RHTower.DeningerCalderonWittGaussianHorizontalNormalization
import GaloisForLFunctions.RHTower.XiPrimeMarkedCofinalTriangleNuclearCarrier

/-!
# Scalar-tensor no-go for Gaussian prime cycles

The all-cross-prime Calderón--Witt residual is one-dimensional: the actual
Gaussian horizontal packet is its scalar Wronskian times a fixed horizon.
The cofinal prime-marked triangle carrier supplies genuine off-diagonal
source holonomy.  Tensoring these two already constructed objects is a
natural candidate for the missing horizontal transgression.

This file classifies that candidate completely.  Triangle holonomy is
cubic along every scalar operator ray.  A fixed prime carrier with nonzero
base holonomy therefore detects the scalar exactly, while a carrier with
zero base holonomy is blind to the whole ray.  It cannot provide an
independent annihilation identity.

For the actual reflected prime-shell entropy, the scalar-coupled carrier is
self-adjoint, Schatten--one, uniformly bounded on the Xi divisor, has zero
diagonal, is reflection-odd, and retains nonzero cofinal holonomy exactly
off the critical line.  Thus it is a fully constructed detector, not an RH
proof.  A surviving annihilator must entangle divisor provenance with prime
cycle data rather than tensoring a fixed prime carrier by the Green scalar.
-/

open scoped BigOperators InnerProductSpace Nat.Prime
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

namespace DeningerMeyerGaussianGreen

/-- Three-cycle matrix holonomy on selected cofinal prime block `n`. -/
def deningerGaussianPrimeTriangleHolonomy
    (T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert) (n : ℕ) : ℂ :=
  inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 0))
      (T (routeKPrimeBasis (routeKCofinalTrianglePrime n 1))) *
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 1))
      (T (routeKPrimeBasis (routeKCofinalTrianglePrime n 2))) *
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 2))
      (T (routeKPrimeBasis (routeKCofinalTrianglePrime n 0)))

/-- Triangle holonomy is cubic on every scalar operator ray. -/
theorem deningerGaussianPrimeTriangleHolonomy_smul
    (c : ℂ) (T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert) (n : ℕ) :
    deningerGaussianPrimeTriangleHolonomy (c • T) n =
      c ^ (3 : ℕ) * deningerGaussianPrimeTriangleHolonomy T n := by
  simp only [deningerGaussianPrimeTriangleHolonomy,
    smul_apply, inner_smul_right]
  ring

/-- A nonzero base triangle is a faithful detector on its scalar ray. -/
theorem deningerGaussianPrimeTriangleHolonomy_smul_eq_zero_iff
    {T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert} {n : ℕ}
    (hT : deningerGaussianPrimeTriangleHolonomy T n ≠ 0) (c : ℂ) :
    deningerGaussianPrimeTriangleHolonomy (c • T) n = 0 ↔ c = 0 := by
  rw [deningerGaussianPrimeTriangleHolonomy_smul]
  simp [hT]

/-- A zero base triangle is blind to every scalar on the same ray. -/
theorem deningerGaussianPrimeTriangleHolonomy_smul_eq_zero_of_base_zero
    {T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert} {n : ℕ}
    (hT : deningerGaussianPrimeTriangleHolonomy T n = 0) (c : ℂ) :
    deningerGaussianPrimeTriangleHolonomy (c • T) n = 0 := by
  rw [deningerGaussianPrimeTriangleHolonomy_smul, hT, mul_zero]

/-- The reflected prime-shell entropy is the signed horizontal displacement. -/
theorem riemannReflectedSourceEntropy_eq_one_sub_two_re (s : ℂ) :
    riemannReflectedSourceEntropy s = 1 - 2 * s.re := by
  rw [riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  simp only [sourceCayleyTransverseRate, Complex.sub_re, Complex.one_re]
  ring

/-- Source entropy vanishes exactly on the critical line. -/
theorem riemannReflectedSourceEntropy_eq_zero_iff (s : ℂ) :
    riemannReflectedSourceEntropy s = 0 ↔ s.re = 1 / 2 := by
  rw [riemannReflectedSourceEntropy_eq_one_sub_two_re]
  constructor <;> intro h <;> linarith

/-- On every actual Xi divisor copy, source entropy has modulus below one. -/
theorem abs_riemannReflectedSourceEntropy_lt_one (q : XiZeroCopy) :
    |riemannReflectedSourceEntropy (q.1 : ℂ)| < 1 := by
  rw [riemannReflectedSourceEntropy_eq_one_sub_two_re, abs_lt]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  constructor <;> linarith [hstrip.1, hstrip.2]

/-- Scalar coupling of the actual entropy to the cofinal prime-cycle tail. -/
def deningerGaussianEntropyPrimeCycleCarrier
    (M : ℕ) (q : XiZeroCopy) :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  (riemannReflectedSourceEntropy (q.1 : ℂ) : ℂ) •
    routeKCofinalTriangleNuclearCarrierFrom M

/-- The entropy-coupled prime carrier remains Schatten--one. -/
theorem deningerGaussianEntropyPrimeCycleCarrier_memSchattenClass_one
    (M : ℕ) (q : XiZeroCopy) :
    MemSchattenClass 1 (deningerGaussianEntropyPrimeCycleCarrier M q) := by
  exact memSchattenClass_one_smul
    (routeKCofinalTriangleNuclearCarrierFrom_memSchattenClass_one M) _

/-- Real entropy scaling preserves self-adjointness. -/
theorem deningerGaussianEntropyPrimeCycleCarrier_isSelfAdjoint
    (M : ℕ) (q : XiZeroCopy) :
    IsSelfAdjoint (deningerGaussianEntropyPrimeCycleCarrier M q) := by
  rw [deningerGaussianEntropyPrimeCycleCarrier]
  apply IsSelfAdjoint.smul
  · simp [IsSelfAdjoint]
  · exact routeKCofinalTriangleNuclearCarrierFrom_isSelfAdjoint M

/-- Exact operator-capacity scaling by the source entropy. -/
theorem norm_deningerGaussianEntropyPrimeCycleCarrier
    (M : ℕ) (q : XiZeroCopy) :
    ‖deningerGaussianEntropyPrimeCycleCarrier M q‖ =
      |riemannReflectedSourceEntropy (q.1 : ℂ)| *
        ‖routeKCofinalTriangleNuclearCarrierFrom M‖ := by
  rw [deningerGaussianEntropyPrimeCycleCarrier, norm_smul,
    Complex.norm_real, Real.norm_eq_abs]

/-- The whole Xi-divisor family has one source-selected uniform capacity. -/
theorem norm_deningerGaussianEntropyPrimeCycleCarrier_le
    (M : ℕ) (q : XiZeroCopy) :
    ‖deningerGaussianEntropyPrimeCycleCarrier M q‖ ≤
      ‖routeKCofinalTriangleNuclearCarrierFrom M‖ := by
  rw [norm_deningerGaussianEntropyPrimeCycleCarrier]
  have hent := abs_riemannReflectedSourceEntropy_lt_one q
  have hnorm : 0 ≤ ‖routeKCofinalTriangleNuclearCarrierFrom M‖ := norm_nonneg _
  nlinarith

/-- Scalar coupling preserves the identically zero marked-prime diagonal. -/
theorem deningerGaussianEntropyPrimeCycleCarrier_diagonal_zero
    (M : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p)
        (deningerGaussianEntropyPrimeCycleCarrier M q
          (routeKPrimeBasis p)) = 0 := by
  rw [deningerGaussianEntropyPrimeCycleCarrier,
    smul_apply, inner_smul_right,
    routeKCofinalTriangleNuclearCarrierFrom_diagonal_zero, mul_zero]

/-- The source-coupled selected cycle is exactly entropy cubed times the
fixed prime-source holonomy. -/
theorem deningerGaussianEntropyPrimeCycleCarrier_selectedHolonomy
    (M n : ℕ) (q : XiZeroCopy) :
    deningerGaussianPrimeTriangleHolonomy
        (deningerGaussianEntropyPrimeCycleCarrier M q) (n + M) =
      (riemannReflectedSourceEntropy (q.1 : ℂ) : ℂ) ^ (3 : ℕ) *
        deningerGaussianPrimeTriangleHolonomy
          (routeKCofinalTriangleNuclearCarrierFrom M) (n + M) := by
  exact deningerGaussianPrimeTriangleHolonomy_smul _ _ _

/-- Every retained base triangle has nonzero source holonomy. -/
theorem deningerGaussianPrimeTriangleHolonomy_carrierFrom_ne_zero
    (M n : ℕ) :
    deningerGaussianPrimeTriangleHolonomy
        (routeKCofinalTriangleNuclearCarrierFrom M) (n + M) ≠ 0 := by
  exact routeKCofinalTriangleNuclearCarrierFrom_selectedHolonomy_ne_zero M n

/-- The entropy-coupled cofinal triangle vanishes exactly on the critical
line.  It is a detector, not an independent annihilator. -/
theorem deningerGaussianEntropyPrimeCycleCarrier_selectedHolonomy_eq_zero_iff
    (M n : ℕ) (q : XiZeroCopy) :
    deningerGaussianPrimeTriangleHolonomy
        (deningerGaussianEntropyPrimeCycleCarrier M q) (n + M) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [deningerGaussianEntropyPrimeCycleCarrier_selectedHolonomy]
  simp [deningerGaussianPrimeTriangleHolonomy_carrierFrom_ne_zero,
    riemannReflectedSourceEntropy_eq_zero_iff]

/-- Off line, nonzero selected triangle holonomy survives beyond every
finite prime-index cut. -/
theorem exists_cofinal_deningerGaussianEntropyPrimeCycleCarrier_holonomy
    (M N : ℕ) (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃ n : ℕ, N ≤ routeKCofinalTriangleStart (n + M) ∧
      deningerGaussianPrimeTriangleHolonomy
          (deningerGaussianEntropyPrimeCycleCarrier M q) (n + M) ≠ 0 := by
  refine ⟨N, ?_, ?_⟩
  · have hstart := routeKCofinalTriangleStart_self_le (N + M)
    omega
  · intro hzero
    exact hoff
      ((deningerGaussianEntropyPrimeCycleCarrier_selectedHolonomy_eq_zero_iff
        M N q).mp hzero)

/-- Functional-equation reflection reverses the entropy-coupled carrier. -/
theorem deningerGaussianEntropyPrimeCycleCarrier_lineConj
    (M : ℕ) (q : XiZeroCopy) :
    deningerGaussianEntropyPrimeCycleCarrier M
        (xiZeroCopyLineConjEquiv q) =
      -deningerGaussianEntropyPrimeCycleCarrier M q := by
  rw [deningerGaussianEntropyPrimeCycleCarrier,
    deningerGaussianEntropyPrimeCycleCarrier]
  change
    (riemannReflectedSourceEntropy
        (1 - star (q.1 : ℂ)) : ℂ) •
        routeKCofinalTriangleNuclearCarrierFrom M = _
  rw [riemannReflectedSourceEntropy_reflection]
  push_cast
  simp

/-- Global vanishing of any one retained scalar-coupled triangle already
has exactly the strength of RH. -/
theorem forall_deningerGaussianEntropyPrimeCycleCarrier_holonomy_eq_zero_iff_rh
    (M n : ℕ) :
    (∀ q : XiZeroCopy,
      deningerGaussianPrimeTriangleHolonomy
          (deningerGaussianEntropyPrimeCycleCarrier M q) (n + M) = 0) ↔
      RiemannHypothesis := by
  rw [←
    deningerMeyerReflectedGaussianLineWronskian_vanishes_iff_riemannHypothesis]
  apply forall_congr'
  intro q
  exact
    (deningerGaussianEntropyPrimeCycleCarrier_selectedHolonomy_eq_zero_iff
      M n q).trans
        (deningerMeyerReflectedGaussianLineWronskian_eq_zero_iff q).symm

end DeningerMeyerGaussianGreen

end

end RHTower
