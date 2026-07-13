import GaloisForLFunctions.RHTower.CompletedSEMContourBoundary
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.WeldCircleFaithfulness

/-!
# A single irrational circle phase detects an integer Xi order

Finite deck charges require a cofinal modulus tower to detect an arbitrary integer order.  The
circle-valued prime-log character is different: `WeldCircleFaithfulness` proves that the map from
the integral prime lattice to `ℝ/ℤ` is injective.  Restricting it to one prime gives

`m ↦ [m log p]`,

which already detects one integer `m` exactly.  Consequently, closure of this one phase on every
right-half Xi zero is equivalent to RH.  The same phase can be read from the completed symmetric
Euler--Maclaurin contour index, replacing simultaneous dyadic charge closure by one circle closure.

This is a target-side criterion and a formal bridge, not a source annihilation theorem.  A proof of
RH would still have to derive the circle closure from the completed prime--Gamma source without
selecting the Xi divisor.
-/

open Complex

namespace RHTower

noncomputable section

/-- The circle phase obtained by repeating the prime-`p` weld `m` times. -/
def primeOrderCircleCharge (p : Nat.Primes) (m : ℤ) : AddCircle (1 : ℝ) :=
  GaloisForLFunctions.RHTower.primeCircleHom (Finsupp.single p m)

/-- One prime-log circle phase is faithful on integer orders. -/
theorem primeOrderCircleCharge_eq_zero_iff (p : Nat.Primes) (m : ℤ) :
    primeOrderCircleCharge p m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have hs : Finsupp.single p m = 0 := by
      apply GaloisForLFunctions.RHTower.primeCircleHom_injective
      simpa [primeOrderCircleCharge] using h
    exact Finsupp.single_eq_zero.mp hs
  · rintro rfl
    simp [primeOrderCircleCharge]

/-- A reflection-paired order and its opposite have zero total circle phase for every multiplicity.
Thus unpolarized FE-pair closure is automatic and carries no RH information. -/
theorem primeOrderCircleCharge_reflectionPair_zero (p : Nat.Primes) (m : ℤ) :
    primeOrderCircleCharge p m + primeOrderCircleCharge p (-m) = 0 := by
  simp [primeOrderCircleCharge]

/-- The prime-circle phase of the local Xi order. -/
def xiPrimeOrderCircleCharge (p : Nat.Primes) (ρ : ℂ) : AddCircle (1 : ℝ) :=
  primeOrderCircleCharge p ((analyticOrderAt xi ρ).toNat : ℤ)

/-- The local Xi prime-circle phase closes exactly when the finite local order is zero. -/
theorem xiPrimeOrderCircleCharge_eq_zero_iff (p : Nat.Primes) (ρ : ℂ) :
    xiPrimeOrderCircleCharge p ρ = 0 ↔ (analyticOrderAt xi ρ).toNat = 0 := by
  rw [xiPrimeOrderCircleCharge, primeOrderCircleCharge_eq_zero_iff]
  simp

/-- For any one fixed prime, closure of its order-circle phase at every right-half zero is exactly
RH. -/
theorem riemannHypothesis_iff_primeOrderCircleCharges_close (p : Nat.Primes) :
    RiemannHypothesis ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 → xiPrimeOrderCircleCharge p ρ = 0 := by
  constructor
  · intro hRH ρ hρ hzero
    exact (rh_iff_xi_ne_zero_right.mp hRH ρ hρ hzero).elim
  · intro hclose
    apply rh_iff_xi_ne_zero_right.mpr
    intro ρ hρ hzero
    have hc := hclose ρ hρ hzero
    have hord := (xiPrimeOrderCircleCharge_eq_zero_iff p ρ).mp hc
    exact (xi_order_toNat_ne_zero hzero hord).elim

/-- The same circle phase read from the integral completed-SEM contour index. -/
def completedSEMPrimeCircleCharge (p : Nat.Primes) (ρ : ℂ)
    (r₀ R : ℝ) (N : ℕ) : AddCircle (1 : ℝ) :=
  primeOrderCircleCharge p (completedSEMContourIndexZ ρ r₀ R N)

/-- Every actual SEM split identifies the contour circle phase with the local Xi order phase. -/
theorem completedSEMPrimeCircleCharge_eq_xiPrimeOrderCircleCharge
    (p : Nat.Primes) {ρ : ℂ} {r₀ R : ℝ} {N : ℕ}
    {zs : List ℂ} {u : ℂ → ℂ} (h : SEMSplitData ρ r₀ R N zs u) :
    completedSEMPrimeCircleCharge p ρ r₀ R N = xiPrimeOrderCircleCharge p ρ := by
  rw [completedSEMPrimeCircleCharge, xiPrimeOrderCircleCharge,
    completedSEMContourIndexZ_eq_xiOrder h]

/-- **Single-circle SEM criterion.**  For any fixed prime, RH is equivalent to closure of one
prime-log circle phase on every actual right-half completed-SEM boundary. -/
theorem riemannHypothesis_iff_all_completedSEMPrimeCircleCharges_close (p : Nat.Primes) :
    RiemannHypothesis ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∀ (r₀ R : ℝ) (N : ℕ),
          (∃ (zs : List ℂ) (u : ℂ → ℂ), SEMSplitData ρ r₀ R N zs u) →
          completedSEMPrimeCircleCharge p ρ r₀ R N = 0 := by
  constructor
  · intro hRH ρ hρ hzero
    exact (rh_iff_xi_ne_zero_right.mp hRH ρ hρ hzero).elim
  · intro hcircle
    apply riemannHypothesis_iff_all_completedSEMContourCharges_zero.mpr
    intro k ρ hρ hzero r₀ R N hex
    obtain ⟨zs, u, hsplit⟩ := hex
    have hc := hcircle ρ hρ hzero r₀ R N ⟨zs, u, hsplit⟩
    rw [completedSEMPrimeCircleCharge_eq_xiPrimeOrderCircleCharge p hsplit,
      xiPrimeOrderCircleCharge_eq_zero_iff] at hc
    rw [integralJetCharge_completedSEMContourBoundaryZ hsplit]
    rw [← semSplitData_count_eq hsplit, hc]
    simp

end

end RHTower
