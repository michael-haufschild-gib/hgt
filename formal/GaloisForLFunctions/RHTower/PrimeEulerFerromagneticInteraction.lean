import GaloisForLFunctions.RHTower.PrimeEulerLeeYangAmplitudeNoGo

/-!
# The Euler square-root amplitude is a ferromagnetic interaction

The physical Euler monomial fails as a Lee--Yang field: its factor `p⁻¹⁄²` displaces the
unit torus from the centered critical line.  The same number is, however, a valid two-spin
ferromagnetic coefficient

`c_p = exp (-log(p)/2) = exp(-2 J_p)`, with `J_p = log(p)/4 > 0`.

Keeping `exp(-log(p) I z)` as the field and moving `p⁻¹⁄²` into the interaction gives the
source-native block

`1 + 2 c_p u_p(z) + u_p(z)^2`.

This file proves that every zero of each such block, and of every finite product of them, lies on
the centered critical line.  It is a positive successor to the amplitude-displacement no-go, not
yet a comparison with the completed Euler product: the reciprocal Euler-pair coefficient is
`c_p + c_p⁻¹`, whereas the ferromagnetic block has coefficient `2 c_p`.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The physical Euler square-root amplitude, now used as a two-spin interaction coefficient. -/
def primeEulerFerromagneticCoefficient (p : Nat.Primes) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * primeLeeYangLog p)

theorem primeEulerFerromagneticCoefficient_pos (p : Nat.Primes) :
    0 < primeEulerFerromagneticCoefficient p := by
  unfold primeEulerFerromagneticCoefficient
  positivity

theorem primeEulerFerromagneticCoefficient_le_one (p : Nat.Primes) :
    primeEulerFerromagneticCoefficient p ≤ 1 := by
  rw [primeEulerFerromagneticCoefficient, Real.exp_le_one_iff]
  have hp : 0 < primeLeeYangLog p := by
    unfold primeLeeYangLog
    exact Real.log_pos (by exact_mod_cast p.2.one_lt)
  nlinarith

/-- The prime-local two-spin partition block, with the centered prime character as field. -/
def primeEulerFerromagneticBlock (p : Nat.Primes) (z : ℂ) : ℂ :=
  GaloisForLFunctions.RHTower.leeYangPairBlock
    (primeEulerFerromagneticCoefficient p) (centeredPrimeLeeYangField p z)

/-- A prime-local ferromagnetic block can vanish only on the centered critical line. -/
theorem primeEulerFerromagneticBlock_zero_im
    (p : Nat.Primes) {z : ℂ}
    (hz : primeEulerFerromagneticBlock p z = 0) :
    z.im = 0 := by
  have hcircle :=
    GaloisForLFunctions.RHTower.leeYangPairCircle_of_ferromagneticCoefficient
      (le_of_lt (primeEulerFerromagneticCoefficient_pos p))
      (primeEulerFerromagneticCoefficient_le_one p)
  have hnormSq : Complex.normSq (centeredPrimeLeeYangField p z) = 1 :=
    hcircle (centeredPrimeLeeYangField p z) hz
  have hnorm : ‖centeredPrimeLeeYangField p z‖ = 1 := by
    rw [← Complex.sq_norm] at hnormSq
    nlinarith [norm_nonneg (centeredPrimeLeeYangField p z)]
  exact (norm_centeredPrimeLeeYangField_eq_one_iff p z).mp hnorm

/-- Finite product of the source-native ferromagnetic prime blocks. -/
def primeEulerFerromagneticPartition
    (P : Finset Nat.Primes) (z : ℂ) : ℂ :=
  ∏ p ∈ P, primeEulerFerromagneticBlock p z

/-- Every zero of every finite prime-aperture ferromagnetic product is centered-critical. -/
theorem primeEulerFerromagneticPartition_zero_im
    (P : Finset Nat.Primes) {z : ℂ}
    (hz : primeEulerFerromagneticPartition P z = 0) :
    z.im = 0 := by
  rw [primeEulerFerromagneticPartition, Finset.prod_eq_zero_iff] at hz
  obtain ⟨p, _, hp⟩ := hz
  exact primeEulerFerromagneticBlock_zero_im p hp

end

end RHTower
