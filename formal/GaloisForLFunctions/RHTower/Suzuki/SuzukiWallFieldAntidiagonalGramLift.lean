import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalWallFieldSquareRootWeld
import GaloisForLFunctions.RHTower.Suzuki.SuzukiMarkedSecantMidpointLorentzCompletion
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Suzuki wall-field anti-diagonal Gram lift

The critical wall-field square carries full far-hinge phase and therefore is not a positive
scalar diagonal.  Its correct positive carrier is two-height Hermitian kernel

`K_e(t,u) = omega_e(t) * conj (omega_e(u))`.

Every finite height section is a rank-one Gram matrix.  Its positive diagonal is exact
von-Mangoldt wall weight, while its functional-equation-reflected anti-diagonal is exact far-hinge
numerator.  Same positive diagonal pays sharp halfgap-squared debt in marked midpoint Lorentz
block.  This separates positivity type without losing arithmetic phase.

No RH premise, estimate, numerical computation, infinite prime sum, or endpoint evaluation is
used.
-/

open Complex
open scoped ComplexConjugate ComplexOrder Matrix

namespace RHTower

noncomputable section

/-! ## Reflected Hermitian wall kernel -/

/-- Rank-one Hermitian kernel of critical prime-power wall field at two independent heights. -/
def suzukiCriticalWallFieldGramKernel
    (t u : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  suzukiCriticalWallField t p e * star (suzukiCriticalWallField u p e)

/-- Wall kernel has exact Hermitian symmetry before any height reflection. -/
theorem star_suzukiCriticalWallFieldGramKernel_swap
    (t u : ℝ) (p : Nat.Primes) (e : ℕ) :
    star (suzukiCriticalWallFieldGramKernel u t p e) =
      suzukiCriticalWallFieldGramKernel t u p e := by
  simp only [suzukiCriticalWallFieldGramKernel, star_mul, star_star]

/-- Functional-equation height reflection converts Hermitian conjugate back to original wall
field. -/
theorem star_suzukiCriticalWallField_neg
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    star (suzukiCriticalWallField (-t) p e) =
      suzukiCriticalWallField t p e := by
  rw [suzukiCriticalWallField_eq_bareAmplitude_mul_kernel,
    suzukiCriticalWallField_eq_bareAmplitude_mul_kernel]
  rw [star_mul]
  change
    conj (suzukiOscillatoryKernel ((-t : ℝ) : ℂ)
        (suzukiPrimePowerEntryWallAperture p e)) *
          conj (suzukiCriticalEntryWallBareAmplitude p e : ℂ) = _
  rw [Complex.conj_ofReal]
  have hkernel :
      conj (suzukiOscillatoryKernel ((-t : ℝ) : ℂ)
          (suzukiPrimePowerEntryWallAperture p e)) =
        suzukiOscillatoryKernel (t : ℂ)
          (suzukiPrimePowerEntryWallAperture p e) := by
    simp only [suzukiOscillatoryKernel]
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hkernel]
  ring

/-- The two-height wall kernel is stationary: it is exact positive weight times half-log
difference character. -/
theorem suzukiCriticalWallFieldGramKernel_eq_differenceCharacter
    (t u : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallFieldGramKernel t u p e =
      (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) : ℂ) *
        suzukiOscillatoryKernel ((t - u : ℝ) : ℂ)
          (suzukiPrimePowerEntryWallAperture p e) := by
  rw [suzukiCriticalWallFieldGramKernel]
  have hstar := star_suzukiCriticalWallField_neg (-u) p e
  simp only [neg_neg] at hstar
  rw [hstar, suzukiCriticalWallField_eq_bareAmplitude_mul_kernel,
    suzukiCriticalWallField_eq_bareAmplitude_mul_kernel]
  simp only [suzukiOscillatoryKernel, ofReal_neg, ofReal_sub]
  rw [show
      (suzukiCriticalEntryWallBareAmplitude p e : ℂ) *
            Complex.exp ((suzukiPrimePowerEntryWallAperture p e : ℂ) * (I * (t : ℂ))) *
          ((suzukiCriticalEntryWallBareAmplitude p e : ℂ) *
            Complex.exp ((suzukiPrimePowerEntryWallAperture p e : ℂ) * (I * -(u : ℂ)))) =
        (suzukiCriticalEntryWallBareAmplitude p e : ℂ) ^ (2 : ℕ) *
          Complex.exp ((suzukiPrimePowerEntryWallAperture p e : ℂ) *
            (I * ((t : ℂ) - (u : ℂ)))) by
      calc
        _ = (suzukiCriticalEntryWallBareAmplitude p e : ℂ) ^ (2 : ℕ) *
            (Complex.exp ((suzukiPrimePowerEntryWallAperture p e : ℂ) * (I * (t : ℂ))) *
              Complex.exp ((suzukiPrimePowerEntryWallAperture p e : ℂ) *
                (I * -(u : ℂ)))) := by ring_nf
        _ = _ := by
          rw [← Complex.exp_add]
          congr 1
          ring_nf]
  rw [← ofReal_pow,
    sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]
  push_cast
  rfl

/-! ## Positive diagonal and far anti-diagonal -/

/-- Wall-kernel diagonal is exact positive von-Mangoldt prime-power weight, independent of
height. -/
theorem suzukiCriticalWallFieldGramKernel_diagonal
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallFieldGramKernel t t p e =
      (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
        Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) : ℂ) := by
  rw [suzukiCriticalWallFieldGramKernel_eq_differenceCharacter]
  simp [suzukiOscillatoryKernel]

/-- **Anti-diagonal far-source weld.**  Functional-equation reflection turns Hermitian kernel
into wall-field bilinear square, hence exact far delayed-hinge numerator. -/
theorem suzukiCriticalWallFieldGramKernel_antidiagonal
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallFieldGramKernel t (-t) p e =
      (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) : ℂ) *
        suzukiOscillatoryKernel (t : ℂ)
          (Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) := by
  rw [suzukiCriticalWallFieldGramKernel, star_suzukiCriticalWallField_neg,
    ← pow_two, sq_suzukiCriticalWallField_eq_farHingeNumerator]

/-- Xi-real far delayed-hinge atom is reflected anti-diagonal of positive wall kernel followed by
its fixed quarter-turn and inverse-square multiplier. -/
theorem suzukiCriticalDelayedHingeJumpAtom_eq_neg_I_mul_wallKernel_antidiagonal_div
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalDelayedHingeJumpAtom
        (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ))
        (Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) (t : ℂ) =
      -I * suzukiCriticalWallFieldGramKernel t (-t) p e / (t : ℂ) ^ (2 : ℕ) := by
  rw [suzukiCriticalDelayedHingeJumpAtom_eq_neg_I_mul_wallField_sq_div,
    suzukiCriticalWallFieldGramKernel, star_suzukiCriticalWallField_neg, ← pow_two]

/-! ## Arbitrary finite height packets -/

/-- Finite height sampling matrix of one prime-power wall kernel. -/
def suzukiCriticalWallFieldGramMatrix {N : ℕ}
    (height : Fin N → ℝ) (p : Nat.Primes) (e : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => suzukiCriticalWallFieldGramKernel (height i) (height j) p e

/-- Finite wall matrix is literally Gram of conjugated wall feature packet. -/
theorem suzukiCriticalWallFieldGramMatrix_eq_gram {N : ℕ}
    (height : Fin N → ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallFieldGramMatrix height p e =
      Matrix.gram ℂ
        (fun i => star (suzukiCriticalWallField (height i) p e)) := by
  ext i j
  simp [suzukiCriticalWallFieldGramMatrix, suzukiCriticalWallFieldGramKernel,
    Matrix.gram_apply, RCLike.inner_apply]
  ring

/-- **Finite-packet PSD.**  Every finite height section of prime-power wall kernel is positive
semidefinite; phase-bearing anti-diagonal is restriction of this genuine Gram matrix. -/
theorem suzukiCriticalWallFieldGramMatrix_posSemidef {N : ℕ}
    (height : Fin N → ℝ) (p : Nat.Primes) (e : ℕ) :
    (suzukiCriticalWallFieldGramMatrix height p e).PosSemidef := by
  rw [suzukiCriticalWallFieldGramMatrix_eq_gram]
  exact Matrix.posSemidef_gram ℂ _

/-- The bare critical wall amplitude is strictly positive: its square is the strictly positive
prime-power far-hinge weight. -/
theorem suzukiCriticalEntryWallBareAmplitude_pos (p : Nat.Primes) (e : ℕ) :
    0 < suzukiCriticalEntryWallBareAmplitude p e := by
  have hsq := sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt p e
  have hpos := suzukiCriticalFarHingeWeight_pos p e
  have hsqpos : 0 < suzukiCriticalEntryWallBareAmplitude p e ^ (2 : ℕ) := by rw [hsq]; exact hpos
  have hnn : 0 ≤ suzukiCriticalEntryWallBareAmplitude p e := Real.sqrt_nonneg _
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso; rw [← h] at hsqpos; simp at hsqpos

/-- The critical wall field never vanishes: a strictly positive amplitude times a unimodular
phase. -/
theorem suzukiCriticalWallField_ne_zero (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallField t p e ≠ 0 := by
  rw [suzukiCriticalWallField_eq_bareAmplitude_mul_kernel]
  refine mul_ne_zero ?_ ?_
  · exact_mod_cast (suzukiCriticalEntryWallBareAmplitude_pos p e).ne'
  · simp only [suzukiOscillatoryKernel]
    exact Complex.exp_ne_zero _

/-- The finite wall section is the outer product of the wall feature packet with its conjugate. -/
theorem suzukiCriticalWallFieldGramMatrix_eq_vecMulVec {N : ℕ}
    (height : Fin N → ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallFieldGramMatrix height p e =
      Matrix.vecMulVec (fun i => suzukiCriticalWallField (height i) p e)
        (fun j => star (suzukiCriticalWallField (height j) p e)) := by
  ext i j
  rfl

/-- **Rank at most one.**  Every finite height section of the prime-power wall kernel is an outer
product, hence has rank at most one. -/
theorem suzukiCriticalWallFieldGramMatrix_rank_le_one {N : ℕ}
    (height : Fin N → ℝ) (p : Nat.Primes) (e : ℕ) :
    (suzukiCriticalWallFieldGramMatrix height p e).rank ≤ 1 := by
  rw [suzukiCriticalWallFieldGramMatrix_eq_vecMulVec]
  exact Matrix.rank_vecMulVec_le _ _

/-- **Exact packet square.**  The quadratic form of the finite wall section on a complex packet is
the squared norm of the single scalar overlap the packet has with the wall feature; this is the
identity behind positive semidefiniteness. -/
theorem suzukiCriticalWallFieldGramMatrix_dotProduct_mulVec {N : ℕ}
    (height : Fin N → ℝ) (p : Nat.Primes) (e : ℕ) (c : Fin N → ℂ) :
    star c ⬝ᵥ (suzukiCriticalWallFieldGramMatrix height p e) *ᵥ c =
      ‖∑ i, star (c i) * suzukiCriticalWallField (height i) p e‖ ^ (2 : ℕ) := by
  have expand : star c ⬝ᵥ (suzukiCriticalWallFieldGramMatrix height p e) *ᵥ c
      = ∑ i, ∑ j, (star (c i) * suzukiCriticalWallField (height i) p e) *
          (star (suzukiCriticalWallField (height j) p e) * c j) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.star_apply, suzukiCriticalWallFieldGramMatrix,
      suzukiCriticalWallFieldGramKernel]
    ring
  have hstar : star (∑ i, star (c i) * suzukiCriticalWallField (height i) p e)
      = ∑ j, star (suzukiCriticalWallField (height j) p e) * c j := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [star_mul, star_star]
  rw [expand, ← Finset.sum_mul_sum, ← hstar]
  exact Complex.mul_conj' _

/-- **Rank exactly one.**  A nonempty height section has nonvanishing diagonal, so its rank is
exactly one. -/
theorem suzukiCriticalWallFieldGramMatrix_rank_eq_one {N : ℕ} (hN : 0 < N)
    (height : Fin N → ℝ) (p : Nat.Primes) (e : ℕ) :
    (suzukiCriticalWallFieldGramMatrix height p e).rank = 1 := by
  refine le_antisymm (suzukiCriticalWallFieldGramMatrix_rank_le_one height p e) ?_
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [Matrix.rank] at h0
  have hbot : LinearMap.range (suzukiCriticalWallFieldGramMatrix height p e).mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp h0
  have hmem : (suzukiCriticalWallFieldGramMatrix height p e).mulVecLin
      (Pi.single ⟨0, hN⟩ 1) ∈
        LinearMap.range (suzukiCriticalWallFieldGramMatrix height p e).mulVecLin :=
    LinearMap.mem_range_self _ _
  rw [hbot, Submodule.mem_bot] at hmem
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at hmem
  have hval := congrFun hmem ⟨0, hN⟩
  simp only [Pi.zero_apply] at hval
  rcases mul_eq_zero.mp hval with h | h
  · exact suzukiCriticalWallField_ne_zero _ p e h
  · exact suzukiCriticalWallField_ne_zero _ p e (star_eq_zero.mp h)

/-! ## Sharp marked-tensor rooted completion -/

/-- Positive diagonal wall mass supplies exact minimal `d^(2 : ℕ)` rooted completion to one scaled
marked Lorentz coordinate. -/
theorem suzukiMarkedSecant_wallAmplitude_minimalRootedCompletion_eq
    (m d r s : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiMarkedSecantSymmetricForm m d
          (suzukiCriticalEntryWallBareAmplitude p e * r)
          (suzukiCriticalEntryWallBareAmplitude p e * s)
          (suzukiCriticalEntryWallBareAmplitude p e * r)
          (suzukiCriticalEntryWallBareAmplitude p e * s) +
        d ^ (2 : ℕ) * (suzukiCriticalEntryWallBareAmplitude p e * s) ^ (2 : ℕ) =
      (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ)) *
        (r - m * s) ^ (2 : ℕ) := by
  rw [suzukiMarkedSecant_minimalRootedCompletion_eq_square]
  rw [show suzukiCriticalEntryWallBareAmplitude p e * r -
      m * (suzukiCriticalEntryWallBareAmplitude p e * s) =
      suzukiCriticalEntryWallBareAmplitude p e * (r - m * s) by ring]
  rw [mul_pow,
    sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]

/-- Wall-amplitude minimal rooted completion is nonnegative for every real marked coordinate. -/
theorem suzukiMarkedSecant_wallAmplitude_minimalRootedCompletion_nonneg
    (m d r s : ℝ) (p : Nat.Primes) (e : ℕ) :
    0 ≤ suzukiMarkedSecantSymmetricForm m d
          (suzukiCriticalEntryWallBareAmplitude p e * r)
          (suzukiCriticalEntryWallBareAmplitude p e * s)
          (suzukiCriticalEntryWallBareAmplitude p e * r)
          (suzukiCriticalEntryWallBareAmplitude p e * s) +
        d ^ (2 : ℕ) * (suzukiCriticalEntryWallBareAmplitude p e * s) ^ (2 : ℕ) := by
  rw [suzukiMarkedSecant_wallAmplitude_minimalRootedCompletion_eq]
  rw [← sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

end

end RHTower
