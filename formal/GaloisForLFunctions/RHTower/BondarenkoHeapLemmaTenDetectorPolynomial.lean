/-
# Bondarenko--Heap Lemma 10: finite detector polynomial

This is the exact finite algebra behind the beginning of the zero detector in
Lemma 10 of Bondarenko--Heap, *Long Dirichlet polynomials, mean values of
character sums, and zero density estimates* (arXiv:2608.07399v1).

Chen--Gupta--Li Section 12 defines the truncated Möbius inverse coefficients
`c_n = \sum_{d \mid n, d \le X} \mu(d)`. With the inclusive cutoff convention
used by `zeroDetectionMobiusCoefficient`, the initial finite Dirichlet
polynomial has only its `n = 1` term and is therefore exactly `1`.
-/

import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaTenZeroDetection

open ArithmeticFunction

noncomputable section

namespace RHTower

/-- The finite initial Möbius detector polynomial. It is the algebraic
part of the zero-detection identity used in Bondarenko--Heap Lemma 10. -/
def zeroDetectionInitialPolynomial (X q : ℕ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (X + 1),
    (zeroDetectionMobiusCoefficient X n : ℂ) * χ n * (n : ℂ) ^ (-s)

/-- The finite initial Möbius detector polynomial is identically one.

No analytic continuation or hypothesis on `s` is used: this is an exact
finite divisor-sum cancellation. -/
theorem zeroDetectionInitialPolynomial_eq_one (X q : ℕ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    zeroDetectionInitialPolynomial X q χ s = 1 := by
  unfold zeroDetectionInitialPolynomial
  have hmem : 1 ∈ Finset.Icc 1 (X + 1) := by
    simp
  rw [Finset.sum_eq_single 1]
  · simp [zeroDetectionMobiusCoefficient_one]
  · intro n hn hn1
    have hnlo : 2 ≤ n := by
      rw [Finset.mem_Icc] at hn
      omega
    let k : Fin X := ⟨n - 2, by
      rw [Finset.mem_Icc] at hn
      omega⟩
    have hnk : n = k.1 + 2 := by
      dsimp [k]
      omega
    rw [hnk, zeroDetectionMobiusCoefficient_vanishes_below_cutoff]
    simp
  · simp

end RHTower
