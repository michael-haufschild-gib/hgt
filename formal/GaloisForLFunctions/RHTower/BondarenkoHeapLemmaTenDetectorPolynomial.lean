/-
# Bondarenko--Heap Lemma 10: finite detector polynomial

This is an auxiliary exact finite cancellation extracted from the coefficient
algebra behind the zero detector in Lemma 10 of Bondarenko--Heap, *Long
Dirichlet polynomials, mean values of character sums, and zero density
estimates* (arXiv:2608.07399v1).

Chen--Gupta--Li Section 12 defines the truncated Möbius inverse coefficients
`c_n = \sum_{d \mid n, d \le X} \mu(d)`. With the inclusive cutoff convention
used by `zeroDetectionMobiusCoefficient`, the auxiliary polynomial formed from
those coefficients has only its `n = 1` term and is therefore exactly `1`.
It is not the truncated Möbius polynomial `M_X(s, χ)` itself; that genuine
finite product is formalized separately.
-/

import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaTenZeroDetection

open ArithmeticFunction

noncomputable section

namespace RHTower

/-- An auxiliary finite polynomial made from the product coefficients.
It records their closed divisor-sum cancellation, not the `M_X` factor itself. -/
def zeroDetectionInitialPolynomial (X q : ℕ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (X + 1),
    (zeroDetectionMobiusCoefficient X n : ℂ) * χ n * (n : ℂ) ^ (-s)

/-- The auxiliary finite coefficient polynomial is identically one.

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
