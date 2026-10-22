import GaloisForLFunctions.ArithmeticIncidencePositivity.TranslatePairingCalculus

/-!
# The squarefree incidence positivity

The coupling law of two shifts is the square of `(1 − λT_a)(1 − μT_b)` applied to a test. Taking a
product over a whole finite set of shifts gives one term per **subset**: the signed combination

    Σ_{S ⊆ s} (−1)^{|S|} (Π_{i ∈ S} λ_i) F(· + Σ_{i ∈ S} a_i),

whose self-pairing is nonnegative. At `a i = log p i` the shifts `Σ_{i ∈ S} a i` are the logarithms
of the **squarefree divisors** of `Π_{i ∈ s} p i`, and the lags of the resulting quadratic form are
the logarithms of their ratios. So the whole incidence lattice of a squarefree modulus constrains
the charges of its primes simultaneously, with weights the allocation may choose freely: one subset
per vertex, one ratio per pair. The cases `|s| = 1, 2` are the one-shift bound
`2λ A(a) ≤ (1+λ²) A(0)` and the two-shift coupling law.
-/

open MeasureTheory
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {F : ℝ → ℝ}

/-- The signed squarefree combination of translates: one term per subset `S ⊆ s`, with weight
`(−1)^{|S|} Π_{i ∈ S} λ_i` at the shift `Σ_{i ∈ S} a_i`. -/
def squarefreeComb {ι : Type*} (F : ℝ → ℝ) (s : Finset ι) (lam a : ι → ℝ) : ℝ → ℝ :=
  finsetComb F s.powerset (fun S => (-1) ^ S.card * ∏ i ∈ S, lam i) (fun S => ∑ i ∈ S, a i)

/-- **The squarefree incidence positivity.** For every finite family of shifts with weights,

    0 ≤ Σ_{S, T ⊆ s} (−1)^{|S|+|T|} (Π_{i∈S} λ_i)(Π_{j∈T} λ_j) A(Σ_{j∈T} a_j − Σ_{i∈S} a_i).

At `a i = log p i` the lags are the logarithms of the ratios of the squarefree divisors of
`Π_{i ∈ s} p i`: the incidence lattice of a squarefree modulus constrains all its prime charges at
once. -/
theorem squarefree_incidence_nonneg {ι : Type*} (hF : Continuous F) (hFc : HasCompactSupport F)
    (s : Finset ι) (lam a : ι → ℝ) :
    0 ≤ ∑ S ∈ s.powerset, ∑ T ∈ s.powerset,
      ((-1) ^ S.card * ∏ i ∈ S, lam i) * ((-1) ^ T.card * ∏ j ∈ T, lam j)
        * autoCorr F ((∑ j ∈ T, a j) - ∑ i ∈ S, a i) := by
  have h := testPairing_self_nonneg (squarefreeComb F s lam a)
  rwa [squarefreeComb, testPairing_finsetComb ⟨hF, hFc⟩] at h

/-- The one-shift case of the same square: `2λ A(t) ≤ (1 + λ²) A(0)`, the trivial bound at
`λ = 1`. -/
theorem two_mul_autoCorr_le (hF : Continuous F) (hFc : HasCompactSupport F) (lam t : ℝ) :
    2 * lam * autoCorr F t ≤ (1 + lam ^ 2) * autoCorr F 0 := by
  have hFn : ContCompact F := ⟨hF, hFc⟩
  have h := testPairing_self_nonneg (fun u => F u - lam * F (u + t))
  rw [testPairing_sub_smul_sub_smul hFn (hFn.translate t) hFn (hFn.translate t) lam,
    testPairing_self_eq_autoCorr_zero, testPairing_translate F F t,
    testPairing_self_eq_autoCorr_zero, testPairing_comm (fun u => F (u + t)) F,
    show testPairing F (fun u => F (u + t)) = autoCorr F t from rfl] at h
  nlinarith [h]

end GaloisForLFunctions.ArithmeticIncidencePositivity
