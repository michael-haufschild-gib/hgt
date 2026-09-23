import GaloisForLFunctions.RHTower.Sieve.MaynardGroupedFactor
import GaloisForLFunctions.RHTower.Sieve.MaynardAllShortHuxley

/-!
# Literal all-short Maynard large-values case

This capstone instantiates the raised fixed-width Huxley theorem with a literal grouped family of
Heath--Brown dyadic factors.  The large-value hypothesis is stated directly for the product of the
individual Möbius, zeta, and logarithmic L-series.  Coefficient energy is the only numerical input;
`MaynardGroupedFactor` supplies it unconditionally with arbitrarily small power loss.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped InnerProductSpace

/-- **Literal grouped-product Huxley estimate.** -/
theorem huxley_heathBrown_grouped_large_values
    {ι : Type*} [Fintype ι] (L X ell : ℕ)
    (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (G : ℝ)
    (henergy : ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
      ‖convPow (groupedDyadicUpper q) ell
        (groupedDyadicCoeffVector (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ (2 : ℕ) ≤ G)
    (U B : Fin (Fintype.card ι * ell + 1) → ℝ)
    {lam : ℕ → ℝ} {delta T V : ℝ}
    (hdelta : 0 < delta) (hV : 0 < V)
    (hU : ∀ r : Fin (Fintype.card ι * ell + 1), 0 < U r)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hnear : ∀ r : Fin (Fintype.card ι * ell + 1),
      3 * U r ≤ 4 * Real.pi *
        (((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ))
    (hlamT : ∀ r : Fin (Fintype.card ι * ell + 1),
      logDyadicLambda ((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ)) T ≤ 1)
    (hB : ∀ r : Fin (Fintype.card ι * ell + 1),
      logDyadicSecondEnvelope
        ((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ)) (U r) T ≤ B r)
    (hB1 : ∀ r : Fin (Fintype.card ι * ell + 1), 1 ≤ B r)
    (R : ℕ)
    (hdiam : ∀ r ∈ Finset.range (R + 1), ∀ s ∈ Finset.range (R + 1),
      |lam s - lam r| ≤ T)
    (hlarge : ∀ r ∈ Finset.range (R + 1),
      V ≤ ‖(∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (kind i)) (q i)))
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell‖)
    (habsorb : ((Fintype.card ι * ell + 1 : ℕ) : ℝ) *
      ∑ r : Fin (Fintype.card ι * ell + 1), G * B r ≤ V ^ (2 : ℕ) / 2) :
    ((R : ℝ) + 1) * V ^ (2 : ℕ)
      ≤ 2 * ((Fintype.card ι * ell + 1 : ℕ) : ℝ) *
        ∑ r : Fin (Fintype.card ι * ell + 1),
          G * (((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) +
            (12 * Real.pi *
              ((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) / delta) *
              ∑ i ∈ Finset.range (R + 1), 1 / ((i : ℝ) + 1)) := by
  let F : ι → ArithmeticFunction ℝ := fun i => heathBrownFactorBase L X (kind i)
  let a : Fin (groupedDyadicUpper q) → ℂ := groupedDyadicCoeffVector F q
  have hsupp : ∀ n : Fin (groupedDyadicUpper q), a n ≠ 0 →
      groupedDyadicLower q ≤ (n : ℕ) + 1 ∧
        (n : ℕ) + 1 ≤ groupedDyadicLower q * 2 ^ Fintype.card ι := by
    intro n hn
    exact groupedDyadicCoeffVector_support_fixedWidth F q n hn
  have hlarge' : ∀ r ∈ Finset.range (R + 1),
      V ≤ ‖raisedDirichletValue (groupedDyadicUpper q) ell a sigma (lam r)‖ := by
    intro r hr
    rw [show raisedDirichletValue (groupedDyadicUpper q) ell a sigma (lam r) =
      (∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (kind i)) (q i)))
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell by
        exact raised_groupedDyadicValue_eq_product_pow
          (fun i => heathBrownFactorBase L X (kind i)) q ell sigma (lam r)]
    exact hlarge r hr
  exact huxley_raised_fixedWidth_factor_large_values
    (one_le_groupedDyadicLower q) a hsupp hsigma G henergy U B
    hdelta hV hU hgap hnear hlamT hB hB1 R hdiam hlarge' habsorb

/-- With `k=60` and the sharpened raising cap `ell<=51`, even a maximal `2k`-factor group uses at
most 6121 simultaneous Huxley blocks. -/
theorem maynard_grouped_huxley_block_count_le
    {w ell : ℕ} (hw : w ≤ 120) (hell : ell ≤ 51) :
    w * ell + 1 ≤ 6121 := by
  have hmul := Nat.mul_le_mul hw hell
  omega

end RHTower.Sieve
