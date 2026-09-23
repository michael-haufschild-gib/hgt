import GaloisForLFunctions.RHTower.Sieve.HuxleyFiniteSetLargeValues
import GaloisForLFunctions.RHTower.Sieve.MaynardAllShortCase

/-!
# Literal all-short Huxley estimate on selected color fibres

This is the exact analytic consumer for uniform aggregate counting.  It combines arbitrary-finset
Huxley with the raised fixed-width decomposition and then instantiates the coefficients with one
literal grouped Heath--Brown factor.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped InnerProductSpace

/-- Raised fixed-width Huxley theorem on an arbitrary subset of an ambient separated range. -/
theorem huxley_raised_fixedWidth_factor_large_values_finset
    {N A w ell K : ℕ} (hA : 1 ≤ A) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ A * 2 ^ w)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (G : ℝ) (henergy : ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ (2 : ℕ) ≤ G)
    (U B : Fin (w * ell + 1) → ℝ)
    {S : Finset ℕ} (hS : S ⊆ Finset.range K)
    {lam : ℕ → ℝ} {delta T V : ℝ}
    (hdelta : 0 < delta) (hV : 0 < V)
    (hU : ∀ q : Fin (w * ell + 1), 0 < U q)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hnear : ∀ q : Fin (w * ell + 1),
      3 * U q ≤ 4 * Real.pi * ((A ^ ell * 2 ^ (q : ℕ) : ℕ) : ℝ))
    (hlamT : ∀ q : Fin (w * ell + 1),
      logDyadicLambda (A ^ ell * 2 ^ (q : ℕ)) T ≤ 1)
    (hB : ∀ q : Fin (w * ell + 1),
      logDyadicSecondEnvelope (A ^ ell * 2 ^ (q : ℕ)) (U q) T ≤ B q)
    (hB1 : ∀ q : Fin (w * ell + 1), 1 ≤ B q)
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T)
    (hlarge : ∀ r ∈ S, V ≤ ‖raisedDirichletValue N ell a sigma (lam r)‖)
    (habsorb : ((w * ell + 1 : ℕ) : ℝ) *
      ∑ q : Fin (w * ell + 1), G * B q ≤ V ^ (2 : ℕ) / 2) :
    (S.card : ℝ) * V ^ (2 : ℕ) ≤
      2 * ((w * ell + 1 : ℕ) : ℝ) * ∑ q : Fin (w * ell + 1),
        G * ((((A ^ ell * 2 ^ (q : ℕ) : ℕ) : ℝ)) +
          (12 * Real.pi * (((A ^ ell * 2 ^ (q : ℕ) : ℕ) : ℝ)) / delta) *
            ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)) := by
  let D : Fin (w * ell + 1) → ℕ := fun q => A ^ ell * 2 ^ (q : ℕ)
  let c : ∀ q : Fin (w * ell + 1), EuclideanSpace ℂ (Fin (D q)) := fun q =>
    dyadicWeightedCoeff (N ^ ell) (convPow N ell a) sigma (D q)
  have hD : ∀ q, 1 ≤ D q := by
    intro q
    dsimp [D]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero ell (by omega)) (pow_ne_zero (q : ℕ) (by norm_num)))
  have hmass : ∀ q, ‖c q‖ ^ (2 : ℕ) ≤ G := by
    intro q
    exact (norm_dyadicWeightedCoeff_sq_le _ _ _ hsigma (hD q)).trans henergy
  have hbig : ∀ r ∈ S,
      V ≤ ∑ q : Fin (w * ell + 1), ‖⟪dyadicDirRow (D q) (lam r), c q⟫_ℂ‖ := by
    intro r hr
    exact (hlarge r hr).trans
      (norm_raisedDirichletValue_le_sum_fixedWidth_dyadic hA a hsupp sigma (lam r))
  have habsorb' : (Fintype.card (Fin (w * ell + 1)) : ℝ) *
      ∑ q : Fin (w * ell + 1), G * B q ≤ V ^ (2 : ℕ) / 2 := by
    simpa using habsorb
  simpa [D, c] using huxley_multiblock_large_values_finset D hD c
    (fun _ => G) U B hS hdelta hV hmass hU hgap hnear hlamT hB hB1
    hdiam hbig habsorb'

/-- Literal grouped Heath--Brown Huxley estimate on one box/group color fibre. -/
theorem huxley_heathBrown_grouped_large_values_finset
    {ι : Type*} [Fintype ι] (L X ell K : ℕ)
    (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (G : ℝ)
    (henergy : ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
      ‖convPow (groupedDyadicUpper q) ell
        (groupedDyadicCoeffVector (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ (2 : ℕ) ≤ G)
    (U B : Fin (Fintype.card ι * ell + 1) → ℝ)
    {S : Finset ℕ} (hS : S ⊆ Finset.range K)
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
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T)
    (hlarge : ∀ r ∈ S,
      V ≤ ‖(∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (kind i)) (q i)))
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell‖)
    (habsorb : ((Fintype.card ι * ell + 1 : ℕ) : ℝ) *
      ∑ r : Fin (Fintype.card ι * ell + 1), G * B r ≤ V ^ (2 : ℕ) / 2) :
    (S.card : ℝ) * V ^ (2 : ℕ) ≤
      2 * ((Fintype.card ι * ell + 1 : ℕ) : ℝ) *
        ∑ r : Fin (Fintype.card ι * ell + 1),
          G * (((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) +
            (12 * Real.pi *
              ((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) / delta) *
              ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)) := by
  let F : ι → ArithmeticFunction ℝ := fun i => heathBrownFactorBase L X (kind i)
  let avec : Fin (groupedDyadicUpper q) → ℂ := groupedDyadicCoeffVector F q
  have hsupp : ∀ n : Fin (groupedDyadicUpper q), avec n ≠ 0 →
      groupedDyadicLower q ≤ (n : ℕ) + 1 ∧
        (n : ℕ) + 1 ≤ groupedDyadicLower q * 2 ^ Fintype.card ι := by
    intro n hn
    exact groupedDyadicCoeffVector_support_fixedWidth F q n hn
  have hlarge' : ∀ r ∈ S,
      V ≤ ‖raisedDirichletValue (groupedDyadicUpper q) ell avec sigma (lam r)‖ := by
    intro r hr
    rw [show raisedDirichletValue (groupedDyadicUpper q) ell avec sigma (lam r) =
      (∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (kind i)) (q i)))
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell by
        exact raised_groupedDyadicValue_eq_product_pow
          (fun i => heathBrownFactorBase L X (kind i)) q ell sigma (lam r)]
    exact hlarge r hr
  exact huxley_raised_fixedWidth_factor_large_values_finset
    (one_le_groupedDyadicLower q) avec hsupp hsigma G henergy U B hS
    hdelta hV hU hgap hnear hlamT hB hB1 hdiam hlarge' habsorb

end RHTower.Sieve
