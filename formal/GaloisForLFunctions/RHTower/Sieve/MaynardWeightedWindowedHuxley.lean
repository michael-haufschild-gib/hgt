import GaloisForLFunctions.RHTower.Sieve.HuxleyWindowDecomposition
import GaloisForLFunctions.RHTower.Sieve.MaynardWeightedEnergy

/-!
# Windowed Huxley for raised fixed-width Maynard factors

This is the support-aware weighted interface to `HuxleyWindowDecomposition`.  Unlike the absorbed
global theorem, it permits a raised factor below Huxley's square scale: absorption is checked on
short ordinate windows and the exact number of windows remains in the conclusion.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped InnerProductSpace

/-- Raised fixed-width Huxley theorem with weighted energy and short ordinate windows. -/
theorem huxley_raised_fixedWidth_factor_large_values_finset_weighted_windowed
    {N A w ell K : ℕ} (hA : 1 ≤ A) (a : Fin N → ℂ)
    (hsupp : ∀ n : Fin N, a n ≠ 0 →
      A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ A * 2 ^ w)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (Graw : ℝ) (henergy : ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2 ≤ Graw)
    (U B : Fin (w * ell + 1) → ℝ)
    {S : Finset ℕ} (hS : S ⊆ Finset.range K)
    {lam : ℕ → ℝ} {delta T W V : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T) (hW : 0 < W) (hV : 0 < V)
    (hU : ∀ q : Fin (w * ell + 1), 0 < U q)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, 0 ≤ lam r ∧ lam r ≤ T)
    (hnear : ∀ q : Fin (w * ell + 1),
      3 * U q ≤ 4 * Real.pi * ((A ^ ell * 2 ^ (q : ℕ) : ℕ) : ℝ))
    (hlamW : ∀ q : Fin (w * ell + 1),
      logDyadicLambda (A ^ ell * 2 ^ (q : ℕ)) W ≤ 1)
    (hB : ∀ q : Fin (w * ell + 1),
      logDyadicSecondEnvelope (A ^ ell * 2 ^ (q : ℕ)) (U q) W ≤ B q)
    (hB1 : ∀ q : Fin (w * ell + 1), 1 ≤ B q)
    (hlarge : ∀ r ∈ S, V ≤ ‖raisedDirichletValue N ell a sigma (lam r)‖)
    (habsorb : ((w * ell + 1 : ℕ) : ℝ) *
      ∑ q : Fin (w * ell + 1),
        (((((A ^ ell * 2 ^ (q : ℕ) : ℕ) : ℝ)) ^ (-sigma)) ^ 2 * Graw) * B q
          ≤ V ^ 2 / 2) :
    (S.card : ℝ) * V ^ 2 ≤
      (huxleyWindowCount T W : ℝ) *
        (2 * ((w * ell + 1 : ℕ) : ℝ) * ∑ q : Fin (w * ell + 1),
          ((((A ^ ell * 2 ^ (q : ℕ) : ℕ) : ℝ)) ^ (-sigma)) ^ 2 * Graw *
            ((((A ^ ell * 2 ^ (q : ℕ) : ℕ) : ℝ)) +
              (12 * Real.pi * (((A ^ ell * 2 ^ (q : ℕ) : ℕ) : ℝ)) / delta) *
                ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))) := by
  let D : Fin (w * ell + 1) → ℕ := fun q => A ^ ell * 2 ^ (q : ℕ)
  let c : ∀ q : Fin (w * ell + 1), EuclideanSpace ℂ (Fin (D q)) := fun q =>
    dyadicWeightedCoeff (N ^ ell) (convPow N ell a) sigma (D q)
  let G : Fin (w * ell + 1) → ℝ := fun q =>
    ((D q : ℝ) ^ (-sigma)) ^ 2 * Graw
  have hD : ∀ q, 1 ≤ D q := by
    intro q
    dsimp only [D]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero ell (by omega)) (pow_ne_zero (q : ℕ) (by norm_num)))
  have hmass : ∀ q, ‖c q‖ ^ 2 ≤ G q := by
    intro q
    exact (norm_dyadicWeightedCoeff_sq_le_edge_weight
      (N ^ ell) (D q) (convPow N ell a) hsigma (hD q)).trans
        (mul_le_mul_of_nonneg_left henergy (sq_nonneg _))
  have hbig : ∀ r ∈ S,
      V ≤ ∑ q : Fin (w * ell + 1), ‖⟪dyadicDirRow (D q) (lam r), c q⟫_ℂ‖ := by
    intro r hr
    exact (hlarge r hr).trans
      (norm_raisedDirichletValue_le_sum_fixedWidth_dyadic hA a hsupp sigma (lam r))
  have habsorb' : (Fintype.card (Fin (w * ell + 1)) : ℝ) *
      ∑ q : Fin (w * ell + 1), G q * B q ≤ V ^ 2 / 2 := by
    simpa only [G, D, Fintype.card_fin] using habsorb
  simpa only [D, c, G, Fintype.card_fin] using
    huxley_multiblock_large_values_finset_windowed D hD c G U B hS
      hdelta hT hW hV hmass hU hgap hband hnear hlamW hB hB1 hbig habsorb'

/-- Literal grouped Heath--Brown product with local Huxley absorption and exact window loss. -/
theorem huxley_heathBrown_grouped_large_values_finset_weighted_windowed
    {ι : Type*} [Fintype ι] (L X ell K : ℕ)
    (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (Graw : ℝ)
    (henergy : ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
      ‖convPow (groupedDyadicUpper q) ell
        (groupedDyadicCoeffVector (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2 ≤ Graw)
    (U B : Fin (Fintype.card ι * ell + 1) → ℝ)
    {S : Finset ℕ} (hS : S ⊆ Finset.range K)
    {lam : ℕ → ℝ} {delta T W V : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T) (hW : 0 < W) (hV : 0 < V)
    (hU : ∀ r : Fin (Fintype.card ι * ell + 1), 0 < U r)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, 0 ≤ lam r ∧ lam r ≤ T)
    (hnear : ∀ r : Fin (Fintype.card ι * ell + 1),
      3 * U r ≤ 4 * Real.pi *
        (((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ))
    (hlamW : ∀ r : Fin (Fintype.card ι * ell + 1),
      logDyadicLambda ((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ)) W ≤ 1)
    (hB : ∀ r : Fin (Fintype.card ι * ell + 1),
      logDyadicSecondEnvelope
        ((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ)) (U r) W ≤ B r)
    (hB1 : ∀ r : Fin (Fintype.card ι * ell + 1), 1 ≤ B r)
    (hlarge : ∀ r ∈ S,
      V ≤ ‖(∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (kind i)) (q i)))
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell‖)
    (habsorb : ((Fintype.card ι * ell + 1 : ℕ) : ℝ) *
      ∑ r : Fin (Fintype.card ι * ell + 1),
        ((((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) ^ (-sigma)) ^ 2 *
          Graw) * B r ≤ V ^ 2 / 2) :
    (S.card : ℝ) * V ^ 2 ≤
      (huxleyWindowCount T W : ℝ) *
        (2 * ((Fintype.card ι * ell + 1 : ℕ) : ℝ) *
          ∑ r : Fin (Fintype.card ι * ell + 1),
            (((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) ^ (-sigma)) ^ 2 *
              Graw * (((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) +
                (12 * Real.pi *
                  ((((groupedDyadicLower q) ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) / delta) *
                  ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))) := by
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
  exact huxley_raised_fixedWidth_factor_large_values_finset_weighted_windowed
    (one_le_groupedDyadicLower q) avec hsupp hsigma Graw henergy U B hS
      hdelta hT hW hV hU hgap hband hnear hlamW hB hB1 hlarge' habsorb

end RHTower.Sieve
