import GaloisForLFunctions.RHTower.ConstrainedProlateLadderExactTransfer

/-!
# Exact prime-scale form of the constrained-prolate ladder

The exact infinite-dimensional Fuchs-model ladder is naturally parametrized by the aperture
`λ`, while the prime-scale variable in the card is `X = λ²`.  This module performs that change of
variables without replacing the exact secular root by a two-mode approximation.  Thus the existing
adjacent-rung `λ⁸` law becomes the literal `X⁴` law for the same depth roots.
-/

open Filter

namespace RHTower

/-- Reparametrize an eighth-power asymptotic by `X = λ²`. -/
theorem tendsto_div_pow_four_comp_sqrt_of_div_pow_eight
    {f : ℝ → ℝ} {L : ℝ}
    (h : Tendsto (fun lam : ℝ => f lam / lam ^ 8) atTop (nhds L)) :
    Tendsto (fun X : ℝ => f (Real.sqrt X) / X ^ 4) atTop (nhds L) := by
  have hs := h.comp Real.tendsto_sqrt_atTop
  refine hs.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  have hsqrt : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
  have hpow : Real.sqrt X ^ 8 = X ^ 4 := by
    calc
      Real.sqrt X ^ 8 = (Real.sqrt X ^ 2) ^ 4 := by ring
      _ = X ^ 4 := by rw [hsqrt]
  change f (Real.sqrt X) / Real.sqrt X ^ 8 = f (Real.sqrt X) / X ^ 4
  rw [hpow]

/-- Exact adjacent-rung prime-scale law for the infinite-dimensional constrained Fuchs roots:
after `X = λ²`, the ratio of the depth-`k+1` and depth-`k` roots grows like `X⁴` with the explicit
Hermite/Fuchs coefficient. -/
theorem ccm_fuchsModel_ladder_adjacent_primeScale_tendsto
    {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C) (k : ℕ)
    (hgrow2 : ∀ j, A (k + 2) ≤ C ^ j * A (j + (k + 2)))
    (hgrow3 : ∀ j, A (k + 3) ≤ C ^ j * A (j + (k + 3)))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 2 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j))) :
    Tendsto (fun X : ℝ =>
      (depthSecularRoot
          (fun j => fuchsRate (A j) (4 * j) (Real.sqrt X))
          (ℓ (Real.sqrt X)) (k + 1) /
        depthSecularRoot
          (fun j => fuchsRate (A j) (4 * j) (Real.sqrt X))
          (ℓ (Real.sqrt X)) k) / X ^ 4)
      atTop (nhds ((constrainedProlateHermiteTheta (k + 1) /
        constrainedProlateHermiteTheta k) * (A (k + 2) / A (k + 1)))) := by
  exact tendsto_div_pow_four_comp_sqrt_of_div_pow_eight
    (ccm_fuchsModel_ladder_adjacent_scaled_ratio_tendsto
      hA hC k hgrow2 hgrow3 hsum hbessel hl)

end RHTower
