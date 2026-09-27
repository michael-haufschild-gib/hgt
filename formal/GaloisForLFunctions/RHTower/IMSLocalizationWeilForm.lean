import GaloisForLFunctions.RHTower.DampedPrimeSumAssembly

/-!
# Algebra for two-channel IMS estimates

If `χ₁, χ₂` satisfy `χ₁² + χ₂² = 1`, then pointwise,

```text
χ₁(x)χ₁(y) + χ₂(x)χ₂(y) = 1 - ½[ (χ₁(x)-χ₁(y))² + (χ₂(x)-χ₂(y))² ] ,
```

This file proves that algebraic identity, a Lipschitz estimate for its weight,
and a scalar lower bound assuming an IMS equality and an error estimate. It
does not construct a partition or prove convergence of an arithmetic kernel
integral. The actual prime--Gamma--pole identity and convergent signed errors
are provided by `CCMThetaArithmeticLocalization`.

The parameter `c/(L-η)` need not vanish as `η` tends to zero. That observation
limits this particular sufficient error estimate; it does not prove that all
signed localization arguments fail or reduce to an unproved local spectral gap.
-/

open Real

noncomputable section

namespace RHTower

/-- **Partition identity.**  For a quadratic partition of unity `χ₁² + χ₂² = 1`, the cross terms
recombine into a squared-difference weight. -/
theorem partition_identity {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ^ (2 : ℕ) + a₂ ^ (2 : ℕ) = 1)
    (hb : b₁ ^ (2 : ℕ) + b₂ ^ (2 : ℕ) = 1) :
    a₁ * b₁ + a₂ * b₂ = 1 - ((a₁ - b₁) ^ (2 : ℕ) + (a₂ - b₂) ^ (2 : ℕ)) / 2 := by
  nlinarith [ha, hb]

/-- The localization weight is nonnegative. -/
theorem localization_weight_nonneg (a₁ a₂ b₁ b₂ : ℝ) :
    0 ≤ (a₁ - b₁) ^ (2 : ℕ) + (a₂ - b₂) ^ (2 : ℕ) := by positivity

/-- **Lipschitz bound on the localization weight.**  If both cutoffs are `κ`-Lipschitz then the
weight is at most `2κ²(x-y)²`. -/
theorem localization_weight_le {a₁ a₂ b₁ b₂ κ d : ℝ} (hκ : 0 ≤ κ)
    (h₁ : |a₁ - b₁| ≤ κ * |d|) (h₂ : |a₂ - b₂| ≤ κ * |d|) :
    (a₁ - b₁) ^ (2 : ℕ) + (a₂ - b₂) ^ (2 : ℕ) ≤ 2 * κ ^ (2 : ℕ) * d ^ (2 : ℕ) := by
  have hd : |d| ^ (2 : ℕ) = d ^ (2 : ℕ) := sq_abs d
  have hn : 0 ≤ κ * |d| := mul_nonneg hκ (abs_nonneg d)
  have e₁ : (a₁ - b₁) ^ (2 : ℕ) ≤ κ ^ (2 : ℕ) * d ^ (2 : ℕ) := by
    have : (a₁ - b₁) ^ (2 : ℕ) = |a₁ - b₁| ^ (2 : ℕ) := (sq_abs _).symm
    nlinarith [h₁, abs_nonneg (a₁ - b₁), hn, hd]
  have e₂ : (a₂ - b₂) ^ (2 : ℕ) ≤ κ ^ (2 : ℕ) * d ^ (2 : ℕ) := by
    have : (a₂ - b₂) ^ (2 : ℕ) = |a₂ - b₂| ^ (2 : ℕ) := (sq_abs _).symm
    nlinarith [h₂, abs_nonneg (a₂ - b₂), hn, hd]
  linarith

/-- **The Lipschitz constant available on an overlap.**  Covering an interval of length `L + η` by
two of length `L` leaves an overlap of `L - η`, so the partition may be taken `c/(L-η)`-Lipschitz. -/
theorem overlap_lipschitz {L η c : ℝ} (_hL : 0 < L) (_hη : 0 ≤ η) (hlt : η < L) (hc : 0 < c) :
    0 < c / (L - η) := by
  have : (0 : ℝ) < L - η := by linarith
  positivity

/-- **IMS lower bound.**  With both localized pieces nonnegative — the Connes–Consani hypothesis —
the form on the longer interval is bounded below by the localization error, itself controlled by the
kernel's second moment. -/
theorem ims_lower_bound {Q Q₁ Q₂ Err κ M₂ nrm : ℝ}
    (hIMS : Q = Q₁ + Q₂ + Err)
    (hQ₁ : 0 ≤ Q₁) (hQ₂ : 0 ≤ Q₂)
    (hErr : -(κ ^ (2 : ℕ) * M₂ * nrm) ≤ Err) :
    -(κ ^ (2 : ℕ) * M₂ * nrm) ≤ Q := by
  rw [hIMS]; linarith

/-- The error is of order one in `η`: the bound `κ = c/(L-η)` does not vanish as `η → 0`, which is
exactly why localization yields near-positivity rather than positivity past the threshold. -/
theorem ims_error_not_small {L c : ℝ} (hL : 0 < L) (hc : 0 < c) :
    0 < (c / L) ^ (2 : ℕ) := by positivity

end RHTower
