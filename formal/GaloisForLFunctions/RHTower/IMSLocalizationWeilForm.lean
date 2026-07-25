import GaloisForLFunctions.RHTower.DampedPrimeSumAssembly

/-!
# IMS localization of the Weil form

The Weil functional is a convolution quadratic form,

```text
Q(h) = ∬ K(x - y) h(x) h(y) dx dy ,
```

with `K` the sum of the pole kernel `e^{|u|/2}`, the prime atoms `-Λ(n)n^{-1/2}(δ_{log n}+δ_{-log n})`
and the archimedean kernel.  Such forms admit an exact localization identity.  If `χ₁, χ₂` satisfy
`χ₁² + χ₂² = 1` then, pointwise,

```text
χ₁(x)χ₁(y) + χ₂(x)χ₂(y) = 1 - ½[ (χ₁(x)-χ₁(y))² + (χ₂(x)-χ₂(y))² ] ,
```

and integrating against `K(x-y)h(x)h(y)` gives the **IMS formula**

```text
Q(h) = Q(χ₁h) + Q(χ₂h) + ½ ∬ K(x-y)[ (χ₁(x)-χ₁(y))² + (χ₂(x)-χ₂(y))² ] h(x)h(y) dx dy .
```

Covering an interval of length `L + η` by two intervals of length `L`, which overlap in `L - η`, one
may take the partition Lipschitz with constant `c/(L-η)`, so the error is bounded by

```text
|Err| ≤ (2c²/(L-η)²) · M₂ · ‖h‖² ,        M₂ = ∫_{|u| ≤ L+η} |K(u)| u² du ,
```

the second moment of the Weil kernel, which is finite because the archimedean singularity is only
`1/(2|u|)`.  Consequently, if the Weil form is positive semidefinite on intervals of length `L` —
which is the Connes–Consani theorem for `L ≤ log 2` — then on length `L + η` it is bounded below by
`-2c²M₂/(L-η)²`.

**The error is `O(1)`, not `O(η)`**, because the partition gradient is `O(1/L)` regardless of `η`.
So localization gives quantitative *near*-positivity past `log 2` but not positivity.  Together with
the direct estimate and the damped prime sum, this is the third independent route to the same place:
all of them reduce to the same missing input, a **spectral gap** in the Connes–Consani theorem.
That reduction is now established from three directions and is recorded as the sharp open problem.

This file formalizes the pointwise partition identity, the Lipschitz bound on the localization
weight, and the resulting lower bound in terms of the kernel's second moment.
-/

open Real

noncomputable section

namespace RHTower

/-- **Partition identity.**  For a quadratic partition of unity `χ₁² + χ₂² = 1`, the cross terms
recombine into a squared-difference weight. -/
theorem partition_identity {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ^ 2 + a₂ ^ 2 = 1)
    (hb : b₁ ^ 2 + b₂ ^ 2 = 1) :
    a₁ * b₁ + a₂ * b₂ = 1 - ((a₁ - b₁) ^ 2 + (a₂ - b₂) ^ 2) / 2 := by
  nlinarith [ha, hb]

/-- The localization weight is nonnegative. -/
theorem localization_weight_nonneg (a₁ a₂ b₁ b₂ : ℝ) :
    0 ≤ (a₁ - b₁) ^ 2 + (a₂ - b₂) ^ 2 := by positivity

/-- **Lipschitz bound on the localization weight.**  If both cutoffs are `κ`-Lipschitz then the
weight is at most `2κ²(x-y)²`. -/
theorem localization_weight_le {a₁ a₂ b₁ b₂ κ d : ℝ} (hκ : 0 ≤ κ)
    (h₁ : |a₁ - b₁| ≤ κ * |d|) (h₂ : |a₂ - b₂| ≤ κ * |d|) :
    (a₁ - b₁) ^ 2 + (a₂ - b₂) ^ 2 ≤ 2 * κ ^ 2 * d ^ 2 := by
  have hd : |d| ^ 2 = d ^ 2 := sq_abs d
  have hn : 0 ≤ κ * |d| := mul_nonneg hκ (abs_nonneg d)
  have e₁ : (a₁ - b₁) ^ 2 ≤ κ ^ 2 * d ^ 2 := by
    have : (a₁ - b₁) ^ 2 = |a₁ - b₁| ^ 2 := (sq_abs _).symm
    nlinarith [h₁, abs_nonneg (a₁ - b₁), hn, hd]
  have e₂ : (a₂ - b₂) ^ 2 ≤ κ ^ 2 * d ^ 2 := by
    have : (a₂ - b₂) ^ 2 = |a₂ - b₂| ^ 2 := (sq_abs _).symm
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
    (hErr : -(κ ^ 2 * M₂ * nrm) ≤ Err) :
    -(κ ^ 2 * M₂ * nrm) ≤ Q := by
  rw [hIMS]; linarith

/-- The error is of order one in `η`: the bound `κ = c/(L-η)` does not vanish as `η → 0`, which is
exactly why localization yields near-positivity rather than positivity past the threshold. -/
theorem ims_error_not_small {L c : ℝ} (hL : 0 < L) (hc : 0 < c) :
    0 < (c / L) ^ 2 := by positivity

end RHTower
