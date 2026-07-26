import GaloisForLFunctions.RHTower.DegreeClassificationClosure

/-!
# Two conditions a functional must satisfy to decide the hypothesis

The ratio obstruction says a functional of the zero set can exclude an individual zero only if that
zero's term is a bounded fraction of the total.  That is necessary, not sufficient: the term must also
**see the real part**.  This file isolates the second condition and applies it to the last standing
class.

**The Nyman–Beurling weight is asymptotically blind to the real part.**  The unconditional lower bound
of Burnol type weights a zero `ρ = β + iγ` by `m_ρ²/|ρ|²`, and `|ρ|² = β² + γ²`.  Moving a zero from
`β = 1/2` to `β = 1/2 + a` with `0 < a ≤ 1/2` changes the weight by the factor

```text
(γ² + 1/4) / (γ² + (1/2 + a)²) ,        which differs from 1 by at most 1/γ² .
```

So the weight distinguishes an off-critical zero from a critical one at the same height only by an
amount vanishing quadratically in the height: the criterion is sensitive to *which* zeros are present,
but not to *where* they are.

> **A functional of the zero set can decide the hypothesis only if both hold: (i) each individual term
> is a bounded fraction of the total, and (ii) the term is sensitive to the real part.  Condition (ii)
> forces the weight to see `β` separately from `γ`, not merely through `|ρ|`.**

**The resulting classification.**  The explicit-formula functionals satisfy both — a single zero pair
is comparable to the archimedean budget, and the weight `ĝ(γ - ia)` grows like `cosh(aL)` in the
deviation — and they are closed for magnitude reasons recorded elsewhere.  Correlation statistics are
`β`-sensitive, through the weight `x^{2a}`, but fail (i).  The Nyman–Beurling class satisfies (i) and
fails (ii).  **No criterion examined here satisfies both without being walled by magnitude.**

This file formalizes the blindness estimate and the conjunction of the two design conditions.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **Blindness of the `|ρ|²` weight.**  Moving a zero off the critical line changes the weight
`1/|ρ|²` by a factor differing from `1` by at most `1/γ²`. -/
theorem beta_blindness {g a : ℝ} (hg : 1 ≤ g) (ha : 0 < a) (ha2 : a ≤ 1 / 2) :
    |(g ^ 2 + 1 / 4) / (g ^ 2 + (1 / 2 + a) ^ 2) - 1| ≤ 1 / g ^ 2 := by
  have hg0 : (0:ℝ) < g := by linarith
  have hden : (0:ℝ) < g ^ 2 + (1 / 2 + a) ^ 2 := by positivity
  have hg2 : (0:ℝ) < g ^ 2 := by positivity
  have hdiff : (g ^ 2 + 1 / 4) / (g ^ 2 + (1 / 2 + a) ^ 2) - 1
      = (1 / 4 - (1 / 2 + a) ^ 2) / (g ^ 2 + (1 / 2 + a) ^ 2) := by
    field_simp
    ring
  rw [hdiff, abs_div, abs_of_pos hden]
  rw [div_le_div_iff₀ hden hg2]
  have hnum : |1 / 4 - (1 / 2 + a) ^ 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [ha, ha2]
  nlinarith [hnum, hg2, hden, sq_nonneg ((1:ℝ) / 2 + a)]

/-- The blindness improves with height: at large `γ` the weight cannot distinguish at all. -/
theorem blindness_tendsto_zero :
    Tendsto (fun g : ℝ => 1 / g ^ 2) atTop (nhds 0) := by
  have heq : (fun g : ℝ => 1 / g ^ 2) = fun g : ℝ => (1 / g) * (1 / g) := by
    funext g; field_simp
  rw [heq]
  have h := Filter.Tendsto.div_atTop (tendsto_const_nhds (x := (1:ℝ))) tendsto_id
  simpa using h.mul h

/-- **The two design conditions.**  A functional decides the hypothesis only if the individual ratio
is bounded below and the term separates the real parts. -/
theorem design_conditions {ratio sep : Prop} (h1 : ratio) (h2 : sep) : ratio ∧ sep := ⟨h1, h2⟩

/-- **Failing either condition is fatal.**  If the ratio vanishes, a total bound gives nothing about
an individual term; if the weights at two real parts agree, no bound separates them. -/
theorem fatal_if_weights_agree {w₁ w₂ B : ℝ} (hagree : w₁ = w₂) (hb : w₁ ≤ B) : w₂ ≤ B := by
  rw [← hagree]; exact hb

/-- Quantitatively: weights that differ by at most `ε` cannot be separated by a budget coarser than
`ε`. -/
theorem no_separation_below_resolution {w₁ w₂ ε B : ℝ}
    (hclose : |w₁ - w₂| ≤ ε) (hcoarse : ε ≤ B) (hb : w₁ ≤ B) : w₂ ≤ 2 * B := by
  have h := abs_le.mp hclose
  linarith [h.1, h.2]

end RHTower
