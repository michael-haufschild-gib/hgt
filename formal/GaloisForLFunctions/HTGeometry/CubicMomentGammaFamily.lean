import Mathlib

/-!
# The cubic moment functional on the Gamma family: positive exactly on the log-concave range

`PrimeArchThetaCumulantRatioSplit` uses two quadratic inequalities

```text
14 m₂² ≤ 9 m₁m₃        and        16 m₀m₂ ≤ 45 m₁²
```

only to derive the **cubic** inequality

```text
C := 3 m₀m₁m₃ + 15 m₁²m₂ − 10 m₀m₂²  ≥  0 ,
```

via the exact identity `m₀(9m₁m₃ − 14m₂²) + m₂(45m₁² − 16m₀m₂) = 3C`.  The split is *sufficient* but
**lossy**: the exponential density has `C = 0` while violating the second inequality outright
(`45·2² = 180 < 384 = 16·1·24`).  So the real target is `C ≥ 0`, and it may be reachable where the
split is not.

This file computes `C` exactly on the Gamma family, with `mⱼ = ∫₀^∞ x^{2j}·x^{α−1}e^{−x}dx / Γ(α)`,
i.e. `mⱼ = Γ(α+2j)/Γ(α)`.  Normalizing by the scale that sets `m₁ = 1` gives

```text
m₂ = (α+2)(α+3)/(α(α+1)) ,      m₃ = (α+2)(α+3)(α+4)(α+5)/(α(α+1))² ,
```

and then

```text
C(α)  =  8 (α+2)(α+3)(α−1) / (α (α+1)²) .
```

**`C(α) ≥ 0` ⟺ `α ≥ 1` ⟺ the Gamma density `x^{α−1}e^{−x}` is log-concave**, with equality exactly at
`α = 1`, the exponential.  So on this family the cubic functional is positive precisely on the
log-concave range, and the exponential is the extremal case.

That is sharp evidence for the general statement — *log-concavity of the density implies `C ≥ 0`* —
which, if true, discharges both of the corpus's quadratic hypotheses from
`strictConcaveOn_thetaCuspLogSource`, a theorem the tree already has.  It is recorded here as a
computation on the family, not as a proof of the general claim.
-/

namespace GaloisForLFunctions

namespace CubicMoment

/-- The cubic moment functional `C = 3m₀m₁m₃ + 15m₁²m₂ − 10m₀m₂²`. -/
noncomputable def cubicFunctional (m₀ m₁ m₂ m₃ : ℝ) : ℝ :=
  3 * m₀ * m₁ * m₃ + 15 * m₁ ^ 2 * m₂ - 10 * m₀ * m₂ ^ 2

/-- The exact split identity used by the corpus: the two quadratic defects, weighted by `m₀` and
`m₂`, sum to `3C`. -/
theorem ratioSplit_identity (m₀ m₁ m₂ m₃ : ℝ) :
    m₀ * (9 * m₁ * m₃ - 14 * m₂ ^ 2) + m₂ * (45 * m₁ ^ 2 - 16 * m₀ * m₂)
      = 3 * cubicFunctional m₀ m₁ m₂ m₃ := by
  unfold cubicFunctional
  ring

/-- Normalized even moments of the Gamma density with shape `α`, scaled so that `m₁ = 1`. -/
noncomputable def gammaMoment₂ (α : ℝ) : ℝ := (α + 2) * (α + 3) / (α * (α + 1))

noncomputable def gammaMoment₃ (α : ℝ) : ℝ :=
  (α + 2) * (α + 3) * (α + 4) * (α + 5) / (α * (α + 1)) ^ 2

/-- **The cubic functional on the Gamma family, in closed form.** -/
theorem cubicFunctional_gamma {α : ℝ} (hα : 0 < α) :
    cubicFunctional 1 1 (gammaMoment₂ α) (gammaMoment₃ α)
      = 8 * (α + 2) * (α + 3) * (α - 1) / (α * (α + 1) ^ 2) := by
  have h1 : α ≠ 0 := ne_of_gt hα
  have h2 : α + 1 ≠ 0 := by positivity
  unfold cubicFunctional gammaMoment₂ gammaMoment₃
  field_simp
  ring

/-- **Positive exactly on the log-concave range.**  For the Gamma family the cubic functional is
nonnegative iff the shape parameter is at least one, which is exactly when the density is
log-concave. -/
theorem cubicFunctional_gamma_nonneg_iff {α : ℝ} (hα : 0 < α) :
    0 ≤ cubicFunctional 1 1 (gammaMoment₂ α) (gammaMoment₃ α) ↔ 1 ≤ α := by
  rw [cubicFunctional_gamma hα]
  have hden : 0 < α * (α + 1) ^ 2 := by positivity
  have hnum : 0 < 8 * (α + 2) * (α + 3) := by positivity
  rw [le_div_iff₀ hden, zero_mul]
  constructor
  · intro h
    nlinarith [h, hnum]
  · intro h
    have : 0 ≤ α - 1 := by linarith
    positivity

/-- **The exponential is extremal.**  At `α = 1` the cubic functional vanishes. -/
theorem cubicFunctional_gamma_one :
    cubicFunctional 1 1 (gammaMoment₂ 1) (gammaMoment₃ 1) = 0 := by
  rw [cubicFunctional_gamma one_pos]
  norm_num

/-- **The corpus's split is lossy at the extremal point.**  The exponential's unnormalized moments
`(1, 2, 24, 720)` give `C = 0`, yet the second quadratic inequality fails by a wide margin. -/
theorem exponential_split_lossy :
    cubicFunctional 1 2 24 720 = 0 ∧ ¬ (16 * 1 * 24 ≤ 45 * (2 : ℝ) ^ 2) := by
  constructor
  · unfold cubicFunctional; norm_num
  · norm_num


/-! ### The cubic functional is a comparison of two log-concavity defects

Writing the even moments as `mⱼ = M_{2j}` with `Mₖ = ∫₀^∞ xᵏφ`, the functional splits exactly into
the two standard log-concavity defects of the normalized moment sequence `Lₖ = Mₖ/k!`:

```text
C  =  (5/2)·M₄·(6M₂² − M₀M₄)   +   3·M₀·(M₂M₆ − (5/2)M₄²) .
```

The first bracket is `24·(L₂² − L₀L₄)` and is **nonnegative for every log-concave density** — it is the
two-step log-concavity of `{Mₖ/k!}` at index `2`.  The second is `−1440·(L₄² − L₂L₆)` and is
**nonpositive** for the same reason at index `4`.  So

> **`C ≥ 0`  ⟺  `(5/2)·M₄·(6M₂² − M₀M₄)  ≥  3·M₀·((5/2)M₄² − M₂M₆)`** ,

a comparison between the log-concavity defect at index `2`, weighted by `M₄`, and three times the
defect at index `4`, weighted by `M₀`.  Both are free; neither dominates the other by any standard
inequality, and for the exponential both vanish — which is exactly why the exponential is the
equality case.

This is the handle: the conjecture is not "a cubic is positive" but "one log-concavity defect
dominates another", and the two defects are adjacent indices of one sequence. -/

/-- The log-concavity defect of `{Mₖ/k!}` at index `2`, cleared of denominators. -/
noncomputable def defectTwo (M₀ M₂ M₄ : ℝ) : ℝ := 6 * M₂ ^ 2 - M₀ * M₄

/-- The log-concavity defect at index `4`, cleared of denominators and signed so that it is
nonnegative for a log-concave density. -/
noncomputable def defectFour (M₂ M₄ M₆ : ℝ) : ℝ := 5 / 2 * M₄ ^ 2 - M₂ * M₆

/-- **The defect decomposition.**  The cubic functional is the index-`2` defect weighted by `M₄`,
minus three times the index-`4` defect weighted by `M₀`. -/
theorem cubicFunctional_eq_defects (M₀ M₂ M₄ M₆ : ℝ) :
    cubicFunctional M₀ M₂ M₄ M₆
      = 5 / 2 * M₄ * defectTwo M₀ M₂ M₄ - 3 * M₀ * defectFour M₂ M₄ M₆ := by
  unfold cubicFunctional defectTwo defectFour
  ring

/-- **The conjecture, restated as a defect comparison.** -/
theorem cubicFunctional_nonneg_iff_defect_comparison (M₀ M₂ M₄ M₆ : ℝ) :
    0 ≤ cubicFunctional M₀ M₂ M₄ M₆
      ↔ 3 * M₀ * defectFour M₂ M₄ M₆ ≤ 5 / 2 * M₄ * defectTwo M₀ M₂ M₄ := by
  rw [cubicFunctional_eq_defects]
  constructor <;> intro h <;> linarith

/-- Both defects vanish on the exponential, where `Mₖ = k!` — the equality case. -/
theorem defects_vanish_exponential :
    defectTwo 1 2 24 = 0 ∧ defectFour 2 24 720 = 0 := by
  refine ⟨?_, ?_⟩
  · unfold defectTwo; norm_num
  · unfold defectFour; norm_num

/-- A sufficient condition free of the index-`4` defect: if the index-`4` defect is nonpositive and
the index-`2` defect nonnegative, `C ≥ 0` needs no comparison at all. -/
theorem cubicFunctional_nonneg_of_defectFour_nonpos (M₀ M₂ M₄ M₆ : ℝ)
    (hM₀ : 0 ≤ M₀) (hM₄ : 0 ≤ M₄)
    (h₂ : 0 ≤ defectTwo M₀ M₂ M₄) (h₄ : defectFour M₂ M₄ M₆ ≤ 0) :
    0 ≤ cubicFunctional M₀ M₂ M₄ M₆ := by
  rw [cubicFunctional_eq_defects]
  have hA : 0 ≤ 5 / 2 * M₄ * defectTwo M₀ M₂ M₄ := by positivity
  have hB : 3 * M₀ * defectFour M₂ M₄ M₆ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) h₄
  linarith


/-! ### Final form: a three-term inequality in the two-step ratio sequence

Write `Lₖ = Mₖ/k!` and `Rₖ = L_{k+2}/Lₖ`.  Log-concavity of `{Lₖ}` makes `R` non-increasing.  Dividing
the defect comparison by `L₀L₂L₄ > 0` collapses it to

```text
R₀ − R₂  ≥  3 (R₂ − R₄) ,        equivalently        R₀ + 3R₄  ≥  4R₂ .
```

Both decrements are nonnegative for a log-concave density, and the claim is that the **first is at
least three times the second** — a weighted convexity of `R` at the indices `0, 2, 4`, strictly
stronger than convexity, tight exactly when `R` is constant, i.e. for the exponential.

On the Gamma family `Rₖ = (α+k)(α+k+1)/((k+1)(k+2))`, and the inequality reads
`15α(α+1) + 3(α+4)(α+5) ≥ 10(α+2)(α+3)`, i.e. `8α(α−1) ≥ 0`, i.e. `α ≥ 1` — the same closed form as
`cubicFunctional_gamma`, reached independently.

This is the whole open core: **no `ζ`, no primes, no transcendental constants** — a three-term
inequality for the two-step ratios of the normalized moment sequence of a log-concave density. -/

/-- The two-step ratio of the normalized moment sequence. -/
noncomputable def stepRatio (La Lb : ℝ) : ℝ := Lb / La

/-- **The cubic functional as a three-term ratio inequality.**  With all normalized moments positive,
the defect comparison is exactly `R₀ + 3R₄ ≥ 4R₂`. -/
theorem defect_comparison_iff_ratio (L₀ L₂ L₄ L₆ : ℝ)
    (h₀ : 0 < L₀) (h₂ : 0 < L₂) (h₄ : 0 < L₄) :
    3 * L₀ * (L₄ ^ 2 - L₂ * L₆) ≤ L₄ * (L₂ ^ 2 - L₀ * L₄)
      ↔ 4 * stepRatio L₂ L₄ ≤ stepRatio L₀ L₂ + 3 * stepRatio L₄ L₆ := by
  unfold stepRatio
  have hD : (0 : ℝ) < L₀ * L₂ * L₄ := by positivity
  have key : (L₂ / L₀ + 3 * (L₆ / L₄)) - 4 * (L₄ / L₂)
      = (L₄ * (L₂ ^ 2 - L₀ * L₄) - 3 * L₀ * (L₄ ^ 2 - L₂ * L₆)) / (L₀ * L₂ * L₄) := by
    field_simp
    ring
  constructor
  · intro h
    have hnum : 0 ≤ L₄ * (L₂ ^ 2 - L₀ * L₄) - 3 * L₀ * (L₄ ^ 2 - L₂ * L₆) := by linarith
    have hdiv := div_nonneg hnum hD.le
    rw [← key] at hdiv
    linarith
  · intro h
    have hd : 0 ≤ (L₂ / L₀ + 3 * (L₆ / L₄)) - 4 * (L₄ / L₂) := by linarith
    rw [key] at hd
    have hmul := mul_nonneg hd hD.le
    rw [div_mul_cancel₀ _ (ne_of_gt hD)] at hmul
    linarith

/-- The Gamma-family two-step ratio at the three indices used. -/
noncomputable def gammaStepRatio₀ (α : ℝ) : ℝ := α * (α + 1) / 2
noncomputable def gammaStepRatio₂ (α : ℝ) : ℝ := (α + 2) * (α + 3) / 12
noncomputable def gammaStepRatio₄ (α : ℝ) : ℝ := (α + 4) * (α + 5) / 30

/-- **The ratio inequality on the Gamma family reduces to `8α(α−1) ≥ 0`**, i.e. to `α ≥ 1`, which is
exactly log-concavity of `x^{α−1}e^{−x}`.  Reached independently of `cubicFunctional_gamma`. -/
theorem gammaStepRatio_inequality {α : ℝ} (hα : 0 < α) :
    4 * gammaStepRatio₂ α ≤ gammaStepRatio₀ α + 3 * gammaStepRatio₄ α ↔ 1 ≤ α := by
  unfold gammaStepRatio₀ gammaStepRatio₂ gammaStepRatio₄
  constructor
  · intro h
    nlinarith [h, hα]
  · intro h
    nlinarith [h, hα]

end CubicMoment

end GaloisForLFunctions
