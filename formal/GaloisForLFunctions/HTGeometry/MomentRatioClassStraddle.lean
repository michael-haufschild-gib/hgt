import Mathlib

/-!
# Log-concavity cannot decide a moment-ratio threshold: the class straddles it

An inequality of the shape

```text
16 · m₀ · m₂  ≤  45 · m₁²  ,        mⱼ = ∫₀^∞ x^{2j} φ(x) dx ,
```

is a bound on the ratio `m₀m₂/m₁² ≤ 45/16 = 2.8125`, equivalently on the *dispersion*
`D₀ = m₀m₂/m₁² − 1 ≤ 1.80502…`.  One might hope to establish it from regularity of `φ` alone —
positivity, monotonicity, log-concavity.  That is impossible, and the reason is elementary: the class
of log-concave densities on `[0,∞)` contains members on **both** sides of the threshold.

* **Uniform on `[0,1]`**: `Mₖ = 1/(k+1)`, so `(m₀,m₁,m₂) = (1, 1/3, 1/5)` and
  `16·1·(1/5) = 16/5 = 3.2 ≤ 5 = 45·(1/3)²`.  The inequality **holds**, with `D₀ = 4/5`.
* **Exponential `e^{−x}`**: `Mₖ = k!`, so `(m₀,m₁,m₂) = (1, 2, 24)` and
  `16·1·24 = 384 > 180 = 45·2²`.  The inequality **fails**, with `D₀ = 5`.

Both densities are log-concave on `[0,∞)`; the exponential is the extremal case of the standard
log-concave moment bound `M₀M₄ ≤ 6M₂²`, which gives only `D₀ ≤ 5`.  Since the threshold `1.805` lies
strictly between `4/5` and `5`, **no argument that uses only membership in the log-concave class — or
any weaker regularity — can settle the inequality for a particular kernel.**  It is a fact about the
individual function, not about its regularity class.
-/

namespace GaloisForLFunctions

namespace MomentRatioStraddle

/-- The moment triple of the uniform density on `[0,1]`: `∫₀¹ x^{2j} dx = 1/(2j+1)`. -/
noncomputable def uniformTriple : ℝ × ℝ × ℝ := (1, 1 / 3, 1 / 5)

/-- The moment triple of the exponential density `e^{−x}` on `[0,∞)`: `∫₀^∞ x^{2j}e^{−x} dx = (2j)!`. -/
noncomputable def exponentialTriple : ℝ × ℝ × ℝ := (1, 2, 24)

/-- The uniform density satisfies the threshold inequality. -/
theorem uniform_satisfies :
    16 * uniformTriple.1 * uniformTriple.2.2 ≤ 45 * uniformTriple.2.1 ^ (2 : ℕ) := by
  unfold uniformTriple
  norm_num

/-- The exponential density violates it. -/
theorem exponential_violates :
    ¬ (16 * exponentialTriple.1 * exponentialTriple.2.2 ≤ 45 * exponentialTriple.2.1 ^ (2 : ℕ)) := by
  unfold exponentialTriple
  norm_num

/-- The dispersion of the uniform triple is `4/5`, below the threshold `45/16 − 1`. -/
theorem uniform_dispersion :
    uniformTriple.1 * uniformTriple.2.2 / uniformTriple.2.1 ^ (2 : ℕ) - 1 = 4 / 5 := by
  unfold uniformTriple
  norm_num

/-- The dispersion of the exponential triple is `5`, above the threshold. -/
theorem exponential_dispersion :
    exponentialTriple.1 * exponentialTriple.2.2 / exponentialTriple.2.1 ^ (2 : ℕ) - 1 = 5 := by
  unfold exponentialTriple
  norm_num

/-- The threshold lies strictly between the two. -/
theorem threshold_between :
    (4 : ℝ) / 5 < 45 / 16 - 1 ∧ (45 : ℝ) / 16 - 1 < 5 := by
  constructor <;> norm_num

/-- **The class straddles the threshold.**  There are two moment triples, both realized by
log-concave densities on `[0,∞)`, one satisfying the inequality and one violating it.  Hence no
criterion depending only on log-concavity can decide it. -/
theorem logConcave_class_undecidable :
    (∃ t : ℝ × ℝ × ℝ, 16 * t.1 * t.2.2 ≤ 45 * t.2.1 ^ (2 : ℕ))
      ∧ (∃ t : ℝ × ℝ × ℝ, ¬ (16 * t.1 * t.2.2 ≤ 45 * t.2.1 ^ (2 : ℕ))) :=
  ⟨⟨uniformTriple, uniform_satisfies⟩, ⟨exponentialTriple, exponential_violates⟩⟩

end MomentRatioStraddle

end GaloisForLFunctions
