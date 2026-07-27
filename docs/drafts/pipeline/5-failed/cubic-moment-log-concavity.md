# The corpus's two theta hypotheses are a lossy split, but log-concavity does not control the cubic

- **ID:** `cubic-moment-log-concavity`
- **Stage:** 5-failed
- **Type:** REFUTED CONJECTURE + exact counterexample
- **Scientific status:** `[GENERAL CLAIM FALSE]` `[COUNTEREXAMPLE PROVED, LEAN]` `[NOT AN RH PROOF]`
- **Why it matters:** ordinary log-concavity cannot discharge either the quadratic split or the
  stronger unsplit cubic target. Any proof for the theta source must use theta-specific structure.

## 1. The two hypotheses are only used to reach one cubic inequality

`RHTower/PrimeArchThetaCumulantRatioSplit`:

```text
ThetaCuspUpperAdjacentRatioSeparation      :  14 m₂² ≤ 9 m₁m₃
ThetaCuspRelaxedFourthMomentConcentration  :  16 m₀m₂ ≤ 45 m₁²
```

and `thetaCusp_ratioSplit_exact_identity`

```text
m₀(9m₁m₃ − 14m₂²) + m₂(45m₁² − 16m₀m₂) = 3C ,     C = 3m₀m₁m₃ + 15m₁²m₂ − 10m₀m₂² .
```

`thetaCusp_raw_cubic_nonneg_of_ratioSplit` uses them for **nothing else** than `C ≥ 0`, which then
feeds `thetaCuspSixthMomentHankelInequality_of_ratioSplit` and
`forall_primeArchSourceTraceHankel_linear_nonneg_of_ratioSplit`.

**So the real target is `C ≥ 0`.** The two-inequality split is sufficient, not necessary.

## 2. The split is lossy, and provably so

The exponential density has even moments `(m₀,m₁,m₂,m₃) = (1, 2, 24, 720)`, hence

```text
C = 3·1·2·720 + 15·4·24 − 10·1·576 = 4320 + 1440 − 5760 = 0 ,
```

while the second inequality fails outright: `16·1·24 = 384 > 180 = 45·2²`.
(`exponential_split_lossy`, Lean.) So a density can satisfy the target and violate the split badly.

## 3. On the Gamma family, `C ≥ 0` **is** log-concavity

For the Gamma density of shape `α`, normalized so that `m₁ = 1`:

```text
m₂ = (α+2)(α+3)/(α(α+1)) ,     m₃ = (α+2)(α+3)(α+4)(α+5)/(α(α+1))² ,
```

and the functional collapses (`cubicFunctional_gamma`, Lean, axiom-clean):

```text
C(α)  =  8 (α+2)(α+3)(α−1) / (α (α+1)²) .
```

Hence, for `α > 0`,

> **`C(α) ≥ 0  ⟺  α ≥ 1  ⟺  x^{α−1}e^{−x}` is log-concave**, with equality exactly at `α = 1`.

(`cubicFunctional_gamma_nonneg_iff`, `cubicFunctional_gamma_one`.) The functional is positive on
exactly the log-concave range of the family and vanishes precisely at the exponential.

## 4. The conjecture

> **Conjecture.** For every log-concave density on `[0,∞)` with finite moments,
> `C = 3m₀m₁m₃ + 15m₁²m₂ − 10m₀m₂² ≥ 0`, where `mⱼ = ∫₀^∞ x^{2j}φ(x)dx`.
> Equality holds iff `φ` is exponential.

**Evidence.** §3 is an exact match on the natural one-parameter family — positivity holds precisely on
the log-concave sub-range and fails precisely off it, with the boundary case `α = 1` giving `C = 0`.
Spot checks agree: uniform on `[0,1]` gives `C = 6.17 > 0` (normalized), Gamma(2) gives `8.89 > 0`,
Gamma(½) — not log-concave — gives `−31 < 0`.

**Why it is not automatic.** With `m₀ = m₁ = 1`, `C = 3m₃ + 15m₂ − 10m₂²`. The free Cauchy–Schwarz
bound `m₃ ≥ m₂²` gives only `C ≥ m₂(15 − 7m₂)`, nonnegative for `m₂ ≤ 15/7 ≈ 2.14`; log-concavity
allows `m₂` up to `6`. So the conjecture needs a *lower* bound on `m₃` given `m₂`, and at the extreme
`m₂ = 6` it needs exactly `m₃ ≥ 90` — attained by the exponential. **The conjecture is sharp at that
point and cannot be slack.**

## 5. What it would buy

The theta source is log-concave on `ℝ` — `RHTower/ThetaCuspKernelLogConcavity.strictConcaveOn_
thetaCuspLogSource`, unconditional, already in the tree — hence log-concave on `[0,∞)`, and its even
moments are exactly `thetaCuspRawEvenMoment`. So the conjecture would give `C ≥ 0` for the theta
source **unconditionally**, discharging both quadratic hypotheses and with them the entire low block
of the Hankel criterion.

That does **not** prove RH: `riemannHypothesis_of_thetaCuspRatioSplit_of_primeArchDegreeTwoTail` still
needs `PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative`. But it converts a three-hypothesis
theorem into a one-hypothesis theorem, and removes the two tight-numeric walls that
`rh-producer-map-corpus.md` §7 and §23 identified.

## 6. This supersedes my own §23

§23 proved that the *quadratic* threshold `45/16` cannot be decided by log-concavity, because the
class straddles it (uniform `D₀ = 4/5`, exponential `D₀ = 5`). That is correct and unaffected — but it
is about the **split**, not the target. The exponential is exactly the point where the split fails and
`C` does not, which is why the straddle does not obstruct the conjecture. **I spent the session
treating the split as the frontier when the corpus's own identity shows it is not.**

## Gates

- [x] the split shown lossy, with the exponential as witness (Lean)
- [x] `C` computed in closed form on the Gamma family (Lean)
- [x] `C ≥ 0 ⟺ log-concave` on that family, exponential extremal (Lean)
- [x] sharpness at `m₂ = 6`, `m₃ ≥ 90` identified
- [ ] the general conjecture: log-concave ⟹ `C ≥ 0`
- [ ] if proved: discharge both theta hypotheses from `strictConcaveOn_thetaCuspLogSource`

## 7. The conjecture is a comparison of two log-concavity defects

With `Mₖ = ∫₀^∞ xᵏφ` and `mⱼ = M_{2j}`, the functional splits **exactly**:

```text
C  =  (5/2)·M₄·(6M₂² − M₀M₄)   −   3·M₀·((5/2)M₄² − M₂M₆) .
```

(`cubicFunctional_eq_defects`, Lean, axiom-clean.) The two brackets are the standard log-concavity
defects of the normalized sequence `Lₖ = Mₖ/k!`:

```text
6M₂² − M₀M₄     =  24 (L₂² − L₀L₄)     ≥ 0  for log-concave φ
(5/2)M₄² − M₂M₆ = 1440 (L₄² − L₂L₆)    ≥ 0  for the same reason
```

so

> **`C ≥ 0`  ⟺  `(5/2)·M₄·defect₂  ≥  3·M₀·defect₄`** ,

a comparison between the defect at index `2`, weighted by `M₄`, and three times the defect at index
`4`, weighted by `M₀`.

### 7.1 Why this is the right handle

- **Both defects are free.** Log-concavity gives each separately; the content is entirely in which
  one is larger, suitably weighted. No standard inequality orders them.
- **The exponential makes both vanish** (`defects_vanish_exponential`: `defect₂(1,2,24) = 0`,
  `defect₄(2,24,720) = 0`), which is exactly why it is the equality case — not a coincidence of the
  cubic but a statement that the log-affine density saturates log-concavity at every index.
- **The obvious attempt fails, and visibly.** Applying log-concavity twice gives
  `L₂² ≥ L₀L₄` and `L₄² ≥ L₂L₆` — the first helps, the **second has the wrong sign**, since `C` needs
  `L₄²` small relative to `L₂L₆`. So the conjecture is genuinely second-order: it asks that the
  defect *shrink* fast enough with the index.
- Numerically the ratio `(5/2)M₄·defect₂ / (3M₀·defect₄)` is `1.49` for the uniform density and `2.07`
  for Gamma(5); it is `0/0` at the exponential and negative for Gamma(½).

### 7.2 What is now needed

A statement of the form *"for a log-concave density the normalized log-concavity defect is
non-increasing in the index, at rate at least `…`"*. That is a question about one sequence
`{Lₖ}`, not about `φ`, and it is the shape of a Newton-type inequality. It is also exactly the kind of
statement that the Gamma computation of §3 says must be sharp at the exponential.

`cubicFunctional_nonneg_of_defectFour_nonpos` records the trivial sufficient case for completeness.

## Gates

- [x] defect decomposition, exact (Lean)
- [x] the conjecture restated as a defect comparison (Lean)
- [x] the exponential shown to annihilate both defects (Lean)
- [x] the naive two-application-of-log-concavity attempt shown to fail on sign
- [ ] the defect-decay statement for `{Mₖ/k!}`

## 8. Final form of the open core: three terms in one ratio sequence

Dividing the defect comparison by `L₀L₂L₄ > 0` collapses it completely. With `Lₖ = Mₖ/k!` and the
two-step ratio `Rₖ = L_{k+2}/Lₖ`:

> **`C ≥ 0`  ⟺  `R₀ + 3R₄ ≥ 4R₂`.**

(`defect_comparison_iff_ratio`, Lean, axiom-clean.) Log-concavity of `{Lₖ}` makes `R` non-increasing,
so `R₀ − R₂ ≥ 0` and `R₂ − R₄ ≥ 0`; the claim is that **the first decrement is at least three times
the second**. Equivalently `R₂ ≤ ¼R₀ + ¾R₄` — a weighted convexity of `R` at indices `0, 2, 4`, and
strictly stronger than plain convexity (`R₂ ≤ ½R₀ + ½R₄`), since `R₀ > R₄`.

**Tight exactly when `R` is constant**, i.e. for the exponential.

### 8.1 Independent confirmation on the Gamma family

For Gamma(α), `Lₖ = C(α+k−1, k)` and `Rₖ = (α+k)(α+k+1)/((k+1)(k+2))`, so the inequality reads

```text
15α(α+1) + 3(α+4)(α+5)  ≥  10(α+2)(α+3)      ⟺      8α(α−1) ≥ 0      ⟺      α ≥ 1 ,
```

exactly log-concavity of `x^{α−1}e^{−x}` (`gammaStepRatio_inequality`, Lean). This reproduces
`cubicFunctional_gamma`'s closed form by a completely different route — moment algebra there, ratio
algebra here — which is the calibration I wanted before trusting the reduction.

### 8.2 The open core, stated once

> **Conjecture.** For a log-concave density on `[0,∞)` with finite moments, the two-step ratios
> `Rₖ = (M_{k+2}/(k+2)!)/(Mₖ/k!)` satisfy `R₀ + 3R₄ ≥ 4R₂`.

**No `ζ`, no primes, no transcendental constants, no asymptotics.** A three-term inequality for the
normalized moment sequence of a log-concave density, tight at the exponential, verified on the Gamma
family and on the uniform density (`R₀−R₂ = 0.1167` against `3(R₂−R₄) = 0.0786`, ratio `1.49`) and on
Gamma(5) (ratio `2.07`), and false precisely off the log-concave range (Gamma(½)).

If it holds, `strictConcaveOn_thetaCuspLogSource` — already proved unconditionally in the corpus —
discharges `ThetaCuspUpperAdjacentRatioSeparation` and `ThetaCuspRelaxedFourthMomentConcentration`,
and with them the entire low block of the Hankel criterion.

### 8.3 Honest status

The reduction is exact and formal; the conjecture is not proved. Two attempts that do **not** work,
recorded so they are not retried: applying log-concavity twice gives the wrong sign at index `4`
(§7.1), and the free Cauchy–Schwarz bound `m₃ ≥ m₂²` covers only `m₂ ≤ 15/7` where log-concavity
allows `m₂ ≤ 6` (§4). What is needed is a decay rate for the log-concavity defect in the index, and
the Gamma computation says any such rate must be sharp at `α = 1`.

## Gates

- [x] reduction to `R₀ + 3R₄ ≥ 4R₂`, exact (Lean)
- [x] independent confirmation on the Gamma family by ratio algebra (Lean)
- [x] two failed approaches recorded
- [x] the conjecture refuted by the Beta `(1,3)` density

## 9. Exact refutation: Beta `(1,3)`

Take

```text
f(x)=3(1-x)^2,  0≤x≤1.
```

This is log-concave on its convex support: on `0≤x<1`,
`log f(x)=log 3+2log(1-x)`, which is concave, and the zero extension preserves
log-concavity. Direct integration gives

```text
m_j = ∫₀¹ x^(2j) 3(1-x)^2 dx
    = 3/(2j+1) - 6/(2j+2) + 3/(2j+3),

(m₀,m₁,m₂,m₃)=(1,1/10,1/35,1/84).
```

Therefore

```text
C = 3(1)(1/10)(1/84) + 15(1/10)^2(1/35) - 10(1)(1/35)^2
  = -3/9800 < 0.
```

So ordinary log-concavity does not imply the unsplit target. The Gamma-family equivalence was a
family-specific coincidence, not evidence for a universal extremal law.

The exact integral formula and negative certificate are unconditional in
`HTGeometry/CubicMomentLogConcavityCounterexample.lean`:

- `betaOneThreeRawEvenMoment_formula`;
- `betaOneThree_cubicFunctional_eq`;
- `betaOneThree_cubicFunctional_neg`.

### Positive survivor

`C≥0` remains the correct unsplit theta target, but no theorem using only membership in the class
of log-concave densities can prove it. A surviving proof must use additional theta-specific
information—modular reflection, the explicit Jacobi atom mixture, or a source identity controlling
the weighted ratio curvature `R₀+3R₄-4R₂`.

## 10. Independent refutation on the power family, and where the failure lives

The Beta `(1,3)` certificate of §9 is a point. The same refutation on a one-parameter family locates
the failure region, which decides whether the theta source is affected.

Take `φ(x) = exp(−x^p)` on `[0,∞)`, log-concave exactly for `p ≥ 1`. Then `Mₖ = Γ((k+1)/p)/p`, and
with `q = 1/p` the two-step ratios of `Lₖ = Mₖ/k!` give

```text
Ψ(q) = R₀ + 3R₄ − 4R₂ = Γ(3q)/(2Γ(q)) + Γ(7q)/(10Γ(5q)) − Γ(5q)/(3Γ(3q)) ,
```

which has the sign of `C`.

**Two exact zeros**, each by one step of the Γ recurrence:

```text
q = 1    (p = 1, exponential)     R = (1, 1, 1)          Ψ = 1 + 3 − 4       = 0
q = 1/2  (p = 2, half-Gaussian)   R = (1/4, 1/8, 1/12)   Ψ = 1/4 + 1/4 − 1/2 = 0
```

The half-Gaussian is a **second** equality case, off the Gamma curve entirely — which is why §3's
Gamma computation could not see it.

**The derivative at the exponential is a `γ`-free positive rational.** With `Tᵢ(1) = 1, 3, 4` and
`ψ(n) = −γ + H_{n−1}`:

```text
3ψ(3) − ψ(1)  = 9/2   − 2γ ,    7ψ(7) − 5ψ(5) = 101/15 − 2γ ,    5ψ(5) − 3ψ(3) = 71/12 − 2γ

Ψ′(1) = 1·(9/2 − 2γ) + 3·(101/15 − 2γ) − 4·(71/12 − 2γ) = 9/2 + 101/5 − 71/3 = 31/30 .
```

Every Euler–Mascheroni term cancels. `Ψ(1) = 0` with `Ψ′(1) > 0` gives `Ψ < 0` immediately to the
left, i.e. for `p` just above `1`. At `p = 3/2`: `0.36924 + 0.52955 − 0.92605 = −0.0273`.

`HTGeometry/CubicMomentPowerFamily.lean`, axiom-clean: `ratioFunctional_exponential`,
`ratioFunctional_halfGaussian`, `ratioFunctional_uniform` (`= 4/105`), the three digamma
combinations, `psi_deriv_at_one` (`= 31/30`), `neg_left_of_deriv_pos`.

### 10.1 The failure band, and the theta source

```text
p = 1   Ψ = 0        p ∈ (1,2)  Ψ < 0        p = 2   Ψ = 0        p > 2   Ψ > 0
```

This tracks the sign of `V‴` for `V = x^p`: `V″ = p(p−1)x^{p−2}` decreases exactly on `1 < p < 2` and
increases exactly for `p > 2`. So on this family the inequality holds precisely where the log-curvature
is increasing.

The theta source has `−(log Φ)″ ≥ 4π e^{2x}` — `thetaCuspBornWittenCurvature = 2·scale + 3·scale/weight²`
with `scale = π n² e^{2x}` — manifestly increasing, with double-exponential margin. **The theta kernel
lies far outside the failure band.**

That is a statement about one family and not a theorem about the class; Gamma(α > 1) has *decreasing*
`V″` and still satisfies the inequality, so increasing log-curvature is sufficient on the power family
but not necessary in general. What it does establish is that the Beta `(1,3)` and `p ∈ (1,2)`
counterexamples are **slowly-decaying** densities, and the theta kernel is the opposite extreme.

### 10.2 The repaired target

The right question is no longer "does log-concavity give `C ≥ 0`" — it does not — but:

> Is there a hypothesis satisfied by the theta source, stronger than log-concavity and weaker than the
> conclusion, that implies `C ≥ 0`? Increasing log-curvature (`V‴ ≥ 0`) is the candidate the power
> family points at, and the corpus already has `−(log Φ)″ ≥ 4πe^{2x}` unconditionally.

That is a well-posed replacement, and unlike the refuted conjecture it does not claim anything about
the whole log-concave class.

## Gates

- [x] §9 Beta `(1,3)` point counterexample (another session)
- [x] §10 power-family refutation, independent, with the `γ`-free derivative `31/30`
- [x] second exact equality case identified: the half-Gaussian, off the Gamma curve
- [x] failure band located at `p ∈ (1,2)`, matching `V‴ < 0`
- [x] theta source shown to lie outside the band
- [ ] `V‴ ≥ 0 ⟹ C ≥ 0`, or a counterexample to that

## 11. The repaired hypothesis fails too: the exponential is a strict local maximum

§10.2 proposed increasing log-curvature (`V‴ ≥ 0`) as the hypothesis the theta source satisfies and
the counterexamples do not. **It fails at the first perturbation of the exponential.**

Take `φ_s(x) = e^{−x}e^{−sx²}` on `[0,∞)`, `s ≥ 0`: `V = x + sx²`, so `V″ = 2s ≥ 0` and `V‴ = 0 ≥ 0`.
Differentiating the moments under the integral at `s = 0`,

```text
∂ₛ Mₖ|₀ = −∫₀^∞ x^{k+2}e^{−x}dx = −(k+2)! ,        ∂ₛ Lₖ|₀ = −(k+1)(k+2) ,
```

and since `Lₖ(0) = 1` for all `k`,

```text
∂ₛ Rₖ|₀ = ∂ₛL_{k+2} − ∂ₛLₖ = −[(k+3)(k+4) − (k+1)(k+2)] = −(4k+10) ,
```

so

```text
∂ₛ Ψ|₀ = −10 + 3(−26) − 4(−18) = −16 .
```

`Ψ(0) = 0` with `∂ₛΨ|₀ = −16 < 0` gives `Ψ < 0` for every small `s > 0`.

`HTGeometry/CubicMomentPowerFamily.lean` (extended), axiom-clean: `gaussianTilt_ratioDeriv`,
`gaussianTilt_psi_deriv` (`= −16`), `neg_right_of_deriv_neg`.

### 11.1 What this closes

The counterexamples are **not** confined to slowly-decaying densities. They reach into every
neighbourhood of the exponential in the Gaussian direction, and the exponential is a strict local
maximum of `Ψ`. So `§10.1`'s reading — failure band `p ∈ (1,2)`, theta source safely outside — was
right about the power family and wrong as a guide to the class: the power family simply does not pass
through the directions in which `Ψ` decreases fastest.

Combined with §9 (Beta `(1,3)`) and §10 (`p ∈ (1,2)`), three independent families now violate the
target, and one of them does so arbitrarily close to the equality case. **No hypothesis of the form
"log-concave plus extra convexity of `V`" can imply `C ≥ 0`**, because `V‴ = 0` already fails.

### 11.2 What survives

`C ≥ 0` remains the correct unsplit target for the theta source — the corpus's identity is exact and
the split is genuinely lossy (§2). What is now excluded is deriving it from any *class* membership.
Any proof must use the theta kernel's own structure: the `k ≥ 2` atom tail, the functional equation,
or the Born–Witten normal form — not a general inequality for log-concave densities.

That is a real narrowing, and it is negative: three refutations, the last of them local to the
extremal point.

## Gates

- [x] §11 `V‴ ≥ 0` refuted: `∂ₛΨ|₀ = −16` on the Gaussian tilt (Lean)
- [x] exponential shown to be a strict local maximum of `Ψ`
- [x] class-based routes to `C ≥ 0` excluded
- [ ] a theta-specific proof of `C ≥ 0`, or a demonstration that it fails for the theta source
