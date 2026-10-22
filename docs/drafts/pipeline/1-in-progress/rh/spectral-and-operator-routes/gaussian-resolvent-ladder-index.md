# Index: the Gaussian / resolvent moment ladder for RH

- **ID:** `gaussian-resolvent-ladder-index`
- **Stage:** 1-in-progress (navigation card for a closed block of Stage-3 work)
- **Purpose:** one place to see what this lane proved, what it ruled out, and what remains.

Cards: `3-formalized/not_new_scientific_knowledge/gaussian-heat-trace-rh-criterion.md`,
`3-formalized/not_new_scientific_knowledge/xi-resolvent-trace-hankel-criterion.md`,
and the no-go/salvage entries on `1-in-progress/weil-positivity-ladder-outside-strip.md`.

## The one-line story

RH is positive semidefiniteness of a moment array of the Xi divisor.  Two weights realise it:
Gaussian `exp (-t w)` and resolvent `(w + X)^(-1)`, `w q = xiSpectralPoint q ^ 2`.  The Gaussian
weight detects well but has no Lean route to primes; the resolvent weight is prime-computable but
detects only at high order.  Everything below is that trade-off made exact.

## Modules, in dependency order

| Module | Content |
|---|---|
| `HTGeometry.CommonRealPartTuranDeterminant` | vertical-line configurations have nonpositive Turán determinant, strictly negative off the axis |
| `HTGeometry.SectorPowerPositivity` | tangent-addition sector law; powers stay in the right half-plane while the budget lasts; general chain form |
| `HTGeometry.NonnegativeWeightMomentHankel` | nonnegative weights have positive semidefinite power-moment arrays |
| `RHTower.XiGaussianHeatTraceCriterion` | **RH ↔ every polynomial-square Gaussian trace is nonnegative**; shell finiteness |
| `RHTower.XiGaussianHeatTuranDefect` | the Turán minor; RH ⇒ nonneg; one negative value refutes RH; shells are vertical-line configurations |
| `RHTower.XiGaussianHeatHankelLadder` | **RH ↔ the Gaussian Hankel array is PSD**; the rung ladder |
| `RHTower.XiGaussianHeatTuranPairSum` | variance expansion of the minor; exact negative core `-4 (Im w)^2 exp(-2 t Re w)` |
| `RHTower.XiResolventTraceHankelCriterion` | **nonnegative resolvent traces ⇒ RH**; moments are the Euler-ray response |
| `RHTower.XiResolventHankelLadder` | the resolvent Hankel array; variance expansion; negative core |
| `RHTower.XiResolventLowRungVacuity` | **rungs 1–7 hold unconditionally** — quantitative blindness |
| `RHTower.VonMangoldtLogMomentHankel` | **the von Mangoldt log-moment array is PSD** — matrix positivity of the arithmetic side |
| `RHTower.XiResolventArchPrimeSplit` | the order-zero entry as archimedean minus prime; **archimedean dominates at order zero, unconditionally** |

All build clean, lint passes, axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.

## What was ruled out, with proof

1. **Scalar functionals are blind.**  The unfiltered Gaussian trace can be nonnegative while the
   divisor is not real (explicit witness: four on-line copies at `g = 14` plus an off-line quadruple
   at `g = 100, b = 1/10`).  Complete monotonicity of the scalar Euler-ray response is strictly
   weaker than RH.
2. **Low rungs of the resolvent ladder are vacuous.**  Rungs 1–7 are unconditional theorems, so
   they carry no information.  The corpus's unconditional two-node Euler-ray determinant lies
   inside that range, which explains its unconditionality.
3. **No fixed finite rung can decide RH.**  The detection order scales like
   `(g^2 + X) / (g |2 Re rho - 1|)`, and the displacement has no a priori positive lower bound.
4. **A better height floor makes detection harder, not easier** — the sector constant is `~1/sqrt H`,
   so a larger floor enlarges the vacuous initial segment.  (Correction of an earlier claim here.)
5. **The archimedean array is not known to be PSD.**  An earlier assertion to that effect is
   retracted; see below.

## What is open, in order of accessibility

1. **[elementary, no zeros, no primes]** Is
   `A(X) = [1/s + 1/(s-1) + logDeriv Gamma_R s] / x`, `s = 1/2 + x`, `x = sqrt X`, completely
   monotone on `X > 1/4`?  Necessary for RH; a negative answer refutes RH.  Its inverse Laplace
   density is `2 exp(t/4)` plus an explicit digamma integral minus `log pi / (2 sqrt(pi t))`, so
   this is a sign question about one explicit function.
2. **[the domination core]** `arch-array ⪰ prime-array` for the resolvent moments.  Order zero is
   now proved (`re_xiResolventMoment_zero_le_arch`); every higher order is open.
3. **[Gaussian lane]** `xiHeatTuranDefect t ≥ 0` for large `t` — equivalent to reality of the two
   lowest strata of the divisor, currently known only by interval arithmetic.
4. **[representation gap]** The corpus's `HTGeometry.PrimeDirichletPositiveDefinite` gives matrix
   positivity of the prime series along **vertical** lines; the ladder needs the derivative array at
   a **real** point.  Bridging them is a Poisson/Herglotz representation problem between two objects
   both already formalized.

## Honest labels

Every criterion in this block is `[REDISCOVERED]` as mathematics — moment positivity of a spectral
measure is the Hamburger/Stieltjes picture, and Weil positivity on a dense test family is classical.
What is `[NEW TO CORPUS]` is the exact theorems, the blindness classification with witnesses, the
quantitative vacuity threshold, and the arithmetic matrix positivity.  Nothing here proves RH.
