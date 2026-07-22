# Möbius–Mertens self-convolution criterion for RH

- **ID:** `mobius-mertens-self-convolution-rh-equivalence`
- **Status:** `[FORMALIZED] [BRIDGE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** Möbius–Laplace continuation wall
- **Claim grade:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]`

## Statement

Write

\[
M(N)=\sum_{1\le n\le N}\mu(n),\qquad
T(N)=\sum_{m+n\le N}\mu(m)\mu(n),
\]

and define the second cumulative triangle

\[
U(N)=\sum_{k\le N}T(k).
\]

Then the following are equivalent:

1. the Riemann hypothesis;
2. for every \(\varepsilon>0\), there is \(C_\varepsilon\ge0\) such that
   \[
   U(N)\le C_\varepsilon(N+1)^{2+\varepsilon}\qquad(N\ge0).
   \]

Only a one-sided upper bound is required in (2). The exact finite identity

\[
U(N)=\sum_{a+b=N}M(a)M(b)                                      \tag{1}
\]

shows that the source is additive self-convolution of the Mertens function, not binary Möbius
correlation at a single derivative level.

## Exact double-Abel identity

For \(0<z<1\), put

\[
A(z)=\sum_{n\ge1}\mu(n)z^n,\qquad B(z)=\sum_{N\ge0}M(N)z^N.
\]

Finite summation gives

\[
B(z)=\frac{A(z)}{1-z}.
\]

The coefficient of \(z^N\) in \(B(z)^2\) is the right side of (1). On the other hand, the
coefficient of \(z^N\) in \(A(z)^2/(1-z)^2\) is

\[
\sum_{k\le N}\sum_{m+n\le k}\mu(m)\mu(n)=U(N).
\]

Absolute convergence for \(|z|<1\) therefore proves both (1) and

\[
A(z)^2=(1-z)^2\sum_{N\ge0}U(N)z^N.                              \tag{2}
\]

## Forward implication

Assume (2)'s coefficient bound for every positive \(\varepsilon\). Set \(z=e^{-x}\),
\(0<x\le1\), and \(\Phi(x)=A(e^{-x})\). Since \(\Phi(x)\) is real, (2) is a nonnegative real
identity. Termwise use of the one-sided hypothesis is valid and gives

\[
|\Phi(x)|^2
\le (1-e^{-x})^2 C_\varepsilon
    \sum_{N\ge0}(N+1)^{2+\varepsilon}e^{-Nx}.
\]

The exponential moment has the Gamma bound

\[
\sum_{N\ge0}(N+1)^{2+\varepsilon}e^{-Nx}
\le K_\varepsilon x^{-(3+\varepsilon)},
\]

and \(1-e^{-x}\le x\). Hence

\[
|\Phi(x)|^2\le C_\varepsilon K_\varepsilon x^{-(1+\varepsilon)},
\qquad
|\Phi(x)|\le (C_\varepsilon K_\varepsilon)^{1/2}
x^{-1/2-\varepsilon/2}.                                        \tag{3}
\]

Because the hypothesis holds for every \(\varepsilon>0\), (3) supplies every strict
half-power bound. The already proved decay-to-Mellin-continuation bridge makes
\(\Gamma(s)/\zeta(s)\) analytic on \(\Re s>1/2\), excluding every zeta zero there. Functional
equation symmetry gives RH.

## Reverse implication

The classical Littlewood criterion says RH is equivalent to

\[
M(N)=O_\delta(N^{1/2+\delta})\quad\text{for every }\delta>0.     \tag{4}
\]

Assume RH and fix \(\varepsilon>0\). Apply (4) with \(\delta=\varepsilon/2\). Identity (1)
and the triangle inequality give

\[
\begin{aligned}
|U(N)|
&\le C_\delta^2\sum_{a+b=N}
  (a+1)^{1/2+\delta}(b+1)^{1/2+\delta}\\
&\le C_\delta^2(N+1)^{2+2\delta}
 = C_\delta^2(N+1)^{2+\varepsilon}.
\end{aligned}
\]

This absolute estimate implies the required one-sided estimate.

## Hostile audit

1. **No unconditional RH input is hidden.** Forward direction uses only exact Abel identities,
   exponential-moment comparison, and the existing Mellin wall. Reverse direction is explicitly
   conditional on classical Littlewood equivalence.
2. **One-sided sign is sufficient but not vacuous.** Individual \(U(N)\) need not be nonnegative.
   Positivity enters only after Abel summation because the full generating function is the real
   square \(\Phi(x)^2/(1-e^{-x})^2\).
3. **Exponent is sharp at scale.** A fixed estimate \(U(N)=O(N^{2+\varepsilon_0})\) yields only
   \(|\Phi(x)|=O(x^{-1/2-\varepsilon_0/2})\). The all-\(\varepsilon\) family is needed to reach
   every half-plane \(\Re s>1/2\).
4. **This is weaker than the first-cumulative binary-Chowla source.** The earlier sufficient
   condition \(T(N)=O_\varepsilon(N^{1+\varepsilon})\) implies this criterion after summation.
   Converse is not asserted. The second cumulative average is exactly what restores equivalence
   with the classical Mertens formulation.
5. **No claim that RH is proved.** Criterion relocates RH into a one-sided additive quadratic
   estimate. Unconditional proof of that estimate remains open.

## Corpus and literature audit

Corpus searches over `formal/`, formalised cards, fully-proved cards, failed routes, and support
extraction found the first-cumulative additive triangle and Mellin wall, but no second-cumulative
identity (1), no double-Abel criterion, and no equivalence statement above.

Targeted literature searches for “Mertens function additive/self convolution RH criterion”,
“sum M(a)M(n-a) Riemann hypothesis”, and “Cesàro additive convolution Möbius Laplace” found:

- the classical Littlewood equivalence, cited as Titchmarsh, Theorem 14.25(c), in current
  peer-reviewed literature;
- work on ordinary or Dirichlet Möbius convolutions, not the one-sided second-Cesàro additive
  criterion here;
- an unrelated MathOverflow question about simultaneous zeros of coefficients of
  \(1/\zeta(s)^k\).

No matching published statement was located. This is evidence only, not proof of novelty; retain
`[NOVELTY UNVERIFIED]` pending expert review.

## Formalisation targets

- `mobiusMertensPartialSum`
- `mobiusAdditiveTriangleSecondCesaro`
- exact finite identity (1)
- exact double-Abel identity (2)
- one-sided subpower bound implies every strict half-power Möbius–Laplace decay
- one-sided subpower bound implies RH
- Mertens all-strict-half-power bound implies the second-Cesàro source bound

## Formalisation milestone — 2026-07-22

Implemented in
`formal/GaloisForLFunctions/RHTower/MobiusMertensSelfConvolutionCriterion.lean`:

- `mobiusAdditiveTriangleSecondCesaro_eq_mobiusMertensSelfConvolution`: exact finite identity (1),
  proved coefficientwise in the formal power-series ring;
- `mobiusDiscreteLaplaceTransform_sq_eq_one_sub_exp_sq_mul_tsum_secondCesaro`: exact identity (2);
- `norm_sq_mobiusDiscreteLaplaceTransform_le_of_secondCesaroSubpowerUpperBound`: explicit Gamma
  estimate yielding (3);
- `mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_implies_riemannHypothesis`;
- `mobiusMertensAllStrictHalfPowerBound_implies_secondCesaroSubpowerUpperBound`;
- `mobiusMertensAllStrictHalfPowerBound_implies_riemannHypothesis`;
- `mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_iff_riemannHypothesis_of_mertens`, the
  exact conditional iff interface after supplying classical Littlewood.

Direct `lake env lean` verification succeeds. `#print axioms` for all endpoint theorems reports only
`propext`, `Classical.choice`, and `Quot.sound`. Formal lint reaches the new module through the
RHTower umbrella; remaining lint errors are unrelated unreachable `HTGeometry` modules.

The paper-level reverse implication RH → the Mertens all-strict-half-power estimate is classical
Littlewood.  It is not reproved here; the formal iff theorem accepts it as an explicit function
argument, keeping the new finite/double-Abel bridge assumption-transparent.
