# Möbius–Mertens reversal-energy RH criterion

- **ID:** `mobius-mertens-reversal-energy-rh-criterion`
- **Status:** `[FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../needs-audit/mobius-mertens-self-convolution-rh-equivalence.md`
- **Source:** second-Cesàro additive Möbius triangle

## Exact statement

Let

\[
M(N)=\sum_{n\le N}\mu(n),\qquad
U(N)=\sum_{a+b=N}M(a)M(b).
\]

On the finite vector \(m_N=(M(0),\ldots,M(N))\), let \(J_N\) be coordinate reversal. Define

\[
P(N)=\frac14\sum_{a+b=N}(M(a)+M(b))^2,
\qquad
A(N)=\frac14\sum_{a+b=N}(M(a)-M(b))^2.                 \tag{1}
\]

Then

\[
U(N)=P(N)-A(N),\qquad P(N),A(N)\ge0.                   \tag{2}
\]

Consequently the following positive estimate implies RH:

\[
\forall\varepsilon>0\ \exists C_\varepsilon\ge0\ \forall N,
\quad P(N)\le C_\varepsilon(N+1)^{2+\varepsilon}.       \tag{3}
\]

Conversely RH implies (3), so (3) is paper-equivalent to RH.

## Proof

For real numbers \(u,v\),

\[
uv=\frac14\big((u+v)^2-(u-v)^2\big).
\]

Summing this identity over the antidiagonal \(a+b=N\) proves (2). In particular,
\(U(N)\le P(N)\). Under (3), the one-sided second-Cesàro estimate

\[
U(N)\le C_\varepsilon(N+1)^{2+\varepsilon}
\]

holds. The exact double-Abel identity already proved in the parent card then yields every strict
half-power bound for the discrete Möbius–Laplace transform, hence RH.

For the reverse direction, RH gives the classical Littlewood family

\[
|M(n)|\le C_\delta(n+1)^{1/2+\delta}
\]

for every \(\delta>0\). Fix \(\varepsilon>0\) and take \(\delta=\varepsilon/2\). For
\(a+b=N\),

\[
|M(a)+M(b)|^2
\le 2|M(a)|^2+2|M(b)|^2
\le 4C_\delta^2(N+1)^{1+2\delta}.
\]

There are \(N+1\) antidiagonal pairs, so

\[
P(N)\le C_\delta^2(N+1)^{2+2\delta}
      = C_\delta^2(N+1)^{2+\varepsilon}.
\]

This proves the equivalence.

## Mean-square normalization

Let

\[
E(N)=\sum_{a=0}^{N}M(a)^2.
\]

The same polarization gives

\[
P(N)+A(N)=E(N),                                         \tag{4}
\]

because coordinate reversal preserves Euclidean norm. Hence \(P(N)\le E(N)\). The all-ε
mean-square estimate

\[
E(N)=O_\varepsilon(N^{2+\varepsilon})                   \tag{5}
\]

therefore implies (3) and RH. RH implies (5) termwise by Littlewood, so (5) is also RH-equivalent.

The classical weak Mertens hypothesis

\[
\int_1^x (M(u)/u)^2\,du\ll\log x
\]

is substantially sharper; Titchmarsh proves it implies RH, simple zeros, and convergence of the
corresponding negative-zero moment. Thus (3) is not a disguised unconditional input.

## Hostile audit

1. **Verdict: `BRIDGE`.** This is an exact positive reformulation, not an RH proof.
2. **No positivity miracle.** Reversal has both \(+1\) and \(-1\) eigenspaces. Dropping the negative
   energy \(A(N)\) creates a stronger positive hypothesis, but RH supplies it back through the
   classical Mertens estimate.
3. **Generic Hilbert-space estimates overpay.** Cauchy–Schwarz bounds \(|U(N)|\) by \(E(N)\), thereby
   replacing the sharp signed excess \(P-A\) by total energy \(P+A\). Equation (2) records the exact
   loss.
4. **No novelty promotion.** The reversal polarization is elementary, and mean-square Mertens
   criteria sit inside classical RH theory. Targeted searches found no exact palindromic formula,
   but absence of wording is not scientific novelty.

## Literature boundary

- Titchmarsh, *The Theory of the Riemann Zeta-function*, §§14.25 and 14.28: Littlewood and weak
  Mertens criteria.
- Shōta Inoue, *Relations among some conjectures on the Möbius function and the Riemann
  zeta-function* (2017), records that weak Mertens implies RH and simple zeros and develops Riesz
  means under that hypothesis.
- Huxley–Watt, *Mertens Sums requiring Fewer Values of the Möbius function* (2018), studies spectral
  quadratic forms for a multiplicative-hyperbola matrix, not the additive reversal form (1).

## Formal targets

- exact decomposition (2);
- nonnegativity of both reversal energies;
- palindromic-energy subpower source implies the second-Cesàro source;
- hence palindromic-energy source implies RH;
- Mertens all-strict-half-power source implies palindromic-energy source;
- conditional iff interface once classical `RH → Mertens` is supplied.

## Formal verification

Module:

```text
formal/GaloisForLFunctions/RHTower/MobiusMertensReversalEnergyCriterion.lean
```

Lean proves the two energy nonnegativity laws, exact reversal polarization, positive source
transfer to the second-Cesaro criterion and RH, Mertens-to-energy transfer, and the conditional
Littlewood iff interface.  Direct `lake env lean` verification passes.  `#print axioms` for the
principal decomposition, RH connector, and iff theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`.
