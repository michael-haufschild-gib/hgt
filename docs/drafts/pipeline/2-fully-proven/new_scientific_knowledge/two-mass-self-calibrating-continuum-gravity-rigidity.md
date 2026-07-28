# Two-mass self-calibrating continuum gravity rigidity

- **ID:** `two-mass-self-calibrating-continuum-gravity-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONTINUUM GRAVITY / CLOCKS / OPERATOR IDENTIFICATION
- **Parents:**
  `two-mass-self-calibrating-clock-metric-law.md`,
  `chronometric-continuum-operator-rigidity.md`
- **Status:** paper-proved and formalized unconditionally in Lean.

## Headline

> **Two kinds of clocks determine spacetime and its law of gravity—even when every detector has
> an unknown local calibration.**

This is the complete-data continuum theorem. It preserves nonlinear solution branches and makes
the remaining experimental/analytic gap explicit.

## Self-calibrating chronometric field

Let \(X\) be an event set and let \(V\) be a real model cotangent fiber. At every event \(x\), let

- \(\kappa(x)\neq0\) be an unknown common endpoint-calibration product;
- \(g_x^{-1}:V\times V\to\mathbb R\) be a symmetric bilinear inverse-metric form.

Choose two calibrated squared masses \(\mu_1\neq\mu_2\). The ideal complete two-mass observation is

\[
\begin{aligned}
  D(x)&=(\mu_1-\mu_2)\kappa(x),\\
  S(x,\xi)&=\kappa(x)g_x^{-1}(\xi,\xi).                                  \tag{1}
\end{aligned}
\]

For dressed inverse Green operators, \(D\) is their zeroth-order difference and \(S\) is the
quadratic principal-symbol channel.

## Theorem 1 — continuum metric and calibration injectivity

The map

\[
  (\kappa,g^{-1})\longmapsto(D,S)                                        \tag{2}
\]

is injective.

### Proof

The first channel gives calibration pointwise:

\[
  \kappa(x)=\frac{D(x)}{\mu_1-\mu_2}.                                    \tag{3}
\]

Since \(\kappa(x)\neq0\), the second channel gives every diagonal value

\[
  g_x^{-1}(\xi,\xi)=\frac{S(x,\xi)}{\kappa(x)}.                           \tag{4}
\]

Polarization gives every off-diagonal component:

\[
  2g_x^{-1}(\xi,\eta)
  =
  g_x^{-1}(\xi+\eta,\xi+\eta)
  -g_x^{-1}(\xi,\xi)
  -g_x^{-1}(\eta,\eta).                                                   \tag{5}
\]

Thus equal observations imply equal calibration fields and equal continuum metric fields.
\(\square\)

No signature, nondegeneracy, smoothness, analyticity, or field equation is required for this
injectivity theorem. Lorentzian signature is a physical restriction on the admissible recovered
forms, not an ingredient of the proof.

## Theorem 2 — branch-safe nonlinear gravity-operator rigidity

Let \(\mathcal G\) be the space of self-calibrating metric fields and let

\[
  \mathcal E:\mathcal G\to\mathcal J
\]

be any source operator; it need not be linear, perturbative, analytic, or single-valued after
solving for geometry. Define its branch-safe two-mass graph

\[
  \Gamma_{2m}(\mathcal E)
  =
  \left\{
    \bigl(\mathcal E(\kappa,g),D_{\kappa},S_{\kappa,g}\bigr):
    (\kappa,g)\in\mathcal G
  \right\}.                                                              \tag{6}
\]

Then

\[
  \boxed{
  \Gamma_{2m}(\mathcal E_1)=\Gamma_{2m}(\mathcal E_2)
  \quad\Longleftrightarrow\quad
  \mathcal E_1=\mathcal E_2.}                                            \tag{7}
\]

### Proof

The reverse implication is immediate. For the forward implication, fix
\((\kappa,g)\). Its graph point under \(\mathcal E_1\) occurs in the graph of
\(\mathcal E_2\), so there is \((\kappa',g')\) with the same two-mass observation and

\[
  \mathcal E_1(\kappa,g)=\mathcal E_2(\kappa',g').
\]

Theorem 1 forces \((\kappa',g')=(\kappa,g)\). Therefore the two operators agree at every field.
\(\square\)

## What is and is not solved

Equations `(2)` and `(7)` close the exact complete-data identifiability problem:

> Unknown local detector gain, conformal scale, multiple nonlinear solution branches, and
> arbitrary nonlinear operator dependence do not create a residual ambiguity once the complete
> two-mass symbol graph is known.

The remaining open core is not algebraic identifiability. It is physical realization:

1. recover complete complex dressed Green responses from finite clock interventions in a
   worldtube;
2. split causal/retarded support without assuming the unknown geometry;
3. prove common or known relative endpoint gain for two physical species;
4. include backreaction and conservation-constrained active sources;
5. pass from coordinate-trivialized fields to smooth Lorentzian bundles modulo diffeomorphism and
   gauge.

Until those steps close, `(7)` is a conditional continuum reconstruction theorem, not a claim that
Nature has already been experimentally reduced to two clock species.
