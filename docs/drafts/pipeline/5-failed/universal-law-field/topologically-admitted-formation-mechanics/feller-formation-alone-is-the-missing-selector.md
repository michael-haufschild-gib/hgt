# Feller formation alone is the missing selector

- **ID:** ULF-TAFM-NG2
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** hostile audit of ULF-TAFM-2 and the proposed topological admission doctrine
- **Statement:** Full-support mutually singular source laws cannot form arbitrarily deep copies of
  a fixed nonneutral finite experiment through exact Feller kernels.
- **Status:** `[FALSIFIED ON PAPER] [EXACT COUNTERMODEL] [POSITIVE SURVIVOR PAPER-PROVED]`
  `[LEAN CERTIFICATION OPEN: CURRENT RESEARCH PHASE FORBIDS LEAN WRITES/BUILDS]`

## Goal

If true, Feller continuity would close the singular-source loophole without an additional compact
effect hull or uniform modulus theorem.

It is false.

## Exact killing mechanism

Choose distinct Bernoulli laws \(q_0,q_1\) on \(Y=\{0,1\}\), both with parameters in \((0,1)\).
Let

\[
 X=Y^{\mathbb N},
 \qquad
 \mu_i=q_i^{\otimes\mathbb N}.
\]

Both product laws have full support. They are mutually singular by the strong law of large numbers:
the limiting empirical one-frequency equals the parameter of \(q_i\) almost surely.

For every \(d\ge1\), prefix projection

\[
 K_d(x)= (x_0,\ldots,x_{d-1})
\]

is deterministic, continuous, hence Feller, and satisfies

\[
 (K_d)_*\mu_i=q_i^{\otimes d}.
\]

Thus one fixed full-support singular source pair admits exact nonneutral Feller formation at every
depth.

For the standard product ultrametric

\[
 d_\theta(x,x')=\theta^{\min\{n:x_n\ne x'_n\}},
 \qquad0<\theta<1,
\]

and the discrete target metric, the pullback Lipschitz amplification is exactly

\[
 \alpha(K_d)=\theta^{-(d-1)}.
\]

The theorem fails because individual continuity permits the modulus to deteriorate with depth.

## No-go closure

- **Exact killing theorem/mechanism:** iid Bernoulli prefix projection gives an all-depth exact
  deterministic Feller formation from two mutually singular full-support laws.
- **Strongest positive survivor:** the dependency-closed paper theorem ULF-TAFM-3,
  `../../../2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/resolution-price-formation-conservation-prefix-localization-and-feller-escape-law.md`,
  proves that every such formation must pay diverging morphism resolution amplification and gives
  the exact value \(\theta^{-(d-1)}\) in this countermodel.
- **New insight:** admission is not a binary property “measurable versus Feller.” It is a filtered,
  compositional resource indexed by pullback resolution price. A viable selector needs a
  source-derived uniform price bound, compact modulus, or equivalent properness theorem.
- **Status:** falsifier and positive survivor are dependency-closed on paper. Lean formalization is
  mandatory before either counts as truly proven under project standard; it is deferred only
  because the active field-research phase explicitly prohibits Lean writes and builds. Missing
  infrastructure will be built rather than used as a pivot when formalization begins.

## Consequence for field programme

Replace

\[
 \text{“Feller formation has bounded nonneutral depth”}
\]

by

\[
 \boxed{
 \text{“all-depth nonneutral Feller formation forces unbounded compositional resolution price.”}}
\]

This is a mechanism-level correction. It does not redirect work into a specific RH route.

## Gates

- [x] 0 -> 1: exact source-pure falsifier
- [x] 1 -> 2: complete paper proof and strongest positive survivor
- [ ] 2 -> 3: unconditional Lean formalization and axiom audit

## Log

- 2026-08-31 -- falsified by iid Bernoulli product source and continuous prefix formations; exact
  exponential resolution-price survivor proved in ULF-TAFM-3.
