# Unweighted reciprocal work is globally proper — failed

- **Stage:** 5 — failed
- **Type:** FAILED CONJECTURE / ADAPTIVE-ESCAPE NO-GO
- **Status:** `[FALSIFIED] [SHARP POSITIVE SURVIVOR PROMOTED]`

## Conjecture

On a countable recovery fibre, the sum of the locally forced reciprocal works

\[
 W(x)=\sum_j\bigl(e^{x_j}+e^{-x_j}-2\bigr)
\]

has compact sublevels and therefore supplies global formation properness.

## Killing counterexample

Fix `t != 0` and let `x^(n)=t e_n`. Then

\[
 W(x^{(n)})=e^t+e^{-t}-2
\]

for every `n`, while the sequence has no convergent subsequence in `ell^1` and does not even become
Cauchy. Thus every fixed ray is detected and amplified, yet formation history can escape by moving
its active coordinate.

## Exact why

Local strict positivity controls amplitude but not location. Countable formation has a second
resource—complexity of the active coordinate—which the unweighted topology erased.

## Sharp positive survivor

For weights `a_j >= 1`, put

\[
 W_a(x)=\sum_j a_j^2\bigl(e^{x_j}+e^{-x_j}-2\bigr).
\]

ULF-RFTM-1 proves the exact boundary:

\[
 \text{all }W_a\text{-sublevels are compact in }\ell^1
 \quad\Longleftrightarrow\quad
 \sum_j a_j^{-2}<\infty.
\]

Failure of reciprocal-square summability produces a fixed-work family with unbounded `ell^1` norm;
summability gives uniform tail control and compactness. This is stronger than patching the
counterexample: it classifies the entire weighted chamber.

## Status of survivor

- Paper: dependency-closed, Stage 2.
- Lean: pending exact formalization.
