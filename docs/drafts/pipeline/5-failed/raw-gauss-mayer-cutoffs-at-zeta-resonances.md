# Uncorrected Gauss–Mayer branch cutoffs at zeta scattering parameters

- **Stage:** 5-failed
- **Type:** No-go with positive survivor
- **Parent:** [three approaches, A](../1-in-progress/argon-three-orthogonal-rh-approaches.md).

## Exact obstruction

On the disc algebra `|z−1|≤3/2`, let
`L_{s,N}f(z)=Σ_{n=1}^N(n+z)^(-2s)f(1/(n+z))`.
For every nontrivial zeta zero `ρ`, at `s=ρ/2`,

`‖L_{s,N}‖/N^(1−Re ρ) → 1/|1−ρ| > 0`.

These raw cutoffs diverge in operator norm at every actual zeta scattering
target, including critical zeros. Ordinary branch convergence cannot
separate critical and off-critical resonances. This retires only the
uncorrected operator-limit shortcut.

## Strongest positive survivors

- **Actual operator:** For `Re s>0`, `s≠1/2`, subtracting
  `N^(1−2s)P/(1−2s)`, `Pf=f(0)1`, gives norm convergence with error
  `O(N^(-2 Re s))`. On `0<Re s<1/2`, this leading correction is unique
  among bounded corrections of the same power scale. The corrected source
  agrees with the ordinary sum for `Re s>1/2`. [Proof and certificate](../3-formalized/gauss-mayer-renormalized-cutoff-operator.md).
- **Actual determinants:** With `w=2s`, `a_N=Σ_{n≤N}n^(-w)`, and
  `D=A+ζB`, the genuine finite-branch determinants obey `E_N−a_NB→A`
  for every `Re w>0` and every spectral parameter. In `0<Re w<1`,
  raw determinant convergence is equivalent to `B=0`; otherwise its
  exact norm-growth coefficient is `|B|/|1−w|` at scale `N^(1−Re w)`.
  [Exact finite part and certificate](../3-formalized/gauss-mayer-raw-determinant-finite-part.md).
- **Negative unit:** The exact successor response makes `B(w,−1)=0`
  throughout `Re w>0`; raw determinants therefore converge even where
  raw operator norms diverge. Their limit is holomorphic through one
  and nonzero for every positive real `w`. [Cancellation](../3-formalized/gauss-mayer-negative-unit-pole-cancellation.md),
  [raw limit](../3-formalized/gauss-mayer-raw-negative-unit-determinants.md),
  [real nonvanishing](../3-formalized/gauss-mayer-negative-unit-real-nonvanishing.md).
- **Actual inverse:** Every real-source scalar-mode perturbation is invertible
  with explicit successor-shear inverse. At `w=1`, the actual source inverse
  retains a nonzero rank-one pole while the negative-unit determinant is
  holomorphic and nonzero. [Exact inverse and residue certificate](../3-formalized/gauss-mayer-negative-unit-resolvent-pole.md).
- **Positive real coefficient:** `B(w,λ)≠0` for real `w>0`,
  `0<λ<(3/2)^w`; `D(w,1)` has a genuine simple pole at one.
  [Source cone, complementary determinant, and certificate](../3-formalized/gauss-mayer-positive-real-pole-coefficient.md).

## New insight and status

The scalar coefficient `B`, not raw operator-norm convergence, determines
raw determinant convergence. Negative-unit cancellation and positive-unit
noncancellation occur in the same actual source family. Determinant cancellation
does not remove the inverse's source pole.

All named survivors have dependency-closed paper proofs, direct Lean
checks, umbrella imports, and transitive audits containing only `propext`,
`Classical.choice`, and `Quot.sound`. The source's
[order-zero nuclear expansion](../3-formalized/gauss-mayer-renormalized-nuclear-expansion.md)
and [global determinant/invertibility identity](../3-formalized/gauss-mayer-source-fredholm-determinant.md)
supply the actual operator framework. Primitive geodesic coding,
Selberg/scattering comparison, and complex-source resonance exclusion remain
open. The full scattering paradigm is not retired.
