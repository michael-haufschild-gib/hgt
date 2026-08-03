# Two-species conformal clock scale law

- **ID:** `two-species-conformal-clock-scale-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONTINUUM GRAVITY / CLOCKS / CONFORMAL SCALE / INVERSE PROBLEM
- **Parent:** `../../1-in-progress/continuum-chronometric-equivalence-theorem.md`
- **Status:** differential-geometric identity and algebraic scale theorem paper-proved; algebraic
  separation unconditional in Lean; smooth conformal wave-operator formalization and inverse-data
  realization open.

## Headline

> **Light gives spacetime its shape. Two different clocks give it size.**

Sharper mathematical form:

> **Two scalar clock species with different calibrated masses determine the conformal scale
> algebraically.**

This targets the exact gap left by nonlinear Lorentzian inverse theorems, which commonly recover
only conformal geometry from light-cone interactions.

## Conformal clock operator

Let \((M,g)\) be a \(d\)-dimensional Lorentzian manifold, \(d\geq 3\), and let

\[
  \widetilde g=e^{2\sigma}g,\qquad
  a=\frac{d-2}{2}.                                                         \tag{1}
\]

For a minimally coupled scalar clock species of squared mass \(\mu=m^2\), define the conjugated
Klein--Gordon operator

\[
  \mathcal P_\mu^\sigma
  =
  e^{(a+2)\sigma}
  \bigl(\Box_{\widetilde g}+\mu\bigr)
  e^{-a\sigma}.                                                            \tag{2}
\]

## Theorem 1 — exact conformal conjugation

\[
  \boxed{
  \mathcal P_\mu^\sigma
  =
  \Box_g+V_\mu^\sigma,}
  \qquad
  V_\mu^\sigma
  =
  \mu e^{2\sigma}
  -a\Box_g\sigma
  -a^2\langle d\sigma,d\sigma\rangle_g.                                   \tag{3}
\]

### Proof

For every scalar \(f\),

\[
  \Box_{\widetilde g}f
  =
  e^{-2\sigma}
  \left(
    \Box_g f+(d-2)\langle d\sigma,df\rangle_g
  \right).                                                                \tag{4}
\]

Set \(f=e^{-a\sigma}u\). Product and chain rules give

\[
\begin{aligned}
  \Box_g(e^{-a\sigma}u)
  =e^{-a\sigma}\bigl(
    \Box_g u
    -2a\langle d\sigma,du\rangle_g
    +(a^2|d\sigma|_g^2-a\Box_g\sigma)u
  \bigr),\\
  2a\langle d\sigma,d(e^{-a\sigma}u)\rangle_g
  =e^{-a\sigma}\bigl(
    2a\langle d\sigma,du\rangle_g
    -2a^2|d\sigma|_g^2u
  \bigr).
\end{aligned}                                                             \tag{5}
\]

The first-derivative terms cancel. Multiplying the result by
\(e^{(a+2)\sigma}\), and adding the mass term, yields `(3)`. \(\square\)

In four dimensions \(a=1\), so

\[
  V_\mu^\sigma
  =
  \mu e^{2\sigma}-\Box_g\sigma-|d\sigma|_g^2.                              \tag{6}
\]

## Theorem 2 — two species reconstruct conformal scale

Let \(\mu_1\neq\mu_2\) be two independently calibrated squared masses. Then

\[
  \boxed{
  e^{2\sigma}
  =
  \frac{V_{\mu_1}^\sigma-V_{\mu_2}^\sigma}
       {\mu_1-\mu_2}.}                                                     \tag{7}
\]

### Proof

Subtract the two instances of `(3)`. The terms
\(-a\Box_g\sigma-a^2|d\sigma|_g^2\) are identical for both species and cancel:

\[
  V_{\mu_1}^\sigma-V_{\mu_2}^\sigma
  =
  (\mu_1-\mu_2)e^{2\sigma}.
\]

Division by the nonzero calibrated mass difference proves `(7)`. \(\square\)

The same pair also reconstructs the shared geometric defect

\[
  D_\sigma=a\Box_g\sigma+a^2|d\sigma|_g^2
  =
  \mu_1e^{2\sigma}-V_{\mu_1}^\sigma.                                      \tag{8}
\]

Thus the map

\[
  (e^{2\sigma},D_\sigma)
  \longmapsto
  (V_{\mu_1}^\sigma,V_{\mu_2}^\sigma)
\]

is injective whenever \(\mu_1\neq\mu_2\). This algebraic injectivity and formula `(7)` are
unconditional in Lean.

## Why one species is structurally weaker

One recovered potential gives only

\[
  V_\mu^\sigma=\mu e^{2\sigma}-D_\sigma,
\]

which mixes scale with a derivative defect. A second mass supplies a second equation with the same
defect and a different scale coefficient. The cancellation in `(7)` does not require integrating a
nonlinear hyperbolic equation or imposing analytic continuation.

This is not a claim that one species can never recover scale with additional boundary data. It is
the exact statement that two species remove the ambiguity pointwise and algebraically.

## Continuum-gravity bridge

Published active inverse results for Einstein--scalar systems recover topology, smooth structure,
and conformal class in the causal diamond of a worldtube under nondegenerate scalar-reference and
source-control hypotheses. To upgrade conformal class to metric:

1. reconstruct the effective zeroth-order potentials of two calibrated scalar probe species;
2. apply `(7)` pointwise to recover \(e^{2\sigma}\);
3. combine with conformal geometry to recover the full metric;
4. combine full metric response with chronometric graph rigidity to identify the complete metric
   gravity operator.

Step 2 is closed. Step 1 is the hard remaining inverse theorem in the coupled backreacting
Einstein--scalar setting. Existing potential-recovery theorems treat semilinear waves on a fixed
Lorentzian geometry and do not by themselves close this coupled bridge.

## Hypertranscendence role

The two species must remain operationally distinguishable after propagation and reporter mixing.
The corpus already proves that a complete clock compass preserves DA/HT species and contains exact
strong-field response sectors whose differential species depend on scalar gap. This supplies a
candidate invariant barcode for the \(\mu_1\) and \(\mu_2\) channels.

HT is not used to prove `(7)`. The new HT task is to prove that two calibrated mass channels cannot
be exchanged or collapsed by admissible DA exterior matching while their clock response species
are distinct.

## Hostile audit

1. **Conformal coupling:** `(3)` is for minimally coupled Klein--Gordon operators. A conformally
   coupled massless scalar has extra covariance and can be scale-blind.
2. **Mass renormalization:** \(\mu_i\) must be independently calibrated physical pole masses, not
   theory-dependent coordinate labels.
3. **Field redefinitions:** the common conjugation weight in `(2)` must be fixed by the same
   reporter normalization for both species.
4. **Backreaction:** the inverse experiment must separate each probe potential while both fields
   alter the metric.
5. **Potential recovery:** wavefront locations alone recover conformal geometry, not the
   zeroth-order amplitudes required by `(7)`.
6. **Species mixing:** a non-diagonal mass matrix must first be reconstructed and diagonalized by
   physical source/reporter channels.
7. **Clock-dark sector:** a scale mode invisible to both probe species defeats the operational
   bridge and violates detector completeness.

## Lean status

Unconditional in
`formal/GaloisForLFunctions/HTGeometry/ContinuumChronometricGravity.lean`:

- `twoSpeciesConformalPotential_difference`;
- `twoSpeciesConformalScale_reconstruction`;
- `twoSpeciesConformalPotentialPair_injective`.

`formal/GaloisForLFunctions/HTGeometry/ConformalClockDiffusion.lean` now also formalizes the exact
general-dimensional exponential calculation in an abstract second-order clock calculus:

- `ExponentialSecondOrderClockCalculus.conformalWaveSigma_conjugation`;
- `ExponentialSecondOrderClockCalculus.conformalKleinGordonSigma_conjugation`;
- `ExponentialSecondOrderClockCalculus.conformalWaveSigma_dimension_conjugation`;
- `ExponentialSecondOrderClockCalculus.conformalKleinGordonSigma_dimension_conjugation`.

These theorems prove the chain/product-rule expansion, first-derivative cancellation, geometric
defect, and mass term at `a=(d-2)/2` without assuming the displayed conclusion.

Missing:

1. realization of the abstract calculus by smooth pseudo-Riemannian conformal metric rescaling and
   the literal scalar d'Alembertian formula `(4)`;
2. coupled inverse theorem recovering both effective potentials from clock data.

## Closest SOTA

- Y. Kurylev, M. Lassas, L. Oksanen, and G. Uhlmann,
  *Inverse problem for Einstein--scalar field equations*,
  <https://arxiv.org/abs/1406.4776>.
- M. Lassas, G. Uhlmann, and Y. Wang,
  *Inverse problems for semilinear wave equations on Lorentzian manifolds*,
  <https://arxiv.org/abs/1606.06261>.
- A. Feizmohammadi and L. Oksanen,
  *Recovery of zeroth order coefficients in non-linear wave equations*,
  <https://arxiv.org/abs/1903.12636>.
- N. Pinamonti,
  *Conformal generally covariant quantum field theory: the scalar field and its Wick products*,
  <https://arxiv.org/abs/0806.0803>.

Targeted searches found no prior result stating the two-mass cancellation `(7)` as a Lorentzian
inverse-gravity scale reconstruction theorem. This is a priority claim, not an exhaustive
bibliographic guarantee.
