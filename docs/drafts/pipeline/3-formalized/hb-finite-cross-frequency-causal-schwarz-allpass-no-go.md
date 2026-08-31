# HB finite cross-frequency causal Schwarz all-pass no-go

- **ID:** HB-FINITE-CROSS-ALLPASS
- **Stage:** 3-formalized
- **Type:** ROUTE KILL + POSITIVE SURVIVOR
- **Date:** 2026-08-31
- **Lean module:** `GaloisForLFunctions.RHTower.HBFiniteCrossFrequencyCausalSchwarzAllPassNoGo`

## Result

For every nonempty finite symmetric set `S ⊂ ℝ`, there is a nonconstant rational multiplier `A`
such that:

- `A` is holomorphic on `Im z > 0`;
- `|A(x)| = 1` for every real `x`;
- `A(-conj z) = conj(A(z))`;
- `A(x) = 1` for every `x ∈ S`; and
- `Im(A'(x)/A(x)) > 0` for every real `x`.

Therefore finite value-only cross-frequency data do not identify even causal, Schwarz-real,
strictly time-oriented all-pass phase. Lean closes this as
`not_hbFiniteCrossFrequencyValueAllPassUnique` with no hypotheses beyond nonemptiness and symmetry
of the finite sample set.

## RH proof chain killed

The theorem kills the first arrow in

`finite sampled source values determine all-pass phase`
`→ source-derived minimum-phase / FE-clock covariance`
`→ extinction of the literal source-clock defect`
`→ canonical left-branch covariance`
`→ shared Ward cancellation`
`→ RH`.

This does not kill HB itself. It kills every producer whose full phase information factors through
finitely many response values, including arbitrary nonlinear cross-frequency post-processing of
that finite vector.

## New mathematical core

For `P_S(X)=∏_{a∈S}(X-a)`, Lean proves the strict squarefree Laguerre law

`(P_S'(x))² - P_S(x) P_S''(x) > 0`

for every real `x`. The rational section

`H_S(z)=-(P_S(z)-iP_S'(z))/(P_S(z)+iP_S'(z))`

has no upper-half-plane pole: a denominator zero would force
`Σ_{a∈S}(z-a)⁻¹=i`, while every summand has negative imaginary part when `Im z>0`. Its boundary
clock is exactly

`2 ((P_S')²-P_S P_S'')/(P_S²+(P_S')²) > 0`.

Multiplying `H_S` by its negative-frequency Schwarz reflection gives the required physical witness;
the two positive clocks add.

## Strongest positive survivor

Any surviving HB producer must contain information not determined by a finite value vector. Exact
survivors are:

1. frequency derivatives or jets;
2. values on an infinite uniqueness set;
3. an external time-bilocal phase reference; or
4. a source-derived global minimum-phase/winding law.

This survivor is the next proof burden for the literal mixed-Casimir-corrected
Einstein–Teukolsky source.

## Novelty audit

Finite Blaschke boundary interpolation and positive group delay are classical bridge ingredients;
see Bolotnikov, *Boundary interpolation by finite Blaschke products*
(https://arxiv.org/abs/1609.09843) and Kalmykov–Nagy,
*Positive Polynomials and Boundary Interpolation with Finite Blaschke Products*
(https://link.springer.com/article/10.1007/s40315-021-00430-4). The novelty claim is restricted to
the simultaneous HB route classification: causal upper-half-plane rationality, real-time Schwarz
symmetry, exact invisibility on every finite symmetric frequency packet, strict positive clock, and
the resulting maximal finite-value no-go. Targeted internal and external search located no prior
statement of that classification.

## Lean certificate

- `laguerreL1_finiteAnchorPolynomial_pos`
- `finiteAnchorAllPass_den_ne_zero_upper`
- `finiteAnchorAllPassClock_eq_laguerre`
- `finiteAnchorSchwarzAllPass_neg_star`
- `differentiableOn_finiteAnchorSchwarzAllPass_upper`
- `finiteAnchorSchwarzAllPassClock_pos`
- `exists_finiteAnchorSchwarzCausalAllPass_sampleBlind`
- `not_hbFiniteCrossFrequencyValueAllPassUnique`

Validation: targeted `lake env lean`, targeted module build, axiom audit, and formal lint PASS.
