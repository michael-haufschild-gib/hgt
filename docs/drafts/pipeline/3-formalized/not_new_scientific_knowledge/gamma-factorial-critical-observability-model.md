# Gamma's factorial conormal is an injective compact reporter with nonclosed range

- **ID:** `gamma-factorial-critical-observability-model`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / NATURAL CRITICAL-OBSERVABILITY MODEL
- **Register:** `[PROVED] [FORMALIZED] [BRIDGE] [PARENT OPERATOR THEORY] [NOT A NOVELTY CLAIM]`
- **Parents:**
  - `../gamma-periodic-constraint-corona.md`
  - `gamma-factorial-corona-comparison.md`
  - `source-gauge-observability-trichotomy.md`
- **Statement:** The source-normalized Gamma Taylor conormal coefficients `1/(n+1)!` define an
  injective Hilbert--Schmidt reporter on the square-summable clock completion. Its range is not
  closed, and the standard unit clocks form an explicit approximate-null sequence with exact
  observation norm `1/(n+1)!`.

## Source-normalized operator

The Gamma unit-shift conormal has coefficients

```text
lambda_n=1/(n+1)!.                                         (1)
```

These are not fitted spectral weights: the earlier Gamma corona theorem derives them from Taylor
translation by one, and the factorial-corona comparison proves that the normalized diagonal scale
is forced by source intertwining.

On `l2(N)`, define

```text
(A_Gamma x)_n=lambda_n x_n.                                (2)
```

Lean proves that the diagonal kernel of `(2)` is Hilbert--Schmidt, hence `A_Gamma` is compact.
Since every `lambda_n` is nonzero, it is injective. For the standard unit clock `e_n`,

```text
||A_Gamma e_n||=lambda_n -> 0.                             (3)
```

Therefore

```text
ker A_Gamma={0},
range(A_Gamma) is not closed,
no anti-Lipschitz observability bound exists.               (4)
```

This is the exact middle phase of the source-gauge observability trichotomy: algebraically every
clock coordinate is retained, but normalized high clocks become factorially invisible.

## Positive statement

The Gamma source supplies a concrete model of

```text
infinite clock capacity concentrated on a thin constraint boundary.  (5)
```

The previously proved Fourier interpolation theorem realizes every finite jet packet. Equations
`(1)`--`(4)` now add the missing topological statement: the all-clock conormal is complete only
through an injective nonclosed-range reporter. Finite windows see no loss, yet the inverse
conditioning diverges factorially at the infinite boundary.

This corrects an overstrong conclusion from the compact-source wall. A canonical HT section need
not lie in the stable phase. Gamma shows the natural critical possibility:

```text
unique/algebraically conservative but noncoercive.           (6)
```

A noncompact transverse channel is necessary for **stable** reconstruction, not necessarily for
global uniqueness selected by a nonlinear all-scale cone such as log-convexity.

## Novelty gate

Diagonal Hilbert--Schmidt operators, compactness, factorial decay, and the closed-range criterion
are classical. The Gamma conormal coefficients and their source-normalized diagonal comparison
were already established in the project from classical Taylor translation. Exact searches found
no paper packaging `(1)`--`(6)` as a Gamma observability spectrum, but the proof is a direct
combination of parent facts and does not clear the significance gate as standalone new science.

The result is nevertheless a decisive natural model for the candidate-new conjecture in
`../../1-in-progress/hypertranscendental-conservativity-spectrum.md`: natural constrained HT
sections may live at a presentation-invariant critical observability boundary whose zero-mode
field is shared by different realization categories.

## Lean certificate

`formal/GaloisForLFunctions/HTGeometry/GammaFactorialObservabilitySpectrum.lean` proves:

- `summable_normSq_gammaPeriodicConormalCoefficient`;
- `gammaFactorialObservabilityKernel_isHS`;
- `gammaFactorialObservabilityOperator_single`;
- `gammaFactorialObservabilityOperator_isCompact`;
- `gammaFactorialObservabilityOperator_apply`;
- `gammaFactorialObservabilityOperator_injective`;
- `norm_gammaFactorialObservabilityOperator_single`;
- `tendsto_norm_gammaPeriodicConormalCoefficient_zero`;
- `gammaFactorialObservabilityOperator_hasApproximateUnitKernel`;
- `gammaFactorialObservabilityOperator_not_isClosed_range`;
- `gammaFactorialObservabilityOperator_not_stablyConservative`.

The certificate has no `sorry`, `admit`, project axiom, opaque postulate, unsafe declaration, or
numerical computation.

## Gates

- [x] source-forced factorial weights reused
- [x] Hilbert--Schmidt summability proved
- [x] compactness proved
- [x] algebraic injectivity proved
- [x] exact factorial singular scale on unit clocks proved
- [x] normalized approximate-null sequence proved
- [x] nonclosed range and failure of stable conservativity proved
- [x] novelty and significance downgrade recorded
- [x] formalized in Lean
