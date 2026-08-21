# Strict log-concavity cannot orient theta-source tilt flux

Status: Lean-formalized, unconditional no-go and survivor theorem. `[FORMAL-BRIDGE-NOVEL]`.
Does not prove RH.

## Formal theorem package

`ThetaSourceHorizontalFluxExtractor.lean` proves a source-independent horizontal extraction law:
if a `ThetaSource` transform vanishes at `A+b*I`, is nonzero at `b*I`, and `A>0`, then some
`0<a<A` has strictly negative diagonal `sourceBezoutian` at `a+b*I`.

`ThetaSourceStrictLogConcavityFluxNoGo.lean` constructs the explicit source

```text
k(x) = exp(-x^2) * (1 + epsilon*cos(3*x)),
epsilon = exp(9/4)/cosh(8).
```

Lean proves:

- `0 < epsilon < 1/8`;
- `k` is positive, even, continuous, and faster than every exponential;
- `log k` is globally strictly concave;
- its bilateral Laplace transform equals a nonvanishing Gaussian factor times
  `1 + cos(3*w/2)/cosh(8)`;
- the transform vanishes at `2*pi/3 + (16/3)*I` and is nonzero at `(16/3)*I`;
- some right-half-plane diagonal source Bezoutian is negative;
- equivalently, a literal one-mode neutral tilt correlation has strictly negative first derivative.

Closed declarations:

```text
exists_sourceBezoutian_diagonal_neg_of_horizontal_zero
bilateralLaplace_modulatedGaussianSource_rightZero
strictConcaveOn_log_modulatedGaussianKernel
exists_modulatedGaussianSource_tiltCorrelation_deriv_neg
exists_strictLogConcave_thetaSource_with_negative_flux
```

## Scientific consequence

The live TTF producer cannot follow from the qualitative source package supplied by positivity,
evenness, rapid decay, strict log-concavity, or their local reflected-midpoint/correlation-angle
consequences. A successful theorem must distinguish the completed theta-cusp source through a
genuinely global physical/frequency coupling. This does not select one replacement route; it rules
out an entire local-shape proof class and redirects search toward corpus-specific global rigidity.

The underlying modulated-Gaussian counterexample idea was already present on paper in
`5-failed/positive-even-schwartz-source-does-not-orient-fourier-current.md`; novelty claimed here is
the exact unconditional Lean closure and its weld to the live TTF neutral-flux carrier.

## Verification

- direct `lake env lean` source checks passed for both modules;
- exact target builds passed for both modules; no umbrella/full build was run;
- `#print axioms` for all five declarations reports only `propext`, `Classical.choice`, and
  `Quot.sound`;
- forbidden-declaration scan is empty.
