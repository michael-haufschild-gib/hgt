# SQB quarter-shift source equation

Status: 21 public declarations formalized and individually audited, using only
`propext`, `Classical.choice`, and `Quot.sound`. RH remains unproved.

Full chain: original modular source → entire-transform operator and admitted cusp
packets → independent occurrence at every full Xi parameter → critical-line
classifier → RH. The frontier map is read-only.

The entire scalar transform satisfies F((s+1/4)(1−s−1/4))=F(s(1−s)).
The existing packet construction has exact full-Xi defect zero precisely at the
critical line. A quarter shift must therefore act on the source field, retain its
full differential equation, and justify modular descent and domain admission.

## Exact source and differential transport

Write `s=u+1/2`. The original complete field is

`E_u(x,y)=Lambda(2u)y^(1/2−u)+Lambda(1+2u)y^(1/2+u)+T_u(x,y)`.

T retains both signed infinite Fourier–Bessel tails with the original factor two.
The existing corpus proves all spatial derivatives and
`Delta_H E_u=(u²−1/4)E_u` at every complex u and positive height.
No truncation or constant-term replacement occurs.

The complete second product rule gives, for complex a and every C² field f,

`Delta_H(y^a f)=y^a[Delta_H f+a(a−1)f+2a y partial_y f]`.

Put `v_u=y^(−1/4)E_u`, `C=−Delta_H`, and
`D_u=y partial_y E_u−(1/2−u)E_u`. Then

`(C−(u+3/4)(1/4−u))v_u=(1/2)y^(−1/4)D_u`.

The generic lemmas use ordinary local regularity hypotheses. The actual-source
specializations discharge that regularity from the full Fourier–Bessel source;
no eigen-equation, derivative identity, or RH premise is supplied externally.

## Actual Xi specialization and retained Fourier forcing

For an actual multiplicity-marked Xi zero rho use the existing physical parameter
`u=(rho−1)/2`, so `s=rho/2`. The canonical actual vertical derivative equals its
full differentiated Weyl sector plus the full vertical Fourier jet. On y≥1,

`D_u=2u Lambda(1+2u)y^(1/2+u)+[y partial_y T_u−(1/2−u)T_u]`.

The Xi source gives `Lambda(rho)=0`; hence the first term vanishes. The outgoing
Weyl coefficient `Lambda(rho−1)` is nonzero. The original completion identity,
functional equation and zero-free right half-plane establish that nonvanishing
in the existing source calibration, which the new proof reuses.

The remaining defect is exactly the bracketed Fourier expression. Existing
all-power bounds for the actual vertical Fourier jet and the complete tail imply,
for each fixed real x and complex w,

`y^w D_((rho−1)/2)(x,y) → 0`.

The same is proved for the full shifted Casimir residual

`y^w [(C−(rho/2+1/4)(1−rho/2−1/4))v_((rho−1)/2)](x,y) → 0`.

These are limits on each fixed vertical ray. They are not a claim of a uniform
Hilbert-space residual estimate, unit-vector normalization, or domain admission.
No estimate for the infinite-order entire-transform operator follows from this
second-order differential identity alone.

## Exact modular transport and unique power compensation

Let `S(x,y)=(-x/Q,y/Q)` with `Q=x²+y²>0`. The original full Xi source is invariant
under S, by its source-derived modular continuation. The shifted source satisfies

`Q^(−1/4) v_u(S(x,y))=v_u(x,y)`.

It fails scalar inversion invariance for every actual Xi copy. The proof does not
assume a selected field value is nonzero: on every positive horizontal line,
the actual mean is `Lambda(rho−1)y^(1−rho/2)≠0`, so the field is nonzero somewhere.
Choose such a point at y=2, where Q>1. Invariance of v would force Q^(−1/4)=1,
contradicting the strict real-power inequality.

For every real b the exact weighted squared norm is

`y^b |v_u(x,y)|²=y^(b−1/2)|E_u(x,y)|²`.

For each actual Xi copy, the density on the left is inversion invariant at every
point **if and only if b=1/2**. The reverse direction is original source invariance.
For necessity, a nonzero point at y=2 cancels the positive squared norm; if
b−1/2 is nonzero, injectivity of the real power on positive heights would force
y/Q=y, contradicting Q>1.

Thus the unique compensating power gives

`y^(1/2)|v_u(x,y)|²=|E_u(x,y)|²`.

This is an exact positive survivor: differential forcing, rapid Fourier remainder,
modular multiplier, and a sharp classification of compatible power densities.
The literal multiplier is not a scalar automorphic occurrence map. The results do
not exclude a different intertwiner, a nonlocal correction, or a different
independently constructed automorphic carrier. SQB remains live.

## Search coverage and plan

Broad OR searches through `scripts/formal_tools.py research`, with no per-module
cap, found 1,709 declarations in 228 modules for Darboux, intertwiners, Maass,
gauge/ground-state transforms, Dedekind and weight shifts; another found 171
declarations in 109 modules for Laplacians, product rules and covariant
derivatives. This is index coverage, not a claim to have read every proof.
A further broad OR search for theta lifts, metaplectic structures, fractional
derivatives, transmutation, Sonine, Poisson transforms and line bundles found
613 declarations in 115 modules. Inspected generic functional-calculus
intertwining preserves an already supplied operator intertwining relation; the
rotating-quadratic metaplectic example records orientation under a loop. Neither
constructs the missing modular Xi source map.
Inspected mechanisms include actual Maass Möbius transport, the complete scalar
two-jet product calculus, theta Morse dressing, and the original complete
Eisenstein cusp equation.

- [x] Locate source derivatives and existing complete product calculus.
- [x] Prove exact height conjugation with the full retained derivative.
- [x] Specialize to the original complete Eisenstein source, without new source premises.
- [x] Identify the source content and descent requirements of the retained term.
- [x] Audit individual modules, axioms, umbrella wiring, and lint.

No numerical computation enters these proofs. Missing independent Xi occurrence
remains the RH-bearing obligation.

## Artifacts and validation

- `formal/GaloisForLFunctions/RHTower/SelbergScatteringHeightConjugation.lean`:
  6 public declarations; final individual module build passed.
- `formal/GaloisForLFunctions/RHTower/SelbergScatteringQuarterShiftSource.lean`:
  15 public declarations and two private source lemmas; final individual module
  build and complete dependency audit passed.
- Both modules are wired exactly once into `GaloisForLFunctions.RHTower`.
- All 21 public declarations are indexed. Forbidden-token and whitespace checks
  pass. `scripts/formal_tools.py lint` passes with existing file-size warnings.
- No numerical data enters a proof. The frontier map was not edited.

All 21 public exports pass `#print axioms` from a scratch file with exactly the
three standard axioms named above. Each final build used its named module only.
Read-only preflights identified 129 stale source dependencies; each was audited
and built separately before the new source module. Every build log records only
its requested compiled module. No full or umbrella build was run. All owned
compiler processes completed and their foreground handles were collected.

The narrow failed mechanism and its positive survivor are recorded in
[the literal height-multiplier card](../5-failed/sqb-literal-quarter-height-multiplier.md).
Independent full-Xi occurrence in the entire-transform operator domain remains open.
