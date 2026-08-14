# Route T: pole-regularized Ingham detector

## Status

- Pipeline stage: in progress
- Route: T, with permission to pivot
- Open core: quantitative coefficient-three Ingham zero-density estimate
- Formal target: an entire mollified detector whose zero divisor dominates the zeta zero divisor,
  followed by the Littlewood/Gabriel moment estimate for that detector

## Corpus audit

The new fixed-contour weighted Littlewood theorem gives an exact multiplicity-weighted first
horizontal moment for zeros of the entire zeta residue unit `G(s) = (s-1)ζ(s)`.  That closes the
contour representation defect, but it is not by itself Ingham's coefficient-three density proof.

The classical proof instead introduces a complex Möbius polynomial

`M_X(s) = Σ_{n≤X} μ(n)n^{-s}`

and the detector

`h_X(s) = 1 - (ζ(s)M_X(s)-1)^2`.

Direct use of `h_X` is invalid on a rectangle containing `s=1`: it has a double pole there.  The
current corpus only has the real-line Dirichlet-polynomial mollifier and therefore cannot yet state
the analytic detector or its divisor relation.

## Heavy conjecturing loop

### C1: the zeta-only Littlewood identity is the full Ingham bridge

Status: **FALSIFIED AS A COMPLETE BRIDGE**.

It is a correct exact zero-mass identity, but the coefficient three comes from interpolation of
moments of the mollified error, not from a direct boundary estimate for `log|G|`.  Treating it as
the full density proof would conceal the main analytic step.

Positive survivor: fixed-contour branch-free Littlewood extraction with analytic multiplicity,
already formalized in `WeightedLittlewoodRectangle.lean` and
`Sieve/ZetaResidueUnitWeightedLittlewood.lean`.

### C2: pole regularization exposes the correct entire detector

Claim:

`H_X(s) := G(s) M_X(s) (2(s-1) - G(s)M_X(s))`

is entire and, for `s ≠ 1`,

`H_X(s) = (s-1)^2 (1 - (ζ(s)M_X(s)-1)^2)`.

Status: **FORMALIZED** in `Sieve/InghamPoleRegularizedDetector.lean`.

This is an algebraic pole clearing, not an externally novel theorem.  Its corpus novelty is that it
connects the existing entire residue unit and exact weighted Littlewood machinery to the actual
Ingham detector without a meromorphic contour loophole.

### C3: zeta zero multiplicity is inherited by the regularized detector

Claim: at every point `ρ`,

`ord_ρ G ≤ ord_ρ H_X`.

In particular every zeta zero is a detector zero with at least its analytic multiplicity, regardless
of extra mollifier zeros.

Status: **FORMALIZED** in `Sieve/InghamPoleRegularizedDetector.lean`, including finite analytic
orders and multiplicity domination.

Proof plan: use the exact global factorization `H_X = G · [M_X(2(s-1)-GM_X)]`, analyticity of both
factors, additivity of `analyticOrderAt`, and finiteness of the factors' local orders.

### C4: selected detector contours dominate the zeta zero mass

Claim: finite zero avoidance selects a rectangle on which weighted Littlewood applied to `H_X`
counts detector zeros; C3 then bounds the zeta zero mass by that detector boundary functional.

Status: **FORMALIZED** in `EntireWeightedLittlewoodRectangle.lean` and
`Sieve/InghamDetectorWeightedLittlewood.lean`.  The exact detector boundary functional dominates
the multiplicity-weighted zeta zero mass.  Quantitative estimation of that boundary remains part of
C5, not a hidden contour premise.

### C5: Gabriel interpolation yields coefficient three

Claim: critical-line fourth moment of zeta plus second moment of `M_X`, interpolation to `3/4`, and
the right-line mollified error estimate imply

`N(σ,T) ≪ T^{3(1-σ)/(2-σ)} (log T)^A`.

Status: **OPEN HARD CORE**.

This is the first remaining step capable of producing the fixed `x^(7/10)` prime supply needed by
the formal Route T upper-phase handoff.

#### C5a: coefficient-three critical Hölder inequality

Status: **FORMALIZED** in `Sieve/InghamCriticalMoment.lean`.

For the actual zeta function and actual finite Möbius mollifier, Lean proves the finite-interval
equation-(41) inequality

`∫ |ζM_X-1|^(4/3) ≤ 2^(1/3)(∫|ζ|⁴)^(1/3)(∫|M_X|²)^(2/3)
                       + 2^(1/3)(V-U)`.

No moment bound is a premise: compact-interval integrability follows from analyticity.

#### C5b: quantitative mollifier second moment

Status: **FORMALIZED** in `Sieve/InghamMollifierSecondMoment.lean`.

Corpus audit exposed a stronger reusable input than expected: the existing general affine
mean-square theorem applies directly to the critical coefficients `μ(n)n⁻¹ᐟ²`.  Since their plain
mass is at most `1+log X` and their `n`-weighted mass is at most `X`, Lean now proves

`∫_{-T}^T |M_X(1/2+it)|² dt ≤ 5πe X + (5π/2)(1+log X)T`

and substitutes it into C5a.  Thus the mollifier moment is no longer an open premise; only the zeta
fourth moment remains on the critical edge.

#### C5c: remaining analytic bridge

Status: **OPEN HARD CORE**.

Remaining dependency-closed obstacles:

1. quantitative fourth moment for the actual zeta function on the critical line;
2. Gabriel strip interpolation on the required finite/truncated height geometry;
3. right-edge mollified-error and horizontal-boundary estimates;
4. conversion of the bounded detector boundary into the stated `N(σ,T)` density exponent.

Existing `FourthMoment.lean` and `FourthMomentDiagonal.lean` do not close item 1: their strongest
bound retains an explicit off-diagonal term.  Treating the filename or docstring as a fourth-moment
theorem would be research theatre.

## Novelty labels

- External theorem novelty: none claimed.
- Corpus representation novelty: pole-regularized divisor-exact formulation of Ingham's detector.
- Research significance: removes the pole at `1`, preserves multiplicities, and identifies the
  correct analytic object for the coefficient-three proof.

## Completion conditions

1. [x] Complex Möbius mollifier entire in `s`.
2. [x] `H_X` entire and exact pole-clearing identity proved.
3. [x] Pointwise zero inheritance and analytic-order domination proved.
4. [x] Detector weighted Littlewood count formalized on selected contours.
5. [ ] Quantitative moment/interpolation estimate closed with no conjectural premises.
6. Named Lean build, lint, and axiom audit pass.

### C5d: fixed-right-edge power saving, and correction of the uniform-bound conjecture

Status: **FORMALIZED** in `Sieve/InghamRightEdgeMeanSquare.lean` and
`Sieve/InghamRightEdgePowerSaving.lean`.

The first conjecture was that a cutoff-uniform `O(T)` right-edge second moment would close the
right input to Gabriel interpolation. This is **FALSIFIED AS SUFFICIENT**: coefficient three needs
the cutoff-tail saving created by `a_X(n)=0` for `n<=X`; discarding that support loses the density
exponent even though the resulting theorem is true.

Positive survivor: fix `beta=181/180`, use the unconditional divisor bound
`d(n)<=C n^(1/360)`, and retain exact support. Lean proves

```text
sum_n n |a_X(n)n^(-beta)|^2 <= C^2 X^(-1/180)/(1/180),
sum_n   |a_X(n)n^(-beta)|^2 <= C^2 X^(-181/180)/(181/180),
```

and therefore the literal power-saving endpoint theorem

```text
integral_[-X,X] |zeta(181/180+it) M_X(181/180+it)-1|^2 dt
  <= C_right X^(-1/180).
```

This fixed edge avoids the moving `1+delta/log X` geometry. Its weaker elementary divisor loss is
still compatible with Route T's `7/10` reserve once combined with the formal critical exponent
`251/250`. Thus the right endpoint is no longer the hard core. Remaining analytic obstruction is
the actual Gabriel integral interpolation theorem, followed by detector boundary/zero-counting
assembly.
