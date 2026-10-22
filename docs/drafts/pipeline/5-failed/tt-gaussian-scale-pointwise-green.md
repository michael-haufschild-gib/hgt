# TT: unweighted scale positivity does not survive the physical center weight

- **ID:** tt-gaussian-scale-pointwise-green
- **Stage:** 5-failed (specific pointwise construction only)
- **Route:** TT, complete signed theta current
- **Status:** paper proof and twelve public Lean theorems audited

## Construction tested

Use the positive Gaussian scale operator to replace the signed native matrix
by a pointwise nonnegative Green energy after inserting the actual physical
weight W_a(r)=r*sinh(a*r). This would require retaining its complete weight
derivatives and center flux. The test uses the literal complete source
U(r)=Phi(r/2), not a freely chosen countermodel.

The first-pair potential is V(r)=16*pi^2*exp(2*r), and A U=-4*U''+V*U.
The source is not assumed to satisfy the first-pair differential equation:
its native reflection jets have contributions from all ordered atom pairs.
Thus failure of this candidate Green form is not failure of the TT current.

## Exact obstruction and positive survivor

The unweighted identity is strictly positive on its right side:

    U*A U+(4*U*U')' = 4*(U')^2+V*U^2 > 0.

Inserting the physical weight gives the exact replacement identity

    W_a*U*A U+(4*W_a*U*U'-2*W_a'*U^2)'
      = 4*W_a*(U')^2+(V*W_a-2*W_a'')*U^2.

At r=0, W_a=W_a'=0 and W_a''=2*a. The flux vanishes, but the
right-hand side equals -4*a*Phi(0)^2<0 for every a>0. Smoothness makes
it strictly negative on an entire positive-radius interval. The flux's
value at the center cannot justify discarding its derivative there.

Second pass: completing a weighted square does not remove the missing
weight-derivative potential. The unweighted positive form and exact
weighted decomposition are the positive salvage, both formalized. No
claim is made about the sign of their full integral or an endpoint at
infinity not proved in this leaf.

## Source-faithful scale equation retained

For every ordered pair define

    K_(p,s)(r,t)=exp[-exp(r)*(p*exp(2*t)+s*exp(-2*t))].

The exact equation is

    -partial_t^2 K = -4*partial_r^2 K+16*p*s*exp(2*r)*K.

Proof: write Z=exp(r)*(p*exp(2*t)+s*exp(-2*t)) and its signed
difference D. Then Z_r=Z, Z_t=2*D, D_t=2*Z, and
D^2=Z^2-4*p*s*exp(2*r). Differentiating exp(-Z) gives the equation.

With p=thetaCuspSingleAtomReflectionScale(n,x) and the analogous s for m,
the actual ordered theta pair is exactly

    4*p*s*exp(x)*[(4*p*s+9)*K_(p,s)(0,t)
                  +6*partial_r K_(p,s)(0,t)].

Both indices and their scale product remain. This is not a universal
single-atom potential for the completed source, a diagonal truncation,
or an assertion that a positive operator produces a positive cross pairing.

## Corpus basis and audit

Sources: `ThetaCuspOddFourGaussianFlow`, `ThetaCuspPairRadialRecurrence`,
`ThetaCuspFirstAtomAllOrderApproximation`, and the literal-source positivity
in `HedenmalmThetaSourceUnconditional`. Fresh corpus searches supplied these
sources; partial searches and background-refresh limits are recorded in
the working log. No external-literature frontier was substituted.

Leaf: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspGaussianScaleOperator.lean`.
Twelve public theorems audited:

- `lake build --old +GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspGaussianScaleOperator`
  passed (leaf 58 seconds; unchanged dependencies replayed).
- Final `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspGaussianScaleOperator.lean`
  passed without warnings.
- A separate `/tmp` audit printed exactly `[propext, Classical.choice,
  Quot.sound]` for every public theorem. No added axioms or proof holes.
- Leaf wired into `RHTower.lean`; no umbrella build, numerical experiments,
  heartbeat increases, subagents, commits or pushes.

Index refresh passed. Global lint failed on ten unrelated unreachable
modules (listed in the working log), with no error for this leaf and no
stale-index report. Scoped whitespace checks passed; owned scratch files
and processes were cleaned up.

## Surviving hard problem

Construct a positive complete-source matrix pairing that retains the
pair-dependent potentials, physical weight derivatives and boundary flux.
The exact identities above constrain that construction but do not establish
the all-rank signed cone, a uniform TT current bound, RH, or its negation.
