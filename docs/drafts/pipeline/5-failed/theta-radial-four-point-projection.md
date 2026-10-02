# Pointwise radial four-point source producer

Status: exact paper falsification and positive survivor, both formalized in
`ThetaRadialSourceCurvature.lean`. Targeted build, final direct-file Lean
audit and all eight public axiom checks passed; umbrella wired.

## Failed statement

For all t,z>0, the proposed source inequality was

    k(t)k(t+z)k(z) < k(0)k(sqrt(t²+tz+z²))².

The actual sixth logarithmic center jet is positive. Consequently there
is δ>0 such that every 0<x<δ satisfies the strict reverse at t=z=x:

    k(0)k(sqrt(3)x)² < k(x)²k(2x).

This is an actual-source obstruction established through exact modular
center jets and derivative propagation, not an arbitrary-source model.
It also falsifies the proposed global positivity of
`T=x²p''-3xp'+3p`, with `p=-(log k)'`.

## Nontrivial positive survivor

T is strictly negative throughout a punctured right neighborhood of zero,
strictly positive eventually, and has a positive zero. The central sign
comes from the exact modular sixth numerator. The cofinal sign follows
from the corpus's actual logarithmic jet limits. This identifies a true
transition in the source's radial curvature, with no RH premise.

The complete paper proof is in
`3-formalized/theta/rn-radial-source-curvature-sign-change.md`; all statements
are formalized in the named leaf. The positive sign-change survivor passed
the same audit as the negative statement.

## Surviving hard problem

The pointwise failure does not decide the integrated normalized-kernel
comparison, actual projection compensation, or RH. RN-P-7j retains the
exact weighted integral for `L(z,z)-L(0,z)` and its relation to the actual
inverse-Gram coefficient. RN-P-7k instead controls the actual source residual
directly as the old nodes coalesce, without assuming either coefficient sign;
its main result is formalized and audited in
`3-formalized/theta/rn-confluent-center-source-residual.md`.
