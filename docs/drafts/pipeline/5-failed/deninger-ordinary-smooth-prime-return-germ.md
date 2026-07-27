# Ordinary smooth prime return germ

- **ID:** `deninger-ordinary-smooth-prime-return-germ`
- **Stage:** 5-failed
- **Type:** FALSIFIED LOCAL-GEOMETRY ROUTE
- **Label:** `DAC_ORDINARY_SMOOTH_PRIME_RETURN_GERM_NO_GO`
- **Parent:** `deninger-prime-holonomy-groupoid`
- **Claim tested:** compactify a finite Kummer normal disk by its
  origin and use \(z\mapsto z^p\) itself as a nondegenerate smooth
  Poincare return germ at the prime orbit.

## No-go theorem

`[PROVED HERE] [DAC_ORDINARY_SMOOTH_PRIME_RETURN_GERM_NO_GO]`

Let \(p>1\).  There is no oriented \(C^1\) surface germ at a point
\(o\) whose punctured neighborhood is identified with a punctured
disk in such a way that the Kummer power map
\[
 F_p(z)=z^p                                                     \tag{1}
\]
extends to a local \(C^1\) diffeomorphism fixing \(o\).

### Proof

On every sufficiently small positively oriented circle around the
origin, `(1)` has winding degree \(p\).  Local topological degree is
unchanged by conjugating with an oriented punctured-neighborhood
identification and by shrinking the neighborhood.  A local
diffeomorphism at an isolated fixed point has local degree \(+1\) or
\(-1\), according to orientation.  Since \(p>1\), the two degrees
cannot agree.

In the ordinary complex-disk smooth structure the same obstruction is
visible infinitesimally:
\[
 dF_p|_0=0.
\]
Thus the fixed point is degenerate and cannot supply the
nondegenerate leafwise return derivative required by the simple
Lefschetz formula.

## Strongest positive survivor

The power correspondence is nevertheless exactly compatible with
the logarithmic source complex:
\[
 F_p^*(d\log z)=p\,d\log z,\qquad
 \operatorname{Res}(F_p^*d\log z)
 =
 p\,\operatorname{Res}(d\log z).                               \tag{2}
\]
On the punctured collar, the source metric
\[
 g_{p,u}
 =
 \frac{u}{-\log|z|}
 \left(d\log|z|^2+d\arg(z)^2\right)                             \tag{3}
\]
is complete at \(z=0\), descends through suspension deck maps, and
has a degree-one Hodge star compatible with `(2)`.  This is proved in
`DAC_PRO_LOG_KUMMER_CUSP_HODGE_EXTENSION`.

Therefore the correct prime object is:

1. a complete logarithmic cusp end on the generic leaf;
2. a separate transverse residue/prime packet;
3. a finite power correspondence between them;
4. a Tate-normalized residue trace.

It is not a smooth point obtained by adjoining \(z=0\) to the same
leaf and calling \(z^p\) a return diffeomorphism.

## Exact new insight

Prime Lefschetz data in Deninger's rational-Witt source must be
correspondence-theoretic or groupoid-theoretic.  Ordinary fixed-point
differential language loses the local degree \(p\): it either produces
the zero derivative in coordinate \(z\), or a branched degree-\(p\)
map that is not a local diffeomorphism.  Logarithmic residue retains
the correct factor \(p\) without this false smoothness claim.

## Lean status

No new Lean theorem is needed before the analytic source comparison.
The topological-degree statement is independent of the algebraic
arithmetic-cohomology kernel already formalized.  If later used in a
formal no-go audit, encode only the elementary derivative-zero
specialization of \(z\mapsto z^p\); do not expand the final RH module
for it.

## Hostile audit

- The theorem excludes only an ordinary smooth local-diffeomorphism
  realization of the finite Kummer power map.
- It does not exclude a pro-Kummer solenoid, branched groupoid,
  finite correspondence, or logarithmic residue model.
- Positive survivor has a dependency-closed paper proof and explicit
  source role.
- No zeta zero, RH premise, CCM object, or numerical computation is
  used.

## Log

- 2026-07-27 — Retired the ordinary smooth return-germ
  interpretation by local-degree obstruction and retained the
  logarithmic cusp/residue correspondence as positive survivor.
