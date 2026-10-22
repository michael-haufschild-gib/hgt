# Shift-one Cassini resolvent source law

- **ID:** `shift-one-cassini-resolvent-source-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / right-to-left source weld
- **Scientific status:** `[PROVED HERE] [CORPUS-NOVEL INTERFACE] [NOT AN RH PROOF]`
- **Target:** `formal/GaloisForLFunctions/RHTower/XiSquaredSeamCassiniResolventSourceLaw.lean`

## Claim

Let `Psi = xiSquaredSeamCassiniSource` and let
`mu_q = xiSquaredSeamOneCoordinate q`.  For `z != 0`, `XiC z != 0`, and
`u = 1 + z^2`, prove

```text
-2 * logDeriv(Psi)(u) = sum_q mu_q / (1 - u*mu_q).       (1)
```

The sum runs over the multiplicity-exact Xi zero copies.  It is therefore twice the
one-sheet logarithmic derivative of the Cassini source, exactly accounting for functional-equation
pairing.

## Derivation

The entire square factor gives `Psi(1+z^2)=XiC(z)`.  Differentiating and dividing at a regular
point gives

```text
2*z*logDeriv(Psi)(1+z^2) = logDeriv(XiC)(z).              (2)
```

The proved paired relative-resolvent identity gives

```text
logDeriv(XiC)(z)
  = -z * sum_q lambda_q/(1-z^2*lambda_q),                (3)
```

where `lambda_q = xiZeroCopyReciprocalSquare q`.  Since

```text
mu_q = lambda_q/(1+lambda_q),
lambda_q/(1-z^2*lambda_q) = mu_q/(1-(1+z^2)*mu_q),       (4)
```

cancelling nonzero `z` proves `(1)`.

## Hostile tests

- The factor `2` is required: Xi zero copies contain both `zeta` and `-zeta`, while the square
  quotient has one zero.
- The sign is negative: `logDeriv XiC = -z * reciprocalSquareResolvent`.
- `z != 0` is needed for cancellation, though the identity may later extend analytically.
- `XiC z != 0` is needed because both logarithmic derivatives and resolvent denominators must be
  regular.
- This does not prove the reverse Cassini inequality.  It replaces its separate prime--Gamma
  moment by a local coefficient of the same entire function used in the Jensen integral.

## Right-to-left consequence

Differentiating `(1)` 63 times at `u=0` (the regular lift is `z=-I`) gives the exact coefficient
law

```text
primeArchShiftedReciprocalMoment 1 63
  = -2 / 63! * iteratedDeriv 63 (logDeriv Psi) 0.          (5)
```

Together with the Cassini--Jensen law, the open RH-bearing comparison becomes an intrinsic
one-function relation between the radial Jensen mass of `Psi` and its 63rd logarithmic-derivative
jet at the Euler-safe center.

More precisely, Lean proves

```text
C32 = 4096*J(Psi) + Re(iteratedDeriv 63 (logDeriv Psi) 0)/63!,

4096*J(Psi) + Re(iteratedDeriv 63 (logDeriv Psi) 0)/63! >= 0,

4096*J(Psi) + Re(iteratedDeriv 63 (logDeriv Psi) 0)/63! = 0
  <-> RH.
```

This removes the separate `primeArchShiftedReciprocalMoment 1 63` object from the rightmost open
comparison.  Both terms are now canonical functionals of the single unconditional entire source
`Psi`.

## Exact theta-boundary predecessor

The square lift of the Euler-safe center is `z=-I`, exactly the lower boundary of the proved
theta Fourier--Laplace strip.  For every `0<t<1`, Lean now proves the exact inward transport

```text
-2*logDeriv(Psi)(1-t^2)
  = (-I/t)*logDeriv(thetaCuspFourierLaplace)(-t*I).       (6)
```

No zero-free hypothesis remains: `XiC(-t*I) != 0` follows for every `t>0` because this centered
ray is the positive real axis of completed Xi.  The subunit part uses strict real-anchor
positivity; the rest uses the Euler half-plane.  Thus the local Cassini jet is the boundary germ
of the genuine theta-cusp source response, not merely a divisor-defined formal series.

Equation `(6)` also fixes the exact next target.  Generic positive/even/Schwartz source shape does
not orient the residual; that route is already retired in
`positive-even-schwartz-source-does-not-orient-fourier-current.md`.  A successful predecessor must
use theta-specific boundary structure to prove the reverse sign

```text
4096*J(Psi) + Re(iteratedDeriv 63 (logDeriv Psi) 0)/63! <= 0.
```

Together with the unconditional opposite inequality, this would force equality and RH.  Since the
residual is literally a sum of individual squares, conjugate cancellation and bounded estimates
cannot discharge it.

The one-sided trace has no analytic-continuation ambiguity.  Define an inward analytic extension
to be a germ `F` at `u=0` whose positive-real restriction equals the response in `(6)`.  Lean proves
that any two such germs agree near zero, by feeding the accumulating sequence `1/(n+1)` into the
analytic identity principle.  Consequently every extension has the all-degree jets in `(5)`.

This local uniqueness globalizes at source level.  If an entire function is normalized by

```text
F(0)=Psi(0)
```

and its logarithmic derivative has the inward response `(6)`, then Lean proves `F=Psi` on all of
`C`.  Thus both the local moment jet and the global Jensen divisor functional are fixed by the
same genuine theta-boundary datum; a different source continuation cannot change the residual.

The resulting pure boundary Prop is

```text
for every analytic inward extension F,
  8192*J(Psi) <= Re(F^(63)(0))/63!.
```

Lean proves this is exactly `XiSquaredSeamCassiniJensenDominated`, hence exactly RH.  It also proves
the reflection form

```text
sum_q |mu_q^32-conj(mu_q^32)|^2 = 4*C32
                                      = 4*intrinsic Cassini residual.
```

Therefore theta-boundary saturation is equivalent to vanishing of the degree-32 Cassini
anti-conjugation energy.  This connects the rightmost Cassini endpoint to the corpus reflection-
defect architecture without introducing a new conditional zero-side hypothesis.

## Reflection-faithful transfer to the reciprocal-square operator

The degree-32 power map is not reflection-faithful on arbitrary complex numbers: a nonreal number
can have real thirty-second power.  The actual shift-one Xi atoms have extra unconditional
structure.  For every zero copy `q`, put

```text
mu_q = xiSquaredSeamOneCoordinate(q),
lambda_q = xiZeroCopyReciprocalSquare(q).
```

The corpus proves

```text
Re(mu_q^(1))>0, Re(mu_q^2)>0, Re(mu_q^4)>0,
Re(mu_q^8)>0, Re(mu_q^16)>0.                             (7)
```

If `Im(mu_q^32)=0`, apply the open-right-half-plane square-root lemma first to `mu_q^16`,
then successively to `mu_q^8,mu_q^4,mu_q^2,mu_q`.  Equation `(7)` selects the real root at every
step and gives `Im(mu_q)=0`.  The converse is immediate.  The exact shift-one Mobius law and its
nonvanishing denominator give

```text
Im(mu_q)=0 <-> Im(lambda_q)=0.                            (8)
```

Consequently

```text
mu_q^32 = conj(mu_q^32) <-> lambda_q = conj(lambda_q)     (9)
```

for every multiplicity copy, and the two nonnegative global reflection energies have the same
zero fibre without routing through RH.  Combining `(9)` with the Cassini boundary identity gives

```text
ThetaCuspCassiniInwardBoundarySaturated
  <-> xiThermalSquareReflectionDefectEnergy = 0
  <-> ||K_square-K_square^*||_HS^2 = 0,                  (10)
```

where `K_square` is the existing reciprocal-square diagonal Hilbert--Schmidt kernel.  This is a
strict connector, not a renamed RH implication: its proof is pointwise dyadic descent plus exact
Mobius reality transport.  It shows that the high Cassini reflection defect neither loses nor
creates off-line support on the actual Xi divisor.

## Countable Cauchy zero-fibre connector

Let `A` be the existing reciprocal-square operator, let `K_square` be its Hilbert--Schmidt
kernel, and for every regular Gaussian-rational continued-Cauchy point `q` let

```text
d(q) = Im <A k_q,k_q>.
```

The corpus separately proves that vanishing of all `d(q)` forces RH, but that route obscures the
operator/source interface.  The zero fibres can instead be welded directly:

```text
||K_square-K_square^*||_HS^2 = 0
  <-> for every regular Gaussian-rational q, d(q)=0.       (11)
```

For the forward direction, Hilbert--Schmidt positive-definiteness turns the zero norm into
`K_square=K_square^*`.  The kernel-to-operator bridge and its adjoint intertwining then make `A`
self-adjoint, so every Cauchy quadratic value is real.

For the reverse direction, countable Gaussian-rational density first extends the scalar
quadratic identities to every continued-Cauchy vector.  The unconditional horizontal
Cauchy-pole exhaustion then gives

```text
conj(lambda_r)=lambda_r
```

on every exact Xi multiplicity fibre.  Hence the diagonal kernel defect vanishes pointwise, and
Hilbert--Schmidt positive-definiteness gives the left side of `(11)`.  Neither direction invokes
RH, an RH equivalence theorem, or a zero-location conclusion.

Combining `(10)` and `(11)` gives a direct right-to-left chain

```text
ThetaCuspCassiniInwardBoundarySaturated
  <-> ||K_square-K_square^*||_HS^2=0
  <-> forall q, d(q)=0.
```

This identifies the next live obligation as exact scalar source response, not another global
estimate.  It also exposes the structural obstruction: critical-line conjugation makes the Weil
source form Hermitian unconditionally, but this supplies only pseudo-self-adjointness of `A`;
ordinary Hilbert self-adjointness still requires the countable defects above to vanish.

## Fixed off-axis Cauchy-pole collapse

The countable family in `(11)` is not minimal.  Fix any regular continued-Cauchy pole
`z=u+iv` with `u*v != 0`, and write `a=x+iy` for a centered Xi spectral point.  Coordinatewise
expansion of the single quadratic orientation defect gives

```text
D(z) = Im <A k_z,k_z>
     = sum_a t_z(a),
t_z(a) = -Im(a^(-2)) / |a-z|^2.
```

The functional equation and Schwarz symmetry act on centered spectral points by
`a -> -a` and `a -> conj(a)`.  Exact common-denominator reduction on one four-element orbit gives

```text
t_z(a)+t_z(conj(a))+t_z(-a)+t_z(-conj(a))
  = 64*u*v * V_z(a),

V_z(a) = x^2*y^2*(|a|^2+|z|^2)
         / (|a|^4 |a-z|^2 |conj(a)-z|^2
                    |a+z|^2 |conj(a)+z|^2).              (12)
```

Every denominator in `(12)` is nonzero because `z` is regular for `XiC`; every factor of
`V_z(a)` is nonnegative.  Moreover `x != 0` for every Xi divisor point, so

```text
V_z(a)=0 <-> y=0.                                        (13)
```

Absolute summability of the Hilbert quadratic form permits reindexing by both divisor
equivalences.  Each original summand occurs four times, hence `(12)` sums to

```text
D(z) = 16*u*v * sum_a V_z(a).                            (14)
```

For `u*v != 0`, equations `(13)` and `(14)` show that `D(z)=0` iff every centered spectral point
is real, hence iff RH.  Thus one fixed regular off-axis Cauchy quadratic value replaces the whole
countable family:

```text
Im <A k_z,k_z> = 0 <-> RH.                               (15)
```

This is a strict predecessor theorem, not an RH-mediated repackaging of the countable criterion:
the forward proof is the explicit positive quartet decomposition `(12)`--`(14)`.  It exposes the
new rightmost obligation as one exact prime--Gamma/Cauchy source value at any regular off-axis
pole.

Equation `(14)` also fixes the defect sign unconditionally.  At the concrete regular pole
`z_0=1/4+i/4`,

```text
D(z_0) >= 0,
D(z_0) > 0 <-> not RH,
D(z_0) <= 0 <-> D(z_0)=0 <-> RH.                         (16)
```

Thus non-RH has one predetermined scalar failure witness; no existential pole, zero, or
Gaussian-rational index remains.  The backward source obligation can equivalently be stated as
one nonpositivity/passivity inequality at `z_0`.  Corpus audit shows why existing continued
prime--Gamma divided differences do not supply it automatically: those formulas realize Weil
polarization after critical-line reindexing, while `D(z_0)` measures ordinary Hilbert-adjoint
orientation.  Replacing the latter by the former would assume precisely the missing orientation.

## Adjoint-response source reconstruction

The orientation mismatch can nevertheless be encoded exactly inside the existing continued
prime--Gamma source core.  For a regular pole `z`, define the explicit adjoint-response test

```text
r_z(a) = conj(a)^(-2) * (conj(a)-z)^(-1),
f_z^+ = k_z + i*r_z,
f_z^- = k_z - i*r_z.                                    (17)
```

The reciprocal-square Hilbert--Schmidt bound proves `r_z`, `f_z^+`, and `f_z^-` are
square-summable.  Direct coordinate expansion then gives the cross-form identity

```text
P(k_z,r_z) = <A k_z,k_z>,
Re P(f_z^+,f_z^+) - Re P(f_z^-,f_z^-) = 4*D(z),          (18)
```

where `P` is the genuine Xi--Weil polarization.  Universal continued-source reconstruction now
produces separated finite packets `P_n^+`, `P_n^-` whose evaluations tend to the two tests and
whose exact finite source energies satisfy

```text
(sourceEnergy(P_n^+) - sourceEnergy(P_n^-))/4 -> D(z).   (19)
```

At `z_0=1/4+i/4`, uniqueness of limits and `(15)` prove the new exact interface

```text
exists P_n^+, P_n^- with the prescribed evaluation limits
  and normalized source-energy contrast -> 0
    <-> RH.                                               (20)
```

The anti-holomorphic response is not itself a continued-Cauchy atom, but its projection data have
a sharper source reduction.  Set

```text
g_z(a) = a^(-2)*(a-z)^(-1).
```

Critical-line reindexing gives `r_z=J g_z`; consequently every Cauchy dictionary moment is

```text
<r_z,k_w> = P(k_w,g_z).                                  (21)
```

The right side is a polarization of holomorphic source tests.  Cauchy density upgrades `(21)`
from a moment identity to uniqueness:

```text
v in closure(Cauchy source core)
and <v,k_w>=P(k_w,g_z) for every continued pole w
  -> v=r_z.                                               (22)
```

Thus the adjoint response is characterized without listing a single divisor value.  Moreover

```text
g_z(a) = z^(-2) k_z(a) - z^(-2) k_0(a) - z^(-1) a^(-2), (23)
```

so only a split double pole at zero remains beyond ordinary Cauchy divided differences.  Thus
target values are not needed for the response moments.  A source-only Gram projection still needs
the ordinary Hilbert Gram `<k_v,k_w>`, however; available prime--Gamma divided differences give the
twisted Weil Gram `<J k_w,k_v>`.  Identifying those Grams would impose the missing orientation.
The producer problem is therefore narrowed to a source construction with independently controlled
Hilbert metric, not response-value reconstruction.

There is no scalar shortcut obtained by replacing `r_z=Jg_z` with `g_z`.  At the matching pole,
commutativity of the two rational factors and Hermitian symmetry give

```text
Im P(k_z,g_z) = 0                                         (24)
```

unconditionally.  This formally kills the tempting one-variable holomorphic trace replacement.
The positive survivor is `(21)`: mixed moments `P(k_w,g_z)` remain source-computable for the
projection problem, but orientation detection must retain the two-point Hilbert metric.

This closes the value/interface gap between the fixed Hilbert-adjoint defect and finite
prime--Gamma source energies.  It does not manufacture the packets from divisor-free source data:
the universal reconstruction selects them through target-side Hilbert closure.  The next live
backward obligation is therefore a predetermined source producer for the two tests in `(17)` whose
contrast is zero (or nonpositive), not another estimate and not another RH-equivalent target
repackaging.

## Reciprocal-Krylov single-source collapse

The ordinary-Gram producer obstacle above can be bypassed existentially.  Fix any continued Cauchy
pole `z` and write `B` for the compact reciprocal Xi operator.  On divisor support set

```text
mu_rho = a_rho^(-1).
```

Inverse-square summability implies every outer shell `{rho : r <= |mu_rho|}` is finite.  For a
target `alpha=mu_rho`, complex Lagrange separation on that finite shell followed by the radial
factor `(X/alpha)^n` gives polynomials `p_n` with

```text
p_n(alpha)=c,
p_n(beta)=0                 for every other outer-shell beta,
p_n(beta)->0                for |beta|<|alpha|,            (25)
sup_{n,beta in spectrum}|p_n(beta)| < infinity.
```

Dominated convergence against the square-summable fixed Cauchy vector `k_z` therefore recovers
each complete multiplicity fiber.  Summing fibers proves the universal cyclicity law

```text
every multiplicity-safe square-summable evaluation belongs to
  closure span_C {B^n k_z : n>=0}.                         (26)
```

Conversely every `B^n k_z` is itself a square-summable holomorphic evaluation, so universal Cauchy
closure gives the exact subspace identity

```text
closure span_C {B^n k_z : n>=0}
  = continued-Cauchy Hilbert source core.                  (27)
```

Complex coefficients are essential here: real separator polynomials would force conjugate target
values, while the off-axis adjoint-response ratio has no such symmetry.  Applying `(26)` at the
fixed pole `z_0` gives complex polynomials with

```text
p_n(B) k_z0 -> r_z0.                                       (28)
```

Each approximant is evaluation of the holomorphic rational test

```text
h_n(a)=p_n(a^(-1))*(a-z_0)^(-1).
```

Continuity of the Hilbert realization of Weil polarization then yields an entirely holomorphic,
one-source contrast law

```text
(Re P(k_z0+i h_n,k_z0+i h_n)
 - Re P(k_z0-i h_n,k_z0-i h_n))/4 -> D(z_0).               (29)
```

Thus the constrained saturation interface

```text
exists p_n satisfying (28) and with the contrast in (29) -> 0
  <-> RH.                                                   (30)
```

This removes both arbitrary Cauchy-packet choice and independent ordinary Cauchy-Gram control from
the existential response-recovery problem.  Remaining rightmost frontier is narrower: separators
in `(25)` still select coefficients from actual divisor shells.  Need a divisor-free prime--Gamma
rule producing reciprocal-polynomial coefficients with the response limit `(28)`, together with a
source theorem forcing contrast in `(29)` nonpositive or zero.  No further response-value or
Hilbert-Gram reconstruction is needed.

## Real-form Krylov boundary

There is a sharper coefficient restriction.  For every real polynomial `p`, its holomorphic
reciprocal-Krylov test `h_p(a)=p(a^(-1))k_z(a)` satisfies

```text
P(k_z,h_p)=P(h_p,k_z).                                    (31)
```

This is pointwise commutativity of the real-polynomial factor with the two Cauchy denominators.
Hermitian symmetry then makes `(31)` real.  Hence every finite real-polynomial source contrast
vanishes exactly:

```text
(Re P(k_z+i h_p,k_z+i h_p)
 - Re P(k_z-i h_p,k_z-i h_p))/4 = 0.                      (32)
```

Combining `(32)` with continuity `(29)` proves a stricter endpoint:

```text
exists real polynomials p_n with p_n(B)k_z0 -> r_z0
  <-> RH.                                                   (33)
```

Reverse direction is concrete: under RH, all spectral coordinates are real, so constant sequence
`p_n=X^2` equals adjoint response exactly.  Forward direction uses no sign estimate: finite
contrasts are identically zero and their limit is `D(z_0)`, forcing `D(z_0)=0` and RH.

This makes coefficient frontier algebraically precise.  Unrestricted complex polynomial recovery
is unconditional; real polynomial recovery is exactly RH.  Any unconditional source mechanism
that keeps reciprocal-Krylov coefficients real while retaining response convergence would close
chain.  Conversely, under non-RH, unavoidable imaginary coefficient component is new obstruction
in every response-recovery sequence.

## Local real-Krylov seam

Real coefficient restriction has a two-point form requiring no source energy.  Write `Jq` for
critical-line reflection, so `a_(Jq)=conj(a_q)`.  Every finite real reciprocal-Krylov vector `v`
satisfies

```text
(conj(a)-z) v(Jq) - (conj(a)-conj(z)) conj(v(q)) = 0.       (34)
```

Coordinate evaluation is continuous on the Xi `ell^2` carrier, so `(34)` survives every
Hilbert-norm limit of real reciprocal-polynomial vectors.  Substitution of adjoint response gives
exact residual

```text
4 Im(a) Im(z) a^(-2) (a-z)^(-1) (a-conj(z))^(-1).          (35)
```

All reciprocal factors in `(35)` are nonzero at a regular pole.  Since fixed pole has
`Im(z_0)=1/4`, its seam vanishes at `q` exactly when `Im(a_q)=0`.  Consequently

```text
adjoint response satisfies (34) for every q
  <-> every centered Xi spectral point is real
  <-> RH.                                                   (36)
```

Thus global real-polynomial response recovery is equivalent to local seam saturation, and
recovery implies seam by continuity.  Smallest rightmost source task is now not a norm estimate:
derive `(34)` for fixed adjoint response from prime--Gamma/source identities.  Constructing a
source-selected real recovery remains one sufficient, strictly stronger route.

## Seam-fixed closure classification

The converse `seam -> real recovery` does not require RH.  For a complex polynomial `p`, let
`p#` conjugate every coefficient and let `Re_coeff(p)` take every coefficient's real part.  Then

```text
V_(Re_coeff(p)) = (V_p + V_(p#))/2.                        (37)
```

Coefficient conjugation obeys the reflected transport law

```text
V_(p#)(Jq) = R_z(q) conj(V_p(q)),
R_z(q) = (conj(a_q)-conj(z))/(conj(a_q)-z).                 (38)
```

Every seam-fixed vector `v` obeys the identical law.  Moreover

```text
R_z(q) = 1 + (z-conj(z))/(conj(a_q)-z),
sup_q |R_z(q)| <= 1 + |z-conj(z)| ||k_z||.                 (39)
```

Thus if `V_(p_n) -> v` complexly and `v` satisfies every seam equation, then
`V_(p_n#) -> v`; averaging with `(37)` gives real polynomials converging to `v`.  Therefore, inside
the unconditional complex reciprocal-Krylov closure,

```text
real reciprocal-Krylov closure = seam-fixed locus.         (40)
```

All multiplicity-safe evaluation vectors already belong to complex closure by fixed-pole
cyclicity.  In particular, adjoint-response seam saturation constructively yields real response
recovery.  The recovery/seam equivalence no longer detours through either RH equivalence.  This
eliminates real-coefficient sequence construction as an independent frontier: fixed
adjoint-response seam saturation itself is exact remaining right interface.

## First-prime source-seam weld

The fixed adjoint-response seam is now connected directly to an actual prime--Gamma source
coordinate.  For a raw Xi divisor point `rho` and its centered coordinate `a`,

```text
Im(a)=0
  <-> orbitwiseFirstPrimeSeamCharge(rho)=0
  <-> normalized translated von Mangoldt/Hurwitz prime-two seam -> 0.  (41)
```

Combining `(35)` with `(41)` pointwise and then restoring multiplicity copies gives, without an RH
intermediate,

```text
fixed adjoint-response seam saturation
  <-> all Xi-indexed first-prime source seams vanish
  <-> all normalized Hurwitz prime-two source seams vanish
  <-> xiHurwitzOrientationEnergy = 0.                           (42)
```

The existing unconditional source reconstructions now feed this right endpoint directly.  Either
of the following exact source signs suffices:

```text
Weil quadratic nonnegative on algebraic Cauchy source core;
eventual nonnegativity on one convergent continued source sequence;
cofinal nonnegative recurrence on one convergent sequence of separated finite prime--Gamma packets.
                                                                  (43)
```

Hence remaining producer is no longer a response/seam matching problem.  It is finite-source sign
in `(43)`, on an already constructed unconditional separated packet sequence.  Once supplied,
Lean chain is `(43) -> (42) -> seam-fixed closure -> real recovery -> RH`.

The reverse source construction is also direct.  Under seam saturation, `(42)` makes both
orientation energy and orientation vector exactly zero.  Constant zero Hilbert vectors and the
constant empty separated packet then witness both source-sequence conditions.  Consequently

```text
continued source-sequence nonnegativity
  <-> separated finite prime--Gamma cofinal nonnegative recurrence
  <-> fixed adjoint-response seam saturation.                    (44)
```

No RH equivalence is used in either direction of `(44)`.  This classifies reconstruction layer:
packet separation, convergence, and finite source representation introduce no remaining gap.
Only sign assertion on nontrivial unconditionally reconstructed packets carries RH strength.

## Gates

- [x] prior-corpus search: no Cassini/log-derivative or Cassini/resolvent theorem exists
- [x] paper derivation and sign/factor audit
- [x] formalize pointwise law `(1)`
- [x] extract local coefficient law `(5)` for every degree
- [x] rewrite the Cassini defect as the intrinsic Jensen/jet residual
- [x] weld the Cassini logarithmic response to the genuine inward theta-source boundary response
- [x] prove one-sided analytic-extension uniqueness and all-degree jet inheritance
- [x] prove global normalized entire-source reconstruction from the boundary response
- [x] isolate the extension-independent theta-boundary saturation Prop
- [x] identify the residual with one quarter of degree-32 reflection-defect energy
- [x] prove degree-32 Cassini reflection is pointwise faithful to reciprocal-square reflection
- [x] transfer theta-boundary saturation directly to the reciprocal-square anti-Hermitian energy
- [x] prove direct reciprocal-square kernel defect/countable Cauchy zero-fibre equivalence
- [x] collapse the countable source family to one regular off-axis Cauchy defect
- [x] prove fixed-pole quadrant sign and predetermined strict non-RH witness
- [x] reconstruct the fixed defect as a contrast of separated finite prime--Gamma source energies
- [x] prove fixed source-contrast saturation iff RH
- [x] reduce every adjoint-response/Cauchy moment to holomorphic source polarization
- [x] prove those source moments uniquely characterize the adjoint response in source closure
- [x] isolate the remaining producer datum as ordinary, not Weil-twisted, Cauchy Gram control
- [x] prove matching-pole holomorphic replacement cancels unconditionally
- [x] bypass ordinary-Gram projection using one fixed reciprocal-Krylov Cauchy orbit
- [x] prove universal reciprocal-Krylov cyclicity and exact equality with continued Cauchy closure
- [x] reconstruct the fixed adjoint response by holomorphic reciprocal-polynomial tests
- [x] prove fixed reciprocal-Krylov source-contrast saturation iff RH
- [x] prove every real reciprocal-polynomial source contrast vanishes exactly
- [x] prove real reciprocal-Krylov response recovery iff RH
- [x] extract local real-Krylov seam, prove exact adjoint-response residual, and localize RH
- [x] prove seam-fixed complex closure equals real reciprocal-Krylov closure constructively
- [x] weld fixed adjoint-response seam to first-prime/Hurwitz source seams and orientation energy
- [x] wire algebraic-core and one-sequence finite-source sign interfaces directly into seam
- [x] prove false RH universally traps every convergent separated packet reconstruction in a
  strict negative basin; weaken required producer from eventual sign to cofinal sign recurrence
- [x] prove exact global source-sign exclusion radius: every nonnegative separated packet has
  squared evaluation error at least half the orientation energy, with attained sharp constant
- [ ] prove cofinal nonnegative recurrence on one unconditional separated finite prime--Gamma
  sequence from source values
- [ ] prove the theta-specific boundary saturation/reverse sign
- [ ] RH

## Formalization log

- 2026-07-22 — Formalized the pointwise square-cover resolvent identity, ordinary shift-one moment
  germ, all-degree local jet law, and degree-63 intrinsic Cassini residual in
  `XiSquaredSeamCassiniResolventSourceLaw.lean`.  Imported by the `RHTower` umbrella.
- 2026-07-22 — Formalized negative-imaginary-ray nonvanishing and exact inward theta-boundary
  transport `(6)` in the same module.  Direct `lake env lean` check passed.
- 2026-07-22 — Formalized one-sided germ uniqueness, global normalized entire-source
  reconstruction, the pure theta-boundary saturation endpoint, and the exact degree-32
  reflection-defect identity.  Direct `lake env lean` check passed.
- 2026-07-22 — Formalized the direct kernel/countable-Cauchy zero-fibre weld and the resulting
  theta-boundary/countable-source equivalences, without using an RH equivalence in either
  direction.  Direct `lake env lean` check passed.
- 2026-07-22 — Proved on paper the fixed-pole quartet variance identity `(12)`--`(15)`: one
  regular off-axis Cauchy orientation defect detects every off-line Xi quartet.  Scratch Lean
  proof of exact algebra, summability, zero-fibre rigidity, and RH equivalence passed.
- 2026-07-22 — Formalized the generic quartet law and concrete pole in
  `XiReciprocalSquareFixedCauchySource.lean`, including unconditional sign law `(16)`.  Wired its
  zero fibre directly to reciprocal-square kernel energy and theta-boundary saturation without an
  RH detour.  Direct checks of the new module and Cassini connector module passed.
- 2026-07-22 — Formalized the explicit adjoint-response polarization `(17)`--`(18)`, packet
  reconstruction `(19)`, and source-contrast saturation criterion `(20)` in
  `XiReciprocalSquareFixedCauchySourceReconstruction.lean`.  Imported by the `RHTower` umbrella.
  Direct `lake env lean` check passed.
- 2026-07-22 — Added the holomorphic response moment reduction `(21)`, source-moment uniqueness
  `(22)`, and exact partial-fraction law `(23)`.  This removes target values from all Cauchy
  response moments and isolates ordinary Cauchy Gram control as the remaining source-producer
  datum.  Direct Lean check passed.
- 2026-07-22 — Formalized the matching-pole cancellation `(24)`.  It rules out replacing the
  adjoint response by a one-variable holomorphic trace while retaining mixed source moments as the
  positive survivor.
- 2026-07-22 — Formalized complex finite-shell separation, universal one-vector reciprocal-Krylov
  cyclicity `(25)`--`(27)`, fixed adjoint-response recovery `(28)`, holomorphic source contrast
  convergence `(29)`, and exact saturation criterion `(30)` in
  `XiReciprocalFixedCauchyKrylovCyclicity.lean`.  Imported by the `RHTower` umbrella.  Direct
  `lake env lean` check passed.
- 2026-07-22 — Formalized real-polynomial mixed-polarization symmetry `(31)`, exact finite contrast
  cancellation `(32)`, and real reciprocal-Krylov recovery equivalence `(33)` in
  `XiReciprocalFixedCauchyRealKrylovRecovery.lean`.  This identifies imaginary coefficient escape,
  rather than response existence or an analytic estimate, as the rightmost obstruction.  Imported
  by `RHTower`; direct `lake env lean` check passed.
- 2026-07-22 — Formalized finite and closed-limit real-Krylov seam law `(34)`, exact adjoint-response
  residual `(35)`, and local seam saturation equivalence `(36)` in
  `XiReciprocalFixedCauchyRealKrylovSeam.lean`.  This replaces global response convergence as the
  smallest rightmost target by a two-coordinate source identity.  Imported by `RHTower`; direct
  `lake env lean` check passed.
- 2026-07-22 — Formalized coefficient conjugation transport `(37)`--`(39)` and constructive
  seam-fixed closure classification `(40)` in the same module.  Complex cyclic approximants of
  any seam-fixed vector symmetrize coefficientwise to real approximants.  Rewired fixed real
  recovery from seam saturation directly, without using RH in either direction.  Direct
  `lake env lean` check passed.
- 2026-07-22 — Formalized direct prime-source weld `(41)`--`(43)` in
  `XiReciprocalFixedCauchyRealKrylovPrimeSeamWeld.lean`.  Pointwise and global zero-fibre proofs do
  not use RH equivalences.  Added direct discharge theorems from Cauchy-core positivity, one
  continued-source sequence, and one separated finite prime--Gamma packet sequence.  Imported by
  `RHTower`; final module build passed (9123 jobs).
- 2026-07-22 — Added empty separated packet and constructive reverse implications `(44)` in the
  same weld module.  This proves source-sequence sign interfaces and local seam saturation are
  identical without RH detours.  Direct Lean check and final module build passed.
- 2026-08-16 — Formalized the cofinal separated-source sign gate and exact nonnegative-cone
  distance law in `XiHurwitzOrientationCofinalSourceSignGate.lean` and
  `XiHurwitzOrientationSharpNonnegativeConeDistance.lean`.  False RH forces every convergent
  section into a strict negative tail, while every individual source-nonnegative packet remains at
  squared target distance at least half the orientation energy.  Source-defined recurrence remains
  open.
