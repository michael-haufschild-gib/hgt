# DR: arithmetic Frobenius on the actual marked Kummer tower

Status: in progress. No additional root level or zero-free half-strip proved.

The previous finite Euler counterterm cycle did not preserve sheet return
through continuation. This cycle tests an action on the actual root cover,
rather than another scalar regularization or contour convergence criterion.
External searches and numerical computations are excluded by user direction.

## Exact candidate

Let E be the pole-filled function (s-1)zeta(s), and let D={Re(s)>1/2}.
On the Euler region Re(s)>1 choose its positive-at-2 logarithm L and roots
r_d=exp(L/d), where d=2^k. On the actual cover w^d=E(s), define

    F_(3,d)(s,w) = (s, r_d(s)^(-2) * w^3).

This is a holomorphic automorphism over the identity on the Euler region:
writing w=r_d(s)*zeta with zeta^d=1 makes it zeta |-> zeta^3.
It is compatible with the tower transition w |-> w^2 and obeys

    F_(3,d) T_zeta = T_(zeta^3) F_(3,d).

Candidate: this *marked* Euler automorphism extends over the actual
punctured Kummer cover above D minus the zero divisor of E, at every depth,
by an arithmetic Frobenius construction. The extension must agree with
the displayed map, not merely be an unrelated automorphism of each fiber.
Continuing it over the normalized branched cover can then be considered.

An extension at all depths would kill all nonzero local integer charges:
continuation around a zero of order m translates the fiber label by m in
Z/d; a map over the identity must commute with this translation, whereas
its cyclotomic action is multiplication by 3. Consequently d divides 2m
at every dyadic depth, forcing m=0.

This implication is not the desired construction. The first unproved step
is [OPEN CORE]: build the actual global, marked, deck-covariant action from
arithmetic source data without assuming the root whose existence it tests.

## Attack: the precise normalization cost

Locally write E(t)=t^m*u(t), with u a holomorphic unit on a disk about zero.
On a branch of E^(1/d), continuation around the puncture multiplies r_d
by exp(2*pi*i*m/d). Thus r_d^(-2), and hence the proposed map, is
single-valued precisely when d divides 2m. This calculation is independent
of the unit u. The apparent arithmetic action has retained the same local
divisor obstruction, shifted by one dyadic level.

More generally, for an integer q coprime to d,

    F_(q,d)(s,w) = (s, r_d(s)^(1-q) * w^q)

descends locally precisely when d divides (q-1)m. The sufficiency is
explicit: when that divisibility holds, r_d^(1-q) is a meromorphic
single-valued coefficient. On each normalization component of the cover,
the resulting map sends the local parameter to a root of unity times that
parameter, so it extends through the point over E=0. Necessity follows
either from continuation of the coefficient or from commuting with the
fiber's monodromy translation.

For q=3 and k>=1, an existing level-(k-1) root h with h^(2^(k-1))=E already gives
F_(3,2^k)(s,w)=(s,w^3/h(s)) off the divisor. Conversely such a marked map
recovers h as w^3 divided by its output coordinate; deck covariance makes
this ratio independent of w and holomorphic off the divisor. The marked
Euler agreement and analytic continuation give h^(2^(k-1))=E. This
identity also bounds h near any omitted zero, so h extends holomorphically
there by removability. The criterion therefore supplies no induction from an
already known root level to a new one.

At k=1 the map is simply w^3/E=w, so it always exists. At k=2 its
normalizing coefficient already requires the first missing square root.
Do not infer a nontrivial rung from the automatic first-level action.

Verdict on obtaining a new rung from this normalization alone: CIRCULAR.
The arithmetic extension candidate itself remains BRIDGE until its source
construction is proved. This does not retire DR or rule out an arithmetic
construction using additional structure.

## Second attack: arithmetic versus analytic coefficient action

The finite cyclotomic action zeta |-> zeta^3 does exist arithmetically.
It does not directly act on a complex analytic function by continuous
field automorphisms. A continuous field automorphism of C fixes Q, then R
by density, and sends i to i or -i. It is therefore identity or conjugation.
On eighth roots neither has exponent 3 modulo 8. Thus this arithmetic
Frobenius cannot be promoted by a continuous action on all coefficients.

This does not prohibit a holomorphic permutation of finite cover fibers.
It shows why that permutation must be constructed on the actual cover;
the cyclotomic theorem alone does not provide analytic source attachment.

Schwarz reflection is not the missing map over the identity. It sends the
base s to conjugate(s), reverses the orientation of a local loop, and acts
on roots of unity by inversion. Thus both its deck exponent and its loop
translation change sign; it is compatible with every local multiplicity.
It yields no divisibility. At degree 4 its exponent -1 agrees with 3,
but the different base action prevents applying the argument above. At
degree 8 even the two exponents differ.

## Current source evidence

- `RHTower/Deninger/DeningerPrimePacketCyclotomicTowerAction.lean`, theorem
  `deningerPrimePacketCyclotomicStageAction_frobenius`, supplies the genuine
  arithmetic p-power action on the named cyclotomic stage. It contains no
  identification with a global analytic Kummer cover of E.
- `RHTower/PairedEtaKummerCoverTransport.lean` defines the actual branched
  analytic cover and supplies source transport with the base, deck maps,
  and root transitions explicit. This is transport, not a Frobenius lift.
- `RHTower/XiKummerDeckActions.lean` keeps the global marked and analytic
  strip base fields separate. Its involutions cannot be interchanged.
- `RHTower/XiGlobalKummerMarkedTower.lean` retains the global Xi square class
  on a specified marked algebraic extension. Its global base includes
  critical zeros; it does not prove a right-half-plane obstruction to RH.
- `RHTower/FrankensteinXiIntegralCartierMonodromyBridge.lean` explicitly
  retains an RH-strength reporter-existence premise. Its equivalences do
  not construct the candidate analytic map.
- `RHTower/Deninger/DeningerSpecZFrobeniusDivisorPullback.lean` concerns the actual
  arithmetic integer divisor over Spec Z. It does not identify this with
  the analytic zero divisor of zeta.
- Mathlib `Analysis/Complex/Basic.lean` proves that a continuous complex
  ring endomorphism is identity or conjugation. This is an existing parent
  theorem for the coefficient-action obstruction, not a novel result.

## Work plan and audit

1. Check actual corpus declarations for the cyclotomic Frobenius action,
   actual Xi root cover, and any existing comparison of these actions.
2. Verify the proposed formula and its normalization cost against those
   sources. Do not introduce a structure that assumes global extension.
3. Test whether the prime-source action supplies the missing normalization
   independently of the lower root. A complete proof is required before
   any new Lean theorem claiming root production.

The local calculation above is standard cyclic-cover theory, not new
scientific knowledge. No repository Lean implementation is justified by
that calculation alone. Source-specific extension is still the hard target.

## Verification and outcome

Scratch command `lake --old env lean /tmp/hgt_dr_frobenius_lift_audit.lean`
exited 0 without warnings after correcting the initial scratch errors.
It verified:

- if h^2=E and w^4=E with h nonzero, w |-> w^3/h preserves the quartic
  fiber, is involutive, and recovers h as w times its image;
- its cubic deck covariance and the exact finite-label condition
  3(j+m)=3j+m for all j iff 2m=0 in Z/d;
- no continuous ring endomorphism of C sends a primitive eighth root to
  its cube;
- the orientation-reversing translation identity used by Schwarz reflection.

The printed axiom lists contain only propext, Classical.choice, and
Quot.sound (the finite-label statement does not need Classical.choice).
This is a scratch audit of the stated algebraic and coefficient claims;
it is not a formal construction of a global Frobenius lift, a proof of the
general cover classification, or a zero-free certificate. No repository
Lean file changed, so no umbrella/lint/index run was warranted.

Four research searches completed with partial=false and no reported
errors. The index reported stale coverage snapshots, unavailable semantic
coverage, and many pending/stale compiler entries. Relevant actual Lean
sources were read before relying on the distinction between arithmetic and
analytic actions.

Anti-theatre / anti-laziness: no new scientific theorem beyond the parent
theories and no movement of the RH frontier. The test exposed the exact
root hidden in the proposed action, rather than assuming an arithmetic
Frobenius acts analytically over the fixed complex base. No known proof
step was declined for effort. Do not spend the next cycle expanding this
standard classification; construct an additional source-specific operation
whose sheet-return effect is proved independently of that missing root.
