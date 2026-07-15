# Every eigen-plurivolume defines a canonical log-crepant orbifold boundary

- **ID:** eigenplurivolume-log-crepant-orbifold
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) + Lean-formalized local core
- **Source:** finite-holonomy refinement of the eigenvolume horizon law
- **Statement:** A rational eigen-`k`-canonical density under a finite endomorphism canonically
  defines a rational boundary `Delta` for which `K_X+Delta` is torsion and exactly pullback
  invariant.  At every periodic ramified divisor, expansion forces the normalized boundary
  coefficient to be one, independently of `k`.

## Goal

Unify the reduced logarithmic horizon of a stable coframe with the rational orbifold boundaries
created by finite holonomy, without falsely assuming that every eigen-density has an effective or
log-canonical divisor.

## Gates

- [x] 0 -> 1 in-progress: weighted ramification law and finite-holonomy boundary isolated
- [x] 1 -> 2 fully-proven: global log-crepant identity and local fixed point proved
- [ ] 2 -> 3 formalized: full divisor and pluricanonical geometry encoded in Lean
- [ ] 3 -> 4 publication-ready: expert novelty audit and applications beyond known orbifolds

## Setup

Let `X/C` be a smooth projective variety, let `f:X->X` be finite and surjective, and let `Theta`
be a nonzero rational section of `K_X^(tensor k)` for an integer `k>=1`.  Assume

`f*Theta=lambda Theta`                                            (1)

for some nonzero constant `lambda`.

Define the rational divisor

`Delta_Theta=-(1/k)div(Theta)`.                                   (2)

No effectivity, coefficient bound, or singularity hypothesis is imposed on `Delta_Theta`.

## Theorem A: canonical log-crepant boundary

**[PROVED HERE]**

The pair determined by (2) satisfies

`K_X+Delta_Theta~_Q 0`                                           (3)

and the exact divisor identity

`f*(K_X+Delta_Theta)=K_X+Delta_Theta`.                            (4)

Thus every rational eigen-plurivolume determines a source-pure log-crepant constraint, whether or
not that constraint is an effective log pair.

### Proof

The divisor of a rational `k`-canonical section represents `kK_X`, so (2) immediately gives
(3).  Pullback of a top differential contributes the ramification divisor `R_f`; hence

`div(f*Theta)=f*div(Theta)+kR_f`.

By (1), the left side is `div(Theta)`.  Therefore

`f*Delta_Theta=Delta_Theta+R_f`.                                  (5)

Combining (5) with Riemann--Hurwitz `K_X=f*K_X+R_f` proves (4).

## Theorem B: universal weighted horizon law

Let `E` be a prime divisor, put `F=f(E)`, let `e_E` be the ramification index at `E`, and write

`c_E=ord_E(Theta)`, `d_E=coeff_E(Delta_Theta)=-c_E/k`.

Then

`c_E+k=e_E(c_F+k)`,                                               (6)

or equivalently

`1-d_E=e_E(1-d_F)`.                                               (7)

If `E` is periodic and the ramification index of the corresponding iterate is greater than one,
then

`c_E=-k`,                                                         (8)

`d_E=1`.                                                          (9)

### Proof

Taking the coefficient of (5), or directly of the pluricanonical pullback formula, gives

`c_E=e_E c_F+k(e_E-1)`,

which is (6); equation (7) is the same identity divided by `-k`.  Pass to an iterate fixing `E`.
Then (6) becomes

`c_E+k=e_E(c_E+k)`.

Expansion `e_E>1` forces `c_E+k=0`, proving (8)--(9).  The exact integral fixed point is
Lean-formalized as `ramificationPluriPoleOrder_fixed_eq_neg_weight` in
`formal/GaloisForLFunctions/HTGeometry/RamificationPoleFixedPoint.lean`.

## What this theorem does and does not classify

For an ordinary eigenvolume (`k=1`) whose divisor support is forced to be totally invariant, the
boundary is reduced and the theorem specializes to the log-Calabi--Yau horizon of a full stable
coframe.

For finite-holonomy quotients, an invariant density may exist only after taking a tensor power.
Then `Delta_Theta` naturally records rational orbifold coefficients.  Equations (6)--(7) are the
higher-dimensional version of the ramification bookkeeping behind parabolic orbifolds.  Every
recurrent ramified component saturates at coefficient one, but preperiodic components can have
other rational coefficients.

The theorem does **not** prove that `Delta_Theta` is effective, that its coefficients are at most
one, or that `(X,Delta_Theta)` is log canonical.  Those are independent gates.  Only after they
are established may one invoke classification theorems for polarized log-Calabi--Yau pairs.

## Physical/topological reading

This paragraph is interpretation, not an additional theorem.

The canonical weight `k` changes the unnormalized pole order but not the normalized horizon
charge.  Ramification rescales `c+k`; recurrence under genuine expansion kills that shifted
quantity and fixes `c/k=-1`.  The resulting rational boundary is a static orbifold constraint.
Finite holonomy changes local fractions away from recurrence but cannot change the saturated
horizon coefficient.

## Novelty and significance gate

Canonical-divisor pullback, Riemann--Hurwitz, and orbifold ramification coefficients are
classical.  The searched literature contains the one-dimensional parabolic-orbifold
classification and modern higher-dimensional log-Calabi--Yau structure theorems, but did not
state the tail-motivated eigen-plurivolume construction (2)--(9) as a common horizon law.

The result is a concise unification and a useful exact bridge, with novelty provisional pending
expert review.  It does **not** clear the Fields-Medal gate: the hard step remains producing an
effective log-canonical eigen-plurivolume or lower-rank analogue from an arbitrary stable
differential-tail observable.

## Lean status

The weighted local fixed point is formalized as
`ramificationPluriPoleOrder_fixed_eq_neg_weight`.  Its targeted build and axiom audit pass.  The
global pluricanonical divisor pullback is paper-level because the project lacks the required
algebraic-geometric divisor infrastructure; it is not introduced as an axiom.

## RH impact audit

No direct RH consequence follows.  If an algebraic completed-zeta model produced a rational
eigen-plurivolume from its tail, (2) would canonically expose the only possible log-crepant
orbifold boundary and (7) would constrain every ramification coefficient.  No such
eigen-plurivolume, effective boundary, or algebraic self-map is currently proved for the zeta
source, so the theorem supplies a diagnostic rather than a critical-line argument.

## Log

- 2026-07-15 -- [PROVED HERE] canonical rational boundary, exact log-crepant pullback, weighted
  ramification law, and periodic coefficient-one fixed point proved.
