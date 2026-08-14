# Divisible Formation-Potential Mechanics

- **ID:** ULF-DFPM-FIELD
- **Stage:** 1-in-progress
- **Type:** FIELD PROGRAMME / SELECTION MECHANISM
- **Status:** [MECHANISM, NOT OBJECT] [EXACT RH EQUIVALENCE PROVED] [SOURCE ROOT GENESIS OPEN]

## 1. Core reinterpretation

Positive formation work is only the real branch of a multiplicative source transfer.  After
analytic continuation, the correct obstruction is not a scalar and need not resemble curvature.
It is the integer divisor of that transfer.

The field grammar is:

\[
 \boxed{
 \text{source formation}
 \to\text{survival cocycle}
 \to\text{universal-wall renormalization}
 \to\text{meromorphic work form}
 \to\text{integer charge}
 \to\text{divisible lift}.}
 \tag{DFPM.1}
\]

The final implication is the selection law: arbitrarily deep compatible roots force every integer
charge to be divisible by unbounded integers, hence zero.

## 2. Laws

### Law I -- multiplicative survival

Every composable source formation has a survival transfer (A_f).  Composition must retain the
source action on parameters:

\[
 A_{gf}=A_g\,g_!A_f.
 \tag{DFPM.2}
\]

On an admitted positive ray, work is (W_f=-\log A_f\).

### Law II -- universal-wall subtraction

If source normalization forces a known zero or pole (u_f), remove it before interpreting the
remaining divisor:

\[
 R_f=A_f/u_f.
 \tag{DFPM.3}
\]

Without this subtraction, universal normalization is mistaken for constitutive charge.

### Law III -- work form and charge

The branch-free complex work form is

\[
 \omega_f=-d\log R_f=-\frac{dR_f}{R_f}.
 \tag{DFPM.4}
\]

Its residue around a local divisor component is an integer.  Gauge changes of logarithm do not
change (\omega_f) or its residues.

### Law IV -- positive gauge

On a positive real chamber, (R_f>0) chooses a real logarithm.  Positive formation work is the
real primitive of (DFPM.4), after universal-wall subtraction.  Positivity is therefore a gauge
choice on a charge-free chamber, not a proof that the global charge vanishes.

### Law V -- divisible lift

A depth-(n) formation lift is a meromorphic (G_n) with

\[
 G_n^n=R_f.
 \tag{DFPM.5}
\]

A coherent divisible lift supplies these for unbounded (n), compatibly under common divisors.
Compatibility is needed for a field theory; unbounded existence alone already annihilates the
divisor.

### Law VI -- integer-charge selection

If (DFPM.5) exists for unbounded (n), then

\[
 \operatorname{ord}_xR_f=n\operatorname{ord}_xG_n
\]

for every point (x).  The only integer divisible by unbounded positive integers is zero.  Thus
(R_f) is holomorphic and nowhere zero.

### Law VII -- open logarithmic history

When (R_f=e^{-\Phi_f}), exponentiated observation may close while the logarithmic potential
changes by (2\pi i\mathbb Z).  Recurrence belongs to the multiplicative observer; open history
belongs to the logarithmic lift.  Divisor charge is the obstruction to making this lift global.

### Law VIII -- functional-equation transport

Reflection transports divisor charges with multiplicity.  An information-neutral packet lift
cannot annihilate a charge; at most it identifies its reflected partner.  Selection needs charge
annihilation by source divisibility, not reflection alone.

### Law IX -- effective root descent

Roots on a ramified cover are not base roots.  If a local divisor has order (q), a depth-(n)
root lift has deck holonomy (e^{2\pi i q/n}).  It descends through common recovery exactly when
(n\mid q).  The selection law is therefore effective descent with trivial Kummer isotropy for
unbounded depths, not existence of an infinite root stack.

### Law X -- cofinal holonomy capacity

Effective descent can be replaced by a quantitative law on retained inertia.  For depth weights
(w_n\ge0), define

\[
 \mathcal A_w(q)=\sum_{n\ge2}w_n|1-e^{2\pi iq/n}|^2.
\]

Then nonzero integer charge has finite action exactly when (\sum_nw_n/n^2<\infty).  A
source-derived divergent capacity, minimally linear among polynomial weights, makes finite action
equivalent to zero charge.  This retains root-stack holonomy instead of demanding its pointwise
descent.

### Law XI -- regular-inertia amplification

The depth-(n) root inertia group has a canonical regular Hilbert module of dimension (n).
Nontrivial holonomy is fixed-point-free on its marked basis, so normalized Hilbert--Schmidt defect
is exactly (2), even though every scalar character approaches (1) as (n\to\infty).  The regular
module therefore generates the sharp capacity internally.  Across all depths, finite normalized
regular action is equivalent to zero integer charge.

## 3. Exact Euler-shell realization

For (m\ge12,r\ge2), Formation-Excess Mechanics produces the positive survival probability

\[
 A_{m,r}(\sigma)=\frac{S_m(r\sigma)}{S_{rm}(\sigma)},
 \qquad\sigma>1.
\]

Its complex continuation has the universal zero (s-1).  Define

\[
 R_{m,r}(s)=\frac{S_m(rs)}{(s-1)S_{rm}(s)}.
 \tag{DFPM.6}
\]

The Stage-2 theorem proves:

1. (R_{m,r}) extends meromorphically to (\Re s>1/2) and regularly across (s=1);
2. it has no zeros there;
3. its poles are exactly strict-right nontrivial zeta zeros, with equal multiplicities;
4. the residues of (-d\log R_{m,r}) count those zeros;
5. RH is equivalent to existence of a holomorphic formation potential
   (R_{m,r}=e^{-\Phi_{m,r}});
6. RH is equivalent to global meromorphic (n)-th-root lifts for any unbounded set of depths.

The companion ULF-DFPM-2 proves that the same divisor is reconstructed from all finite Kummer
holonomies and that linear depth capacity is the sharp global-action threshold selecting zero
charge.

ULF-DFPM-3 strengthens this: the canonical regular representation of depth-(n) inertia supplies
that linear capacity automatically, gives exact cycle/rank/spectrum shadows, and turns nonzero
charge into cofinal action of slope (2).

This is an exact selection mechanism.  It is not an RH proof because source genesis of the roots is
open.

## 4. Why this may be the sought higher theory

The same mechanism gives precise meanings to several corpus-wide slogans without identifying them:

| corpus phenomenon | formation-potential law |
|---|---|
| routes as local gauges | local logarithm/root choices |
| no-gos | nonzero divisor or failure of global root lift |
| positivity | real logarithm on admitted chamber |
| recurrence | closed exponential with open logarithmic history |
| hypertranscendental depth | no finite root/jet stage controls full global potential |
| functional equation | involutive transport of charge, not annihilation |
| properness | raw work diverges at universal wall before renormalization |
| selection | unbounded divisibility kills integer charge |

Only the first, third, fourth, sixth, seventh, and selection equivalence are currently exact in the
Euler-shell realization.  The hypertranscendence line remains a conjectural interaction law.

## 5. Source-genesis programme

The missing theorem is not “find a zero-free function.”  It is:

> construct, from pre-target source operations, a coherent rational-depth formation envelope whose
> image under the Euler-shell realization gives global roots of (R_{m,r}) on
> (\Re s>1/2).

Candidate mechanisms to attack:

1. rational Adams/plethystic completion of shell power operations;
2. a big-Witt or lambda-ring group-like lift of normalized survival;
3. a determinant-line root gerbe whose obstruction is the divisor charge;
4. a source-normal infinite-divisibility law on formation histories;
5. a compatible prime--infinity regulator trivializing root monodromy.

The first hostile attack already rules out the naive version of candidates 1--2.  A nontrivial
series in (1+t\mathbb Z[[t]]) cannot have integral (n)-th roots for unbounded (n), and Adams
operations are mode powers rather than roots of the full transfer.  Any surviving Witt/lambda
mechanism must therefore pass through a genuine rational or stacky enlargement and retain the
integrality obstruction as structured isotropy.

The second hostile attack rules out bare root-stack existence.  Root stacks manufacture roots after
ramified base change even for (R(z)=z).  Their useful datum is the retained inertia character.
Selection requires a source theorem making that character trivial under descent to the original
base.

Each candidate dies if roots are added only after seeing the zeta divisor, if the lift exists merely
on (\sigma>1), or if it factors through an information-neutral common recovery kernel.

## 6. Acceptance gates

- [x] source-generated positive survival transfer
- [x] universal-wall renormalization
- [x] exact divisor-charge computation
- [x] work-form contour conservation
- [x] holomorphic-potential RH equivalence
- [x] unbounded-divisibility RH selection theorem
- [ ] pre-target construction of one nontrivial global root
- [ ] coherent unbounded root tower
- [x] same-integral-doctrine root tower ruled out
- [x] root-stack existence without base descent ruled out
- [ ] effective trivial-inertia descent through common recovery
- [x] sharp pro-Kummer capacity/properness threshold
- [x] source-canonical linear capacity from regular inertia
- [ ] independent finite/sublinear regular-action admission theorem
- [ ] compatibility with functional-equation packet action
- [ ] independent realization in a second source family
- [ ] RH conclusion

## 7. Scope

Divisors, logarithmic derivatives, root gerbes, and infinite divisibility are established
mathematics.  Field claim concerns their constitutive coupling to source formation, GNS work,
functional-equation transport, and selection.  No novelty claim is needed for the programme to be
useful; the gate is whether source operations construct the roots.

Closest external collisions are Connes--Consani's Hardy/inner-function analysis of local-factor
ratios (arXiv:1910.14368) and infinite-root-stack descent, including
Binda--Lundemo--Merici--Park (arXiv:2408.15627).  They reinforce the typing of the gate but do not
supply the required Euler-shell root tower.
