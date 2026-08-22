# Verified-height amplification for a first off-line zeta zero

- **ID:** verified-height-amplification
- **Stage:** 5-failed
- **Type:** `[RETIRED: REDUCES TO THE TARGET OR TO ENUMERATION]`
- **Source:** user research prompt; Platt--Trudgian verified-height theorem
- **Statement:** `[CONJECTURE]` There is an explicit `T_1 > T_0`, with
  `T_0 = 3,000,175,332,800`, for which the published verification below
  `T_0` plus a new non-computational analytic theorem imply that every
  nontrivial zero `rho = beta + i gamma` with `0 < gamma <= T_1` has
  `beta = 1/2`.

## Goal

Produce an actual strict numerical improvement to the unconditional lower
bound for the ordinate of a possible RH counterexample.  The improvement must
come from a proved analytic implication, not from a new zero enumeration,
rounded endpoint recovery, a conditional hypothesis, or a reformulation of
RH.  It must clear both gates:

- **Novel:** the implication and its proof are not already present in the
  literature or elsewhere in this repository.
- **Significant:** after inserting the published Platt--Trudgian certificate,
  the conclusion gives a strict explicit `T_1 > 3,000,175,332,800`.

## Gates

- [x] 0 -> 1 in-progress: exact target, falsifiers, and competing attack
  routes are stated.
- [ ] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, explicit
  `T_1`, no open dependency.
- [ ] 2 -> 3 formalized: theorem interface and proof formalized in Lean, with
  the external Platt--Trudgian certificate isolated as an explicit input.
- [ ] 3 -> 4 publication-ready: standalone theorem, novelty audit, proof,
  certificate provenance, and Lean certificate.

## Constraint

Let `Gamma` be the least positive ordinate of an off-critical-line zero, if RH
is false.  Platt--Trudgian prove that the lowest `12,363,153,437,138`
nontrivial zeros are simple and on the line, giving `Gamma > T_0`.  A
successful amplifier must prove `Gamma > T_1` from zeta-specific analytic
structure.  The functional equation alone gives a quartet at the same
absolute ordinate and therefore cannot increase `Gamma`.  Fixed finite
positivity or moment tests are also excluded: the repository theorem
`finite-degree-reciprocal-tests-height-limited` proves that sufficiently high
off-line pairs evade every prescribed finite degree.

## Candidate moves

1. `[CONJECTURE]` **Minimal-counterexample descent.**  Construct an adaptive
   explicit-formula kernel attached to a hypothetical first off-line quartet
   at height `Gamma` and prove that its negative contribution forces a second
   off-line zero at ordinate at most `Gamma / lambda`, for some explicit
   `lambda > 1`.  Minimality would then give `Gamma > lambda T_0`.
2. `[CONJECTURE]` **Certificate-to-annulus transfer.**  Turn the verified
   boundary zero count at `T_0` into a zero-free annulus above `T_0` using an
   explicit lower bound for the completed zeta function on the top boundary
   and an upper bound for its logarithmic variation.  This succeeds only if
   the published certificate supplies a nonzero quantitative boundary margin;
   openness without an explicit margin is insufficient.
3. `[CONJECTURE]` **First-defect support theorem.**  Prove that a first
   off-line zero at `Gamma` creates a zeta-specific prime-side witness whose
   spectral support lies strictly below `Gamma`; combine that witness with the
   already verified divisor below `T_0`.  The witness must use the Euler
   product essentially, since functional-equation-symmetric fake functions can
   carry an arbitrarily placed first off-line quartet.
4. `[CONJECTURE]` **Integer zero-density exclusion.**  Derive a localized
   upper bound `< 2` for the number of off-line zeros in a window just above
   `T_0`; functional-equation reflection would make any nonempty upper-half
   off-line set have multiplicity at least two.  The bound must remain uniform
   as `beta` approaches `1/2`, where standard zero-density estimates normally
   lose all pointwise force.
5. `[CONJECTURE]` **One-zero total-count budget.**  Prove
   `N(T_1)-N(T_0) <= 1`.  Since an upper-half-plane off-line zero is accompanied
   by the distinct reflected zero `1-conj(rho)` at the same ordinate and with
   the same multiplicity, this total-count bound would force every new zero to
   lie on the critical line.  The published paper supplies `N(T_0)` but no
   local bound for `N(T_1)-N(T_0)`.
6. `[CONJECTURE]` **Endpoint minimum-modulus transfer.**  Certify explicit
   constants

   ```text
   m_0 <= min_{0<=sigma<=1} |xi(sigma+i T_0)|,
   max_R |xi'(s)| <= M_0,
   ```

   with `m_0>0` on a rectangle `R` immediately above the endpoint.  The mean
   value estimate then gives a zero-free continuation of height less than
   `m_0/M_0`.  The derivative bound is available from standard entire-function
   growth; the missing datum is an explicit positive `m_0`.

## Immediate attacks

- A functional-equation-only descent is false: the symmetry orbit preserves
  ordinate.
- The formal theorem `finiteEulerClass_no_height_amplification` strengthens
  this falsifier: for every `0 <= H < U`, functional-equation symmetry plus
  any finite exact Euler head admits a member zero-free through `H` with an
  off-line zero in `(H,U)`.  Thus a positive amplifier must use the exact
  infinite Euler product or quantitative endpoint data.
- A standard zero-density estimate cannot exclude an off-line zero
  arbitrarily close to the critical line unless it is uniform at
  `sigma = 1/2` and counts only off-line zeros.
- Partial-RH logarithmic-derivative bounds do not reach the top edge.  Their
  unknown-zero tail has scale
  `(delta^(-2)+1) log(T)/(2*pi*T)` for evaluation height
  `t <= (1-delta)T`; taking `t=T-h` with fixed `h` makes this scale comparable
  to `T log(T)/h^2`, so it blows up rather than yielding a fixed buffer.
- Speiser geometry supplies a left-of-line zero of `zeta'` when RH fails, but
  no theorem gives the strictly smaller ordinate needed for minimal-height
  descent.  Functional-equation quartic models show that derivative critical
  points may remain on the symmetry line at essentially the same height.
- Hadamard reciprocal sum rules cannot isolate the first high pair: for a
  reciprocal kernel of fixed order, the total tail above `H` is larger than a
  single height-`H` contribution by the zero-density factor of order
  `H log H`.  An order growing with height returns to the all-order/source
  problem and requires endpoint-scale divisor data.
- A finite positivity certificate cannot work uniformly in height by the
  repository's finite-degree blindness theorem.
- A qualitative continuity argument yields only an unspecified extension
  `T_0 + epsilon`; without an explicit lower boundary margin it gives no new
  numerical theorem.
- Recovering a larger endpoint already contained in the published computation
  is `[SEARCH]`, not a new theorem.

## Open core

`[OPEN CORE]` Produce one of two missing zeta-specific inputs:

1. an explicit endpoint minimum modulus `m_0>0` (or an equivalent winding
   margin) strong enough to give a positive numerical continuation radius; or
2. a source-built one-sided local count proving `N(T_1)-N(T_0)<=1` without
   enumerating further zeros.

The published theorem states the endpoint and zero count but publishes neither
datum.  Functional-equation symmetry, finite exact Euler data, fixed-degree
moments, standard zero density, partial-RH tail estimates, and Speiser geometry
do not supply them.  No strict explicit `T_1` has yet cleared the proof gate.

## Log

- 2026-07-10 -- created directly in 1-in-progress for the verified-height
  amplification research program.

## 2026-07-10 second attack: the boundary-discriminant reduction

### Exact count envelope

Let

```text
M(T) = T/(2*pi) * log(T/(2*pi*e)).
```

Bellotti--Wong's explicit zero-count theorem gives

```text
N(T) <= M(T) + E(T),
E(T) = 0.10076 log T + 0.24460 log log T + 8.08292       (T >= e).
```

Consequently the Platt--Trudgian integer `N_0=12,363,153,437,138`
would imply RH through any explicit `T_1>T_0` satisfying

```text
M(T_1) + E(T_1) < N_0 + 2.                                  (A)
```

Indeed, `(A)` gives `N(T_1)-N(T_0)<=1`, while a zero off the
critical line contributes the distinct reflected pair at one ordinate.  This is
the cleanest non-enumerative sufficient criterion found in this attack.

It does not yet promote.  At `T=T_0`, condition `(A)` is equivalent to an
endpoint phase being within two units of the one-sided explicit envelope.  The
published certificate gives the integer `N_0`, but it does not publish a
one-sided phase estimate sharp enough to establish `(A)`.  Thus the global
`N(T)` envelope does not remove the endpoint datum; it rewrites the missing
winding margin.

### Collision degeneracy

Write the completed critical trace in the `t` variable.  A reflected off-line
pair at `t=Gamma +/- i*delta` contributes

```text
q_delta(t) = (t-Gamma)^2 + delta^2,
```

whereas its collision limit on the critical line is the allowed double zero

```text
q_0(t) = (t-Gamma)^2.
```

On any verified compact set with `t <= Gamma-h`, `h>0`, direct algebra gives

```text
|q_delta'/q_delta - q_0'/q_0| <= 2*delta^2/h^3,
|log|q_delta| - log|q_0||     <= delta^2/h^2.
```

Hence the off-line pair and a double on-line zero become quadratically
indistinguishable to every bounded log-derivative or log-modulus reader below
the proposed first counterexample.  Since RH does not include simplicity, the
double on-line collision is an admissible RH configuration.  This kills every
continuous scalar boundary reader unless it comes with a source-built positive
gap; the quantized local count survives, but then one is back at `(A)` or an
argument-principle margin.

### Source-level endpoint target

If `T_0` is not itself a zero, simplicity of all verified zeros and their count
fix the sign of the Hardy trace at `T_0` once the initial sign is fixed.  If the
endpoint is a zero, the corresponding datum is the one-sided sign together with
its simple crossing.  Neither case gives a quantitative magnitude.  A new
theorem must first supply an effective central special-value separation of the
form

```text
0 < L(T_0) <= |Z(T_0)|.
```

That central value alone need not cover the full horizontal strip.  A sufficient
version is

```text
0 < m_0 <= min_(0<=sigma<=1) |xi(sigma+i*T_0)|,
```

or a finite chain of overlapping source-built local margins joining the
critical line to the known zero-free flanks.  The margin must be obtained from
the infinite Euler/archimedean constraint rather than a new evaluation.  An
explicit derivative envelope then gives a positive continuation radius.
Hölder hypertranscendence is qualitative and supplies no such special-value
measure.  Standard transcendence theorems also do not control the required
Dirichlet-phase sums at the algebraic integer height `T_0`.

The live object is therefore the distance of the completed Euler germ at
`T_0` from its divisor discriminant: analytically a minimum modulus, in the
Krein chart a smallest spectral gap, and topologically the margin preventing a
double on-line collision from resolving into an off-line pair.  Producing an
explicit positive source-built lower bound for that one quantity would clear
the requested height gate.  No such bound has been proved here.

## 2026-07-10 third attack: equivariant collar rather than a full top margin

### Correction of the endpoint target

The full-strip top-edge target in the second attack is unnecessarily strong
and can be impossible at the published endpoint.  If `T_0` is itself the
ordinate of one of the verified simple critical-line zeros, then

```text
min_(0<=sigma<=1) |xi(sigma+i*T_0)| = 0.
```

Simplicity gives a transverse local crossing, not a positive minimum on a
boundary containing that zero.  The correct object is therefore an
equivariant collar around the critical line, together with a one-sided outer
wing.

For `a>0` and `U>T_0`, split the new positive-ordinate strip divisor into

```text
C(a;T_0,U)  = {rho : T_0<Im rho<=U, |Re rho-1/2|<a},
W+(a;T_0,U) = {rho : T_0<Im rho<=U, Re rho>=1/2+a}.
```

`[PROVED]` If

```text
#C(a;T_0,U) <= 1,
W+(a;T_0,U)  = empty,
```

then RH is verified through `U`.  An off-line zero in the collar has a distinct
critical-line reflection in the same collar; a zero in the left wing reflects
into the empty right wing.  Only a critical-line zero may survive the one-point
central budget.  This exact theorem is formalized as
`RHTower.rhVerifiedThrough_amplify_of_equivariant_collar` in
`VerifiedHeightAmplification.lean`.  The whole-strip special case is
`RHTower.rhVerifiedThrough_amplify_of_increment_ncard_le_one`.

`[BRIDGE]` The result is an elementary equivariant counting interface, not a
new theorem about zeta and not yet a numerical height improvement.  Its value
is to identify a strictly better analytic target: no margin is required at the
allowed central endpoint zero, and only one outer wing must be certified.

### Discriminant form of the central input

Near a simple line zero, `|Xi|` vanishes but the first jet does not.  Thus a
local joint quantity of the schematic form

```text
|Xi(t)|^2 + r^2 |Xi'(t)|^2
```

can remain positive on a small central boundary even when the old endpoint is
a zero.  A quantitative lower bound for such a first-jet discriminant,
together with an explicit second-derivative bound, can isolate at most one
central zero by a Taylor/Rouche argument.  This supplies the shape of the
central hypothesis but not its source-built lower bound.  Standard local
analytic isolation is again only `[BRIDGE]`.

### Falsified route and open core

`[FALSIFIED]` The existing sweep-cascade route does not source-build the
required collar.  Its inputs include zero births, future pushes, a creation
rate, and a first-passage mechanism; these are flow/zero-fed assumptions, not
consequences extracted from the infinite Euler product.  It cannot be used to
claim a verified-height theorem.

`[OPEN CORE]` Produce explicit `a>0` and `U>T_0` from the exact completed Euler
constraint such that

1. a Jensen, Weierstrass, or first-jet discriminant estimate proves
   `#C(a;T_0,U)<=1`; and
2. an Euler/archimedean boundary estimate proves `W+(a;T_0,U)=empty`.

The estimates must be analytic consequences of the source, not a new zero
enumeration.  Until those two numerical inequalities are proved, no strict
`T_1` is promoted and the Platt--Trudgian lower limit has not been increased.

## 2026-07-10 fourth attack: divisor-orbit extension without height or jets

### Heightless formulation

Replace the interval statement by an extension problem for the certified divisor.  Let `D_0` be the
finite effective divisor formed by all certified positive critical-line zeros, with their exact
multiplicities.  The question is:

```text
Can the completed zeta source constraint force every admissible extension of D_0
to add a fixed reflection orbit before it can add a free reflection orbit?
```

A fixed orbit is represented by a critical-line zero.  A free orbit is the four-point orbit of a
generic off-line, off-real zero under the functional-equation and Schwarz reflections.  This
formulation has no preferred height variable and asks directly whether the source selects orbit
type.

### Exact finite-divisor falsifier

`[PROVED IN LEAN]` The finite divisor itself does not select.  For every finite set of positive
critical-line representatives with arbitrary multiplicities, every finite exact Euler head, every
fresh positive critical-line representative, and every prescribed generic off-line point of the
open strip, there are two FE/Schwarz carriers that preserve all old multiplicities exactly.  One
adds the fresh simple fixed orbit; the other adds the prescribed simple free orbit.  The theorem is
`RHTower.finiteDivisorPrefix_orbitNonselection` in
`FiniteDivisorPrefixNonselection.lean`.

The construction uses only products and analytic orders.  It contains no derivative, Taylor datum,
local expansion, or jet.  It strengthens the earlier empty-prefix falsifier
`finiteEulerClass_no_height_amplification`: even the complete exact finite verified divisor does not
help inside the FE/Schwarz plus finite-Euler class.

`[BRIDGE]` This is not a new zeta theorem and does not move the numerical bound.  Its proof is finite
polynomial packing, so it fails the novelty half of the dual gate if presented as new knowledge.  It
is retained as a formal no-go theorem because it removes an entire class of proposed amplifiers.

### Revised open core

`[FALSIFIED]` Finite verified divisor data, even with all multiplicities and any finite exact Euler
head, cannot force the orbit type of an extension.  The earlier first-jet discriminant is not the
active route.

`[OPEN CORE]` Construct a global source-to-divisor selection law for the completed infinite Euler and
archimedean constraint whose value changes under multiplication by a free-orbit quartic but not under
adjoining an allowed fixed orbit.  Such a law must be genuinely infinite: it cannot factor through a
finite divisor prefix, finitely many Euler factors, finitely many moments, or finite local data.  A
quantitative lower-bound theorem would follow only after this law is made effective for the published
certificate.

## 2026-07-10 fifth attack: infinite divisor versus infinite Euler source

### Infinite divisor

`[BRIDGE]` The complete infinite reciprocal divisor is faithful.  In the coordinate

```text
y_rho = -(rho-1/2)^(-2),
```

the all-order shifted moments `T_k=sum M_y y^k`, `k>=1`, determine the weighted divisor under the
standard reciprocal-zero summability and discreteness hypotheses.  This is the theorem in
`shifted-reciprocal-moments-determine-divisor.md`.  Consequently an infinite divisor, or any faithful
all-order transform of it, is zero-complete: it already records whether a free orbit exists.  It is a
valid coordinate for the conclusion but not an independent proof input.

The associated Markov/Pick statement is also already normalized in
`seam-log-markov-pick-rh-equivalence.md`: the representing measure is positive on the fixed-orbit
locus exactly when RH holds.  Assuming that positivity would restate the target.

### Infinite Euler source

The complete Euler data is different.  On `Re s>1`, the von Mangoldt Dirichlet series gives the
logarithmic derivative of zeta, and analytic continuation together with the Gamma factor and the
functional equation fixes the completed source globally.  A nonconstant fixed- or free-orbit
polynomial multiplier changes this exact logarithmic derivative, so the finite-divisor fakes do not
preserve the infinite Euler source.

`[BRIDGE]` Bare uniqueness of the source-selected function does not locate its zeros.  It selects
`zeta`; it does not prove that the selected divisor has no free orbit.  The latter implication is the
missing theorem.

### No-jet residual Weil form

Let `D_0` be the certified finite fixed divisor.  For an admissible explicit-formula test function
`g`, define schematically

```text
Q_D0(g) = EulerGamma(g * g_tilde)
          - contribution_D0(g * g_tilde).
```

By the Weil explicit formula this is the quadratic form of the residual infinite divisor.  It uses
the full von Mangoldt source and the archimedean term, not values or derivatives of `xi` at a point.
It therefore supplies the correct infinite-Euler, no-height, no-jet carrier.

`[CONJECTURE]` There is a source-defined proper test class `H_D0`, weaker than the full Weil cone but
complete for free orbits in a nonempty extension collar of `D_0`, on which `Q_D0` is nonnegative by a
direct Euler--Gamma argument.

### Attack and open core

If `H_D0` is dense enough to isolate every reciprocal divisor atom, positivity of `Q_D0` on
`H_D0` is again RH-equivalent.  If it is not dense, a free orbit can lie in the invisible annihilator
unless an independent source theorem excludes that annihilator.  Thus merely renaming the full Weil
criterion as residual positivity is circular.

`[OPEN CORE]` Construct a proper source-defined test space together with two independent proofs:

1. an Euler--Gamma proof that `Q_D0` is nonnegative on that space; and
2. a detector-completeness theorem showing that every free orbit in a strictly larger certified
   region has a negative witness in that space.

Neither proof may use the unknown residual divisor.  Producing this pair with explicit constants
would give a genuine strict lower-bound amplification.  No such pair has been proved here.

## 2026-07-10 sixth attack: bounded-support infinite-Euler tests

### Burnol-positive source class

Burnol's local-support theorem supplies an unconditional, genuinely infinite-Euler input: there is a
fixed `c_B>1` such that the Weil quadratic form is nonnegative for every smooth multiplicative test
supported in `[1/c_B,c_B]`.  This uses the complete prime and archimedean source and contains no
height parameter, zero enumeration, derivative datum, or jet.

For a finite certified fixed divisor `D_0`, the subspace of such tests whose Mellin transforms vanish
on `D_0` is nonzero.  In logarithmic coordinates, apply

```text
P(D) = product_j (D^2 + gamma_j^2)
```

to a bump supported strictly inside the same interval.  This preserves support and kills every
certified ordinate `+/- gamma_j`.  Burnol positivity therefore descends to an exact positive
quadratic form for the residual infinite divisor.

### Critical-tail uniqueness obstruction

`[PROVED HERE; ANALYTIC CORE IN LEAN]` The Mellin transform of a nonzero smooth compactly supported
test has finite exponential type and hence only `O(R)` zeros in a disc of radius `R`.  The exact
Jensen bound is formalized by `RHTower.exponentialType_zeroCount_le` and
`RHTower.exponentialType_zeroCount_linear` in `ExponentialTypeZeroDensity.lean`.

Pratt--Robles--Zaharescu--Zeindler prove that a positive proportion of zeta zeros are simple and on
the critical line.  Hence their distinct ordinates have `Omega(R log R)` density.  It follows that no
nonzero bounded-support Mellin test can vanish at all but finitely many simple critical-line zeros.
The infinite fixed-orbit tail remains a uniqueness set after deletion of the complete
Platt--Trudgian prefix.

`[FALSIFIED]` The bounded-support residual-Weil route cannot isolate a first free orbit by
annihilating all future fixed-orbit contributions.  The certified finite divisor is removable, but
the unknown infinite fixed tail is not.  This is a route obstruction, not a numerical improvement;
its paper theorem is recorded in
`bounded-support-weil-critical-tail-uniqueness.md` and classified `[BRIDGE]` because it is a direct
combination of classical Jensen/Paley--Wiener theory with published density and support-positivity
inputs.

### Surviving height-free problem

`[OPEN CORE]` Let `E` denote the exact completed infinite Euler--Gamma source and `D_0` the certified
finite fixed divisor.  Construct, directly from `E` and `D_0`, an effective integer or one-sided
functional `I(E;D_0)` satisfying both:

1. adjoining any further fixed reflection orbits cannot create the forbidden sign/index; and
2. adjoining a free reflection orbit in a nonempty source-defined extension domain must create it.

The construction may not factor through a bounded-support Mellin test, a finite Euler head, a finite
divisor prefix, or local jets.  Equivalently, the remaining possibilities are an unbounded-support
all-place positivity theorem, an integer index/local zero count with source-built boundary control,
or an explicit upper budget for the unknown fixed-orbit tail.  Any one of these must be made
effective before it yields a strict new Platt--Trudgian extension.

## 2026-07-10 seventh attack: cofinite Euler-tail rigidity

### The faithful infinite-source theorem

`[PROVED; NOT NEW]` Let `Lambda_1,Lambda_2` be two nonzero meromorphic completed carriers with the same
reflection functional equation and the same archimedean factor.  Suppose that in a right half-plane
their logarithmic-derivative Euler coefficients differ at only finitely many integers.  Then

```text
q(s) = Lambda_1'(s)/Lambda_1(s) - Lambda_2'(s)/Lambda_2(s)
```

is a finite Dirichlet polynomial `P(s)` there.  Since `q` is meromorphic on the plane and `P` is
entire, the meromorphic identity theorem gives `q=P` globally.  Differentiating the common reflection
law gives

```text
P(s) = -P(1-s).
```

No nonzero finite Dirichlet polynomial has this reflection antisymmetry: along the real axis, its
largest frequency grows exponentially on the reflected side and cannot be cancelled by the smaller
frequencies; descending induction kills every coefficient, and the constant coefficient then kills
itself.  Thus `q=0`, the quotient `Lambda_1/Lambda_2` is constant, and a common normalization makes
the carriers and their complete divisors equal.

This is the sharp contrast with the finite-prefix no-go: a finite divisor plus a finite Euler head is
orbit-blind, whereas the cofinite logarithmic-derivative Euler tail plus the exact completed
functional equation is divisor-faithful.

### Novelty and route verdict

`[BRIDGE]` This is an elementary special case of the strong-multiplicity-one/uniqueness landscape for
Dirichlet series and the Selberg class, so it does not clear the novelty gate.  It also does not
locate the source-selected divisor: uniqueness proves that the source selects zeta, not that zeta's
selected zeros are fixed reflection orbits.

`[FALSIFIED]` Replacing the full Euler source by the phrase "infinite data determines the function"
does not amplify the verified range.  The missing implication remains a one-sided source law:
cofinite Euler rigidity supplies faithfulness but no positivity, inertia bound, or local zero-count
budget.

## 2026-07-10 eighth attack: the one-prime Fredholm seam

### Competing integer-index constructions

The index branch has three distinct forms.

1. The finite Krein negative index is faithful and counts free-orbit pairs exactly, but its carrier is
   constructed from the zero poles and is therefore divisor-fed.
2. A normalized measured trace is source-shaped but cannot see a finite or density-zero off-line
   set; this is the formalized measured-index blindness theorem.
3. A Toeplitz/Fredholm index could in principle be both source-built and integer-valued, provided the
   Euler action preserves a source polarization modulo compact operators.

The third form is the only live no-jet integer candidate.  It can be tested directly on the concrete
Hardy--Titchmarsh Euler carrier.

### Exact one-prime theorem

`[PROVED IN LEAN]` For every `p>1`, the physical local factor

```text
T_p = I - p^(-1/2) U_p*
```

is invertible by the norm-convergent geometric series, and exact unitary transport makes its concrete
weighted-spectral realization invertible.  Its positive Euler Gram `G_p=T_p* T_p` is therefore also
invertible.

Nevertheless, for every positive Sonin cutoff `a`,

```text
[Pi_a,G_p] = Pi_a G_p - G_p Pi_a
```

is not compact.  If it were compact, then its lower corner would be compact; but

```text
(1-Pi_a) G_p Pi_a = -(1-Pi_a)[Pi_a,G_p],
```

contradicting the existing concrete noncompactness theorem for the Euler cross-boundary corner.
The new declarations are

```text
RHTower.evenPrimeLocalFactor_isUnit
RHTower.archimedeanPrimeLocalFactor_isUnit
RHTower.archimedeanPrimeEulerGram_isUnit
RHTower.archimedeanPrimeEuler_projectionCommutator_not_isCompactOperator
```

in `HardyTitchmarshEulerConcrete.lean`.  Direct build and the axiom audit pass.  The paper card is
`one-prime-euler-fredholm-seam.md`.

### Verdict

`[FALSIFIED]` The standard compact-commutator Toeplitz/Fredholm index cannot be attached to the
canonical one-prime Euler action.  The failure is not a zero of the local Euler symbol: the symbol
and Gram are units.  It is the noncompact source seam between the Euler action and the
Hardy--Titchmarsh polarization.

`[BRIDGE]` This is a direct formal connection and a useful route obstruction, but its functional
analysis is standard and it does not clear the novelty-by-significance gate or move the numerical
bound.

`[OPEN CORE]` The only surviving index formulation is an all-prime renormalization theorem: construct
from the complete Euler--Gamma source a polarization `Pi_E`, an action `G_E`, and a specified operator
ideal `J` such that `[Pi_E,G_E] in J` even though every one-prime commutator is noncompact, and prove
that the resulting relative index ignores fixed reflection orbits but changes under one free orbit.
The cancellation or renormalization must be proved from the prime/archimedean constraint and cannot
be imposed from the residual divisor.

## 2026-07-10 ninth attack: finite Euler Calkin independence

### Exact finite-family theorem

`[PROVED IN LEAN; NEW SOURCE THEOREM]` Fix a positive Sonin cutoff `a`, distinct scales
`r_1,...,r_m>1`, and coefficients `c_j` not all zero.  Then the lower corner

```text
(1-Q_a) (sum_j c_j (U_(r_j)+U_(r_j)*)) Q_a
```

is noncompact.  The same statement holds on the actual even Sonin carrier.  After multiplying each
coefficient by the nonzero Euler scalar `-r_j^(-1/2)` and applying the concrete dual
Hardy--Titchmarsh unitary, it gives the literal source theorem: every nonzero finite linear
combination of the positive Euler metric corners `M_(|1-r_j^(-1/2-is)|^2)` is noncompact.

The proof chooses the least active scale, separates its inward shell from the finitely many other
scaled shells, and observes an exact surviving coefficient on a corrected weakly-null Sonin shell
sequence.  The declarations are in `FiniteEulerCalkinIndependence.lean`, with endpoints

```text
RHTower.finiteDilationCorners_calkinIndependent
RHTower.finitePositiveEulerCorners_calkinIndependent
RHTower.finiteEvenDilationCorners_calkinIndependent
RHTower.finiteEvenPositiveEulerCorners_calkinIndependent
RHTower.finiteArchimedeanPrimeEulerCorners_calkinIndependent
```

Direct compilation, the endpoint build, the full `RHTower` umbrella build, and the axiom audit pass.
The theorem and dual-gate audit are recorded in
`../3-formalized/new/finite-euler-calkin-independence.md`.

### Literature correction and exact consequence

`[IMPORTANT CORRECTION]` This does not prove that every finite Euler/archimedean repair is
impossible.  Connes--Consani prove that the *product* of the archimedean phase ratio with finitely
many non-archimedean phase ratios is quasi-inner, even though an individual non-archimedean ratio is
not.  Their multiplicative Hardy-space construction is not the additive span of positive Gram
metric corners considered here.

`[PROVED]` What is excluded is every finite additive cancellation inside the positive Euler-metric
span.  These prime-scale corners generate an infinite-dimensional subspace in the Calkin quotient.
Thus an index repair cannot be a finite linear counterterm among the canonical positive local
metrics.  It must instead use nonlinear/product archimedean compensation, a genuinely infinite
renormalized all-place limit, a different polarization, or a different operator ideal.

### Bound verdict

`[BRIDGE]` This theorem is new source-side operator knowledge but does not locate a zeta zero and does
not move the numerical Platt--Trudgian bound.  It sharpens the surviving infinite-Euler problem
without solving it.

`[OPEN CORE]` Construct from the complete Euler--Gamma product a convergent renormalized all-place
operator or phase-ratio action on a specified polarization, prove the required compactness or ideal
membership after the archimedean compensation, and prove that its integer index is unchanged by any
additional fixed reflection orbit but changes under one free orbit.  Only after that index is made
effective relative to the certified finite divisor can it yield a strict verified-range extension.

## 2026-07-10 scientific-novelty correction

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The ninth attack's finite Calkin-independence theorem remains a
valid Lean theorem and a useful source bridge, but the label `[NEW SOURCE THEOREM]` above is
withdrawn as a scientific-novelty claim.  Its separating-shell proof is an instance of established
localization / limit-operator reasoning, and the Sonin and Hardy--Titchmarsh transports do not make
that parent mechanism new to the scientific literature.  The canonical classification is now
`../3-formalized/not_new_scientific_knowledge/finite-euler-calkin-independence.md`.

The proposed absolutely summable extension is retired for the same reason.  New work in this lane
must produce a proved, significant invariant of the infinite or multiplicative Euler data, survive
a broad primary-literature and parent-theory audit, and must not treat project-local formalization as
scientific novelty.

## 2026-07-10 primary-certificate audit

The Platt--Trudgian source was checked directly rather than inferred from the theorem statement.
Their Theorem 1 gives the exact endpoint

```text
T_0 = 3,000,175,332,800
```

and the exact count `12,363,153,437,138`.  The computational section says that the method evaluated
the completed zeta function on the half-line, counted sign changes, and used Turing's method to
certify that all expected zeros were accounted for.  It also states explicitly that the run did not
isolate most zeros beyond the precision needed to see a sign change, did not build the high-precision
zero database used in the earlier computation, and had nowhere to store that many zeros.

A full source inspection found no published value or lower bound for

```text
min_(0 <= sigma <= 1) |xi(sigma+i T_0)|,
```

no endpoint phase/winding margin, no one-sided boundary sign with magnitude, and no public data or
code link from which such a margin can be reconstructed.  Therefore the endpoint-minimum-modulus and
one-zero-count-envelope attacks genuinely require a new certificate datum; they are not blocked only
by an unread table in the paper.

Primary source: D. J. Platt and T. S. Trudgian, *The Riemann hypothesis is true up to
`3·10^12`*, arXiv:2004.09765, DOI 10.1112/blms.12460.

## 2026-07-10 correction: the global count-envelope gate is numerically decidable

The statement in the second attack that condition `(A)` still requires an unpublished endpoint
phase is incorrect once the Platt--Trudgian integer is used as the exact value `N(T_0)=N_0`.  The
quantity

```text
F(T_0)=M(T_0)+E(T_0)
```

is explicit, so

```text
F(T_0)<N_0+2                                                (A_0)
```

is a finite certified real-arithmetic proposition.  The exact count already fixes the corresponding
endpoint phase through the Riemann--von Mangoldt formula; no separate phase sample is logically
needed to decide `(A_0)`.

Moreover, for `T>2*pi`,

```text
M'(T) = (1/(2*pi)) log(T/(2*pi)),
E'(T) = 0.10076/T + 0.24460/(T log T),
```

so `F` is strictly increasing.  Therefore:

1. if `(A_0)` holds strictly, continuity gives a unique `T_* > T_0` with
   `F(T_*)=N_0+2`; every explicit rational `T_1` in `(T_0,T_*)` satisfies `(A)` and yields a strict
   verified-height amplification;
2. if `(A_0)` fails, this particular global envelope cannot amplify the endpoint, because `F` only
   increases.

`[OPEN ARITHMETIC CERTIFICATE]` Decide `(A_0)` with rigorous interval arithmetic and, if positive,
certify one explicit rational `T_1`.  This is not a new analytic theorem and would still require a
scientific-novelty audit, but it could move the published numerical lower bound.  It is intentionally
not evaluated in the present no-computation research pass.

This correction does not affect the separate minimum-modulus route: that route still lacks an
endpoint magnitude.  It removes the endpoint-magnitude claim only from the count-envelope route.

## 2026-07-11 final Route D verdict

### Medalist lens

The native Route D object is not the height variable.  It is the first possible atomic change of
reflection-orbit type after the certified divisor prefix.  Every successful amplifier must prevent a
free orbit from entering while allowing an arbitrary future fixed orbit.  A continuous window reader,
a finite source summary, or an asymptotic relative-density statistic cannot make that distinction at
absolute multiplicity two.

### Surviving theorem and its limit

`[PROVED; BRIDGE]` Let `F(T)=M(T)+E(T)` be any continuous strictly increasing explicit upper envelope
for `N(T)` on `[T_0,infinity)`, and let the certified count be `N(T_0)=N_0`.  If

```text
F(T_0) < N_0+2,
```

then continuity supplies `T_1>T_0` with `F(T_1)<N_0+2`; integrality gives
`N(T_1)-N(T_0)<=1`, and reflection excludes a free orbit in `(T_0,T_1]`.  If instead
`F(T_0)>=N_0+2`, monotonicity proves that this envelope cannot certify any strict extension.  Thus the
Bellotti--Wong envelope route is exactly an endpoint-slack test, not a new source-to-divisor law.

The Platt--Trudgian count and the Bellotti--Wong formula make that endpoint inequality decidable by
rigorous real arithmetic.  Under the present no-computation constraint it is deliberately not
evaluated.  Even a positive evaluation would be a new certified numerical bound obtained by combining
known theorems, not new scientific knowledge under the parent-theory gate.

### Dual-gate audit

- `[PROVED IN LEAN; BRIDGE]` The one-zero and equivariant-collar implications are exact consumers of a
  local count, but they do not produce that count.
- `[PROVED IN LEAN; BRIDGE]` A finite Euler head and an arbitrary exact finite certified divisor do
  not select the next reflection-orbit type.
- `[PROVED ON PAPER; BRIDGE]` Bounded-support residual Weil tests cannot annihilate the unknown simple
  critical-line tail; that tail is a uniqueness set for finite-exponential-type Mellin transforms.
- `[PROVED; BRIDGE]` Cofinite Euler-tail rigidity selects the completed function but supplies no sign,
  index, or local count for its divisor.
- `[OPEN CORE]` No theorem derived directly from the completed infinite Euler--Gamma source supplies
  an absolute off-line count `<2`, a source-to-divisor orbit selector, or a uniform localization
  margin above `T_0`.

No Route D claim produced in this program passes both NOVEL and SIGNIFICANT.  Accordingly no card is
promoted to `2-fully-proven/new_scientific_knowledge`, and no new Route D theorem is placed in
`3-formalized/new_scientific_knowledge`.  Promoting a reduction, a finite arithmetic check, or a Lean
interface would violate the scientific-novelty gate.

### Final classification

`[FINAL VERDICT]` Route D is **not a primary RH generator** with the present mathematics.  It is a
rigorous consumer and falsification laboratory: once another route supplies a source-built absolute
count, orbit-selection law, or explicit uniform margin, Route D can convert it efficiently into a
strict verified-height extension and ultimately an unconditional Lean theorem.  Without one of those
inputs, Route D neither proves RH nor creates new scientific knowledge, and the card correctly remains
in `1-in-progress` rather than being promoted or retired.

A future reactivation must arrive with all three items already mathematical, not merely interfaced:

1. an explicit `T_1>T_0`;
2. a completed-source proof of `N(T_1)-N(T_0)<=1` or an equivalent absolute free-orbit exclusion; and
3. a complete paper proof suitable for narrow Lean formalization with the external verified-prefix
   certificate isolated as an input.

## 2026-07-11 certified endpoint-envelope falsification

The user authorized the previously excluded arithmetic check on a remote RunPod.  Two independent
MPFR evaluations with directed rounding were used: a 256-bit evaluation of

```text
M(T) = T/(2*pi) * (log(T/(2*pi))-1)
```

and a 512-bit evaluation of the algebraically equivalent expression containing an independently
enclosed `e`.  With

```text
T_0 = 3,000,175,332,800,
N_0 = 12,363,153,437,138,
F(T) = M(T) + 0.10076 log T + 0.24460 log log T + 8.08292,
```

the 512-bit certificate is

```text
F(T_0) in
[12363153437148.023401580621417225055461234264425486198633997161465353298354590902524895940594434686325498,
 12363153437148.023401580621417225055461234264425486198633997161465353298354590902524895940594434686325499],

N_0+2-F(T_0) in
[-8.023401580621417225055461234264425486198633997161465353298354590902524895940594434686325499,
 -8.023401580621417225055461234264425486198633997161465353298354590902524895940594434686325498].
```

Hence

```text
F(T_0) > N_0+2
```

by more than `8.0234`.  Because `F` is strictly increasing for `T>2*pi`, every `T_1>T_0` satisfies

```text
F(T_1) > F(T_0) > N_0+2.
```

`[PROVED; CERTIFIED COMPUTATION; BRIDGE]` The Bellotti--Wong global zero-count envelope cannot amplify
the Platt--Trudgian endpoint by the one-new-zero budget.  This is now a falsified Route D branch, not
an open arithmetic certificate.  The reproducible certificate is
`computations/2026-07-11-route-d-count-envelope-mpfr.c`, with captured output in the adjacent `.txt`
file.

`[SCIENTIFIC-NOVELTY VERDICT]` The certificate decides a finite specialization of published bounds.
It neither creates new scientific knowledge nor changes the verified RH height.  It sharpens the
remaining Route D core: any count-based amplifier must use a genuinely local increment estimate or a
source-built argument-principle margin, not a monotone global upper envelope for `N(T)`.

### Quantitative replacement threshold

The same interval computation gives

```text
N_0+2-M(T_0) in
[3.775672128481673224984731719363664100672159533632891071743717,
 3.775672128481673224984731719363664100672159533632891071743718].
```

Therefore any replacement global upper envelope `M(T)+E_new(T)` of the same monotone form must prove

```text
E_new(T_0) < 3.775672128481674
```

before it can supply even an infinitesimal strict height extension by this argument.  The current
Bellotti--Wong error is greater than `11.799073709103090`.  The required improvement is thus structural,
not a rounding refinement.  A local increment bound can evade this global headroom obstruction; a
second global bound with comparable additive constants cannot.

## 2026-07-11 tenth attack: certified Turing one-zero amplification

The user authorized computation on a remote RunPod after the global-envelope branch was falsified.
Arb 2.17.0 supplies a rigorous `acb_dirichlet_zeta_nzeros` implementation of Turing's method.  At the
exact dyadic endpoint

```text
T_1 = T_0 + 111/256
    = 768044885196911/256
    = 3,000,175,332,800.43359375,
```

192-bit ball arithmetic returns the exact count

```text
N(T_1) = 12,363,153,437,139 = N_0+1.
```

`[PROVED; CERTIFIED COMPUTATION]` Platt--Trudgian give `N(T_0)=N_0` and place every zero through
`T_0` on the critical line.  The increment `(T_0,T_1]` therefore contains exactly one zero counted
with multiplicity.  An off-line zero would bring its distinct reflection `1-conj(rho)` at the same
ordinate, forcing an increment of at least two.  Hence the unique new zero is on the critical line,
and RH is verified through `T_1`.

Arb independently isolates the two adjacent nontrivial zeros:

```text
Im rho_(N_0+1) =
  [3000175332800.286524182413025478326707081851708198936873971352041023810581745375833376428202901696507
   +/- 3.80e-65],

Im rho_(N_0+2) =
  [3000175332800.434527689105328273081765501600923663114740853282724213190790269688442533139617031447943
   +/- 3.80e-65].
```

Thus the dyadic endpoint lies rigorously between them.  The source and output are
`computations/2026-07-11-route-d-turing-height-extension-arb.c` and the adjacent `.txt`; the complete
paper-level proof is banked in
`2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry/verified-height-one-zero-turing-extension.md`.

### Corrected Route D verdict

`[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` Route D is a successful **computational consumer**: an exact
Turing count plus the formal one-zero reflection theorem gives a genuine strict height extension.
The result fails the scientific-novelty gate because the mechanism is published zero counting plus
an elementary symmetry argument.  It does not solve the noncomputational source-to-divisor problem.

The remaining research route is now sharply separated from computation:

1. **computational Route D:** live and effective; it can continue extending the verified height by
   rigorously counting more zeros, but this is enumeration rather than new scientific knowledge;
2. **noncomputational Route D:** still open; it requires a completed-source local increment bound or
   argument-principle margin that does not evaluate further zeros.

No Lean promotion is made for the numerical certificate.  The generic implication is already
formalized as `rhVerifiedThrough_amplify_of_increment_ncard_le_one`; the Arb Turing count is an
external certified input, not a Lean theorem.

## 2026-07-11 eleventh attack: pointwise local-count literature and margin closure

### The exact headroom test survives every global-envelope update

Write

```text
H_0 := N_0+2-M(T_0).
```

The certified MPFR enclosure above proves

```text
H_0 < 3.775673.
```

Bellotti--Wong's June 2026 Corollary 1.3 gives, for every `T>=1`, each of the two
unconditional alternatives

```text
|N(T)-M(T)| <= 0.0946 log T + 5.746,
|N(T)-M(T)| <= 0.0970 log T + 4.954.
```

These improve earlier global estimates in some height ranges, but neither can amplify this endpoint.
Indeed `e<3` gives

```text
e^20 < 3^20 = 3,486,784,401 < T_0,
```

hence `log T_0>20`.  Therefore the two error terms at `T_0` are respectively larger than

```text
0.0946*20+5.746 = 7.638,
0.0970*20+4.954 = 6.894.
```

Both exceed `H_0`.  Their associated upper envelopes are increasing at this height, so neither can
prove `N(T_1)<N_0+2` for any `T_1>T_0`.  Thus even the strongest newer global bound found in the
primary-source audit misses the one-zero budget by a factor greater than `1.8`; no endpoint
rounding or constant-choice optimization can repair it.

Primary source: C. Bellotti and P.-J. Wong, *Counting zeros of Artin L-functions*, Corollary 1.3,
[arXiv:2606.31441](https://arxiv.org/abs/2606.31441).

### Why the short-interval papers do not specialize to the prescribed endpoint

The explicit short-gap results of Simonic--Trudgian--Turnage-Butterbaugh bound moments of
`S(t+h)-S(t)` over a macroscopic interval and deduce positive-proportion statements.  Zhao's 2026
strengthening likewise proves positive-proportion `r`-gap results and measure estimates for extreme
values of `S(t+h)-S(t)`.  These are genuinely local in scale (`h` can be comparable with
`1/log T`) but not pointwise in the base height.  Their conclusions permit any prescribed height,
including `T_0`, to lie in the exceptional set.  A single first off-line orbit has zero relative
density and therefore cannot contradict a density or positive-proportion theorem.

The pointwise Bellotti--Wong short-interval corollary instead bounds `N(T+1)-N(T)` by combining the
main term with two independent absolute bounds for `S`.  At `T_0` its upper bound is of order
`log T_0`, not `<2`.  Shrinking the interval removes the main-term contribution but does not remove
the two endpoint argument errors.  Consequently it also does not provide the required prescribed
one-zero increment.

Primary sources:

- A. Simonic, T. Trudgian, and C. Turnage-Butterbaugh, *Some explicit and unconditional results on
  gaps between zeroes of the Riemann zeta-function*,
  [arXiv:2010.10675](https://arxiv.org/abs/2010.10675).
- T. Zhao, *Density results for r-gaps between zeros of the Riemann zeta-function*,
  [arXiv:2603.17334](https://arxiv.org/abs/2603.17334).
- C. Bellotti and P.-J. Wong, *Improved estimates for the argument and zero-counting function of the
  Riemann zeta-function*, Corollaries 1.5--1.6,
  [arXiv:2412.15470](https://arxiv.org/abs/2412.15470).

### The repository consumer trichotomy

`[PROVED; PROJECT-LOCAL CLASSIFICATION]` Every Route D implication actually formalized or proved in
this repository belongs to one of the following three certificate classes.

1. **Integer-count consumers.**  The one-zero and equivariant-collar theorems require an exact local
   count or a cardinality bound `<=1`.
2. **Boundary-index consumers.**  Argument-principle, winding, homotopy, and Rouche transfers require
   a zero-free boundary together with either an evaluated winding or a strict boundary domination
   margin.
3. **Analytic-collar consumers.**  Minimum-modulus and derivative propagation require a positive
   anchor `a<=|F(s_0)|` (or a cofactor anchor after removing a known zero) and an upper derivative or
   sup-norm bound; the explicit radius is proportional to that positive anchor.

This is a classification of the proved Route D machinery, not a theorem that no future method can
exist.  It is nevertheless terminal for the present candidate: an upper growth estimate alone is
not one of the missing lower/index data, moment and density estimates do not specialize to `T_0`,
and Turing's method supplies the integer only after new sign/phase evaluations or zero isolation.
That last option is exactly the successful Arb computation already split into its own stage-2 card.

### Terminal verdict for the original candidate

`[RETIRED: REDUCES TO THE TARGET OR TO ENUMERATION]` The conjectural card asked for a **new
non-computational analytic theorem** that turns the published prefix into an explicit strict height
extension.  After eleven attacks, the alternatives have separated cleanly:

- direct Turing enumeration succeeds and has already produced the strict endpoint
  `T_0+111/256`, but is established computational zero verification and not new scientific
  knowledge;
- every proved noncomputational consumer still needs an exact local count, an evaluated winding, or
  a positive endpoint/boundary anchor;
- the best current global and pointwise published bounds do not meet the one-zero threshold;
- average, density, and positive-proportion bounds cannot control the prescribed first interval;
- finite-source and bounded-support substitutes have exact countermodels or uniqueness
  obstructions; and
- invoking the full completed Euler--Gamma source without producing one of the three data above is
  merely a restatement of the missing local RH assertion.

The existential proposition that some future analytic theorem could prove a larger verified height
is not declared false.  The **research route represented by this card** is retired because it has no
independent source-producing mechanism left: its successful branch is enumeration, and its
noncomputational branch reduces to the datum it was meant to generate.  Reopening requires a new
completed-source theorem that is not another interface to count, winding, or margin.

No claim from this closure passes the NOVEL x SIGNIFICANT gate.  Accordingly there is no Route D
card in `2-fully-proven/new_scientific_knowledge` and no Route D promotion to
`3-formalized/new_scientific_knowledge`.  The computational result remains correctly banked as
`2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry/verified-height-one-zero-turing-extension.md`.
