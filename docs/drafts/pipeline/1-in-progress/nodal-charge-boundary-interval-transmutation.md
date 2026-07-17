# Nodal charge boundary intervals and polarized shift transmutation

- **ID:** `nodal-charge-boundary-interval-transmutation`
- **Stage:** 1-in-progress
- **Type:** TYPED LOCALIZATION CORRECTION / POLARIZED CHARGE INTERVAL
- **Scientific status:** `[CONJECTURE UNDER ATTACK] [LOCAL INTERVAL LAWS LEAN-FORMALIZED]`
  `[PARENT EQUIVARIANT DEVISSAGE / TOEPLITZ INDEX] [GLOBAL HT COMPARISON OPEN]`
  `[NOT AN RH RESULT]`
- **Parents:**
  - `../2-fully-proven/not_new_scientific_knowledge/tate-theta-koszul-barnes-localization-transmutation.md`
  - `../2-fully-proven/not_new_scientific_knowledge/nodal-charge-character-fan-realization.md`
  - `../3-formalized/tate-clock-unilateral-boundary-defect.md`
- **Live successor:**
  `hypertranscendental-source-face-vanishing-cycle-conservation.md`

## Discriminator: charge two

The current endpoint proposal says that the localization boundary of `[x^m]` should land in the
`m`-th source-character line.  This cannot preserve the additive localization boundary when
`m>1`.  Already

```text
partial_K([x^2])=2[A/(x)],                                      (Q1)
```

whereas one endpoint character line has rank one.  Matching `[x^2]` with the charge-two line loses
the multiplicity and the intermediate charge crossing.

```text
[NO-GO]
The equivariant or source-character localization boundary of `[x^m]` is not the endpoint
character fibre `L_m`.
```

The positive replacement is an oriented charge interval.

## `[CONJECTURE -- CHARGE-INTERVAL LOCALIZATION]`

Let `L_k` be the charge-`k` line on one selected source face.  For `m>0`, define an oriented
interval representation `B(m)` with vertices `0,...,m-1`, stalk `L_k` at vertex `k`, and the
charge-raising structure map between consecutive stalks.  Its associated graded object is

```text
gr B(m)=directSum_(0<=k<m) L_k.                                (Q2)
```

For negative charge use the oppositely oriented interval and opposite lines.  Then the correctly
typed equivariant boundary should be

```text
partial_char([x^m])=[B(m)],                                     (Q3)
```

whose nonequivariant rank is `m`.  The endpoint `L_m` is the state reached after applying `x^m`;
it is not the boundary crossed on the way there.  Replacing `B(m)` by its split associated graded
retains its K-class but forgets the successor maps and hence the order of the crossings.

The interval obeys the cocycle law

```text
B(m+n)=B(m) concatenate shift_m(B(n)),                           (Q4)
```

which is the character-refined additivity of the `K_1` boundary.

## Polarized unilateral realization

On the unpolarized Laurent charge module `directSum_(k in Z)L_k`, multiplication by `x` is a
bilateral shift and is invertible.  It has no boundary defect and cannot choose an orientation.

Choose the positive chamber

```text
H_+=directSum_(k>=0)L_k
```

and let `S` raise charge by one.  Its backward partial inverse `B` satisfies

```text
B S=1,
S B=1-P_0.                                                     (Q5)
```

For every `m>=0`, the expected power law is

```text
B^m S^m=1,
S^m B^m=1-P_[0,m),
coker(S^m)=B(m), with gr B(m)=directSum_(0<=k<m)L_k.           (Q6)
```

The negative chamber reverses kernel and cokernel and hence reverses the oriented index.  Thus
the positive chamber missing from the unpolarized character fan is exactly what converts an
invertible bilateral charge translation into a nonzero localization boundary.

## Analytic opposite-charge realization

For the nodal modes

```text
ell_k(z)=exp(2 pi i k z/omega),
```

opposite charges pair to one.  Therefore the interval pairing is

```text
sum_(0<=k<m) ell_(-k)(z) ell_k(z)=m.                           (Q7)
```

Equation `(Q7)` is the analytic realization of the nonequivariant boundary multiplicity in
`(Q1)`.  It retains the full sector decomposition before forgetting the source characters, while
the shift action retains the interval arrows that the numerical pairing cannot see.

The algebraic power defect, exact prefix-plus-tail decomposition, pairing law, and interval cocycle
are Lean-formalized as

```text
tateClockIndBackwardN_forwardN
tateClockInd_boundaryInterval_add_forwardN_backwardN
tateClockPairing_boundaryInterval_add_shift
tateClockIndBoundaryInterval_add.                               (Q6L)
```

The analytic multiplicity and sharp endpoint no-go are Lean-formalized as

```text
nodalChargeBoundaryIntervalPairing_eq
nodalChargeBoundaryIntervalPairing_eq_endpoint_iff.             (Q7L)
```

## Typed covariant module

The nodal coordinate and the Barnes source operators should act on one graded module without being
identified.  On the Laurent model with coordinate `u`, put

```text
M_u(u^k)=u^(k+1),
delta(u^k)=lambda_k u^k,
T_j(u^k)=u^k,
T_r(u^k)=exp(lambda_k omega_r)u^k.                            (Q8)
```

Then

```text
[delta,M_u]=lambda_1 M_u,
T_r M_u=exp(lambda_1 omega_r) M_u T_r,
(T_j-1)M_u^k(1)=0.                                           (Q9)
```

Thus `x` is a charge-raising operator, `T_j-1` is its selected annihilator, and the vacuum `1`
provides the calibration sending `x^k` to `ell_k`.  This resolves the vector/operator symbol
collision without collapsing them into one ring element.

## Anti-theatre and novelty gate

The power defect of a unilateral shift, the Toeplitz index, the filtration of `A/(x^m)` by the
powers of `x`, and the equivariant identity

```text
[A/(x^m)]=1+q+...+q^(m-1)
```

are parent mathematics.  Equations `(Q1)`--`(Q9)` alone are therefore a bridge, not new science.

The candidate-new content is the global HT theorem that the oriented interval objects `(Q2)` glue
over the source-face resonance fan, that their covariant modules carry the same localization
sequence as the coherent Barnes `Tor` class, and that the independently defined analytic,
integral, positive, and spectral realizations are conservative on this interval field.  This is a
strict strengthening of endpoint matching and is falsified by any face for which the localization
boundary has a different character filtration.

Persistence modules already identify finite equioriented `A_m`-quiver representations with graded
modules over a polynomial ring, and coherent devissage already reconstructs additive invariants
from filtered subquotients.  Fujikawa's unilateral phase operator already supplies the unit index
and rank-one anomaly.  Therefore neither the local interval module, its cocycle, nor its index is
new.  The preliminary exact-search gate found no construction tying such interval modules to
hypertranscendence, source-face localization, and jointly conservative transverse reporters.

## Raw interval-capacity no-go

For a source-minimal germ equipped with a transverse reporter, the source-face boundary field is
not merely a constructible sheaf of obstruction groups.  It is a self-dual representation of the
**oriented exit-path category** of the resonance fan.  Every normal path carries an interval module
`B(m)`; path concatenation is `(Q4)`; and orientation reversal sends `B(m)` to the dual oppositely
oriented interval.

Raw interval capacity, however, does **not** characterize hypertranscendence.  The
differential-algebraic function `f(z)=exp(z)` satisfies `f(z+1)=e f(z)`.  For every `N`,

```text
p_N(z)=1+(exp(2 pi i z)-1)^(N+1)
```

is a nontrivial period-one differential-algebraic gauge whose difference from `1` vanishes through
order `N` at zero.  Both `f` and `p_N f` are differential-algebraic, satisfy the same source, and
have the same `N`-jet.  The existing Lean theorem
`existsUnique_gammaPeriodicFourierPolynomial_jet` proves the stronger arbitrary-finite-jet
freedom of the period-one analytic fixed field.

```text
[NO-GO]
Unbounded finite-jet invisibility is an invariant of the enlarged analytic difference-constant
field, not an invariant of hypertranscendence.                                             (Q10)
```

This explains why the bare-source theorem and local interval law cannot by themselves detect HT.
They must be compared only after descent to the declared joint constant field of the minimal
parameterized source-Galois problem.

## `[CONJECTURE -- CONSTANT-DESCENDED INTERVAL/KOLCHIN COMPARISON]`

Let `G_S^delta` be the minimal parameterized source-Galois groupoid over the declared joint
difference constants, and let `B_an` be the independently constructed polarized exit-path interval
representation.  The algebraic--analytic comparison should generate a constant-descended
subrepresentation

```text
B_rel(S,R) subset B_an
```

which excludes interval freedom coming only from enlargement of the analytic fixed field.  If
`iota_(S,R)(n)` is the cumulative Jordan--Hölder length of its differential-order-`n` interval
truncation, then

```text
iota_(S,R)(n)=KolchinDimensionPolynomial_(G_S^delta)(n)          for all large n.       (Q11)
```

The right side is parent parameterized Galois/Kolchin theory.  The left side must be constructed
from source-face localization, charge-raising arrows, transverse observation, and analytic
completion without defining it to equal the right side.  Equality `(Q11)` is the new comparison
target and a sharpened local form of the existing clock/Galois and dimension/curvature
conjectures.

For a single differential-algebraic observable the right side is eventually bounded; for a single
HT observable it grows as `n+1`.  Thus, if `(Q11)` is proved, hypertranscendence is exactly
unbounded **constant-descended** interval capacity, not raw periodic-gauge capacity.  The
conjecture is falsified if Gamma's descended interval growth is bounded, if `exp` retains the raw
periodic intervals after descent, or if two source-equivalent presentations give different
`iota_(S,R)`.

If `(Q11)` survives, the representations seen by the RH chains have exact meanings: continuation
failure is failure to extend an interval across an exit path; spectral incompleteness is nonclosed
completion of the unbounded interval limit; positivity is the chamber orientation; monodromy is
holonomy of interval concatenation; and noncanonical boundary conditions are choices of endpoint
splitting.  These identifications become mathematics only after comparison functors are
constructed and proved jointly conservative.

## Gates

- [x] isolate the charge-two endpoint contradiction
- [x] prove the all-power unilateral boundary identities, prefix decomposition, and cocycle `(Q6)`
- [x] prove the analytic interval pairing and sharp endpoint no-go `(Q7)`
- [ ] prove the covariant commutation laws `(Q9)`
- [x] run the preliminary parent and exact-search gate on the interval formulation
- [x] replace endpoint language in the Tate--Barnes bridge and character-fan target
- [x] kill raw interval capacity as an HT criterion by differential-algebraic periodic gauges `(Q10)`
- [ ] construct constant-field descent and the relative interval representation in `(Q11)`
- [ ] compare its length growth with the Kolchin polynomial
- [ ] construct the source-face resonance gluing of boundary intervals
- [ ] construct the global map of localization sequences
