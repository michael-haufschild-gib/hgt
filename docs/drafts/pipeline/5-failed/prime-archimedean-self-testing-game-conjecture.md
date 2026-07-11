# Prime--archimedean self-testing game conjecture

- **ID:** `prime-archimedean-self-testing-game-conjecture`
- **Stage:** 5-failed
- **Type:** FAILED ROUTE; greenfield nonlocal-game / source-SOS route
- **Scientific status:** `[REFUTED AS AN INDEPENDENT MECHANISM]`; the relation bridge is valid,
  but source-to-perfectness is RH itself in game coordinates
- **Source:** pivot from the failed acausal-process route, 2026-07-11
- **Statement:** There should exist an all-prime, archimedean-anchored nonlocal constraint game,
  defined from Euler--Gamma data before reading the divisor, for which every completed-zeta zero
  gives a perfect strategy. Rigidity of a perfect strategy should self-test the prime relations
  `A_p psi = p^(1/2-s) B_p psi`; norm preservation then forces `Re(s)=1/2`.

## Goal

Keep the pre-Big-Bang premise but remove the failed channel physicality assumption. The players are
atemporal local laboratories: no communication, shared global constraint, no global causal order,
and no evolution parameter. The scalar field does not propagate. Its zero is proposed to be a point
of *perfect global consistency* among prime and archimedean measurement constraints.

The crucial difference from the retired process route is:

```text
retired route: the object is physical only on the critical line;
present route: the game is physical for every s, but perfect play may occur only on the line.
```

Thus an off-line hypothetical zero does not make the ambient construction undefined. It would make
the source-to-perfectness conjecture false, which is a genuine falsifier.

## Absolute anti-vacuity rules

The route is invalid if it uses any of the following.

1. A payoff entry containing `xi(s)`, `|xi(s)|`, the zero list, or an oracle deciding whether
   `xi(s)=0`.
2. A generic complexity-theoretic encoding of an arbitrary mathematical proposition into a
   nonlocal game. Such an encoding would work equally for every statement and contain no arithmetic
   mechanism.
3. A Hamiltonian-history-state or transfer-matrix construction in which time propagation does the
   work.
4. A finite-prime determinant declared to converge to `xi` without a source proof.
5. A game whose rules already impose `|p^(1/2-s)|=1`.
6. A self-testing theorem applied to operators or a state chosen from the zeta divisor.

The payoff must be assembled from finite Euler data, the theta/Gamma completion law, and universal
normalizations. The divisor may appear only as a theorem about the resulting optimal value.

## Candidate moves

### Bell inequality with zeta as a coefficient

`[REFUTED]` Put `xi(s)` directly into a Bell functional and make its vanishing equivalent to
saturation.

This is an exact target encoding and proves nothing about the zero location.

### Generic MIP-star encoding

`[REFUTED]` Use the expressive power of nonlocal games to encode the proposition "RH is true" or
"xi(s)=0".

This is computational universality, not arithmetic. It violates source purity and the anti-theatre
test.

### Independent prime modulus tests

`[BRIDGE; INSUFFICIENT]` Test each relation

```text
A_p psi = p^(1/2-s) B_p psi
```

with unitary observables `A_p,B_p`. These tests locate the critical line but contain no zeta
information and are invariant under independent prime phase gauges.

### Archimedean-anchored all-prime rigidity game

`[CONJECTURE; SELECTED]` Construct finite games `G_(P,s)` for finite prime sets `P`, with:

- prime relation tests tying two noncommuting player representations to `p^(1/2-s)`;
- an archimedean test derived from theta/Poisson reciprocity;
- cross-tests that fix the relative phase gauge between every prime laboratory and the single
  archimedean laboratory; and
- a coherent exhaustion `P -> all primes` whose loss has a source-derived limit.

The desired implication is

```text
xi(s)=0  ->  omega_star(G_s)=1,                         (ZP)
```

where `omega_star` is the optimal quantum winning probability. Perfect-strategy rigidity must then
produce the prime relations above. The game remains valid with `omega_star(G_s)<1` away from the
perfect locus.

## Two-prime relation test

Fix `P={2,3}`. Let `psi` be a unit vector and let `A_p,B_p` be unitaries. Put

```text
r_p(s)=p^(1/2-s),
ell_p(s;psi,A_p,B_p)
  = ||A_p psi-r_p(s)B_p psi||^2/(1+|r_p(s)|)^2.
```

This is a normalized loss in `[0,1]`.

### Exact minimum `[PROVED; BRIDGE]`

For every nonzero complex `r`,

```text
inf_(psi,A,B) ||A psi-r B psi||^2/(1+|r|)^2
  = ((1-|r|)/(1+|r|))^2,                               (M)
```

where the infimum ranges over unit vectors and unitaries on any nonzero Hilbert space.

#### Proof

Both `A psi` and `B psi` are unit vectors. The reverse triangle inequality gives

```text
||A psi-r B psi|| >= ||A psi||-|r| ||B psi|| = |1-|r||.
```

Equality is attained by choosing `A psi` to have the same phase and direction as `r B psi`.
Dividing by `(1+|r|)^2` proves `(M)`.

### Critical-line consequence `[PROVED; BRIDGE]`

The relation test is perfect exactly when `|r_p(s)|=1`, equivalently

```text
p^(1/2-Re(s))=1  <->  Re(s)=1/2.
```

Hence perfection of even one prime relation localizes `s` to the critical line. The second prime is
needed not for localization but to prevent a one-generator gauge or accidental single-frequency
realization in the eventual archimedean cross-test.

## Conditional RH theorem

`[PROVED CONDITIONAL BRIDGE]` Suppose the source-pure all-prime game exists and satisfies `(ZP)`, and
every perfect strategy self-tests at least one prime relation

```text
A_p psi=p^(1/2-s)B_p psi
```

with `A_p,B_p` unitary and `psi` nonzero. Then RH follows from the exact minimum theorem.

The mathematical load is entirely in `(ZP)` and the source-specific self-test. The norm argument is
only the final localization gate.

## The source-SOS form of the open core

Nonlocal-game optimality is naturally certified by a noncommutative sum-of-squares identity. The
route asks for a pre-divisor identity of the schematic form

```text
1-winning_operator(G_(P,s))
  = sum_j R_(P,j,s)^* R_(P,j,s) + boundary_(P,s),        (SOS_P)
```

where every `R_(P,j,s)` is built from Euler generators, the archimedean reference, and the game
relations. In the all-prime limit, a completed-source zero must annihilate the boundary and force
every square to vanish, including a prime relation square.

`[OPEN CORE]` Construct `(SOS_P)` with a limit theorem derived from theta/Poisson completion such
that `xi(s)=0` forces zero total loss, without placing `xi` in the verifier or defining the boundary
as `|xi(s)|^2`.

This is the only place the route could prove RH. If the boundary can vanish off line independently
of the relation squares, or if its identification with the completed scalar is tautological, the
route dies.

## Attacks

### Holomorphic-payoff obstruction

`[PROVED; BRIDGE]` A physical payoff table is real-valued. A holomorphic family of real payoff
tables on a connected complex domain is constant entrywise. Therefore the game cannot depend
holomorphically on `s` in the naive sense. It must be a real-analytic family in `(Re(s),Im(s))`, a
sesquiholomorphic construction involving `s` and `conj(s)`, or a fixed game with `s` entering only
through a tested representation.

### Phase-gauge fake

Completely multiplicative unimodular twists can preserve all independent prime relation losses
after local rephasing while moving the continued divisor. The archimedean cross-test must therefore
fix a single external phase reference and reject Helson-type twists before their zeros are read.

### Finite-game density barrier

`[CONJECTURAL NO-GO; TO PROVE]` A fixed finite-question, finite-answer game with finite-dimensional
strategies and coefficients drawn from finitely many prime exponentials has an optimality locus of
finite exponential type and cannot reproduce the `T log T` zero count. The all-prime limit is not
optional. A proof requires an elimination and zero-count theorem for the exact game class; it is
not asserted here as established.

### Self-testing can be irrelevant

A game may self-test a beautiful noncommutative representation while its perfectness has no relation
to the completed scalar. Rigidity is useful only after `(ZP)` is derived from the source.

### Shifted completed fake

The shifted family `xi(s+a)xi(s-a)` has a completed Euler product and off-line zeros. Its local
radial parameters fail the prime relation test, so a successful game rejects it. This is necessary
but not sufficient: local temperedness by itself does not prove RH for the untwisted source.

### Hidden-flow test

The constraint game is static. Any conversion into a history-state Hamiltonian, repeated strategy,
transfer operator, or time-evolution proof is a flow in disguise and is not this route.

## Boundary cases

- `P=empty`: no modulus relation, so perfection cannot localize `s`.
- one prime: localization works, but the phase can be absorbed into a single local gauge; no
  arithmetic specificity remains.
- two primes without an archimedean test: unique factorization separates their frequencies, but
  independent local phases remain invisible.
- source test without prime relations: it may detect `xi(s)=0` but cannot force the line.
- prime relations without source test: it detects the line but not the divisor.

The irreducible object is therefore a relative prime--archimedean game, not either component alone.

## Preliminary collision and literature audit

`[SEARCH; NO EXACT SIGN FOUND]` Project-wide searches found no nonlocal-game, Bell-inequality,
self-testing, contextuality, or perfect-strategy RH route. Focused arXiv searches found no Riemann
zeta/RH construction using nonlocal-game perfection or self-testing.

The parent literature does contain general self-testing, synchronous game algebras, linear
constraint system games, and sum-of-squares rigidity. Those are infrastructure, not evidence for
the source-to-perfectness implication `(ZP)`.

No scientific-novelty claim is made. The route remains `[NOVELTY UNVERIFIED]` until an actual game,
proof, and broad literature comparison exist.

## Exact open cores

`[OPEN CORE 1: FINITE SOURCE GAME]` Give the full questions, answers, payoff, and strategy class for
the two-prime theta-anchored game; prove it is a valid game for every `s` in the strip.

`[OPEN CORE 2: SOURCE SOS]` Derive `(SOS_P)` from finite Euler factors and theta reciprocity with no
`xi` coefficient or zero oracle.

`[OPEN CORE 3: ALL-PRIME LIMIT]` Prove convergence of the game values or SOS certificates in a
topology strong enough to preserve perfectness and retain isolated zeros.

`[OPEN CORE 4: ZERO TO PERFECTNESS]` Prove `(ZP)` from the completed source identity.

`[OPEN CORE 5: RIGIDITY]` Prove that every perfect strategy annihilates a prime relation square,
rather than hiding the loss in an infinite-dimensional or commuting-operator sector.

## Current verdict

`[ROUTE RETIRED: SOURCE-PERFECTNESS IS RH IN GAME COORDINATES]`

The ambient game can exist off the critical line, but the proposed source-to-perfectness theorem
cannot be split into an arithmetic source lemma followed by an independent self-testing lemma. Any
nonnegative loss containing a prime relation term already has a strictly positive, strategy-free
floor off the line. Proving that a completed-source zero annihilates that loss is therefore RH, not
a mechanism from which RH follows.

### Terminal additive-loss theorem `[PROVED; NO-GO]`

Let a finite or infinite game loss satisfy, for some prime `p` and some `w_p>0`,

```text
L(s;strategy) = S(s;strategy) + sum_q w_q ell_q(s;strategy),
```

where `S>=0`, every `ell_q>=0`, and `ell_p` is the normalized unitary relation loss above. Then for
every strategy

```text
L(s;strategy)
  >= w_p ((1-p^(1/2-Re(s)))/(1+p^(1/2-Re(s))))^2.        (F)
```

The same bound holds for the infimum over strategies. Consequently

```text
optimal loss at s = 0  ->  Re(s)=1/2.                   (P)
```

This remains true if the infimum is not attained and in commuting-operator or
infinite-dimensional strategy classes: `(F)` is the reverse-triangle bound for every individual
strategy.

Therefore any theorem

```text
xi(s)=0 -> optimal loss at s = 0
```

for such a source-built game proves RH in that theorem itself. Self-testing adds no missing force;
it only recovers a relation whose unavoidable modulus floor has already localized `s`.

### Theta cancellation does not supply perfectness `[PROVED; NO-GO]`

On the critical line the repository's exact theta trace is

```text
completedRiemannZeta_0(1/2+it)
  = Fourier(xiThetaLogSource)(t/(4*pi))/2
  = Re Fourier(xiThetaPositiveSource)(t/(4*pi)).         (T)
```

Thus a zero in `(T)` is cancellation of a linear averaged Fourier correlation. Perfect play in the
proposed game is zero of a nonnegative loss and, by `(F)`, simultaneous annihilation of a local
relation defect. A vanishing average does not imply pointwise or squarewise annihilation.

The obvious conversions exhaust the direct construction:

1. Use the theta trace linearly: a zero is an interior cancellation value, not a perfect-strategy
   certificate.
2. Square the trace: this gives a source loss equal to `|xi|^2`, but adding a prime relation loss
   leaves the positive floor `(F)` at a hypothetical off-line zero.
3. Multiply the relation loss by `|xi|^2`: every zero becomes perfect, but all relation rigidity is
   erased there because every strategy has zero weighted relation loss.
4. Add cross terms that turn source cancellation into relation squares: proving their
   noncommutative SOS identity is precisely an independent inequality excluding off-line zeros.
   It is the RH-strength step, not a consequence of theta/Poisson completion.

The fourth option also collides exactly with the completed-source positivity verdict already in the
corpus: changing a commutative trace-Hankel Gram into a noncommutative game SOS does not create the
missing source sign principle. A genuinely new pre-divisor object would be required.

### What survives

The exact unitary relation minimum is a valid critical-line detector, and the nonlocal-game
formulation appears absent from the focused literature search. Neither is significant new RH
knowledge. The first is elementary norm geometry; the second is a novel vocabulary for the same
missing implication. The route fails the significance half of the dual gate and is retired rather
than promoted as an outlandish proof programme.

## Gates

- [x] 0 -> 1 in-progress: exact two-prime relation loss and localization theorem proved; vacuous
  encodings excluded; source-SOS and fake-family gates named; initial collision search clean.
- [x] terminal attack: every nonnegative source-plus-relation loss has the explicit off-line floor
  `(F)`; the theta source supplies averaged cancellation but no relation-square annihilation.
- [ ] 1 -> 2 fully-proven: no source game, SOS identity, all-prime limit, or zero-to-perfectness
  theorem exists; the proposed route is retired because that theorem is RH itself in game
  coordinates.
- [ ] 2 -> 3 formalized: intentionally out of scope until the mathematics survives.
- [ ] 3 -> 4 publication-ready: ineligible before dual gate and independent expert audit.

## Parent references

- Cui--Mehta--Mousavi--Nezhadi, *A generalization of CHSH and the algebraic structure of optimal
  strategies*, [arXiv:1911.01593](https://arxiv.org/abs/1911.01593).
- Zhao, *Robust self-testing for nonlocal games with robust game algebras*,
  [arXiv:2411.03259](https://arxiv.org/abs/2411.03259).
