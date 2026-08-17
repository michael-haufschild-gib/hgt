# Floquet emergence of hypertranscendental orbifold memory

- **ID:** `floquet-orbifold-tail-emergence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Two rational coarse-grainings can each erase every nonconstant HT observable when
  repeated alone, while their alternating periodic protocol retains a complete nonconstant
  orbifold-current field.  The topology lives in the time cycle, not in either static map.

## Theorem: emergent memory under alternation

Let `C` be the complex numbers with trivial derivation and let `y` be differentially
transcendental over `C`.  Define

```text
R_1(z)=z^2+1,
R_2(z)=(z-1)^2.
```

Then:

```text
Tail(R_1)=C,
Tail(R_2)=C,                                                 (1)
```

but the two phase-rotated period maps are

```text
P_0=R_2 composed with R_1,       P_0(z)=z^4,
P_1=R_1 composed with R_2,       P_1(z)=(z-1)^4+1,           (2)
```

and have exact nonconstant tails

```text
Tail(P_0)=C<delta y/y>,
Tail(P_1)=C<delta y/(y-1)>.                                  (3)
```

The phase currents

```text
tau_0=dz/z,
tau_1=dz/(z-1)
```

are transported rather than fixed by the individual steps:

```text
R_1^* tau_1=2 tau_0,
R_2^* tau_0=2 tau_1.                                        (4)
```

Thus one full period returns the current with multiplier `4`.

## Proof

The identities in (2) and (4) are direct symbolic identities.  In evaluated differential form,
they are

```text
delta(R_1(y))/(R_1(y)-1)=2 delta y/y,
delta(R_2(y))/R_2(y)=2 delta y/(y-1).                        (5)
```

The autonomous tail classification applied to the two period maps gives (3): `P_0` is the fourth
power map and `P_1` is its conjugate by `h(z)=z+1`.

It remains to justify (1).  Every rational map with a nonconstant tail is, up to homography, a
power, Chebyshev, or Lattes map.

- `R_1` is the centered quadratic polynomial `z^2+1`.  Its finite critical orbit starts
  `0,1,2,5,...` and is strictly increasing on the real line from `1` onward, hence infinite.  Every
  power, Chebyshev, and Lattes map is postcritically finite, so `R_1` is not exceptional.
- Translating the critical point of `R_2` to zero conjugates it to `z^2-1`.  Its finite critical
  point lies on a superattracting cycle of exact period two.  A quadratic power map has fixed
  critical points; a quadratic Chebyshev map has a strictly preperiodic finite critical point; and
  a Lattes map has no periodic critical point.  Critical orbit portrait is preserved by
  homographic conjugacy, so `R_2` is not exceptional.

The classification theorem therefore forces both static tails to be `C`, proving (1).

## General periodic transport law

Let phase-labelled rational maps `R_j : P1_(j-1) -> P1_j` form a period-`m` protocol.  Suppose
there are nonzero rational `k`-tensors `tau_j` and scalars `lambda_j != 0` such that

```text
R_j^* tau_j=lambda_j tau_(j-1)                              (6)
```

with phase indices read cyclically.  Then the rotated period map at every phase preserves its
phase tensor with multiplier

```text
Lambda=product_j lambda_j.                                  (7)
```

Evaluation on a free HT jet gives a cyclic family of eigenobservables and hence a nonconstant
stroboscopic tail at every phase.  When each phase tensor is minimal and the period composite is a
parabolic-orbifold map, the autonomous tail theorem identifies these as the complete phase tails.

Conversely, if one period composite has a nonconstant tail, its parallel tensor pulls backward
through the factors to a cyclic tensor chain satisfying (6).  Factorization of the corresponding
orbifold cover supplies the phase orbifolds.  Thus nontrivial periodic memory is equivalent to a
closed parabolic-orbifold transport cycle, even when no individual step preserves an orbifold in
the static frame.

## Physical interpretation

This is a genuinely time-dependent topology.  Each static law is in the complete-erasure phase,
but the ordered protocol has a protected stroboscopic current.  The singular support of the
current alternates between `0` and `1`; only after a full period does the topology close.

The closest physical analogy is an anomalous Floquet phase: a protected boundary quantity exists
for the period evolution although it is absent from every repeated snapshot rule.  Here the
statement is exact algebraic differential geometry, not a claim that the HT source is a quantum
system.  The mathematical object is a parabolic-orbifold bundle over a discrete time circle, with
the HT tail as its stroboscopic boundary field.

## Novelty and significance gate

- Non-autonomous rational dynamics is established, and Floquet topology is established in physics,
  but the checked searches found no result about differential-substitution tail fields or the
  emergence of a complete HT orbifold current from individually tail-trivial rational maps.
- The example is not merely existential: both static tails and both phase tails are classified
  exactly.
- The theorem changes the ontology of the topology.  It belongs to an ordered protocol, not to a
  single rational coarse-graining.
- The construction is elementary once the autonomous classification exists.  It is therefore a
  significant new consequence and research direction, but not by itself claimed to clear the
  medal-level gate.

## RH impact audit

There is no direct RH implication.  The result warns that testing one candidate zeta
coarse-graining at a time is incomplete: a periodic family could have a protected tail even if
each autonomous tail is trivial.  An RH application would still need an actual source-pure cycle
of rational transformations of the completed zeta differential field; none is known or supplied
here.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/FloquetOrbifoldTail.lean` formalizes the symbolic identities
(2), (4), and (5), together with both phase-rotated two-step eigenobservables.  It now also proves
the general finite periodic transport law (6)--(7):
`finitePhasePullbackComposite_apply_of_transport` composes an arbitrary finite chain of linear
pullbacks and multiplies its local transport scalars, while `finitePeriodicTransport_multiplier`
closes the phase chain and obtains the product Floquet eigenvalue.  Direct elaboration uses the
existing cache, and the axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The static-tail triviality and exact-tail completeness assertions still use the paper-level
autonomous classification, so the card remains in step 2.

## Gates

- [x] 0 -> 1: exact time-dependent phenomenon and explicit protocol isolated
- [x] 1 -> 2: static triviality, phase tail identities, and general transport law proved
- [x] general finite periodic transport law formalized unconditionally
- [ ] 2 -> 3: symbolic transport is formalized; assemble with the autonomous tail classification
- [ ] 3 -> 4: independent novelty audit and standalone exposition

## 2026-08-14 — the phase tails contain their currents, unconditionally

The shared layer `formal/GaloisForLFunctions/HTGeometry/OrbifoldCurrentTailInclusion.lean`
(unconditional, axiom-clean) supplies the containment half of `(3)` for both phases of this
protocol:

- `HTGeometry.differentialAdjoin_logDeriv_le_stableRangeCore_of_pow` applied to the phase-zero
  period map `P₀(z) = z⁴` gives `C⟨δy/y⟩ ≤ Tail(P₀)` — the phase-zero current is stable at every
  depth, with multiplier `4`, which is exactly the Floquet eigenvalue this card's
  `phaseZeroCurrent_twoStep` computes;
- `HTGeometry.differentialAdjoin_logDeriv_sub_le_stableRangeCore_of_pow` applied to
  `P₁(z) = (z-1)⁴ + 1` gives `C⟨δy/(y-1)⟩ ≤ Tail(P₁)`, the phase-one current.

So the *emergence* half of the theorem — that the alternating protocol retains a nonconstant
orbifold current although neither static step does — is now formal on the side that asserts
retention.  What still rests on the paper-level autonomous classification is the complementary
assertion `(1)`, that each static tail is exactly `C`, and the exactness (rather than containment)
of `(3)`.

## Lean status — the protocol identities and the scaling branch are formalized

`HTGeometry/FloquetOrbifoldPeriodMaps.lean` (unconditional, axiom-clean, umbrella-wired) owns
equations (2), (4) and the easy half of (3):

- `quadTwo_comp_quadOne : quadTwo.comp quadOne = quadPow` — the phase-zero period map is `z^4`.
- `quadOne_comp_quadTwo : quadOne.comp quadTwo = quadPowShift` — the phase-one period map is
  `(z-1)^4 + 1`.
- `quadOne_pullback_current` and `quadTwo_pullback_current` — equation (4) as identities in
  `RatFunc C`:

  ```text
  R_1^*( (z-1)^(-1) )·R_1' = 2·z^(-1),      R_2^*( z^(-1) )·R_2' = 2·(z-1)^(-1).
  ```

- `quadPow_invariant_relation`, `quadPowShift_invariant_relation` — each period map fixes its
  current up to the multiplier `4`, and `quadPow_isInvariantDifferential`,
  `quadPowShift_isInvariantDifferential` read these as invariant differentials of weight one on the
  free jet field, with currents `delta y / y` and `delta y / (y-1)`.
- `differentialAdjoin_le_orbifoldTail_quadPow`,
  `differentialAdjoin_le_orbifoldTail_quadPowShift` — equation (3), inclusion `<=`:
  `C<delta y / y>` lies in `Tail(P_0)` and `C<delta y/(y-1)>` lies in `Tail(P_1)`.

Equation (1) is reduced to one residual case.  `HTGeometry/QuadraticNoInvariantDifferential.lean`
proves that for both individual steps every relation `Q∘R·(R')^k = mu Q` with `Q != 0`, `mu != 0`
has `k = 0` and constant `Q`; `HTGeometry/QuadraticOrbifoldTail.lean` turns this into
`quadOne_no_order_one_eigen` / `quadTwo_no_order_one_eigen` (no nonconstant eigenvector of jet
order at most one) and `quadOne_eigen_eq_one` / `quadTwo_eigen_eq_one` (a finite-order eigenvector
can only have eigenvalue one).  So `Tail(R_i) = C` is now equivalent to excluding a nonconstant
finite-order element *fixed* by `Phi_(R_i)`.  See the pass-4 section of
`rational-coarse-graining-orbifold-tail-classification.md` for why the current descent does not
close that branch and what it needs.

## Lean status — equation (1) holds through jet order two, and is now one condition

Two advances, both unconditional and axiom-clean.

**Normalizing shifts are fixed elements.**  `HTGeometry/JetFixedFieldShift.lean` proves
`hasNormalizingShift_iff_exists_fixed`: at jet level `M ≥ 2` a normalizing shift is *the same thing
as* a `Phi_R`-fixed element of jet order exactly `M`.  A shift `t` makes `y_M + t` scale by `R'`;
so does `y_1`; so `(y_M + t)/y_1` is fixed and its `M`-th partial is `1/y_1`.  Conversely a fixed
element of order exactly `M` is an eigen-relation of weight zero and eigenvalue one whose order does
not drop, so `lowerOrder_or_hasNormalizingShift` returns a shift.

Hence `forall_fixed_isConst_iff`, and for the two steps of this protocol
(`HTGeometry/QuadraticTailShiftEquivalence.lean`):

```text
quadOne_forall_fixed_isConst_iff,  quadTwo_forall_fixed_isConst_iff :
  Tail(R_i) = C   <=>   no jet level of order at least two carries a normalizing shift.
```

**Equation (1) through jet order two.**  Since neither map admits a normalizing shift at level two
(`quadOne_not_hasNormalizingShift_two`, `quadTwo_not_hasNormalizingShift_two`, from the
non-existence of a rational affine connection), the equivalence gives unconditionally

```text
quadOne_fixed_of_order_two,  quadTwo_fixed_of_order_two :
  a Phi_(R_i)-fixed element of jet order at most two is constant.
```

This strictly extends the pass-5 statement at jet order one.

**What is left.**  One family of statements, one per jet level `M >= 3`.  The descent
(`HTGeometry/QuadraticShiftDescentBranches.lean`) reduces each of them: a shift at level `N + 3`
either descends to level `N + 2` — through the affine cocycle of the two top coefficients of the
slice, whose denominator is a scalar eigenvector of the same degree — or is a polynomial of degree
one or two in `y_(N+2)`, the degree-zero case being impossible because
`∂_(N+2) sigma_(N+3) = (N+3)·R''·y_1` is nonzero.  The two residual degrees are analysed at the end
of `rational-coarse-graining-orbifold-tail-classification.md`.

## Closed — the orbifold tail of both quadratics is trivial, unconditionally in Lean

```text
GaloisForLFunctions.HTGeometry.quadOne_tail_trivial :
  Phi_(z^2+1)(g) = g  ->  g is constant
GaloisForLFunctions.HTGeometry.quadTwo_tail_trivial :
  Phi_((z-1)^2)(g) = g  ->  g is constant
```

for every element `g` of the free jet field, at every jet order, with no hypotheses and no added
axioms (`[propext, Classical.choice, Quot.sound]`).  `HTGeometry/QuadraticOrbifoldTailTrivial.lean`.

The general engine is `HTGeometry/JetTailTrivial.lean`:

```text
fixed_isConst :  no fixed element of jet order one, no shift at level two, no shift at level three
                 ==>  every Phi_R-fixed element of the free jet field is constant.
```

Its proof is the descent chain.  The level-free tower `V_t = −δ^{t+1}(1/y₁)/y₁^t`
(`JetInverseTower.lean`) has jet order exactly `t + 2` with unit top descent, solves
`R'^{t+2}Φ(V_t) = R'V_t + Ê_t`, and satisfies the binomial convolution `invTowerDefect_eq`.  The
chain `chain t = w + ∑_{u<t} binom(N+1,u+1)·V_u·z_{N−u}` (`JetChainDescent.lean`) strips a
normalizing shift one coordinate at a time: its defect descends to `binom(N+1,t+1)·Ê_t` by the
subdiagonal law `topDescent_K(s_m) = binom(m,K)·T_{m−K}` (`JetShiftSubdiagonal.lean`) together with
the subset-of-a-subset identity, so uniqueness pins `topDescent_{N−t}(chain t) = −binom(N+1,t+1)V_t`.
Since `topDescent_{N−t}` cannot output jet order above `N − t` while `V_t` has jet order `t + 2`, the
chain dies at the first `t` with `t + 2 > N − t`; for `N = 2T+1` odd that is `t = T`, where the
extra term produced by `V_{T−1}` gives
`topDescent_{T+1}(chain T) = −binom(N+1,T+1)V_T + binom(N+1,T)z_{T+2}` and the top descent
`binom(N+1,T) − binom(N+1,T+1) ≠ 0` contradicts the order bound.  Odd levels are reduced to even
ones by `zshift_succ` (`JetShiftPropagation.lean`), whose first stripping step is supplied by the
pinned top coefficient at the original level.
