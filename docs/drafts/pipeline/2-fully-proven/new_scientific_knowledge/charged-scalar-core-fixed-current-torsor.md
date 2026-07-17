# A charged scalar HT core is a multiplicative torsor over a fixed current field

- **ID:** `charged-scalar-core-fixed-current-torsor`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every positive-clock-character scalar persistent core is a rank-one
  `G_m` Picard--Vessiot torsor over a nonconstant fixed hypertranscendental current field; its full
  fixed field is determined exactly by whether the constraint multiplier has finite or infinite
  order.

## Goal

Identify the static object underneath a charged persistent hypertranscendental phase.  The result
turns a relative invariant into an exact invariant and classifies the information left after
quotienting by the constraint.

## Theorem

Let `C` be an algebraically closed constant field of characteristic zero.  Let

```text
T=C<q>
```

be a scalar free differential field, so `q` is differentially transcendental over `C`.  Let
`Phi` be a differential `C`-automorphism of `T` satisfying

```text
Phi(q)=a q,  a in C^*.                                   (1)
```

Define the logarithmic clock current

```text
J=Dq/q.                                                   (2)
```

Then:

1. `J` is nonconstant and differentially transcendental over `C`;
2. `Phi(J)=J`;
3. with `L=C<J>`, one has the exact ordinary-field identity

   ```text
   T=L(q);                                                (3)
   ```

4. `T/L` is the Picard--Vessiot extension of

   ```text
   DY=JY,                                                 (4)
   ```

   and its differential Galois group is the full multiplicative group `G_m(C)` acting by
   `q |-> c q`;
5. the fixed differential field of `Phi` is

   ```text
   Fix(Phi)=L                         if a has infinite multiplicative order,
   Fix(Phi)=C<q^N>=L(q^N)             if a has finite order N.              (5)
   ```

In particular, every charged scalar persistent core contains a nonconstant observable fixed
exactly by the constraint.  The apparent dynamics `q |-> a q` is a gauge motion above a static
hypertranscendental current field.

## Proof

### 1. The logarithmic current is fixed

Since `Phi` commutes with `D` and fixes `a`,

```text
Phi(J)=D(Phi(q))/Phi(q)=D(aq)/(aq)=aDq/(aq)=J.            (6)
```

This identity is Lean-formalized as `logDeriv_fixed_of_eigenvector`.

The current cannot lie in `C`.  If `J=c` were constant, then `q` would satisfy the nonzero linear
differential equation

```text
Dq-cq=0
```

over `C`, contradicting the differential transcendence of `q`.  Thus `J` is nonconstant.  Any
differential-algebraic equation for `J` over `C`, combined with `Dq=Jq`, would make `q`
differentially algebraic over `C` by transitivity.  Hence `J` is itself differentially
transcendental.

### 2. One amplitude reconstructs every jet

Put `L=C<J>`.  Equation (2) gives `Dq=Jq`.  Inductively there are differential polynomials
`B_n` in `J` such that

```text
D^n q=B_n(J,DJ,...,D^(n-1)J) q.                          (7)
```

The recurrence is `B_0=1`, `B_(n+1)=DB_n+JB_n`.  Therefore every jet of `q` lies in `L(q)`, so

```text
C<q> subset L(q).
```

The reverse inclusion is immediate from `J=Dq/q`.  This proves (3).  Thus passing from the static
current field to the full persistent core adds exactly one ordinary transcendental amplitude, not
another infinite jet tower.

### 3. The extension is a full multiplicative torsor

For every `c in C^*`, freeness of `q` defines a differential `L`-automorphism

```text
sigma_c(q)=c q.                                           (8)
```

It fixes `J` and hence all of `L`.  Conversely, if `sigma` is a differential `L`-automorphism,
then both `sigma(q)` and `q` solve (4), so

```text
D(sigma(q)/q)=0.
```

The constants of `T` are `C`, hence `sigma(q)=c q` for one `c in C^*`.  The automorphism group is
therefore exactly `G_m(C)`.  The existence of infinitely many maps (8) also shows directly that
`q` is transcendental over `L`.  Since `T=L(q)` and the constants do not enlarge, `T/L` is the
Picard--Vessiot extension of (4).

### 4. The constraint fixed field is controlled by holonomy

The automorphism `Phi` is the point `a in G_m(C)` of this Galois group.

If `a` has infinite multiplicative order, its cyclic subgroup is Zariski dense in `G_m`.  An
element fixed by `Phi` is fixed by every power of `a`, hence by the Zariski closure and therefore
by the full Picard--Vessiot group.  Its fixed field is `L`.

If `a` has order `N`, the generated subgroup is `mu_N`.  Since `T=L(q)` and `mu_N` acts by scalar
multiplication on the rational coordinate `q`, ordinary cyclic invariant theory gives

```text
T^(mu_N)=L(q^N).                                          (9)
```

Moreover

```text
D(q^N)/(q^N)=N J,
```

so `J` belongs to `C<q^N>` and every derivative of `q^N` belongs to `L(q^N)`.  Hence

```text
L(q^N)=C<q^N>.
```

This proves (5), including `N=1`.

## Constraint-boundary interpretation

The theorem supplies an exact object behind the phrase “infinite algebraic clock capacity
concentrated on a thin constraint boundary.”

```text
static boundary field:       L=C<J>,      Phi|_L=id;
one-dimensional gauge fibre: T=L(q),      Dq=Jq;
constraint holonomy:         q |-> a q.
```

The boundary is not finite-dimensional: `J` is hypertranscendental and `L` contains its entire
free differential jet.  It is thin in a different and precise sense: the full core lies over it by
one ordinary multiplicative coordinate, and the constraint acts only along that coordinate.

Thus hypertranscendence is not “time.”  It is the infinite observable algebra of the fixed current
field; what resembles time is the removable `G_m` gauge motion of the amplitude above it.

## No-go and positive residue

**No-go.**  A charged scalar persistent core cannot have irreducible nonlinear dynamics after
passing to its logarithmic current.  The constraint becomes the identity on a nonconstant
differential subfield.

**Positive theorem.**  The fixed subfield is explicit and large.  For infinite holonomy it is
exactly `C<J>`; for finite holonomy it is the cyclic current cover `C<q^N>`.  The discarded motion
is completely classified by one multiplicative torsor.

## Novelty and significance gate

The novelty comparison is only against external literature.

### Classical parents

- Logarithmic derivatives of eigenvectors and the equation `DY=JY` are standard differential
  algebra.
- The Picard--Vessiot group of a generic rank-one exponential equation is `G_m`.
- Fixed fields of scalar `G_m` and `mu_N` actions on a rational coordinate are classical.
- Bekbaev and the broader differential-invariant literature study fields invariant under scaling
  and changes of derivation.

### Candidate-new delta

Targeted literature searches found no source deriving (1)--(5) from an infinite-depth stable core
of a hypertranscendental constraint.  The candidate-new statement is not the logarithmic-derivative
calculation or Picard--Vessiot theory separately.  It is the forced architecture

```text
charged persistent HT core
    = one G_m torsor over a fixed hypertranscendental current field,
```

together with the complete finite/infinite holonomy fixed-field dichotomy.

This theorem is structurally significant because it identifies the static object hidden inside
every charged scalar tail.  In combination with the clock-character and rational-orbifold
classification theorems, it supports a standalone scalar theory paper.  External specialist and
database review is still required before a publication claim of novelty.

## Relation to the universal HT constraint problem

The scalar result suggests the higher-rank target:

`[CONJECTURE — FIXED-CURRENT REDUCTION]` Every nonconstant persistent core of a clock-neutral
algebraic constraint admits a maximal differential subfield fixed pointwise by the constraint,
and the remaining extension is a Picard--Vessiot torsor under an algebraic group whose character
lattice is generated by homogeneous principal symbols.  For algebraic self-maps, this fixed field
should be the differential function field of the maximal semiabelian/log-Calabi--Yau/automorphic
factor.

The scalar theorem proves this with group `G_m`.  The open higher-rank step is to extract a
finite-dimensional algebraic gauge group from an arbitrary minimal higher-order persistent
observable.

## RH pressure test

There is no RH conclusion.  A proposed common object behind spectral, positivity, continuation,
monodromy, and boundary-condition obstructions would have to produce the same fixed current field
after quotienting any charged scalar realization by its multiplicative amplitude.  Failure of
that fixed-field match would disprove the claimed unification; agreement would identify a concrete
shared invariant.  This is a compatibility criterion only.

## Lean status

The following exact steps are formalized in
`formal/GaloisForLFunctions/HTGeometry/StableCoreFunctoriality.lean`:

```text
map_stableRangeCore_eq_of_commuting_algEquiv
stableRangeCore_symmetry_mem_iff
stableRangeCoreSymmetryAlgEquiv
algHom_preserves_character_of_commuting
logDeriv_fixed_of_eigenvector
logDeriv_unit_character_of_semilinear
```

`formal/GaloisForLFunctions/HTGeometry/ScalarLogCurrentReconstruction.lean` now formalizes the
free differential-field layers that were previously missing:

```text
logDeriv_hypertranscendentalOver
logDeriv_ne_algebraMap
differentialAdjoin_eq_logCurrentOrdinaryExtension
differential_logDeriv_pow
differentialAdjoin_logDeriv_pow_eq
differentialAdjoin_pow_eq_logCurrentOrdinaryExtension
```

Thus Lean proves that `J` is hypertranscendental and nonconstant, proves the exact field identity
`T=L(q)`, and proves the finite-cover identity `C<q^N>=L(q^N)` for every positive `N`.  The new
`differentialAdjoin_logDeriv_pow_eq_of_cast_ne_zero` theorem strengthens the current-field equality
to every characteristic in which the exponent remains nonzero; the positive characteristic-zero
surface is retained as a corollary.  The new
module passed its one exact leaf build, direct file check, and scratch axiom audit with only
`propext`, `Classical.choice`, and `Quot.sound`.

`formal/GaloisForLFunctions/HTGeometry/RatFuncScaleFixedField.lean` now formalizes the complete
ordinary invariant theory used in proof section 4.  It constructs the faithful action
`X |-> uX` on `K(X)`, proves that the action has exactly the order of `u`, and proves unconditionally

```text
Fix(<u>) = K(X^N)   when orderOf(u)=N>0,
Fix(<u>) = K        when orderOf(u)=infinity.
```

The leaf passed its one exact build, direct file check, and axiom audit with only `propext`,
`Classical.choice`, and `Quot.sound`.  The remaining stage-3 work is the differential torsor
transport: prove that `q` is algebraically transcendental over `L=C<J>`, construct the resulting
`L(X) ~= T` equivalence compatibly with the derivation and constraint, and identify the full
Picard--Vessiot automorphism group.  Once that transport exists, the two fixed-field equalities are
provided by the new rational-coordinate theorem rather than being reproved.  No placeholder axiom
is used.

## Gates

- [x] 0 -> 1 in-progress: exact fixed-current statement and falsifier identified
- [x] 1 -> 2 fully-proven: complete algebraic and fixed-field proof
- [x] logarithmic-current hypertranscendence, `T=L(q)`, and `C<q^N>=L(q^N)` formalized
- [x] exact finite- and infinite-order scalar fixed fields on the ordinary rational coordinate
- [ ] 2 -> 3 formalized: construct the exact differential `G_m` torsor transport over `L`
- [ ] 3 -> 4 publication-ready: specialist external novelty review and integration with scalar
  orbifold classification

## Primary literature checked

- E. R. Kolchin, differential algebra and Picard--Vessiot theory.
- M. van der Put, M. Singer, *Galois Theory of Linear Differential Equations*.
- U. Bekbaev, *On the field of differential rational invariants of a subgroup of affine group
  (ordinary differential case)*, 2006.
- R. Jin, R. Moosa, *Internality of logarithmic-differential pullbacks*, 2019.

## Log

- 2026-07-15 -- proved the fixed-current/torsor theorem, completed the preliminary external novelty
  gate, and formalized exact logarithmic-current fixedness in Lean.
- 2026-07-17 -- formalized logarithmic-current hypertranscendence, exact one-amplitude
  reconstruction, and the positive-power finite-cover reconstruction law.
- 2026-07-17 -- formalized the faithful rational-coordinate scalar action and its exact finite- and
  infinite-order fixed fields; differential PV transport from `L(X)` to `T` remains.
