# Bounded formation--recovery rigidity law

- **ID:** ULF-TAFM-30
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every response factoring through bounded formation and bounded recovery is
  sequentially closable; hence no such factorization realizes a nonzero constant codiagonal.

## Higher-law interpretation

The anomaly is an interaction extension, not a scalar stored in either marginal. It can be hidden
by moving unbounded scale between formation and recovery, as the `(n+1)` graph gauge does, but it
cannot pass through a completion whose ingress and egress are both bounded. Thus admissibility is
not ordinary properness; it is two-sided transport of the source interaction through one topology.
Responses differing by a bounded completed-source term have the same closability status, so the
gauge-invariant datum is the response class modulo bounded coboundaries.

## Corpus audit

Corpus search before stating the theorem found:

1. `constantCodiagonal_closable_iff`: base `ell^2` closability forces coefficient zero.
2. `formationGraphTopologyFracture`: unbounded `(n+1)` loading plus bounded inverse-grade recovery
   realizes every coefficient.
3. `finiteDerivativeReporterConditionalInformation_boundedRecovery_sandwich`: exact bounded
   recovery controls information in both directions.
4. `SuzukiCausalDepthGammaCommonDomainRobinTraceNoGo`: fixed-domain bounded ingress/egress cannot
   repair cofinal trace escape.
5. No existing theorem excluded constant codiagonal recovery through an arbitrary bounded
   intermediate formation space.

## Theorem

Let `D` be a real linear source core, `j : D -> E` its map into a normed source realization, and
`T : D -> K` an algebraic response. For arbitrary normed space `F`, if continuous linear maps

`L : E -> F`,  `R : F -> K`

satisfy `R(L(j(x))) = T(x)` for every `x in D`, then `T` is sequentially closable relative to
`j`.

Moreover, for every continuous linear `B : E -> K`,

`T + B o j` is sequentially closable relative to `j` iff `T` is.

Specialize to `D = c00(N; C)`, `E = ell^2(N; C)`, canonical embedding `j`, and

`C_c(x) = sum_n c x_n`.

For any complex normed space `E`, continuous linear maps

`L : ell^2(N; C) -> E`,  `R : E -> C`

cannot satisfy

`R(L(j(x))) = C_c(x)` for every `x in D`

unless `c = 0`.

## Proof [PROVED HERE]

The composite `R o L : E -> K` is continuous. Hence for every sequence `x_k in D` with
`j(x_k) -> 0`, continuity gives `R(L(j(x_k))) -> 0`. Under exact factorization this is
`T(x_k) -> 0`; uniqueness of limits proves sequential closability.

For bounded-coboundary invariance, `j(x_k) -> 0` implies `B(j(x_k)) -> 0`. Thus a convergent
response sequence for `T` becomes one for `T + B o j` with the same limit, and conversely by
subtracting `B o j`. Applying closability in either direction proves the equivalence.

In the codiagonal specialization this gives

`R(L(j(x_k))) -> 0`.

Under the displayed recovery identity this is `C_c(x_k) -> 0`. Therefore `C_c` is sequentially
closable relative to `j`: if also `C_c(x_k) -> y`, uniqueness of limits gives `y = 0`.
The certified constant-codiagonal dichotomy says this closability holds exactly when `c = 0`.

Equivalently, if `c != 0`, the normalized finite packets supplied by the codiagonal no-go satisfy
`j(x_k) -> 0` but `C_c(x_k) -> 1`; no bounded composite can agree with that response.

## Consequences

1. Every corpus failure of `IsSequentiallyClosableBetween` forbids factorization through any
   common bounded formation/recovery completion, independent of route vocabulary.
2. Bounded completion corrections are coboundaries: they cannot create or remove a nonclosable
   response class.
3. The formation-graph rescue in ULF-TAFM-29 necessarily uses an unbounded load on base `ell^2`.
4. This remains true for every intermediate normed space, not only a weighted `ell^2` model.
5. Any information-neutral completion with bounded formation and bounded recovery annihilates the
   constant cofinal anomaly.
6. The theorem predicts the fixed-domain Suzuki no-go: bounded ingress and egress cannot absorb a
   cofinally divergent defect; a survivor must move domain or use an unbounded channel.

## Exact RH closure and open source obligation

The theorem does not prove RH by itself. Corpus fusion already identifies the same horizontal
coefficient in Gamma-six, Mobius, Green, Hellinger, shell-Ward, and recurrence organs. To close RH,
one must now construct from the pre-divisor Xi source—not from a selected zero—one common normed
completion `E` and bounded maps `L,R` satisfying the codiagonal recovery identity. The theorem then
forces the horizontal coefficient to zero; existing global stratification turns that statement
into RH.

This narrows the source-model class: any proposed completion using unbounded ingress, unbounded
egress, or different topologies for formation and recovery is not information-neutral and cannot
serve as the selector.

## Gates

- [x] 0 -> 1: source-independent hostile theorem isolated by corpus search
- [x] 1 -> 2: dependency-closed proof above
- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.BoundedFormationRecoveryRigidity`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only
- [ ] 3 -> 4: publication-ready synthesis


## Lean certificate

Module `GaloisForLFunctions.HTGeometry.BoundedFormationRecoveryRigidity` (5 constants, axiom audit clean).

| Claim | Lean declaration |
|-|-|
| bounded factorization `R∘L∘j = T` ⇒ `T` sequentially closable | `isSequentiallyClosableBetween_of_bounded_factorization` |
| closability invariant under bounded corrections `T + B∘j` | `isSequentiallyClosableBetween_add_boundedFactor_iff` |
| `ℓ²` codiagonal specialization: bounded `L`, `R` recover `C_c` only if `c = 0` | `boundedFormationRecovery_constantCodiagonal_eq_zero` |
| premise-free conjunction | `boundedFormationRecoveryRigidityLaw` |

## Log

- 2026-09-01 — theorem proved; exact pre-divisor bounded-formation obligation isolated.
- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
