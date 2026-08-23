# Symmetric shifts: critical-line entry survives Euler products but crosses the tempered boundary

- **ID:** symmetric-shift-entry-temperedness-boundary
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM / NO-GO (paper) -- scientifically non-new bridge
- **Statement:** `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` A symmetric
  real shift of any self-dual completed Euler product preserves the functional equation and the
  Euler product while splitting every critical-line zero into a reflected off-line pair. In the
  Euler factors the same displacement appears exactly as opposite local modulus slopes. Hence
  functional equation, finite order, partial Ramanujan bounds, and infinite Euler data do not by
  themselves prevent entry; the explicit path crosses the fully tempered boundary at exactly the
  collision parameter.

## Goal

Determine which global structure can actually prevent an off-line pair from entering the critical
line. The first task is a no-go theorem: identify familiar structures that demonstrably do not
prevent entry, and isolate the axiom lost by an explicit Euler-product deformation.

## Gates

- [x] 0 -> 1: explicit family, divisor motion, functional equation, and Euler slopes identified.
- [x] paper proof complete below.
- [ ] novelty audit against shifted products, nonunitary twists, complementary series, and
  counterexamples to multiplicity-one without Ramanujan.
- [ ] determine whether the exact source-target slope identity has a significant extension beyond
  translation-generated families.

## General theorem

Let

```text
Lambda(s)=A_infinity(s)L(s)
```

be a completed Euler product satisfying

```text
Lambda(s)=epsilon conjugate(Lambda(1-conjugate(s))),   |epsilon|=1.
```

For real `a`, define

```text
Lambda_a(s)=Lambda(s+a)Lambda(s-a),
L_a(s)=L(s+a)L(s-a).
```

Then:

1. `Lambda_a` satisfies a functional equation about `Re s=1/2` with root number `epsilon^2`.
2. If `rho` is a zero of `Lambda` of multiplicity `m`, then `rho-a` and `rho+a` are zeros of
   `Lambda_a` of multiplicity at least `m`, with equality absent accidental overlap. In particular,
   a zero `rho=1/2+i gamma` splits into the reflected pair

   ```text
   1/2-a+i gamma,   1/2+a+i gamma,
   ```

   and the pair enters the critical line as `a -> 0`, becoming a zero of multiplicity `2m` at
   `a=0`.
3. If the local factor of `L` at `p` has reciprocal roots `alpha_(p,r)`, then the local reciprocal
   roots of `L_a` are

   ```text
   alpha_(p,r)p^(-a),   alpha_(p,r)p^a.
   ```

   Thus their logarithmic modulus slopes are

   ```text
   log|alpha_(p,r)|/log p - a,
   log|alpha_(p,r)|/log p + a.
   ```

   For a tempered base (`|alpha_(p,r)|=1` at unramified primes), the transverse zero displacement
   `|a|` equals the largest absolute local slope. The family is tempered exactly at `a=0`.

## Proof

Apply the functional equation twice:

```text
Lambda_a(s)
= epsilon^2 conjugate(Lambda(1-conjugate(s)-a))
              conjugate(Lambda(1-conjugate(s)+a))
= epsilon^2 conjugate(Lambda_a(1-conjugate(s))).
```

The divisor formula follows directly from translation:

```text
div(Lambda_a)=translate_(-a)(div Lambda)+translate_a(div Lambda).
```

Finally,

```text
L(s+a)=product_p product_r
  (1-alpha_(p,r)p^(-a)p^(-s))^(-1),

L(s-a)=product_p product_r
  (1-alpha_(p,r)p^a p^(-s))^(-1),
```

which proves the local-root and slope identities.

## A genuine standard-gamma Euler-product example

Let `chi` be a real primitive odd Dirichlet character and `Lambda(s,chi)` its completed
Dirichlet `L`-function. For `0<a<1/2`,

```text
Lambda_a(s,chi)=Lambda(s+a,chi)Lambda(s-a,chi)
```

is an entire finite-order completed Euler product. Its two gamma shifts have nonnegative parameters
`(1+a)/2` and `(1-a)/2`; its Euler parameters obey the partial Ramanujan bound with exponent `a<1/2`.
Every critical-line zero of `L(s,chi)` nevertheless splits into an off-line pair and re-enters at
`a=0`. At every unramified prime the local reciprocal-root moduli are exactly `p^(-a)` and `p^a`.

Therefore even the following package does not prevent entry:

```text
functional equation + standard gamma factors + finite order
+ infinite Euler product + a partial Ramanujan exponent theta<1/2.
```

The explicit path fails full temperedness, and it also changes the archimedean parameters.

## Infinite-data discontinuity

For the base zeta Euler factors, compare

```text
L_a(s)=zeta(s+a)zeta(s-a)
```

with `L_0(s)=zeta(s)^2`. Their logarithmic Euler discrepancy is

```text
c_a(p,k)=p^(ak)+p^(-ak)-2.
```

For every `a>0`, its absolute-convergence abscissa is exactly

```text
sigma_E(L_a,L_0)=1+a,
```

although every fixed local factor tends coefficientwise to the base factor as `a->0`. Thus the
entry path is continuous in the finite-prime/product topology but discontinuous in the global Euler
discrepancy topology. Entry is not a finite-prime event: arbitrarily large primes carry the fixed
power-law slope `a`.

## Scientific interpretation

The theorem rules out a universal barrier based only on completed-function symmetry or the bare
existence of an infinite Euler product. In the explicit deformation the target-side displacement
and source-side nonunitarity are the same scalar:

```text
horizontal zero displacement = Euler local modulus slope = |a|.
```

This does not prove that temperedness alone prevents every possible entry. It proves the sharper
and more defensible statement that any general entry obstruction must distinguish fully tempered
Euler data (and/or fixed archimedean data) from partial-Ramanujan Euler products; otherwise the
symmetric-shift family is a counterexample.

## Scientific-novelty verdict and open core

`[NOT NEW SCIENTIFIC KNOWLEDGE]` Symmetric shifted products are standard nonunitary twists, and the
functional-equation, divisor-translation, local-slope, and partial-Ramanujan statements follow by
inspection. The source-target interpretation is useful route triage, but fails the parent-theory
and anti-theatre gates.

- Symmetric shifted products and nonunitary twists are standard constructions.
- The functional-equation calculation and local-slope identity are elementary once the family is
  written down.
- The topological wording does not upgrade the elementary shifted-product calculation to new
  scientific knowledge.
- `[OPEN CORE]` Prove or refute a genuine tempered-entry theorem: in a natural class of fully
  tempered completed Euler products with fixed archimedean data, can a nonconstant deformation move
  a divisor point transversely? A positive theorem here would be significant; the present shifted
  family identifies the precise boundary any such theorem must use.

## Log

- 2026-07-10 -- explicit symmetric-shift family and source-target slope identity proved; novelty
  audit open.

## Lean status update (2026-08-23)

`formal/GaloisForLFunctions/RHTower/SymmetricShiftFunctionalEquation.lean` now
formalizes the exact algebraic functional-equation/divisor-motion seam of the
symmetric-shift construction: a Schwarz line-reflection equation is preserved
with root number `epsilon^2`; every zero produces both shifted zeros; and a
critical-line zero gives a line-reflected pair with real parts `1/2 + a` and
`1/2 - a`. The leaf is wired into `RHTower.lean`, direct-checked with
`lake env lean`, and target-built with
`lake build GaloisForLFunctions.RHTower.SymmetricShiftFunctionalEquation`.
All four newly introduced theorem declarations audit only to Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` foundations.

This closes only the carrier-independent functional-equation and zero-motion
part. It does not yet construct the completed Euler family, prove its local
reciprocal-root slope and partial-Ramanujan boundary, or formalize the global
Euler-discrepancy topology. The card therefore remains at stage 2.

The same leaf now includes the concrete closed specialization
`xi_symmetricShiftProduct_lineReflect`: the symmetric product of the project's
completed `xi` satisfies the line-reflection identity directly from the banked
`xi_one_sub` and `xi_conj` theorems, with no functional-equation premise left
on that specialization. Its axiom audit has the same standard Lean-only result.

The leaf also now proves the exact nonzero-shift entry statement for the
completed `xi`: every critical-line zero yields two zeros of the shifted product,
both off the critical line, at real parts `1/2 ± a`; they are reflection partners.
The two added declarations were target-built and audit only to standard Lean
foundations. This still does not supply the Euler/local-slope and global-topology
parts required for a stage-3 card move.

Finally, the zero-shift endpoint is now exact in Lean:
`symmetricShiftProduct F 0 s = F s^2`, hence its zero set is precisely the
original carrier zero set. This proves the stated re-entry at `a = 0` and the
new endpoint declarations likewise have only standard Lean foundations.

## Lean status update (2026-08-23): local Euler slope boundary

`formal/GaloisForLFunctions/RHTower/SymmetricShiftEulerSlopes.lean` now formalizes the exact local algebra for a unitary reciprocal root at every prime, with primality and unit modulus represented in the data rather than as unproved assumptions.  Its shifted pair has norms `p^(-a)` and `p^a`, logarithmic modulus slopes exactly `-a` and `a`, maximal absolute slope exactly `|a|`, and is locally tempered if and only if `a = 0`.  Thus the source-target equality in the paper, transverse zero displacement = largest local modulus slope = `|a|`, is now a closed Lean theorem when combined with the zero-pair location theorem in `SymmetricShiftFunctionalEquation.lean`.

The leaf is imported by `GaloisForLFunctions/RHTower.lean`, direct-checked with `lake env lean`, and exact-target-built with `lake build GaloisForLFunctions.RHTower.SymmetricShiftEulerSlopes`.  The four new declarations audit only to `[propext, Classical.choice, Quot.sound]`.

This is not yet an actual completed Euler-product realization of the shifted Xi/Dirichlet family, nor the global Euler-discrepancy abscissa proof.  Those remaining analytic constructions still prevent moving the complete card to stage 3.
