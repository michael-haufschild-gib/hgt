# Symmetric shifts: critical-line entry survives Euler products but crosses the tempered boundary

- **ID:** symmetric-shift-entry-temperedness-boundary
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (Lean) / NO-GO -- scientifically non-new bridge
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
- [x] 1 -> 2: paper proof complete below.
- [x] novelty audit: shifted products/nonunitary twists are standard; scientific verdict is non-new.
- [x] 2 -> 3: all stated functional-equation, divisor-multiplicity, Euler-root, standard-gamma,
  finite-order, infinite-product, partial-Ramanujan, and discontinuity claims formalized in Lean.
- [ ] determine whether the exact source-target slope identity has a significant extension beyond
  translation-generated families.
- [ ] 3 -> 4: publication-ready exposition of the open fully-tempered/fixed-archimedean boundary.

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
- 2026-08-23 -- dependency-closed Lean formalization completed; focused builds and axiom audits
  passed; card promoted to stage 3.

## Lean formalization (2026-08-23)

Formalization is dependency-closed and matches every proved component of the card.

- `SymmetricShiftFunctionalEquation.lean` proves preservation of the Schwarz functional equation,
  exact zero transport, off-critical reflected pairs, and the zero-shift square endpoint.
- `SymmetricShiftMultiplicity.lean` proves the exact analytic-order divisor formula, multiplicity
  lower bounds, equality without accidental overlap, and exact doubling at collision.
- `SymmetricShiftGeneralEulerSlopes.lean` proves the base-slope laws
  `lambda(alpha p^-a)=lambda(alpha)-a` and `lambda(alpha p^a)=lambda(alpha)+a` for every nonzero
  reciprocal root. `SymmetricShiftEulerSlopes.lean` gives the unitary specialization, maximal slope
  `|a|`, and temperedness exactly at `a=0`.
- `SymmetricShiftFiniteEuler.lean` identifies those roots with the actual shifted finite Euler
  factors. `SymmetricShiftFinitePrimeContinuity.lean` proves coefficientwise local convergence and
  convergence of every finite semilocal product at collision.
- `SymmetricShiftDirichletExample.lean` constructs the explicit primitive odd conductor-four
  character example. Its completed carrier is entire and order one; has the actual constant-root
  functional equation with unit-modulus root number; carries standard shifted odd Gamma factors
  with positive parameters `(1±a)/2`; has a literal infinite Dirichlet Euler product; obeys strict
  partial Ramanujan exponent `<1/2`; is fully tempered only at `a=0`; and realizes horizontal
  displacement = largest local slope.
- `SymmetricShiftEulerDiscrepancy.lean`, `SymmetricShiftEulerPrimePowers.lean`, and
  `SymmetricShiftEulerGlobalDiscrepancy.lean` prove the exact nonnegative all-prime/all-prime-power
  discrepancy and summability boundary `sigma>1+a`.
- `SymmetricShiftZetaEulerBridge.lean` identifies that natural-number coefficient series with the
  literal infinite zeta-product ratio
  `zeta(s-a) zeta(s+a) / zeta(s)^2`.
- `SymmetricShiftEulerAbscissaDiscontinuity.lean` proves the literal absolute-convergence abscissa:
  `1+a` for every `a>0`, bottom at `a=0`, and non-continuity of the abscissa map at collision.
- `SymmetricShiftAnalyticClass.lean` proves preservation of entire/order-one analytic class for Xi
  and every nontrivial completed Dirichlet L-function.

All leaves are wired into `formal/GaloisForLFunctions/RHTower.lean`. Each new leaf was checked with
`lake env lean` and exact-target-built with `lake build <leaf-module>`; no umbrella build was run.
Every newly created declaration audits only to Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` foundations. No premise, axiom, `sorry`, finite surrogate, or computational
certificate replaces any theorem stated on this card.
