# Ritt transfer boundary: algebraicity of the base map is load-bearing

- **ID:** ritt-algebraicity-load-bearing
- **Stage:** 0-backlog
- **Type:** GATEKEEPER THEOREM
- **Source:** Haiku after Turing id=1772; Ritt / Di Vizio--Fernandes source check
- **Priority:** HIGH for the Feigenbaum HT lane

## Statement

Ritt's theorem for Poincare/Schroeder functions cannot be extended by replacing the rational/algebraic base map
with an arbitrary differentially algebraic analytic germ.

More precisely: there exist non-algebraic differentially algebraic attracting local germs `h` with nonzero
multiplier whose Koenigs coordinate is itself differentially algebraic. Therefore any Feigenbaum proof by
Ritt transfer must use the polynomial-like finite-type/global structure, not merely the local functional equation

```text
F(h(z)) = mu F(z)
```

and not merely differential algebraicity of the base germ.

## Promptability audit

No computation is involved. The fork is structural:

- Weak extension: "Ritt remains true for DA analytic base germs."
- Finite-base extension: "Ritt may extend to polynomial-like finite-degree maps with a suitable intrinsic
  difference-Galois setup."

The theorem below kills only the weak extension. It does not kill the polynomial-like target.

## Theorem `[PROVED HERE]`

Fix `mu in C*` with `0 < |mu| < 1` and `mu^2 != 1`. Work as local analytic germs at `0`.
Let

```text
F(z) = tan(z),
h(z) = arctan(mu tan(z)),
```

where `arctan` is the local inverse branch at `0`. Then:

1. `h(0)=0` and `h'(0)=mu`, so `0` is a non-superattracting attracting fixed point when `|mu|<1`;
2. `F(h(z)) = mu F(z)`, so `F` is a Koenigs coordinate for `h`;
3. both `F` and `h` are differentially algebraic over `C(z)`;
4. `h` is not algebraic over `C(z)`.

Thus a non-algebraic DA base germ can have a DA Koenigs coordinate.

## Proof

The fixed point and multiplier are immediate from `tan(0)=0`, `tan'(0)=1`, and `arctan'(0)=1`.
The Koenigs equation follows by construction:

```text
tan(arctan(mu tan z)) = mu tan z.
```

The function `F=tan z` is DA because

```text
F' = 1 + F^2.
```

The local branch `arctan z` is DA because it satisfies the first-order differential equation

```text
y' = 1/(1+z^2).
```

DA germs are closed under composition, hence `h=arctan(mu tan z)` is DA.

It remains to show `h` is not algebraic. Its derivative is the meromorphic function

```text
h'(z) = mu (1 + tan(z)^2) / (1 + mu^2 tan(z)^2).
```

Since `mu != 0`, the equation `1 + mu^2 tan(z)^2 = 0` has infinitely many solutions modulo the period
`pi` of `tan`. At these points `h'` has poles. If the germ `h` were algebraic over `C(z)`, then its derivative
would also be algebraic over `C(z)`. An algebraic meromorphic germ over `C(z)` has only finitely many
singularities in the finite plane, so it cannot have a continuation with infinitely many poles. Contradiction.
Therefore `h` is not algebraic. ∎

## Consequence for Ritt transfer

Di Vizio--Fernandes prove a Galoisian form of Ritt's theorem for a rational base map `R in C(x)` and a partial
extension for an algebraic base map `R` in the relative algebraic closure of `C(x)` inside `C((x))`. In both
cases, the finite algebraic base is load-bearing:

- the substitution endomorphism `Phi_R: f -> f(R(x))` preserves a finite algebraic function field;
- the constants of that difference field are controlled;
- differential algebraicity of the linearizer collapses to a first-order Ritt-type equation.

The `tan/arctan` model shows that this architecture cannot be relaxed to "the base germ is DA." In that wider
category the conclusion is false.

For Feigenbaum, this means:

1. Ritt's rational/algebraic theorem supplies the correct baseline: non-exceptional polynomial Poincare
   functions are HT.
2. The live Feigenbaum target is a genuine polynomial-like transfer problem, not a DA-germ transfer problem.
3. A proof must use global finite-degree/polynomial-like data or a scaling-compatible straightening mechanism.
   A proof using only local DA functional-equation data is ruled out by this countermodel.

## Novelty and significance

The example is elementary once the right normal form is named, so it is not deep. Its significance is diagnostic:
it prevents a false transfer of Ritt from algebraic dynamics to DA local dynamics and pinpoints the exact
structure that a Feigenbaum proof must still exploit.

Grade: BRIDGE / gatekeeper for the Feigenbaum HT lane, not a final goal-level theorem.

## Source boundary

Primary source for the positive theorem being bounded:

- Di Vizio--Fernandes, *A Galoisian proof of Ritt theorem on the differential transcendence of Poincare
  functions*, arXiv:2102.08268. The paper states Ritt's theorem for rational `R`, proves the Galoisian
  reduction to a first-order Ritt-type equation, and gives a partial algebraic-base extension.

This card's countermodel is not found in that source; it is a local-germ boundary example built from elementary
DA functions.

## Gates

- [x] 0 -> 1 in-progress: theorem stated with proof and Feigenbaum consequence.
- [ ] 1 -> 2 fully-proven: team audit of proof and significance.
- [ ] 2 -> 3 formalized: optional; can be reduced to DA closure plus a finite-singularity lemma for algebraic
  functions.
- [ ] 3 -> 4 publication-ready: include only as a short warning in a Feigenbaum/Ritt transfer note.

## Log

- 2026-06-24 - Created by Haiku after Turing id=1772 identified Ritt/Di Vizio--Fernandes as the correct
  polynomial Poincare anchor. The card kills the overbroad DA-germ extension and leaves the polynomial-like
  extension as the live target.

## Source-risk note

Targeted searches for `"arctan(mu tan" Koenigs linearizer differentially algebraic`, `"arctan" "mu tan" "Schroder"`, and `"tan" "Koenigs" "differentially algebraic"` did not find this countermodel in the Ritt/Poincare-function setting. Results were unrelated uses of tangent/arctangent or general DA material. This is weak negative evidence only; the example is elementary and should be treated as a boundary check, not as proof of broad novelty.
