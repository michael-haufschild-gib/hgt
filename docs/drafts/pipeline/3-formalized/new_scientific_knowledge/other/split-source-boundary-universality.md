# Split source-boundary universality

- **ID:** `split-source-boundary-universality`
- **Stage:** 3-formalized / complete theorem surface Lean-proved / final integration gate pending
- **Type:** THEOREM (paper) / Lean formalization complete
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** For observables valued in any split commutative group
  `G_a^r x G_m^s` and governed by an arbitrary, possibly noncommuting family of compatible
  differential-field automorphisms, the complete differential-algebraic matroid is represented by
  one simultaneous linear source-boundary quotient. Mixed nonlinear additive/multiplicative
  circuits do not exist beyond finite differential-character coboundaries.

## Setup

Let `C -> K -> L` be a tower of ordinary differential fields of characteristic zero, with `C` a
differential constant field. Let

```text
tau_i   : K ~= K,
sigma_i : L ~= L                         (i in I)
```

be compatible differential-field automorphisms. Assume that every `sigma_i` fixes `C` and that
the common fixed field in `L` is exactly `C`. No composition law or pairwise commutativity is
imposed.

Let additive observables `u_a in L`, multiplicative observables `x_b in L^*`, and source
increments

```text
p_(i,a) in K,
q_(i,b) in K^*
```

satisfy

```text
sigma_i(u_a) = u_a + p_(i,a),
sigma_i(x_b) = q_(i,b) x_b.              (1)
```

Define the linearized observable and increment families

```text
z_a       = u_a,
z_b       = D(x_b)/x_b,
omega_i,a = p_(i,a),
omega_i,b = D(q_(i,b))/q_(i,b).          (2)
```

Then every source action is additive:

```text
sigma_i(z_c) = z_c + omega_i,c.          (3)
```

Define

```text
Q_Sigma(K) = K^I / {(tau_i(k)-k)_i : k in K},
V_Sigma(K) = Q_Sigma(K) tensor_(C[D]) C(D).               (4)
```

## Main theorem

For every finite mixed set `S` of additive and multiplicative observable labels,

```text
dtrdeg_K K<u_a, x_b : a,b in S>_D
  = dim_(C(D)) span{[omega_c] : c in S} in V_Sigma(K).    (5)
```

Equivalently, the mixed family is differentially algebraically dependent if and only if there are
operators

```text
P_c(D) in C[D], not all zero,
```

and one `k in K` such that for every source direction `i`,

```text
tau_i(k)-k = sum_(c in S) P_c(D) omega_i,c.               (6)
```

Thus every nonlinear mixed differential circuit is exactly one finite differential character
whose entire source increment family is the simultaneous coboundary of a single base element.

The index sets of source directions and observables may be infinite. Every dependence certificate
is finite because a differential polynomial and the operator family in (6) have finite support.

## Proof

For a finite mixed set `S`, let

```text
E = K<u_a, x_b : a,b in S>_D,
F = K<u_a, D(x_b)/x_b : a,b in S>_D.                     (7)
```

Then `F subset E`. Conversely, every `x_b` satisfies

```text
D(Y) - (D(x_b)/x_b)Y = 0                                 (8)
```

over `F`. Hence `E/F` is differentially algebraic and

```text
dtrdeg_K E = dtrdeg_K F.                                 (9)
```

Equation (3) makes every coordinate of the linearized family `z` an additive primitive for the
same arbitrary automorphism family. The noncommutative automorphism-family Ostrowski theorem
therefore gives:

```text
z|S is differentially dependent
iff
there exist nonzero finite c_(c,n) in C and k in K with
tau_i(k)-k = sum_(c,n) c_(c,n) D^n(omega_i,c) for all i. (10)
```

The forward implication is the full-jet additive theorem. For the reverse implication, the
element

```text
sum_(c,n) c_(c,n) D^n(z_c)-k
```

is fixed by every `sigma_i`, hence lies in `C` and gives a nonzero differential relation.

Combining (9) and (10) proves the dependence criterion (6). Applying the criterion to every
subfamily identifies its differential-algebraic independent sets with the linearly independent
sets of the corresponding classes in `V_Sigma(K)`. Equality of the rank functions gives (5).
`QED`

## Scientific content

1. The theorem is mixed. It proves that an additive primitive and a multiplicative primitive
   cannot support a hidden nonlinear differential circuit that escapes every source character.
2. It is a complete matroid theorem, not a criterion for one function: every finite mixed
   differential transcendence degree is the rank of one explicit boundary quotient.
3. The source family is arbitrary and may be infinite or noncommuting. The conclusion uses one
   base primitive simultaneously in every direction.
4. Parameterized Picard--Vessiot simplicity, differential closure of constants, and a commuting
   operator lattice are not required.
5. The theorem gives the first proved nontrivial model of the conjecture that infinite algebraic
   clock capacity is concentrated on a thin constraint boundary: the entire nonlinear matroid is
   carried by finite differential characters in (4).

## Novelty gate

Classical Kolchin--Ostrowski theory classifies mixed antiderivative/exponential dependence for one
derivation. Hardouin--Singer give single-difference-operator additive and multiplicative
differential-dependence criteria. Karr--Schneider product/sum extensions use one distinguished
difference operator. Parameterized difference Galois theory and the located multi-operator
literature impose a distinguished operator or structured commuting operators.

No checked source states (5) or (6) for an arbitrary, possibly noncommuting family of semilinear
automorphisms, with one simultaneous base primitive and a complete mixed differential-matroid
representation. The new claim is not logarithmic differentiation or the classical mixed
Kolchin--Ostrowski mechanism. It is arbitrary-source exactness and the representation of every
mixed nonlinear circuit by one source-boundary module.

This is affirmative evidence, not proof of absence from the literature. Independent specialist,
MathSciNet, and Zentralblatt review remain required.

## Anti-theatre gate

- `[PASS]` Exact theorem, exact proof, and exact falsifier.
- `[PASS]` Nonlinear-to-linear classification of the complete mixed differential matroid.
- `[PASS]` Strictly stronger than the pure additive and pure multiplicative parents.
- `[PASS, PROVISIONAL]` Exact arbitrary-family parent not located.
- `[OPEN]` Independent specialist novelty audit.
- `[OPEN]` Concrete analytic system whose essential source directions genuinely fail to commute.
- `[FAIL if oversold]` The theorem applies to split commutative source primitives; it is not yet a
  theorem for arbitrary hypertranscendental functions or an RH result.

## Strong no-go and positive successor

`[NO-GO]` A topology of finite jets is not the complete invariant even in this favorable class:
the dependence data are changed by simultaneous base coboundaries that finite jet topology does
not canonically quotient.

`[POSITIVE THEOREM]` After quotienting source increments by simultaneous coboundaries and
localizing the differential-character action, the resulting ordinary vector-space configuration
is complete: it recovers every mixed differential-algebraic independent set and every rank.

## Proved successor and new horizon

`[PROVED HERE]` The same theorem holds for every finite-dimensional commutative algebraic
`D`-group after replacing the coordinatewise logarithmic derivative by the algebraic `D`-group
logarithmic derivative

```text
ell_D : G(L) -> Lie(G)(L).
```

The source boundary then lives in a simultaneous Lie-algebra coboundary quotient.  Contrary to the
initial conjecture, the kernel of `ell_D` is not a hidden HT radical: it is defined by a first-order
differential equation and has zero differential transcendence degree over the base.  The complete
theorem and resulting linearization-horizon dichotomy are recorded in
`commutative-d-group-source-boundary-universality`.

`[CONJECTURE]` The first genuinely nonlinear boundary begins with noncommutative adjoint twisting
or a pro-algebraic source envelope.  Its invariant should be a localized twisted source-cohomology
object together with the Tannakian tensor relations of its adjoint local system.

## Gates

- [x] well-posed arbitrary-family statement
- [x] complete paper proof
- [x] mixed additive/multiplicative case
- [x] exact matroid rank formula
- [x] parent-theory and anti-theatre audit
- [ ] independent specialist novelty audit
- [ ] concrete noncommuting analytic application
- [x] Lean exact dependence/coboundary equivalence for one multiplicative observable
- [x] Lean exact dependence/coboundary equivalence for the complete mixed linearized family
- [x] Lean factorization of joint differential independence through the generated differential
  field
- [x] Lean finite differential-algebraic base-extension invariance
- [x] Lean raw/logarithmic finite-family rank preservation
- [x] Lean exact dependence/coboundary equivalence for the raw mixed family
- [x] Lean exact arbitrary-family algebraic matroid criterion
- [x] Lean mixed-family matroid representation
- [x] Stage-3 umbrella reachability and capstone axiom audit

## Lean formalization boundary

`formal/GaloisForLFunctions/HTGeometry/SourceLogarithmicBoundary.lean` now proves the exact
arbitrary-family additive Ostrowski equivalence and applies it to the combined family

```text
(u_a, D(x_b)/x_b).
```

The theorem
`automorphismFamily_mixedLinearized_differentialIndependent_iff` is the exact Lean form of `(10)`:
the full mixed linearized family is differentially independent if and only if every nonzero finite
differential character of the combined increments fails to be one simultaneous base coboundary.
The source family remains arbitrary and need not commute.

The same module proves the full finite replacement bridge.  The tower theorem
`differentialIndependent_sumElim_iff` factors joint independence through the differential field
generated by the left block.  The finite transitivity theorem
`differentialAlgebraicOver_differentialAdjoin_fin_succ_iff` proves that adjoining a finite
differentially algebraic family does not change differential algebraicity of a further element.
From these, `coordinatewiseMutuallyDifferentialAlgebraic_fin_succ_iff` identifies the independent
sets of coordinatewise mutually differential-algebraic finite families.

Specializing the replacement theorem to `x_b` and `D(x_b)/x_b` gives
`differentialIndependent_deriv_div_self_fin_succ_iff`, and the mixed version preserves joint
independence with an arbitrary additive block.  The capstone theorem
`automorphismFamily_mixedRaw_differentialIndependent_iff` is therefore the exact raw-family form
of `(6)`: the family `(u_a, x_b)` is differentially independent exactly when every nonzero finite
differential character of the linearized increments fails to be a simultaneous base coboundary.
All these theorems use only Lean's standard axioms.

The same module now isolates the common finite-resolution engine as
`automorphismFamily_algebraicIndependent_iff_no_constant_simultaneous_telescoping`.  It proves for
an arbitrary selected packet that algebraic independence is exactly absence of a nonzero
constant-coefficient simultaneous coboundary.  Both the logarithmic-jet boundary matroid and the
complete differential Ostrowski equivalence are specializations of this one theorem, rather than
duplicated fixed-field arguments.

`formal/GaloisForLFunctions/HTGeometry/LocalizedQuotientMatroid.lean` constructs a generic
localized quotient configuration and proves that its represented matroid has finite-packet rank
equal to the fraction-field dimension of the localized quotient-class span.
`SourceBoundaryQuotientMatroid.lean` instantiates this construction for the simultaneous
coboundary map over `C[D]`.  Its theorem `sourceBoundaryQuotientMatroid_indep_iff` is the exact
operator-character form of `(6)`, while `sourceBoundaryQuotientMatroid_eRk_finset` is the generic
finite-packet rank formula.

Finally, `SplitSourceBoundaryMatroid.lean` identifies the complete raw mixed differential matroid
with that source-boundary quotient through
`automorphismFamily_mixedRaw_differentialFamilyMatroid_eq_sourceBoundaryQuotientMatroid`.  The
capstone `automorphismFamily_mixedRaw_differentialFamilyMatroid_eRk_finset` is exactly `(5)` for
every finite mixed packet.  The owning target, `HTGeometry` umbrella, and a scratch `#print axioms`
audit pass using only `propext`, `Classical.choice`, and `Quot.sound`.  No theorem assumes the
quotient representation or rank equality as input.  The Stage-3 formalization certificate is
`../split-source-boundary-universality.md`.

## References checked

- E. R. Kolchin, *Algebraic groups and algebraic dependence*, 1968.
- C. Hardouin and M. F. Singer, *Differential Galois Theory of Linear Difference Equations*,
  Math. Ann. 342 (2008), 333--377.
- C. Hardouin, *Hypertranscendance des systemes aux differences diagonaux*, Compos. Math. 144
  (2008), 565--581.
- C. Schneider, *Parameterized Telescoping Proves Algebraic Independence of Sums*, 2008.
- E. Ocansey and C. Schneider, *Representing (q-)hypergeometric products and mixed versions in
  difference rings*, 2017.

## Log

- 2026-07-15 -- Paper proof completed from logarithmic linearization plus the arbitrary-family
  additive Ostrowski theorem.
- 2026-07-16 -- Lean completed the exact mixed linearized dependence/coboundary equivalence for
  arbitrary source families. The raw/logarithmic finite-family rank bridge remains the sole
  formal obstruction to the complete matroid statement and stage-3 promotion.
- 2026-07-17 -- Lean consolidated the finite-resolution source-boundary argument into the exact
  arbitrary-family algebraic Ostrowski equivalence; logarithmic-jet and differential-family
  criteria now specialize this common matroid theorem. The localized quotient rank representation
  remains open.
- 2026-08-01 -- closed the localized quotient representation, exact raw-family matroid equality,
  finite-packet rank law, serialized umbrella verification, and Stage-3 certificate.
