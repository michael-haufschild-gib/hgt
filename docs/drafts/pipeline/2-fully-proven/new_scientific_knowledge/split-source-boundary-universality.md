# Split source-boundary universality

- **ID:** `split-source-boundary-universality`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / formalization open
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

## Next conjecture

`[CONJECTURE]` The same theorem holds for commutative algebraic differential groups after replacing
the coordinatewise logarithmic derivative by the algebraic `D`-group logarithmic derivative

```text
ell_D : G(L) -> Lie(G)(L).
```

The source boundary then lives in a simultaneous Lie-algebra coboundary quotient. The kernel of
`ell_D`, a sharp/Manin-kernel-type group, is the canonical character-invisible radical core. This
would extend the proved split boundary corona to the proposed second layer needed for spectral and
positivity realizations.

## Gates

- [x] well-posed arbitrary-family statement
- [x] complete paper proof
- [x] mixed additive/multiplicative case
- [x] exact matroid rank formula
- [x] parent-theory and anti-theatre audit
- [ ] independent specialist novelty audit
- [ ] concrete noncommuting analytic application
- [ ] Lean exact dependence/coboundary equivalence
- [ ] Lean matroid representation

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
