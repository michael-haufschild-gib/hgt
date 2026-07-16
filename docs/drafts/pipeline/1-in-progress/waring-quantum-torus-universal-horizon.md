# Before There Was Time: Waring quantum tori and universal maximal horizons

- **ID:** `waring-quantum-torus-universal-horizon`
- **Stage:** 1-in-progress
- **Type:** THEOREM / HYPERTRANSCENDENCE / QUANTUM TORUS / WARING DECOMPOSITION
- **Scientific status:** `[PAPER PROOF COMPLETE SUBJECT TO LINE-BY-LINE CHECK] [PRINCIPAL SYMBOL LEAN-PROVEN] [UNIVERSAL EXISTENCE LEAN-PENDING] [NOVELTY UNVERIFIED]`
- **Depends on:** `generalized-clifford-ulrich-hypertranscendence-horizons`

## 1. Main theorem

Let `K` be an algebraically closed field of characteristic zero, let `V` be finite-dimensional,
let `d>=2`, and let `F` be a degree-`d` homogeneous form on `V` whose projective zero locus is
smooth.  Then there exist a finite-dimensional vector space `M` and a linear pencil

```text
A : V -> End_K(M)
```

such that

```text
A(c)^d = F(c) I_M                                                     (1)
```

and the exterior commutator symbol

```text
B_A : exterior^2 V -> End_K(M),   u wedge v |-> [A(u),A(v)]           (2)
```

is injective.

The Lean-proven shift-suspension and principal-symbol kernel theorems then give one rational
differential field, one root observable, and one linear law space whose complete ordinary
differential-dependence horizon is exactly `Z(F)` and whose exterior law-commutator map is
injective.

Thus every smooth projective hypersurface over `K` is realized by a finite-width exact
hypertranscendence horizon retaining every pairwise incompatibility channel.

## 2. Waring-to-quantum-torus construction

Pure powers span the vector space of degree-`d` forms in characteristic zero.  Algebraic closure
absorbs scalar coefficients into `d`th roots, so choose a finite Waring decomposition

```text
F(c) = ell_1(c)^d + ... + ell_R(c)^d.                                 (3)
```

Let `q` be a primitive `d`th root of unity.  In the finite quantum torus `Q_(R,d)`, choose
generators `g_1,...,g_R` satisfying

```text
g_i^d = 1,
g_i g_j = q g_j g_i  for i<j.                                       (4)
```

The ordered monomials with exponents in `{0,...,d-1}` form a basis, so `Q_(R,d)` has dimension
`d^R`.  Its left regular representation on `M=Q_(R,d)` is faithful.  Define

```text
A(c) = sum_i ell_i(c) g_i.                                           (5)
```

The quantum binomial theorem at a primitive `d`th root gives `(X+Y)^d=X^d+Y^d` whenever
`XY=qYX`.  Induction on `R` is legal because `sum_(i<R) ell_i(c)g_i` q-commutes with the last
summand.  Equations `(3)`--`(5)` therefore prove `(1)`.

## 3. Maximal commutator rank

Let

```text
L : V -> K^R,   L(c)=(ell_1(c),...,ell_R(c)).                         (6)
```

If the `ell_i` did not span `V*`, some nonzero `v` would satisfy `ell_i(v)=0` for every `i`.
Then `(3)` gives `F(v)=0`; because `d>=2`, every first derivative of every `ell_i^d` also vanishes
at `v`.  Hence `[v]` would be a singular point of `Z(F)`.  Smoothness therefore makes `L`
injective.

Expanding the bracket in `(5)` gives

```text
[A(u),A(v)]
  = (q-1) sum_(i<j)
      (ell_i(u)ell_j(v)-ell_i(v)ell_j(u)) g_j g_i.                   (7)
```

The elements `g_j g_i` for `i<j` are nonzero scalar multiples of distinct ordered basis
monomials, hence are linearly independent.  Since `q!=1` and `exterior^2 L` is injective,
equation `(7)` proves that `B_A` is injective.

This proof also works for every **concise** form, meaning that its first derivatives have no
common annihilated direction.  Smoothness is a geometric sufficient condition, not the algebraic
minimum.

## 4. What is known and what may be new

Known parent theory:

- Waring decompositions of forms over algebraically closed characteristic-zero fields;
- finite generalized-Clifford linearizations of arbitrary polynomials;
- the 1992--1994 sum construction using pairwise root-of-unity-commuting matrices;
- finite quantum tori, their ordered monomial bases, and regular representations;
- generalized Clifford algebras in finite quantum mechanics, higher-order wave operators, and
  fractional supersymmetry.

The 1994 Fleury--Rausch de Traubenberg construction already proves general finite matrix
linearizability, so equation `(1)` alone is `[SEARCH]`, not new knowledge.  The exact residue under
audit is the spanning-Waring argument plus `(7)`: one can choose a general polynomial
linearization whose entire canonical bivector map is injective, and the faithful
principal-symbol lift makes this exactly the maximal commutator rank of an ordinary
hypertranscendence horizon.

No located source states this maximal-bivector theorem, its concise-form criterion, or its exact
hypertranscendence-horizon consequence.  This remains an absence-of-hit result until experts in
generalized Clifford linearization and Ulrich bundles check equivalent formulations.

## 5. Consequences for Ulrich matter

The pencil `(5)` is a finite-dimensional representation of the Roby generalized Clifford algebra
`C_F`.  Under the Clifford/Ulrich correspondence it supplies an Ulrich bundle on the cyclic cover
`w^d=F` whose Clifford commutator symbol is injective.  Therefore the previously conjectural
finite-world blind bivector space satisfies

```text
I_2(F)=0                                                             (8)
```

for every smooth `F` in the stated setting.  More strongly, one representation already separates
all bivectors; no family or limiting argument is needed.

This construction gives the explicit bound

```text
nu_HT(F) <= d^R                                                     (9)
```

for any spanning Waring decomposition of length `R`.  Minimizing the quantum-torus representation
and minimizing Waring rank are now concrete problems rather than existence questions.

## 6. Physical meaning and its limit

The scalar form `F` fixes the common classical horizon.  The Waring decomposition embeds its law
space into a finite phase-space packet; the quantum-torus cocycle turns every oriented two-plane
of laws into a nonzero commutator channel.  Shift suspension creates unbounded differential depth
from this finite transverse packet without introducing an evolution parameter.  In this precise
sense, the incompatibility algebra exists before any choice of time flow.

This is not yet a physical theory.  The construction is algebraic and generally non-self-adjoint.
The positive-Hilbert obstruction shows why: a smooth real horizon with a real point cannot arise
from a finite pencil of self-adjoint symbols.  A physical promotion requires a Lorentzian/Krein,
graded, or non-Hermitian axiom and a field-theoretic locality principle.

## 7. Anti-theatre gates

The theorem is not promoted until:

1. the Waring spanning lemma is written without hiding the concise/smooth implication;
2. the finite quantum torus and ordered-monomial independence are constructed, not assumed;
3. the root-of-unity quantum multinomial theorem is proved for all `d>=2`;
4. equation `(7)` is checked with a fixed commutation convention;
5. all four parts are formalized unconditionally in Lean;
6. theorem-level searches cover the 1967--1998 generalized-Clifford linearization literature;
7. an expert checks that maximal bivector rank is not implicit in an existing universal
   linearizing-algebra theorem.

## 8. RH impact

The theorem is deliberately nonselective: every smooth form receives a maximally noncommutative
exact horizon.  Therefore mere existence of such a realization cannot distinguish the Xi horizon
and cannot imply RH.  The RH-relevant datum must be a **distinguished** arithmetic representation,
its star/positivity structure, or a source-selected bound on `nu_HT`; this theorem removes generic
existence as a plausible RH bottleneck.

## 9. Lean route

1. **Completed:** finish and axiom-audit the general principal-symbol kernel theorem.
2. **Principal-symbol half completed:** an abstract finite `q`-commuting family with linearly
   independent ordered quadratic monomials has an explicit exterior decoder; injective linear
   coefficient families preserve maximal rank; shift suspension preserves it exactly.  The
   all-degree root-of-unity quantum multinomial theorem remains.
3. **Completed for the principal-symbol surface:** construct an explicit finite cyclic phase-space
   representation, prove exact ordered `q`-commutation, prove its ordered quadratic monomials
   linearly independent, and instantiate maximal commutator rank.  The all-degree ordered-monomial
   basis is no longer needed for rank, but the generator power identity remains necessary for the
   scalar horizon.
4. Prove equation `(7)` and injectivity from a spanning linear family.
5. Formalize pure-power spanning and coefficient absorption over an algebraically closed field.
6. Prove smoothness implies the Waring linear family spans.
7. Instantiate the exact horizon and maximal commutator-rank theorem.

The completed theorem surfaces are in
`GaloisForLFunctions.HTGeometry.QuantumTorusPrincipalSymbol` and
`GaloisForLFunctions.HTGeometry.FiniteQuantumTorusRepresentation`.  They isolate the remaining
burden sharply: universal existence now requires the Waring packet and the all-degree power
identity; no representation-existence or commutator-rank assumption remains hidden.
