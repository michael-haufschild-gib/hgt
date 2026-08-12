# Canonical big-Witt multiplication over arbitrary rings

Status: formalized in Lean 4 (2026-08-13)

## Exact target

For every commutative ring `A`, including rings with nonzero nilpotents, construct a functorial
commutative-ring structure on the literal carrier

```text
Λ(A) = 1 + T A[[T]]
```

whose addition is ordinary multiplication of power series, whose multiplicative unit is `1 - T`,
and whose Teichmüller factors satisfy

```text
(1 - aT) ⊙ (1 - bT) = 1 - abT.
```

No torsion-freeness, reducedness, characteristic, field, or splitting hypothesis may occur in the
Lean theorem.

## Primary sources and novelty boundary

- H. W. Lenstra, *Construction of the Ring of Witt Vectors* (2002), theorem on `Λ(A)` and
  exercises (1)--(3). Lenstra proves existence by truncated splitting extensions and proves
  uniqueness by functoriality/Yoneda continuity.
- J. Cuntz and C. Deninger, *Witt Vector Rings and the Relative de Rham Witt Complex*,
  arXiv:1410.5249v4, Sections 1--2. Their torsion-free-presentation descent proves that ghost
  verification over a free ring descends to every ring.
- L. Hesselholt, *The big de Rham-Witt complex*, Proposition 1.2 and Lemma 1.5, for universal
  functorial ring laws, Frobenius/Verschiebung identities, and the gcd--lcm multiplication law.

The mathematical theorem is classical. New contribution here is first in-corpus unconditional
Lean construction on the literal Deninger power-series carrier; local corpus and current mathlib
contain only p-typical Witt vectors and finite complex ghost mechanics.

## Construction frozen for formalization

Every `f ∈ 1 + TA[[T]]` has unique integral Euler coordinates `(a_m)_{m≥1}`:

```text
f(T) = ∏_{m≥1} (1 - a_m T^m).
```

Existence and uniqueness are triangular and use no division: after factors below degree `m` have
been chosen, `a_m` is the difference between the current degree-`m` coefficient and that of `f`.

For `gcd(m,n)=d` and `lcm(m,n)=ℓ`, define the product of two Euler factors by

```text
(1 - aT^m) ⊙ (1 - bT^n)
  = (1 - a^(ℓ/m) b^(ℓ/n) T^ℓ)^d.
```

The coefficient of degree `N` in the double product uses only pairs with `lcm(m,n) ≤ N`; hence it
is a finite integral expression. This defines `f ⊙ g` over every commutative ring and is visibly
natural under coefficient-ring maps.

## Proof obligations

1. Euler reconstruction and uniqueness on `1 + TA[[T]]`.
2. Logarithmic ghost components
   `γ_k(f) = coeff (k-1) (-f'(T)/f(T))` are additive for ordinary series multiplication.
3. Factor formula:
   `γ_k(1-aT^m) = m a^(k/m)` when `m ∣ k`, and `0` otherwise.
4. Gcd--lcm reindexing gives
   `γ_k(f ⊙ g) = γ_k(f) γ_k(g)` using `gcd(m,n) lcm(m,n)=mn`.
5. Ghost map is injective when the coefficient ring is additively torsion-free, by formal
   differentiation and equality of constant coefficients.
6. Ring laws hold over iterated integer polynomial rings by ghost injectivity.
7. For arbitrary `A`, lift the Euler coordinates of each input to independent variables in a free
   integer polynomial ring, prove the law there, and evaluate variables back into `A`. Naturality
   descends equality. Nilpotents are therefore included without a separate case.
8. Transport operations to `Additive (DeningerBigWittAdditive A)` and prove functoriality,
   multiplicative unit `1-T`, and `[a][b]=[ab]`.
9. Prove Lenstra canonicity without assuming continuity. Package an arbitrary multiplication law
   with functoriality, distributivity, and the Teichmüller rule. Its value on two universal Euler
   vectors has coefficients in a free integer polynomial ring, so each coefficient sees only
   finitely many variables. Kill the remaining variables, inject the finite Euler polynomials into
   an algebraic closure, split them into linear Teichmüller factors, and descend the forced equality
   to every commutative target ring.

## Failure conditions

- Defining multiplication through division by ghost leading coefficients.
- Assuming ghost injectivity on the target ring.
- Transporting a ring structure from a field or reduced quotient.
- Adding an abstract operation as data and restating its axioms.
- Proving only the Teichmüller-factor law without closing all commutative-ring laws.

## Closure

Formal modules:

- `DeningerBigWittEuler.lean`: unique integral Euler coordinates and functorial reconstruction.
- `DeningerBigWittMultiplication.lean`: coefficientwise-complete gcd--lcm pair product.
- `DeningerBigWittGhost.lean`: integral logarithmic ghost, factor formula, pair reindexing,
  completed ghost multiplicativity, and torsion-free ghost injectivity.
- `DeningerBigWittRing.lean`: universal integer-polynomial descent of associativity, identity,
  absorption, and distributivity to arbitrary commutative rings; literal `CommRing`, functorial ring
  maps, Teichmüller multiplication, positive ghost-component ring homomorphisms, injectivity of the
  Teichmüller map, and exact preservation/reflection of every vanishing power and nilpotence.
- `DeningerBigWittCanonicity.lean`: automatic universal-polynomial dependence of every natural
  candidate multiplication coefficient, finite Euler splitting, and the unconditional theorem
  that the type of functorial distributive Teichmüller multiplication laws is a subsingleton.

All target theorems quantify only over `[CommRing A]`. Target ghost injectivity, reducedness,
torsion-freeness, characteristic zero, and field hypotheses are absent. The only torsion-free use is
inside the universal source `MvPolynomial (Fin d × ℕ) ℤ`, before evaluation into `A`.

Nilpotent retention is certified internally, not inferred from prose: for every `a : A` and `n`,

```text
[a]^n = 0  ↔  a^n = 0,
IsNilpotent [a]  ↔  IsNilpotent a.
```

Thus the construction neither reduces the coefficient ring nor silently kills its nilradical.

Canonicity is now certified internally as well. For every candidate law `law`, every commutative
ring `A`, and all `x,y`, Lean proves

```text
law.mul A x y = deningerBigWittMul x y.
```

Equivalently, `DeningerBigWittMultiplicationLaw` is a subsingleton. The proof does not add
T-adic continuity as a premise: `coeff_eq_eval_universalPolynomial` derives finite polynomial
dependence coefficientwise from naturality itself.

Verification: direct foreground Lean checks passed for every module; targeted final build of
`GaloisForLFunctions.RHTower.DeningerBigWittCanonicity` passed, thereby rebuilding the construction
chain through the uniqueness capstone without a full build. The whole-repository formal lint finds
no proof debt or wiring error in these modules, but exits nonzero on unrelated pre-existing
unreachable modules. Axiom audit reports only standard `propext`, `Classical.choice`, and
`Quot.sound` dependencies.
