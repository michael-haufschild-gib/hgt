# Arithmetic sections preserving conductor multiplication

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md)

## Exact construction

Let `A=⊕_(n≥0) ℤe_n` and let `J` consist of probes supported on
nonsquarefree conductors. Both use integer divisibility alone. Multiplication
of conductors sends `e_n` to `e_(an)` and preserves `J`. The actual quotient is

`A/J ≃ ⊕_(n squarefree) ℤe_n`, `rank_ℤ(A/J)=ℵ₀`.

For `q≥1`, its residue sections at cutoff `N` have cardinality `q^Q(N)`, where
`Q(N)` counts squarefree positive integers through `N`. This is a count of
arbitrary residue labels on the surviving integer conductors.

For the independently defined module, put `C(v)=Σ_n μ(n)v_n`. Then

`J = ⋂_(a≥0) ker(C ∘ T_a)`.

Consequently `J` is the largest conductor-dilation-stable submodule of
`ker C`. This is the smallest quotient of the original free probe module
that retains the charge and every ordinary conductor dilation.

## Integral separation proof

On the squarefree labels through `N`, let `E(a,d)=[d|a]` and let
`U=diag(μ(a))`. The squarefree labels form a divisor down-set. Möbius
inversion on common divisors therefore gives

`[gcd(a,b)=1] = E U Eᵀ`,
`[μ(ab)] = U E U Eᵀ U`.

`E` is triangular with diagonal one and `U²=1`. The multiplication matrix
is thus invertible over `ℤ`. No conductor-dependent denominators occur.
Tests `C_a(v)=Σ_(n≤N) μ(an)v_n`, `a≤N`, recover every squarefree coefficient;
nonsquarefree coefficients enter none of these tests. Applying this at the
finite support bound proves the global kernel identity. If a submodule of
`ker C` is stable under all dilations, every translated charge vanishes on
it, proving maximality. Restriction to squarefree conductors is surjective
by extension by zero, giving the actual quotient equivalence. Its squarefree
conductor basis is countable and contains every prime, so its rank is exactly
`ℵ₀`.

## Original gluing class and signed target

Embed the original gluing column as `b_N=−Σ_(2≤n≤N)e_n`. Its class in `A/J`
retains the charge

`C([b_N])=1−M(N)=Σ_p index_p(N)`.

Its conductor translates retain the exact sums `−Σ_(2≤n≤N) μ(an)`.
The comparison uses the original divisor normal and singular local indices.
The full residue count `q^Q(N)` gives no cancellation bound for this signed
functional.

## Obstruction and positive replacement

The single-charge quotient cannot carry ordinary prime dilation:
`C(e₁+e_p)=0`, but `C(T_p(e₁+e_p))=−1`. Thus the fixed-conductor Gaussian
height does not automatically become a height on conductor correspondences.

The positive replacement is the complete independent quotient above, with
its explicit integral coordinates and multiplicative action. For every
prime `p`, that action satisfies `T_p≠0` and `T_p²=0`. Hence the only real
function satisfying `H(0)=0` and `H(T_p x)=p H(x)` everywhere is zero:
applying the scaling law twice gives `0=p²H(x)`.

This rules out a nonzero height with that similitude law on this exact
replacement. It does not rule out a different geometric correspondence
operator or an enlarged arithmetic object. Additive class dilation in the
existing Tate construction and multiplication of conductors are different
operations. No `√N` cancellation or independent gluing-height upper bound
has been proved.

## Lean declarations

- `HeckeChargeSeparation.lean`: `squarefreeHeckeMatrix_isUnit`,
  `conductorDilatedCharge_vanish_iff`.
- `HeckeArithmeticSections.lean`: `arithmeticSectionCharge_all_vanish_iff`,
  `arithmeticSectionRelations_eq_iInf`, `arithmeticSectionQuotientEquiv`,
  `arithmeticSectionRelations_isGreatest`, `arithmeticSectionHecke_comp`,
  `arithmeticSectionHecke_prime_square`, `arithmeticSectionHecke_prime_ne_zero`,
  `arithmeticSectionCharge_no_prime_factor`, `squarefreeResidueSections_card`,
  `arithmeticSectionHecke_height_classification`.
- `HeckeGluingComparison.lean`: `arithmeticSectionBasis`,
  `arithmeticSectionQuotient_rank`, `arithmeticGluingSection_localIndices`,
  `arithmeticGluingSection_hecke_charge`.

All three modules pass direct `lake --old env lean` checks. Their 21 transitive
axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
