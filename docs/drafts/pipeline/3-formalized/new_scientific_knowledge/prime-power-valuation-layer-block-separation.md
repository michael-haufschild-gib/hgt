# Prime-power valuation-layer block separation

- **ID:** `prime-power-valuation-layer-block-separation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[NOVELTY UNVERIFIED]`
- **Parent:** `prime-power-dilation-tail-differential-matroid.md`
- **Statement:** Finite prime-power layers with layerwise tail-independent source alphabets form one
  algebraically independent family over the intrinsic finite-prime coefficient field and realize
  as jointly algebraically independent dilated analytic Dirichlet germs; for nonuniform alphabets
  `A_r`, the family has cardinality `sum_r card(A_r)`.

## Theorem

Let `d` be finite.  For each `r : Fin d`, let `A_r` be a finite type and let

```text
a_r : A_r -> Primes -> C
```

be tail-independent: no nonzero finite linear combination of the columns `a_r(alpha)` has finite
prime support.  Define the arithmetic carrier

```text
F_(r,alpha)(p^(r+1)) = a_r(alpha)(p),
F_(r,alpha)(n) = 0 otherwise.
```

Embed these carriers in the fraction field of the Dirichlet-convolution algebra.  Then the family

```text
{F_(r,alpha) : r : Fin d, alpha : A_r}
```

is algebraically independent over the field of fractions detected by only finitely many
prime-coordinate derivations.

Equivalently, every finite collection of tail-independent source columns placed on distinct
prime-power valuation layers contributes its full number of independent coordinates.  The total
rank is therefore

```text
sum_{r : Fin d} card(A_r).
```

If each source column is the coefficient stream of a finite-abscissa prime Dirichlet series, its
layer-`r` carrier is exactly the integral argument dilation of that series.  Consequently the same
dependent-sum family is algebraically independent as actual analytic germs at the complex upper
end.  In particular, nonuniform finite families of Boolean prime orientations, pairwise
real-part-separated shifts, and arbitrary finite derivative cutoffs contribute every displayed
jet coordinate independently.

## Structural law

For globally distinct packet primes `q_i` and layer exponents `e_i`, the coefficient at

```text
N_0 = product_i q_i^(e_i)
```

of the arithmetic Jacobian determinant is exactly the determinant of the scalar matrix obtained
by setting every entry between unequal exponent layers to zero.  Thus the valuation grading
canonically separates the finite dilation layers: the distinguished coefficient is block
diagonal even when the full Jacobian is not.

## Analytic prime-power law

For a prime-supported arithmetic function `f` and `m = r+1`, let `mPart(m,f)` place `f(p)` at
`p^m` and vanish off `m`th powers.  Then, identically as Dirichlet series,

```text
L(mPart(m,f), s) = L(f, m s),
```

with exact equivalence of absolute convergence.  After the upper-end rotation this is literal
precomposition by `z -> m z`.  The complete derivative chain law is

```text
D^k (G(m z)) = m^k (D^k G)(m z)
```

for every finite `k`.  Thus the layer grading is simultaneously a valuation grading on
coefficients and a homogeneous derivative grading on analytic germs.

## Proof

1. A point mass at `m` convolved with a point mass at `n` is the point mass at `mn`.
2. Unique factorization shows that a determinant monomial can contribute at `N_0` exactly when its
   permutation preserves every exponent layer, including the exponent-zero layer corresponding to
   first-prime support.
3. The prime derivation of the carrier supported at `p^(e+1)` is the point mass at `q^e` with mass
   `(e+1)a(q)`.
4. A domain-valued Jacobian with nonzero determinant has trivial kernel; the minimal-polynomial
   Jacobian argument therefore gives algebraic independence.
5. Tail independence supplies a nonsingular packet outside any prescribed finite prime set.
   Recursion over the finite layer set makes the packets globally prime-disjoint.
6. The resulting dependent block-diagonal matrix is a unit because every layer matrix is a unit.
7. For a polynomial over the finite-prime coefficient field, choose the packet outside the finite
   activity set of its coefficients and lift the relation to the packet's common kernel.  The
   packet theorem then contradicts a nonzero relation.
8. Identify the prime-power carrier with the general `m`th-power arithmetic dilation and apply the
   exact L-series reindexing theorem.  Finite abscissa is preserved, and faithful upper-end
   realization transports the arithmetic independence to analytic germs.
9. The logarithmic coefficient derivation commutes with layer dilation with weight `m`; iteration
   gives the exact all-order factor `m^k`.  The existing shifted-jet tail theorem then instantiates
   every nonuniform orientation--shift--derivative layer.

## Formal certificate

- `primePowerPointMassMatrix_det_apply`
- `primeDeriv_arithmeticOfPrimePowerColumn`
- `algebraicIndependent_arithmeticPrimePowerColumns_of_packet`
- `algebraicIndependent_fractionPrimePowerColumns_over_finitePrimeCoefficientField`
- `cofinitePrimePowerPacket_of_layerwise_tailIndependent`
- `algebraicIndependent_primePowerSigmaTower_over_finitePrimeCoefficientField`
- `mPart_arithmeticOfPrimeColumn`
- `LSeries_arithmeticOfPrimePowerColumn`
- `finiteAbscissaRotatedDeriv_iterate_primePowerDilation`
- `upperEndGermDeriv_iterate_primePowerScale_LSeries`
- `algebraicIndependent_primePowerDilatedUpperEndGerms`
- `signedPrimeShiftedJet_primePowerDilatedUpperEndGerms_algebraicIndependent`

The arithmetic capstone is `GaloisForLFunctions.HTGeometry.PrimePowerTailPacket`; the analytic
capstone is `GaloisForLFunctions.HTGeometry.PrimePowerAnalyticDilation`.  Their targeted builds and
direct file checks pass.  The displayed capstone theorems use only `propext`, `Classical.choice`,
and `Quot.sound`.

## Positive RH-facing consequence

Every finite derivative--translation palette of tail-independent prime Dirichlet sources on
finitely many dilation layers contributes its full block of analytic coordinates.  Therefore any
mechanism that reconstructs `log zeta` from the prime source while producing a new finite
algebraic constraint must contain an operation that genuinely couples infinitely many valuation
layers or leaves the derivative--translation category, such as global continuation or reflection.
Finite dilations, finite translations, and finite derivative jets cannot supply that coupling.

This is a constraint on the architecture of a possible route, not a zero-location theorem and not
an RH proof.

## Remaining boundary

The tail-independent analytic theorem is complete.  The broader dilation card still asks for the
rank-deficient classification: when a displayed source alphabet has tail rank below its
cardinality, identify the complete relation ideal and prove the exact rank formula rather than
only the full-rank case.  Countable summation itself remains outside the finite
derivative--translation field; no countable analytic-sum claim is made here.
