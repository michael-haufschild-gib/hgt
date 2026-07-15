# Prime-power valuation-layer block separation

- **ID:** `prime-power-valuation-layer-block-separation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[NOVELTY UNVERIFIED]`
- **Parent:** `prime-power-dilation-tail-differential-matroid.md`
- **Statement:** Finite prime-power layers with layerwise tail-independent source alphabets form one
  algebraically independent family over the intrinsic finite-prime coefficient field; for
  nonuniform alphabets `A_r`, the family has cardinality `sum_r card(A_r)`.

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

## Structural law

For globally distinct packet primes `q_i` and layer exponents `e_i`, the coefficient at

```text
N_0 = product_i q_i^(e_i)
```

of the arithmetic Jacobian determinant is exactly the determinant of the scalar matrix obtained
by setting every entry between unequal exponent layers to zero.  Thus the valuation grading
canonically separates the finite dilation layers: the distinguished coefficient is block
diagonal even when the full Jacobian is not.

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

## Formal certificate

- `primePowerPointMassMatrix_det_apply`
- `primeDeriv_arithmeticOfPrimePowerColumn`
- `algebraicIndependent_arithmeticPrimePowerColumns_of_packet`
- `algebraicIndependent_fractionPrimePowerColumns_over_finitePrimeCoefficientField`
- `cofinitePrimePowerPacket_of_layerwise_tailIndependent`
- `algebraicIndependent_primePowerSigmaTower_over_finitePrimeCoefficientField`

The capstone module is
`GaloisForLFunctions.HTGeometry.PrimePowerTailPacket`.  Its targeted build and direct file check
pass.  The displayed capstone theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Positive RH-facing consequence

Whenever a finite derivative--translation palette of prime Dirichlet sources is represented by
tail-independent coefficient columns on finitely many dilation layers, every layer must contribute
its full block of algebraic coordinates.  Therefore any mechanism that reconstructs `log zeta`
from the prime source while producing a new finite algebraic constraint must introduce an
operation that genuinely couples valuation layers; it cannot arise from finite layerwise
Dirichlet-convolution algebra alone.

This is a constraint on the architecture of a possible route, not a zero-location theorem and not
an RH proof.

## Remaining boundary

The theorem is arithmetic-algebraic.  Promotion of the broader dilation card requires the exact
analytic transfer to `P_b((r+1)s+a)`, verification of tail independence for the desired shifted
jet palettes, and the complete relation ideal in the rank-deficient case.  Countable reconstruction
is only a finite-character corollary after that transfer; countable summation is not an operation of
the finite derivative--translation field.
