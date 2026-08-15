# Deninger big-Witt Frobenius cross-pair coherent compensator

- **Status:** Formalized in Lean 4
- **Route:** L
- **Lean:** `RHTower.DeningerBigWittFrobeniusCrossPairCoherentCompensator`
- **All-cross kernel theorem:**
  `deningerBigWittFrobeniusTwo_crossPairAll_ghost_one`
- **Source decomposition:**
  `deningerBigWittFrobeniusTwo_crossPair_source_decomposition`
- **Physical comparison:**
  `deningerBigWittFrobeniusTwo_crossPairDiagonal_ghost_one_eq_original`
- **Cancellation theorem:**
  `deningerBigWittFrobeniusTwo_crossPair_cancellation_ghost_one`

## Construction

For an ordered prime seam `(p,q)`, split the physical quadratic atom into two
linear oriented legs

```text
L_pq(a) = (1/p)(1/q)(a_p-a_q),
R_pq(a) = conjugate(a_p-a_q).
```

Both are antisymmetric under pair reversal. Therefore, on every finite prime
set `S`, their complete ordered-edge sums vanish exactly:

```text
sum_(p,q in S) L_pq = 0,
sum_(p,q in S) R_pq = 0.
```

Their product retains the exact physical atom:

```text
L_pq R_pq = |a_p-a_q|^2/(pq).
```

Define the all-cross Big-Witt source by polarizing every left edge `(p,q)`
against every right edge `(r,t)`. Its diagonal part is the sum with
`(p,q)=(r,t)`; its off-diagonal complement is formed before Frobenius or
scalar readout.

## Exact theorem

Bilinearity of the second ghost and the two coherent-leg vanishing laws give

```text
ghost_2(AllCross_S) = 0,
ghost_2(Diagonal_S) = -2 E_S(a),
ghost_2(OffDiagonal_S) = +2 E_S(a).
```

Canonical Frobenius two transports these to first ghost and preserves the
source decomposition:

```text
F_2(Diagonal_S) + F_2(OffDiagonal_S) = F_2(AllCross_S),
ghost_1(F_2(AllCross_S)) = 0.
```

Hence the off-diagonal cross-pair compensator cancels the full physical
diagonal coefficient exactly. The diagonal first ghost is proved equal to
the original polarized prime-seam aggregate, so this is not a replacement of
the physical coefficient by a weaker proxy.

For the Xi seam, `E_S` is also the exact finite sum of squared essential norms
of the actual Sonin--Euler Calkin corners.

## Conjecture loop

1. **Multiplicative coupling:** Witt powers might generate cross-pair
   cancellation. **Failure:** every level only powers the positive Calkin
   residue.
2. **Pre-Hermitian coherent-leg coupling:** factor each physical atom into two
   antisymmetric oriented legs and polarize before diagonal extraction.
   **Success:** complete all-cross source has zero physical ghost and its
   off-diagonal complement is exactly the negative of the physical diagonal.
3. **Immediate RH conclusion:** exact algebraic cancellation might itself
   imply submass. **Failure:** fixed physical reader sees the diagonal, not the
   off-diagonal compensator. A source-derived singular transport comparing
   those two sectors is still required.

## Novelty boundary

Finite antisymmetric double-sum cancellation and bilinear polarization are
elementary separately. Targeted searches across Deninger Big-Witt,
all-cross-prime incidence/Koszul, pair-variance/Plücker, and failed-route
corpora found no prior construction joining them into this exact
coefficient-faithful Big-Witt/Calkin compensator.

Candidate new knowledge is the source architecture and exact identity: the
full physical Calkin energy is the diagonal of a zero-coherent all-cross
Frobenius source, with an explicit off-diagonal source carrying precisely the
opposite coefficient.

## Frontier effect

Route L now has a concrete cross-pair object rather than an unspecified
nonlocal completion. Remaining theorem is narrower: transport the explicit
off-diagonal compensator through actual Gamma/co-Poisson/Calderón incidence
and prove its fixed ground readout is cyclically invisible or cofinally
submass while preserving the all-cross source identity. The missing step is
no longer discovery of cross-pair cancellation itself.

## Verification

- direct `lake env lean` on leaf: pass
- exact leaf-only `lake build`: pass; umbrella not built
- declaration axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- no computation, RH-equivalent premise, or new axiom occurs
