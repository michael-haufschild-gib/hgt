# Deninger big-Witt Frobenius ring endomorphism

- **Status:** Formalized in Lean 4
- **Route:** L
- **Lean:** `RHTower.DeningerBigWittFrobeniusRingEndomorphism`
- **Bundled theorem:** `deningerBigWittFrobeniusTwoRingHom`
- **Canonical ghost law:** `deningerBigWittFrobeniusTwoRingHom_ghost`
- **Naturality:** `deningerBigWittFrobeniusTwoRingHom_natural`
- **Nilpotent law:** `deningerBigWittFrobeniusTwo_teichmuller_pow_eq_zero_iff`

## Result

The literal division-free norm

```text
f(T) |-> coefficient contraction of f(T) f(-T)
```

is now proved to define a natural ring endomorphism `F_2` of the canonical
big-Witt ring over every commutative base ring. No reducedness,
torsion-freeness, characteristic-zero, or ghost-injectivity premise occurs in
the final statements. In particular, rings with nilpotents and additive
torsion are retained.

For every positive integer `k`, Lean proves the full canonical ghost law

```text
ghost_k(F_2(w)) = ghost_(2k)(w).
```

The earlier prime-seam module had proved only the `k=1` instance directly.
The new theorem identifies the constructed norm operation as the actual
big-Witt Frobenius, not merely an operation with the correct first physical
coefficient.

The bundled endomorphism is natural under every ring homomorphism and squares
Teichmüller representatives. Nilpotent retention is explicit:

```text
(F_2([a]))^n = 0  <->  a^(2n) = 0.
```

## Proof mechanism

1. Over an additively torsion-free ring, `f(T)f(-T)` is invariant under
   `T |-> -T`; torsion-freeness forces its odd coefficients to vanish.
2. Its even-coefficient contraction therefore expands back to the literal
   norm series.
3. Formal logarithmic differentiation under rescaling and expansion yields
   `ghost_k(F_2(w))=ghost_(2k)(w)` in every degree.
4. Ghost injectivity proves zero, one, addition, and multiplication only in
   the universal polynomial ring over `Z`.
5. Simultaneous universal Euler-coordinate evaluation descends those laws and
   the full ghost shift to arbitrary target rings, including nilpotent rings.

Target ghost injectivity is never used.

## Literature and novelty boundary

Big-Witt Frobenius and the ghost shift are classical; this card does not claim
their mathematical discovery. The literature audit used Hazewinkel's
*Witt vectors. Part 1* (`arXiv:0804.3888`) and Rabinoff's *The Theory of Witt
Vectors* (`arXiv:1409.7445`) as primary references for the classical target.

Project-new contribution is dependency-closed Lean realization on this
literal `1+TA[[T]]` carrier over arbitrary rings, connected to the exact
prime-seam norm source and with nilpotent survival stated explicitly. Corpus
search found no prior all-degree or RingHom theorem for the constructed `F_2`.

## Frontier effect

This closes an algebraic ambiguity in Route L. Multiplicative or iterated
source arguments may now use a canonical natural RingHom and every shifted
ghost degree; they no longer rely on the isolated first-ghost identity.

It does not solve the analytic open core. No ring law forces the normalized
Calkin energy to vanish. Remaining frontier is still a source-derived
cross-pair singular Stokes comparison producing the required cofinal submass
estimate.

## Verification

- direct `lake env lean` on leaf: pass
- exact leaf-only `lake build`: pass; umbrella not built
- declaration axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- forbidden-declaration scan: pass
