# Deninger Big-Witt Frobenius Calkin-energy bridge

- **Status:** Formalized in Lean 4
- **Route:** L
- **Lean:** `RHTower.DeningerBigWittFrobeniusCalkinEnergyBridge`
- **Primary pair theorem:**
  `deningerBigWittFrobeniusPrimeSeamPairCoefficient_eq_calkin`
- **Primary aggregate theorem:**
  `deningerBigWittFrobeniusTwo_polarizedAggregate_ghost_one_eq_calkin`
- **Cofinal theorem:**
  `tendsto_deningerBigWittPrimeSeamFiniteCalkinEnergy_div_mass`

## Result

For an ordered prime pair `(p,q)` and strip fibre `rho`, let `T_pq(rho)` be
the actual seam-weighted Sonin--Euler Calkin corner at canonical aperture one.
Its essential norm is already known exactly:

```text
essentialNorm(T_pq(rho))
  = |a_p(rho)-a_q(rho)| / sqrt(pq).
```

This module squares that operator-quotient identity and proves that it is
exactly the reciprocal-prime Dirichlet atom carried by the Big-Witt source:

```text
E_pq^Calkin(rho)
  = essentialNorm(T_pq(rho))^2
  = |a_p(rho)-a_q(rho)|^2/(pq).
```

Consequently the Frobenius-transgressed pair coefficient satisfies

```text
ghost_1(F_2(P_pq(rho))) = -2 E_pq^Calkin(rho).
```

For every finite prime set `S`, summing the actual squared essential norms
gives a nonnegative Calkin energy `E_S^Calkin`. Lean proves

```text
E_S^Calkin(rho) = E_W(a_rho,S),
ghost_1(F_2(P_S(rho))) = -2 E_S^Calkin(rho).
```

The normalized cofinal energy has exact residue

```text
E_S^Calkin(rho) / sum_{p in S} 1/p
  -> 2 * orbitwisePrimeSeamWeightedNormSq(rho).
```

No compactness, trace-class, RH-equivalent, or source-annihilation premise is
used.

## Conjecture loop

1. **Trace-repair conjecture:** local cyclic readers might shrink the physical
   residue. **Failure:** the pairwise cyclic-correction no-go proves they
   retain the full residue.
2. **Operator-quotient carrier conjecture:** the reciprocal-prime physical
   coefficient should be squared Calkin distance of the genuine prime-seam
   Euler corner. **Success:** equality is exact pairwise, finitely, and in the
   cofinal residue.
3. **Immediate compactness conjecture:** landing in Calkin energy might imply
   it vanishes. **Failure:** existing Calkin faithfulness proves the opposite;
   off-line charge produces positive essential norm. A new source relation is
   still required.

## Novelty boundary

Exact essential norms of the seam-weighted corners and the Big-Witt physical
Dirichlet source existed separately. Candidate new knowledge is their exact
Frobenius bridge: Big-Witt first ghost is negative twice a canonical sum of
squared essential norms. Targeted corpus search found no prior theorem
identifying these carriers.

## Frontier effect

Route L no longer needs to guess a nonlocal completion space for the strict
Stokes comparison. The physical source already has a canonical positive
operator-quotient energy. Remaining theorem is now precise: construct a
source-derived nonlocal transgression proving this finite Calkin energy is
submass, or equivalently that its normalized squared essential-norm packet
tends to zero. Existing local/pairwise compactness criteria merely classify
that statement as RH; they do not produce it.

## Verification

- direct `lake env lean` on leaf: pass
- targeted leaf build: pass
- declaration axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- forbidden-declaration scan and `git diff --check`: pass
