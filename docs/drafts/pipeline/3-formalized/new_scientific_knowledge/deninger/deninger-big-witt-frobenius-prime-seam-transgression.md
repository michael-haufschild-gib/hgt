# Deninger Big-Witt Frobenius prime-seam transgression

- **Status:** Formalized in Lean 4
- **Route:** L
- **Lean:** `RHTower.DeningerBigWittFrobeniusPrimeSeamTransgression`
- **Primary frontier theorem:**
  `deningerBigWittFrobeniusTwo_polarizedAggregate_ghost_one`
- **Cofinal theorem:**
  `tendsto_deningerBigWittFrobeniusTwo_polarizedAggregate_ghost_one_div_mass`

## Result

The prior Route-L source object placed exact physical prime-seam energy in ghost degree two while
the strict Green--Stokes reader acts in degree one. This module constructs the required
degree-changing transport without dividing by `2` and without assuming ghost injectivity.

For the literal series `f(T)` of a canonical big-Witt vector, define

```text
N2(f)_n = coefficient of T^(2n) in f(T) f(-T).
```

The resulting big-Witt operation `F2` exists over every commutative ring, including rings with
nilpotents and additive torsion. Lean proves:

```text
ghost_1(F2(w)) = ghost_2(w),
F2([a]) = [a^2],
W(f)(F2(w)) = F2(W(f)(w))
```

for every base-ring map `f`. These are coefficient proofs on the literal series carrier; no
rationalization or reduced target is used.

For a complex prime potential `a`, ordered primes `(p,q)`, and `d=a_p-a_q`, define the polarized
source

```text
P_pq(a) = C(d/p, conjugate(d)/q),
C(x,y)  = [x] + [y] - [x+y].
```

Then

```text
ghost_1(P_pq(a)) = 0,
ghost_2(P_pq(a)) = -2 |a_p-a_q|^2/(pq).
```

The functional equation acts before norm extraction by literal ordered-pair reversal:

```text
P_pq(a_(1-rho)) = P_qp(a_rho).
```

Hence the finite ordered-pair aggregate `P_S` is FE-invariant. Its physical energy is reversal
even, so a naive orientation-odd cancellation cannot annihilate it. Applying `F2` instead changes
ghost degree:

```text
ghost_1(F2(P_S(a))) = -2 E_W(a,S).
```

On a strip fibre, the normalized transgressed first ghost has exact cofinal residue

```text
re(ghost_1(F2(P_S(a_rho)))) / sum_{p in S} 1/p
  -> -4 * orbitwisePrimeSeamWeightedNormSq(rho).
```

Thus the degree-one object is nontrivial off the critical line and has exactly the singular mass
that a strict Green--BV boundary theorem must remove.

## Conjecture loop

1. **Orientation cancellation conjecture:** FE reflection might make the prime-pair source odd.
   **Failure:** reflection reverses `(p,q)`, but the aggregate and its physical second ghost are
   reversal even. Antisymmetrization kills the source only by also killing the desired energy.
2. **Polarized source conjecture:** retain `d` and `conjugate(d)` before taking the norm.
   **Success:** this gives exact pair reversal and exact physical ghost two.
3. **Ghost-degree transgression conjecture:** the division-free degree-two Witt norm should move
   this physical ghost into degree one.
   **Success:** `ghost_1(F2(w))=ghost_2(w)` over arbitrary rings, yielding the exact first-ghost
   energy and its cofinal residue.

## Novelty boundary

Big-Witt Frobenius, Teichmuller squaring, and ghost-coordinate shifting are classical; no novelty
is claimed for them. Primary references include Hazewinkel, *Witt vectors. Part 1*
<https://arxiv.org/abs/0804.3888>, and Rabinoff, *The Theory of Witt Vectors*
<https://arxiv.org/abs/1409.7445>. Targeted corpus and primary-literature searches found no prior
construction of this polarized Xi prime-seam source, its exact FE ordered-pair reversal, its
coefficientwise physical Dirichlet ghost, or its Frobenius-transgressed cofinal first-ghost
residue. Candidate new knowledge is this source-specific constitutive chain, not classical Witt
infrastructure.

## Frontier effect

Ghost-degree mismatch is no longer Route L's open core. Remaining hard theorem is a strict
source-to-physical chain-map comparison from `F2(P_S)` to the ordinary-integer Gamma/co-Poisson
Green--BV boundary, followed by an unconditional Stokes estimate proving its first ghost is
annihilated or `o(sum 1/p)`. Since its exact residue is `-4 * normSq`, either conclusion forces the
critical line. This module does not assume that boundary membership or estimate.

## Verification

- direct `lake env lean` on leaf: pass
- targeted leaf build: pending final audit
- declaration axiom audit: pending final audit
