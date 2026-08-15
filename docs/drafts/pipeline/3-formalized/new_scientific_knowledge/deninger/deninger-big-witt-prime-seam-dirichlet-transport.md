# Deninger Big-Witt prime-seam Dirichlet transport

- **Status:** Formalized in Lean 4
- **Route:** L
- **Lean:** `RHTower.DeningerBigWittPrimeSeamDirichletTransport`
- **Primary capstone:** `DAC_DENINGER_BIG_WITT_PRIME_SEAM_DIRICHLET_TRANSPORT`

## Result

For distinct ordinary primes `(p,q)`, the canonical first-ghost-null Big-Witt codiagonal has
literal quadratic atom

```text
w(p,q) = 1/(p q).
```

For a prime potential `a` and finite prime window `S`, define its source energy by summing those
atoms against squared pair differences (the diagonal may be included because its difference is
zero):

```text
E_W(a,S) = sum_{p,q in S} w(p,q) |a_p-a_q|^2.
```

Lean proves the exact identity

```text
E_W(a,S) = primePairDifferenceEnergy(a,S)
```

with no comparison constant or normalization. Consequently `E_W` is uniformly bounded over all
finite windows exactly when `a` is constant. On the actual Xi seam, uniform boundedness on every
divisor fibre is equivalent to the Riemann hypothesis. This is an unconditional equivalence, not
a proof of its bounded side.

The same module proves the completion obstruction. If the physical atom were coordinate energy
of a packet Hilbert vector, its amplitude would have modulus `1/sqrt(pq)`. Restriction to the
injective slice `(p,2)` shows its squared norm contains one half of the divergent prime harmonic
series. Hence no such `ell^2` vector exists. In contrast, the raw Big-Witt coefficient `1/(pq)`
is square summable because its Hilbert energy is `1/(p^2q^2)`.

## Paper proof

1. Cast the Big-Witt atom from `Q` to `R`; functoriality of rational casts gives
   `w(p,q)=p^{-1}q^{-1}`.
2. Expand the nested source sum. Commutativity gives
   `p^{-1}q^{-1}|a_p-a_q|^2 = (|a_p-a_q|^2/q)/p`, exactly the physical seam summand.
3. Invoke the proved reciprocal-prime Dirichlet rigidity: bounded finite-window energy forces all
   prime potentials equal; constants give zero energy.
4. Apply that classification to the canonical FE--Schwarz Xi seam and its already proved
   critical-line coherence criterion.
5. For Hilbert non-admission, inject the prime set into ordered pairs by `p -> (p,2)`, replacing
   the exceptional `p=2` by `(2,3)`. Summability on all pairs would imply summability of
   `(1/2)(1/p)` outside one index, contradicting Euler's prime harmonic divergence.

## Conjecture loop and novelty boundary

Two candidate shortcuts failed before this theorem was selected.

- Pair-orientation cancellation fails: ordered Calderon--Witt witnesses are linearly independent,
  and corpus already retains their resolved antidiagonal before codiagonal loss.
- A physical Hilbert half-density fails by the divergence theorem above.

Generic Big-Witt codiagonals and prime-harmonic divergence are classical. Connes--Consani's
semi-local trace formula also explains the critical half-density in the explicit-formula
framework. Targeted corpus and primary-literature searches found no prior theorem identifying the
canonical reciprocal-prime Big-Witt quadratic atoms, coefficient for coefficient, with the Xi
prime-seam Dirichlet form. Candidate new knowledge is this exact constitutive weld and the
resulting topology classification; no novelty is claimed for its individual ingredients.

Primary context:

- Cuntz--Deninger, *Witt Vector Rings and the Relative de Rham Witt Complex*,
  <https://arxiv.org/abs/1410.5249>.
- Rabinoff, *The Theory of Witt Vectors*, <https://arxiv.org/abs/1409.7445>.
- Connes--Consani, *The Scaling Hamiltonian*, <https://arxiv.org/abs/1910.14368>.
- Deninger, *The Hilbert--Polya strategy and height pairings*,
  <https://arxiv.org/abs/1001.1621>.

## Frontier effect

Physical coefficient provenance is no longer missing. Route L now has a canonical source-derived
cofinal Dirichlet form whose boundedness is the exact RH gate. Remaining theorem must obtain a
uniform upper bound or strict target-boundary annihilation from completed Green/BV source
geometry. A bounded Hilbert lift using the raw `1/(pq)` horizon cannot do this because it replaces
physical energy `1/(pq)` by its square.

## Verification

- direct `lake env lean` on leaf: pass
- targeted leaf build: pass
- declaration axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
