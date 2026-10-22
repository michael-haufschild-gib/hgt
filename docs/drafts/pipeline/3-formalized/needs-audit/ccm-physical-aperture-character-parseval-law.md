# CCM physical aperture character Parseval law

- **ID:** `ccm-physical-aperture-character-parseval-law`
- **Stage:** 3-formalized / needs external novelty audit
- **Type:** UNIVERSAL EXACT TOMOGRAPHY LAW
- **Scientific status:** `[LEAN-FORMALIZED] [CANDIDATE-NEW] [NOT RH]`
- **Source:** physical prime-log aperture fusion and Hilbert metric

## Statement

Let `I_p subset (0,A]` be finitely many clipped intervals, let `w_p` be real weights, and center
the coherent carrier

```text
F=sum_p w_p (1_(I_p)-|I_p|/A * 1_(0,A]).
```

For every nonzero integer `n`, let

```text
c_n=sum_p w_p integral_(I_p) exp(2*pi*i*n*u/A) du.
```

Then, unconditionally,

```text
sum_(n in Z, n!=0) |c_n|^2=A*||F||_2^2.                 (1)
```

The theorem is universal in the interval endpoints and weights.  In the physical prime
specialization `||F||_2^2` is exactly the previously defined coherent aperture fusion energy.
For every disjoint bulk/edge partition, each `c_n` factors into the exact rectangular transfer
function times one twisted prime sum plus the exact edge amplitude, and `(1)` remains an equality.

## Proof architecture

1. Embed every clipped indicator and the aperture indicator in complex `L2(R)`.
2. Identify their Gram matrix with the real physical overlap kernel.
3. Prove centering kills the zero character.
4. Normalize all integer aperture characters and prove orthonormality directly.
5. Match their inner products with mathlib's interval Fourier coefficients of the conjugate
   aggregate carrier.
6. Apply interval Parseval, remove the zero mode, and rewrite the global `L2` norm as the physical
   fusion energy.
7. Substitute the exact bulk rectangular-window factorization character by character.

No estimate, computation, RH premise, or source-sign premise occurs.

## Frontier consequence

Equation `(1)` rules out three false escape routes for the endpoint-energy problem:

- cancellation in an unobserved Hilbert direction;
- recovery from finitely many character channels;
- improvement obtained only by repartitioning bulk and aperture-edge primes.

It does **not** prove the required cofinal energy decay and therefore does not prove RH.  Remaining
work must control the complete arithmetic character family at the critical scale or decide the
independent published-source descent problem.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/CCM/CCMPhysicalPrimeApertureCharacterTomography.lean`.

Principal declarations:

- `orthonormal_xiPhysicalNormalizedApertureCharacters`
- `tsum_normSq_xiPhysicalPrimeLogCharacterAmplitude`
- `tsum_normSq_bulkTwistedSum_eq_energy`
- `tsum_normSq_bulk_add_edge_eq_energy`

Direct validation:

```text
lake env lean GaloisForLFunctions/RHTower/CCM/CCMPhysicalPrimeApertureCharacterTomography.lean
```

passes without warnings.  Final targeted module build and axiom audit remain pending until the
active source-frontier batch is complete.

## Gates

- [x] exact complex Hilbert realization
- [x] all integer characters and orthonormality
- [x] zero-mode removal
- [x] full Parseval equality
- [x] bulk/edge arithmetic factorization
- [ ] external novelty audit
- [ ] decisive arithmetic decay or source-descent theorem
