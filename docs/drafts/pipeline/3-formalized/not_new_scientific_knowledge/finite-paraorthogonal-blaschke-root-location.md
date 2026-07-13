# Finite paraorthogonal Blaschke root location

- **ID:** `finite-paraorthogonal-blaschke-root-location`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE] [POSITIVE SUCCESSOR TO ORDINARY OPUC DISK LOCATION]`
- **Scientific status:** not new scientific knowledge; finite Blaschke/POPUC parent theory
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ParaorthogonalBlaschkeRoot.lean`
- **Parent:** `../../1-in-progress/xi-cayley-paraorthogonal-opuc-rh.md`

## Statement

Let `|a_i|<1`, let `|tau|=1`, and suppose

```text
z product_i (z-a_i)/(1-conj(a_i)z)=tau.                 (1)
```

Lean proves `|z|=1`.  The key exact identity is

```text
|z-a|^2-|1-conj(a)z|^2=(|z|^2-1)(1-|a|^2).             (2)
```

Thus every factor in `(1)` is contractive inside the circle and expansive outside it.  The
unimodular terminal equation can hold only on the boundary.  Lean further proves, for every
nonzero complex polynomial `p` whose roots lie strictly in the disk, that every root of

```text
w p(w) - tau (map_conj p).reverse(w)
```

lies on the unit circle.  Instantiating `p` with `finiteOPUCPolynomial` closes the concrete finite
OPUC interface for every positive-definite Toeplitz section.

## Positive statement from the ordinary-OPUC no-go

The existing finite OPUC polynomials have roots strictly inside the disk, which is the wrong locus
for a Cayley-to-real-root argument.  Formula `(1)` shows the precise positive repair: retain the
disk roots as Blaschke parameters, then impose one unimodular paraorthogonal terminal condition.
The resulting roots lie exactly on the unit circle.

## Lean surface

```text
blaschke_normSq_sub
one_lt_norm_blaschke_of_norm_lt_one_of_one_lt_norm
finiteBlaschke_paraorthogonal_root_norm_eq_one
conjugateReverse_eval_eq_root_product
finiteParaorthogonalPolynomial
finiteParaorthogonalPolynomial_isRoot_norm_eq_one
finiteOPUCParaorthogonalPolynomial_isRoot_norm_eq_one
```

## Gates

- [x] two-sided Blaschke modulus identity formalized
- [x] strict exterior expansion formalized
- [x] finite paraorthogonal unit-circle theorem formalized
- [x] exact conjugate-reversal root product formalized
- [x] generic paraorthogonal polynomial root theorem formalized
- [x] `finiteOPUCPolynomial` and its reversal connected to the unit-circle theorem
