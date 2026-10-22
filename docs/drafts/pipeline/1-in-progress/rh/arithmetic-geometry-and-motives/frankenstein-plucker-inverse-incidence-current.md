# Frankenstein Pluecker inverse-incidence current

- **ID:** `FR-PIC-1`
- **Stage:** `1-in-progress`
- **Type:** cross-route coefficient-faithful source operator
- **Status:** `[BRIDGE] [PAPER-PROVED] [LEAN EXACT-BUILT] [UMBRELLA-WIRED] [NOT RH]`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/FrankensteinPluckerInverseIncidenceCurrent.lean`

## Frozen conjecture

P-G91's positive four-label covariance cannot be summed as independent adjacent blocks: that
retains P-G85 locality. P-G86's cumulative primitive cannot be formed first as one scalar and then
inserted into one covariance: that erases prime labels. The coefficient-faithful order is instead

```text
physical covariance factor -> signed adjacent incidence -> cumulative sum -> squared norm.
```

For packet `(e,n)`, let `p_n,p_(n+1)` be consecutive primes, `D_(e,n)>0` P-G84's literal raw
Fisher denominator, `pi_(e,n)` P-G91's six-minor probability, and

```text
x_(e,n)(a) = (a_(p_n,e), a_(p_n,e+1), -a_(p_(n+1),e), -a_(p_(n+1),e+1)).
```

For selected-pair indices `s,t`, define the canonical pair-dispersion factor

```text
B_(e,n)(a)_(s,t)
  = sqrt(pi_s pi_t / 2)
      ((selected_s R_(e,n)x_(e,n)(a)) - (selected_t R_(e,n)x_(e,n)(a))),
```

where `R_(e,n)` is P-G92's literal diagonal of square roots of squared reciprocal-gap nodes.

The source current and energy are

```text
T_e(a) = sum_n (n+1) sqrt(D_(e,n)) B_(e,n)(a),
E(a)   = sum_e sum_(s,t) |T_e(a)_(s,t)|^2.
```

## Hostile attack and pivots

1. **Route-T/Hodge attempt failed.** Infinite Cesaro extraction was already formal; the remaining
   radial sourcing equality is RH-equivalent.
2. **First-information Schur attempt failed.** Existing Lean proves its depleted carrier still has
   mass above the completed seam.
3. **Aggregate-then-covary attempt failed.** Summing P-G86 left/right orientations before applying
   P-G91 loses packet labels.
4. **Covary-then-direct-sum attempt failed.** Squaring each packet independently remains adjacent
   local and cannot create P-G86's nonadjacent cross terms.

The frozen current is the unique surviving order among these four: every prime/depth coefficient
enters before summation, while the norm is taken only after summation, so cross-packet terms are
present.

## Paper proof

For normalized nonnegative `pi`, the pair-dispersion identity gives, for every real four-vector
`x`,

```text
sum_(s,t) |sqrt(pi_s pi_t / 2) (selected_s x-selected_t x)|^2
  = Cov_pi(selected x, selected x).
```

Thus `B_(e,n)` is a canonical rectangular square root of the exact P-G91 covariance after P-G92's
reciprocal-gap congruence; no spectral basis or sign choice is introduced.

P-G84 gives `sum_(e,n) D_(e,n)<infinity`, hence each `sqrt(D_(e,n))` is bounded by the square root
of total denominator mass. P-G86's first Koethe estimate gives

```text
sum_n (n+1)|a_(p_n,e)| < infinity
```

and the same estimate for the shifted prime and depth coordinates. Every component of `B` is a
bounded linear combination of those four coordinates because `0<=pi_s<=1`. Therefore the
two-index family of current terms is absolutely summable. Tonelli then gives absolute convergence
of every `T_e` and `sum_e |T_e|`; the latter implies square summability and finiteness of `E`.
Every summand in `E` is nonnegative.

## Novelty audit

Graph-incidence pseudoinverses and covariance square roots are standard. Corpus/external search
found no theorem combining literal Gamma-sewn Pluecker probabilities, P-G84 raw packet masses,
P-G86 ordered-prime inverse incidence, valuation multiplicity, and the sum-before-square order.
Classification: `[BRIDGE]`, not a claimed new general covariance theorem.

## Honest boundary

`FR-PIC-1` constructs the previously missing coefficient-faithful nonlocal source current. Lean
also proves both signed orientations recover P-G86's exact complete all-prime layer sums before
physical weighting. It does
not identify its energy or resolvent with completed prime--archimedean moments, prove a signed
anti-Herglotz landing, force vanishing, or prove RH. Those are subsequent falsifiable gates.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/FrankensteinPluckerInverseIncidenceCurrent.lean
lake build GaloisForLFunctions.RHTower.FrankensteinPluckerInverseIncidenceCurrent
scripts/formal_tools.py lint
```

All pass. Capstone declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
