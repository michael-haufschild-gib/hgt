# Frankenstein Pluecker covariant inverse incidence

- **ID:** `FR-PCII-1`
- **Stage:** `1-in-progress`
- **Type:** coefficient-faithful cross-route bridge
- **Status:** `[FROZEN] [PAPER-PROVED] [LEAN-PENDING] [NOT RH]`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/FrankensteinPluckerCovariantInverseIncidence.lean`

## Failed predecessor

`FR-PIC-1` correctly places P-G84 mass and P-G91/P-G92 Pluecker factors before the global
sum-before-square operation, but its calibration theorem removes those factors before applying
P-G86 inverse incidence.  Packet-dependent factors cannot be pulled through a cumulative
telescope.  Treating the resulting current as the sought producer would therefore be false.

## Heavy-conjecture loop

1. **Freeze physical reporters and apply ordinary P-G86 telescope. — FAIL.**  P-G84 denominator,
   P-G91 probabilities, and P-G92 reciprocal nodes vary with adjacent-prime index.  Freezing them
   erases literal source coefficients.
2. **Absorb all variation into one scalar remainder. — FAIL.**  Four packet coordinates have two
   retained depth orientations and distinct left/right reporters.  One scalar remainder loses
   orientation data.
3. **Use covariant inverse incidence with an asymmetric reporter pair. — SURVIVES.**  For arbitrary
   `L,R,a : Nat -> Complex` and finite prefix `N`, conjecture the exact identity

   ```text
   sum_(n<N) (n+1)(L_n a_n - R_n a_(n+1))
     = sum_(n<N) L_n a_n
       + sum_(n<N-1) (n+1)(L_(n+1)-L_n)a_(n+1)
       + sum_(n<N) (n+1)(L_n-R_n)a_(n+1)
       - N L_(N-1)a_N.
   ```

   Terms are respectively diagonal source response, moving-reporter connection, left/right
   chirality mismatch, and terminal flux.

4. **Declare connection or mismatch signed. — FAIL.**  Algebra alone gives no sign.  Sign must be
   supplied by an independent source law; assuming it would be producer theatre.

## Paper proof

Insert and subtract `(n+1)L_n a_(n+1)`.  This separates the asymmetric current into

```text
sum_(n<N) (n+1)L_n(a_n-a_(n+1))
  + sum_(n<N) (n+1)(L_n-R_n)a_(n+1).
```

Induction on `N` gives the weighted moving-frame identity

```text
sum_(n<N) (n+1)L_n(a_n-a_(n+1))
  = sum_(n<N) L_n a_n
    + sum_(n<N-1) (n+1)(L_(n+1)-L_n)a_(n+1)
    - N L_(N-1)a_N.
```

Base `N=0` is zero.  At `N+1`, append the new incidence term and the new connection term; all
interior coefficients cancel and the boundary changes from
`-N L_(N-1)a_N` to `-(N+1)L_N a_(N+1)`.  Adding the asymmetric remainder proves the frozen law.

For the literal Pluecker current, expand the pair-dispersion feature in the four signed packet
coordinates.  Coordinate reporter `rho_(e,n,s,t,i)` is the feature evaluated on the `i`th basis
vector after P-G92 node weighting.  Linearity gives exactly

```text
B_(e,n)(a)_(s,t) = sum_(i<4) rho_(e,n,s,t,i) x_(e,n)(a)_i.
```

Multiplying each reporter by P-G84's `sqrt(D_(e,n))` produces two asymmetric pairs:
coordinates `(0,2)` at depth `e` and `(1,3)` at depth `e+1`.  Applying the frozen law to both
pairs yields an exact finite decomposition of the actual `FR-PIC-1` prefix with every prime label,
valuation multiplicity, reciprocal node, Pluecker probability, and reflection orientation intact.

## Novelty and honest boundary

Summation by parts is standard.  Corpus search found related source-specific Abel connections and
Route-U moving-admission connections, but no theorem placing an asymmetric left/right connection
inside the literal P-G84/P-G91/P-G92/P-G86 packet.  Classification is `[BRIDGE]`, not a claim that
the generic finite identity is new.

This theorem will expose, not sign, the exact two missing source channels.  It does not prove their
cancellation, identify a completed Xi target, or prove RH.  Next admissible conjecture must derive
the sign or cancellation of connection plus mismatch from an independent source law.
