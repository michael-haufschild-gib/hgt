# Xi prime-seam pair energy is a rank-one weighted variance

- **ID:** `xi-prime-seam-pair-variance`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[FORMALIZATION]`, `[VALUE RELATION]`, `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiPrimeSeamPairVariance.lean`
- **Parent:** `xi-prime-seam-pair-energy-rh.md`
- **Reused theorem:**
  `XiCTaylorThetaTailSquareIndexPolarization.two_mul_weightedBilinear_eq_rankOne_add_pairwiseDispersion`

## Statement

For a finite prime set `F` and a prime-indexed complex potential `a`, put

```text
M_F = sum_(p in F) 1/p,
S_F = sum_(p in F) |a_p|^2/p,
A_F = sum_(p in F) a_p/p.
```

The ordered reciprocal-prime pair energy satisfies the exact identity

```text
E_F(a) = sum_(p,q in F) |a_p-a_q|^2/(p q)
       = 2 M_F S_F - 2 |A_F|^2.                            (1)
```

Consequently,

```text
|A_F|^2 <= M_F S_F.                                       (2)
```

Both statements are formalized for arbitrary complex prime potentials.  Equation `(1)` is also
specialized to the canonical FE--Schwarz Xi seam

```text
a_p(rho)=log(p)(p^(-conj(rho))-p^(-(1-rho))).              (3)
```

## Proof

Write `a_p=x_p+i y_p`.  The finite real weighted bilinear variance identity, already formalized
for the theta-tail square-index polarization, gives

```text
sum_(p,q) (x_p-x_q)^2/(p q)
  = 2 M_F sum_p x_p^2/p - 2 (sum_p x_p/p)^2,
```

and the identical formula for `y`.  Adding the two identities and using
`|a_p-a_q|^2=(x_p-x_q)^2+(y_p-y_q)^2` proves `(1)`.  Nonnegativity of `E_F` gives `(2)`.

## Top-down simplification

The arithmetic content of the two-particle Sonin obstruction is a one-particle covariance defect,
not an irreducible double-prime interaction.  For the canonical seam and any open-strip `rho`,
the elementary majorants

```text
|a_p(rho)| <= log(p)(p^(-Re rho)+p^(-(1-Re rho)))
```

show on paper that `sum_p |a_p(rho)|^2/p` and `sum_p |a_p(rho)|/p` converge.  Thus along cofinal
finite prime sets,

```text
S_F -> S_infinity(rho),
A_F -> A_infinity(rho),
M_F -> infinity,
```

and `(1)` predicts the quantitative law

```text
E_F(a(rho)) / M_F -> 2 S_infinity(rho).                    (4)
```

Off the critical line, `S_infinity(rho)>0`; on the critical line it is zero.  Hence the qualitative
unboundedness theorem in `XiPrimeSeamPairEnergy.lean` has a sharper logarithmic-prime-mass form.
The convergence and limit statement `(4)` are not yet formalized here.

This changes the missing source problem.  It is enough to seek an operator identity whose Calkin
class realizes

```text
mass amplification times one-particle seam energy
  minus one rank-one mean channel,
```

rather than estimate every prime pair separately.  Any compact or rank-one realization of the mean
channel leaves the one-particle weighted seam norm as the only noncompact coefficient invariant.
The actual Sonin operator identity and source-pure uniform upper bound remain open.

## Positive boundary

The existing all-prime Sonin Hilbert--Schmidt modules control principal-subtracted prime-power
residuals.  They can account for compact corrections to the variance realization but not the
divergent factor `M_F`.  Positively, all growth capable of detecting an off-line fibre is now
isolated in the principal reciprocal-prime mass multiplying `S_F`; the residual and mean channels
are lower-order once their source realization is established.

## Principal declarations

```text
primeReciprocalMass
primePairWeightedNormSq
primePairWeightedMean
primePairDifferenceEnergy_eq_weightedVariance
primePairWeightedMean_norm_sq_le
orbitwisePrimeSeamPairEnergy_eq_weightedVariance
```

## Gates

- [x] exact complex weighted-variance identity
- [x] reuse of an existing theta-corpus theorem
- [x] finite weighted-mean inequality
- [x] canonical Xi seam specialization
- [x] Lean proof and axiom audit
- [ ] formal canonical seam square summability on every open-strip fibre
- [ ] formal canonical seam weighted-mean absolute summability
- [ ] formal cofinal asymptotic `(4)`
- [ ] actual Sonin Calkin variance realization
- [ ] source-pure uniform upper bound
