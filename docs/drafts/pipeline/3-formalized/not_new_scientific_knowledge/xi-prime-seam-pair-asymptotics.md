# Xi prime-seam pair energy has a positive reciprocal-mass asymptotic

- **ID:** `xi-prime-seam-pair-asymptotics`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[FORMALIZATION]`, `[VALUE RELATION]`, `[TOP-DOWN HYPOTHESIS WEAKENING]`
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiPrimeSeamPairAsymptotics.lean`
- **Parents:** `xi-prime-seam-pair-variance.md`; `xi-prime-seam-pair-energy-rh.md`
- **Reused source theorem:**
  `EulerFisherCurvature.summable_abs_log_natCast_pow_mul_rpow_neg`

## Statement

For an open-strip point `rho`, write

```text
C_p(rho)=log(p)(p^(-conj(rho))-p^(-(1-rho))).
```

Lean proves unconditionally

```text
sum_p |C_p(rho)|^2/p < infinity,                           (1)
sum_p |C_p(rho)|/p   < infinity.                           (2)
```

Define

```text
S(rho)=sum_p |C_p(rho)|^2/p,
M_F=sum_(p in F)1/p,
E_F(rho)=sum_(p,q in F)|C_p(rho)-C_q(rho)|^2/(p q).
```

As the finite prime set `F` tends to all primes in the directed finite-set filter,

```text
E_F(rho)/M_F -> 2 S(rho).                                  (3)
```

Moreover,

```text
Re(rho) != 1/2 -> S(rho)>0.                                (4)
```

Thus

```text
E_F(rho)=o(M_F) iff Re(rho)=1/2.                           (5)
```

The global condition `(5)` on every actual Xi divisor fibre is equivalent to RH.

## Proof

For `sigma=Re(rho)` in `(0,1)`, the complex-power norm formula and the triangle inequality give

```text
|C_p(rho)| <= log(p)(p^(-sigma)+p^(-(1-sigma))).           (6)
```

After squaring and inserting `1/p`, the two majorant exponents are `1+2 sigma>1` and
`3-2 sigma>1`.  For the weighted mean, they are `1+sigma>1` and `2-sigma>1`.  The existing
logarithmically weighted Dirichlet summability theorem proves `(1)` and `(2)`.

The formal weighted-variance identity gives

```text
E_F=2 M_F S_F-2|A_F|^2,
A_F=sum_(p in F) C_p/p.                                    (7)
```

Here `S_F->S(rho)`, `A_F` converges by `(2)`, and `M_F->infinity` by Euler's reciprocal-prime
divergence.  Divide `(7)` by `M_F` to obtain `(3)`.  If `rho` is off the line, the prime-two seam
is nonzero, so its positive summand makes `S(rho)>0`.  This proves `(4)` and the forward direction
of `(5)`.  On the critical line every seam charge vanishes, proving the converse.

## The weakened Sonin target

The previous top-down chain asked for a uniform finite-section Calkin bound.  That is stronger than
necessary.  Let `D_F(rho)` be the Calkin distance of the actual finite two-particle Sonin section.
The paper-proven tensor lower estimate gives, up to the ordered/unordered factor,

```text
E_F(rho) <= 2 D_F(rho)^2.                                  (8)
```

Therefore the sufficient source-side target is only

```text
D_F(rho)^2/M_F -> 0,
```

or equivalently

```text
D_F(rho)=o(sqrt(M_F)).                                     (9)
```

The resulting chain is

```text
source-pure sub-root reciprocal-mass Calkin growth
  -> E_F/M_F -> 0
  -> S(rho)=0
  -> C_2(rho)=0
  -> Re(rho)=1/2
  -> RH on all Xi fibres.                                  (10)
```

This is independent of the rectangular/subpower mesh route.  It concerns cofinal prime-set Calkin
growth on the Sonin tensor square, not Taylor flux on anisotropic rational meshes.

## Source interpretation and literature boundary

The subtraction `|A_F|^2` is the single weighted-mean channel.  It is lower order after division
by `M_F` because `A_F` converges, but it should not be discarded before source identification.
Connes--Consani's [*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368) proves that a purely
local inner-function approach fails and emphasizes that the global Poisson normalization controls
the semilocal principal values.  The weighted mean in `(7)` is therefore the natural place to look
for that normalization, not an expendable local correction.

Connes--Consani's
[*Weil positivity and Trace formula, the archimedean place*](https://arxiv.org/abs/2006.13771)
constructs the archimedean positive compression and explains that its ingredients extend to the
semilocal setting.  Connes--Consani--Moscovici's
[*Zeta zeros and prolate wave operators*](https://arxiv.org/abs/2310.18423) builds the stable
semilocal Sonin/prolate framework.  Neither located source states the normalized growth estimate
`(9)` or identifies the canonical seam mean with the global Poisson finite-part term.

`[OPEN CORE]` Construct the actual source-defined finite two-particle sections with coefficients
`C_p(rho)-C_q(rho)` and prove `(9)` from the prime--Gamma/Sonin source, retaining the global Poisson
normalization and without using Xi zero locations.  The operator lower estimate is paper-proven but
not yet formalized in Lean.

## Principal declarations

```text
summable_orbitwisePrimeSeam_weighted_norm_sq
summable_orbitwisePrimeSeam_weightedMean
tendsto_primeReciprocalMass_atTop
orbitwisePrimeSeamWeightedNormSq
tendsto_orbitwisePrimeSeamPairEnergy_div_mass
orbitwisePrimeSeamWeightedNormSq_pos_of_re_ne_half
OrbitwisePrimeSeamPairEnergySubmass
orbitwisePrimeSeamPairEnergySubmass_iff_re_eq_half
XiPrimeSeamPairEnergySubmass
xiPrimeSeamPairEnergySubmass_iff_riemannHypothesis
```

## Gates

- [x] canonical seam reciprocal-prime square summability
- [x] canonical seam reciprocal-prime mean absolute summability
- [x] reciprocal-prime finite-set mass tends to infinity
- [x] exact normalized pair-energy limit
- [x] strict positivity of the off-line asymptotic coefficient
- [x] fiberwise submass/critical-line equivalence
- [x] global submass/RH endpoint
- [x] Lean proof
- [ ] actual Sonin tensor lower estimate in Lean
- [ ] source realization of the canonical pair section
- [ ] source-pure sub-root reciprocal-mass Calkin growth `(9)`
