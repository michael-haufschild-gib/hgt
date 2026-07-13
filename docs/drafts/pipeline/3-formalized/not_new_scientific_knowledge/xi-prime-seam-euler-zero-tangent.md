# The Xi horizontal prime seam is an empty-parameter Euler tangent

- **ID:** `xi-prime-seam-euler-zero-tangent`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[VALUE RELATION]`, `[SOURCE-COEFFICIENT DISCHARGE]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `xi-prime-seam-reflection-energy.md`;
  `sonin-prime-seam-exterior-factorization.md`;
  `CriticalDiscEulerOrbitDensity.lean`

## Statement

For one prime `p`, a spectral point `s`, and a local Euler coefficient `a`, put

```text
F_(p,s)(a)=log(p) [a p^(-s)/(1-a p^(-s))
                    -a p^(-(1-s))/(1-a p^(-(1-s)))].       (1)
```

Then

```text
F_(p,s)'(0)=log(p)[p^(-s)-p^(-(1-s))].                     (2)
```

At a real point `s=sigma`, the right side is exactly the canonical Xi prime seam evaluated at the
horizontal projection:

```text
F_(p,sigma)'(0)=C_p(sigma),
C_p(rho)=log(p)[p^(-conj(rho))-p^(-(1-rho))].              (3)
```

The reflection-energy theorem proves that the squared norm of `(3)` is unchanged when `rho` is
replaced by its real projection.  Consequently the full source-coefficient energy

```text
H(rho)=sum_p |F_(p,Re(rho))'(0)|^2/p                       (4)
```

satisfies the exact value relation

```text
H(rho)=sum_p |C_p(rho)|^2/p
      =P''(1+2 Re(rho))+P''(3-2 Re(rho))-2P''(2),          (5)
```

where `P` is the prime zeta function on its absolutely convergent real half-line.  In particular,

```text
(Re(rho)-1/2)^2 log(2)^4 <= H(rho).                        (6)
```

The differentiation in `(2)` is also proved in the compact-carrier Banach algebra used by the
nonlinear Euler-unit orbit theorem.  If `q` is a compact-carrier Euler coordinate and `tau` the FE
reflection, then

```text
d/da|_(a=0) log(p)[a q/(1-aq)-a(q after tau)/(1-a(q after tau))]
  =log(p)[q-q after tau].                                  (7)
```

Thus the horizontal seam is not a divisor-fed coefficient invented at the RH endpoint.  It is the
literal first coefficient of a finite FE-paired Euler source.

## Proof

The scalar derivative of `a q/(1-aq)` at zero is `q`; subtraction and multiplication by `log p`
give `(2)`.  The same calculation is performed using the Fréchet derivative of inversion in the
Banach algebra `C(K,C)`, giving `(7)`.  Real-axis specialization gives `(3)`.  The per-prime
height-independence theorem in `XiPrimeSeamReflectionEnergy.lean`, followed by summation, gives
`(5)`.  The existing prime-two hyperbolic lower bound gives `(6)`.

## Top-down consequence

The scalar source-realization part of the exterior-factorization route is closed.  The two
one-particle sections may now use coefficients obtained from an explicit finite Euler deformation;
no zero enumeration, zero-location assumption, or limiting measure is needed to define them.

The remaining step is not coefficient discovery.  It is the operator transfer and estimate:

```text
finite Euler first coefficients
  -> seam-weighted Sonin section A_F
  -> dist_Calkin(A_F tensor B_F-B_F tensor A_F)=o(sqrt(sum_(p in F)1/p)).  (8)
```

The existing critical-disc Euler-orbit density theorem gives qualitative local-uniform closure of
FE-odd Schwarz-real analytic functions by genuine local Euler increments, even after deleting
finitely many primes.  It does **not** supply the quotient-norm rate in `(8)`, nor a bounded map from
that uniform function topology to the tensor Calkin norm.  This is now the exact interface to
research.

The expansion point matters.  `a=0` extracts the degree-one Euler shell exactly.  The existing
nonlinear orbit theorem differentiates at the actual local parameter `a=1`, where the coefficient
is `q/(1-q)^2`.  A successful transfer must compare these two tangent charts or show that their
difference contributes only a controlled relative/compact tail.  Treating them as identical would
be a gap.

## Literature boundary

The derivative in `(2)` is elementary Euler-factor calculus.  Connes--Consani's finite local-factor
quasi-inner construction provides the nonlinear completed local source, while the semilocal
Sonin/prolate papers provide the operator carrier.  No theorem located in those sources turns the
empty-parameter coefficient identity into the cofinal tensor-Calkin estimate `(8)`.

## Lean

`formal/GaloisForLFunctions/RHTower/XiPrimeSeamEulerZeroTangent.lean` proves:

```text
hasDerivAt_compactMobiusFlux_zero
hasDerivAt_compactDegreeOneEulerLocalFlux_zero
hasDerivAt_compactDegreeOneEulerFEFlux_zero
compactDegreeOneEulerZeroFETangent_exponential_apply
hasDerivAt_degreeOneEulerFEFlux_zero
degreeOneEulerFEFlux_deriv_zero_eq_horizontalPrimeSeam
degreeOneEulerFEFlux_deriv_zero_weighted_norm_sq_eq_primeSeam
degreeOneEulerFEFirstCoefficientEnergy_eq_primeSeamWeightedNormSq
degreeOneEulerFEFirstCoefficientEnergy_eq_primeLogSquareMoment_secondDifference
tendsto_orbitwisePrimeSeamPairEnergy_div_mass_to_degreeOneEulerFEFirstCoefficientEnergy
horizontalDisplacement_sq_mul_log_two_pow_four_le_degreeOneEulerFEFirstCoefficientEnergy
```

## Gates

- [x] scalar finite Euler coefficient identity
- [x] compact-carrier Banach-algebra coefficient identity
- [x] exact identification with the horizontal Xi seam
- [x] full energy equality and quantitative horizontal coercivity
- [x] no Xi zero-location or RH input
- [ ] bounded transfer from the compact-carrier source topology to the Sonin Calkin quotient
- [ ] comparison of the empty-parameter and actual-parameter tangent charts
- [ ] cofinal exterior-Calkin rate `(8)`
