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

The comparison with the actual local parameter is also exact.  If

```text
T_(p,s)^(>1)=primeEulerUnitTangent(p,s)-log(p)p^(-s),       (8)
```

then on the open right half-plane

```text
T_(p,s)^(>1)
 =log(p)p^(-2s)(2-p^(-s))/(1-p^(-s))^2
 =sum_(m>=2)m log(p)p^(-ms).                              (9)
```

After FE pairing, the actual-source tangent is therefore

```text
primeEulerUnitFETangent(p,s)
 =F_(p,s)'(0)+T_(p,s)^(>1)-T_(p,1-s)^(>1).               (10)
```

Thus the two tangent charts differ by a completely explicit higher-prime-power tail and by no
degree-one shell.

There is now a sharper companion when the desired output is only the scalar FE--Schwarz
orientation value.  For the literal actual-point tangent

```text
T_p(s)=primeEulerUnitTangent(p,s),
q=p^(-conj(rho)), r=p^(-(1-rho)),
```

the exact factorization

```text
T_p(conj(rho))-T_p(1-rho)
 =C_p(rho)(1-q r)/[(1-q)^2(1-r)^2]                       (10a)
```

has only invertible extra factors throughout the open strip.  Consequently, for every one prime
`p`,

```text
T_p(conj(rho))=T_p(1-rho) iff C_p(rho)=0 iff Re(rho)=1/2. (10b)
```

Thus a scalar source reader already living at `a_p=1` need not return to the empty chart or remove
the higher grades.  Equations `(8)`--`(10)` remain necessary for the distinct operator-Calkin route,
where the actual and empty sections must be compared in quotient norm rather than merely tested
for a scalar zero.

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
  -> dist_Calkin(A_F tensor B_F-B_F tensor A_F)=o(sqrt(sum_(p in F)1/p)).  (11)
```

The existing critical-disc Euler-orbit density theorem gives qualitative local-uniform closure of
FE-odd Schwarz-real analytic functions by genuine local Euler increments, even after deleting
finitely many primes.  It does **not** supply the quotient-norm rate in `(11)`, nor a bounded map from
that uniform function topology to the tensor Calkin norm.  This is now the exact interface to
research.

The expansion point still matters, but the scalar comparison is no longer open.  Equations
`(8)`--`(10)` identify the entire mismatch with the Lambert grades `m>=2`.  The paper-proven
critical all-grade corona theorem shows that these grades vanish in the critical Marcinkiewicz
quotient.  This does not imply Calkin compactness: the formal Sonin corpus proves that each
principal prime-power corner has nonzero essential norm, while only its principal-subtracted
residual is Hilbert--Schmidt.  The remaining chart-transfer theorem is therefore specifically a
Sonin exterior estimate for the higher-grade principal tail, not another scalar Euler identity.

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
primeEulerUnitTangentHigherTail_eq
primeEulerUnitTangentHigherTail_hasSum
primeEulerUnitFETangent_eq_zeroTangent_add_higherTail
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
- [x] exact actual-versus-empty tangent comparison
- [x] chart mismatch isolated to the Lambert grades `m>=2`
- [x] actual-point scalar FE--Schwarz tangent difference factored through the same prime seam
- [x] any single prime actual-tangent equality shown faithful in the open strip
- [ ] bounded transfer from the compact-carrier source topology to the Sonin Calkin quotient
- [ ] exterior-Calkin control of the higher-grade principal tangent tail
- [ ] cofinal exterior-Calkin rate `(11)`

## Connection-value companion

`../../2-fully-proven/not_new_scientific_knowledge/08-sonin-semilocal-copoisson/semilocal-dual-pair-euler-connection-source-law.md`
separates the Euler **value** required by the semilocal logarithmic-position connection from the
Euler-parameter tangent studied here.  For the same scalar family `(1)`,

```text
F_(p,z)(1)=Phi_p(z)-Phi_p(1-z)
          =F_(p,z)'(0)
           +sum_(m>=2)log(p)[p^(-m z)-p^(-m(1-z))].       (12)
```

Thus the direct source-connection route has a coefficient-one higher-grade tail, whereas `(9)` is
the derivative-at-one tail with coefficient `m`.  The simpler tail is still Calkin-faithful off the
critical line by the general summable-Euler injectivity theorem.  Equation `(12)` therefore
clarifies the interface without making the higher grades disposable: completed prime--Gamma
cutoff/resolvent cancellation remains necessary.
