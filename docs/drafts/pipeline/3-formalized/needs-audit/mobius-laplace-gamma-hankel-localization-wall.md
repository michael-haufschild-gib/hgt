# Gamma--Hankel localization of the Möbius--Laplace frontier

- **ID:** `mobius-laplace-gamma-hankel-localization-wall`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH CRITERION / NO-GO CLOSURE
- **Scientific status:** `[PROVED] [NEW TO CORPUS] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/MobiusLaplaceGammaHankelWall.lean`
- **Parents:** Möbius--Laplace continuation wall, additive Möbius triangle, critical channel mass
  escape, critical prime-block resonance

## Statement

For real coefficients `a_1,...,a_N`, put

```text
P_N(s)=sum_(n<=N) a_n n^(-s),
F_N(x)=sum_(n<=N) a_n exp(-n x).
```

For every `sigma>0`, archimedean Gamma localization has the exact three-way identity

```text
integral_R |Gamma(sigma+i t) P_N(sigma+i t)|^2 dt
 = 2 pi Gamma(2 sigma)
     sum_(m,n<=N) a_m a_n/(m+n)^(2 sigma)
 = 2 pi integral_0^infinity x^(2 sigma-1) |F_N(x)|^2 dx.       (GH1)
```

The middle matrix is positive semidefinite for every finite aperture.  Specializing `a_n=mu(n)`
shows exactly what Gamma damping does to the source-resolved Möbius channel: it does not
orthogonalize prime or integer directions; it converts their scalar synthesis into the additive
Hankel kernel `(m+n)^(-2 sigma)` and retains every cross correlation.

Define the full weighted-energy condition

```text
E_sigma = integral_0^infinity
  x^(2 sigma-1) |Phi(x)|^2 dx < infinity
for every sigma>1/2,                                      (GH2)

Phi(x)=sum_(n>=1) mu(n) exp(-n x).
```

Then `(GH2)` is equivalent to RH.  This is a new-to-corpus `L2` formulation of the existing
Mellin-continuation wall.  The exact formulation was not found in the targeted literature audit;
priority remains unverified.

## Proof of the finite localization law

Euler's Gamma integral gives, for `r>0`,

```text
integral_0^infinity x^(r-1) exp(-(m+n)x) dx
  = Gamma(r)/(m+n)^r.                                    (GH3)
```

Expanding the finite square and integrating termwise proves the second equality in `(GH1)`.

For the height equality, the beta integral gives the Fourier kernel

```text
integral_R Gamma(sigma+i t) Gamma(sigma-i t) exp(-i t u) dt
 = 2 pi Gamma(2 sigma)/(2 cosh(u/2))^(2 sigma).           (GH4)
```

Take `u=log(n/m)`.  Since

```text
(m n)^(-sigma)/(2 cosh(log(n/m)/2))^(2 sigma)
 = 1/(m+n)^(2 sigma),                                    (GH5)
```

expansion of `|P_N|^2` proves the first equality.  Equivalently, `(GH1)` is Mellin--Plancherel
applied to the finite Laplace pencil.

Positivity follows from either outer expression in `(GH1)`.  Lean formalizes the complete finite
Laplace/Gamma--Hankel identity and its quadratic-form nonnegativity for arbitrary real
coefficients, then specializes it to shifted Möbius coefficients.

## Proof of the `L2` RH criterion

### `(GH2) -> RH`

Fix `s` with `Re(s)>1/2` and choose

```text
1/2 < sigma < Re(s).
```

Cauchy--Schwarz on `(0,1)` gives

```text
integral_0^1 x^(Re(s)-1) |Phi(x)| dx
 <= E_sigma^(1/2)
    (integral_0^1 x^(2(Re(s)-sigma)-1) dx)^(1/2)
 < infinity.                                             (GH6)
```

The already-proved exponential tail of `Phi` handles `(1,infinity)`.  Choosing one `sigma`
strictly below a compact substrip supplies a common integrable dominator, so the Mellin transform

```text
M Phi(s)=integral_0^infinity Phi(x)x^(s-1) dx
```

is holomorphic on `Re(s)>1/2`.  On `Re(s)>1`, the existing exact identity is

```text
M Phi(s)=Gamma(s)/zeta(s).                               (GH7)
```

Identity continuation therefore supplies the formalized Möbius--Laplace Mellin wall, hence RH.

### `RH -> (GH2)`

Fix `sigma>1/2`.  RH gives, for every `epsilon>0`,

```text
Phi(x)=O_epsilon(x^(-1/2-epsilon)) as x->0+.             (GH8)
```

Choose `0<epsilon<sigma-1/2`.  Then the integrand in `(GH2)` is

```text
O(x^(2 sigma-2-2 epsilon)),
```

whose exponent is greater than `-1`.  Exponential decay again handles infinity.  Thus `E_sigma`
is finite.

## Exact relation to the additive triangle

Writing

```text
c(k)=sum_(m+n=k) mu(m)mu(n)
```

turns the middle expression in `(GH1)` into

```text
Gamma(2 sigma) sum_k c(k)/k^(2 sigma).                   (GH9)
```

Abel summation writes it in terms of the cumulative triangle

```text
T(K)=sum_(m+n<=K) mu(m)mu(n).
```

Consequently Gamma-weighted height control and additive-triangle control are not independent
frontiers.  Gamma localization is an exact positive Hankel presentation of the same arithmetic
endpoint.  Any proof using `(GH1)` must bound signed off-diagonal Möbius covariance before taking
the positive norm.

## Hostile audit

1. **Bohr mean does not imply Gamma-local control.**  Long-height Cesaro orthogonality sees
   distinct logarithmic frequencies.  Gamma localization has fixed height width and produces the
   dense, non-diagonal kernel `(m+n)^(-2 sigma)` instead.
2. **Positivity is not cancellation.**  Positive semidefiniteness says the full quadratic form is
   nonnegative.  It supplies no upper bound uniform in aperture.
3. **Hilbert-matrix boundedness loses the source scale.**  At `sigma=1/2`, the kernel is Hilbert's
   matrix, but its operator bound applied to the length-`N` Möbius vector is `O(N)`, not a cofinal
   finite energy bound.
4. **Compact synthesis is already excluded.**  Critical Möbius channel mass escapes every fixed
   compact synthesis.  `(GH1)` identifies the required surviving synthesis as cutoff-dependent
   and noncompact, with exact additive Hankel covariance.
5. **Primewise positive norms remain impossible.**  The synchronized terminal prime block has
   exponential resonance and inverse amplification.  Gamma--Hankel sewing must occur before any
   product norm; applying a positive norm prime by prime loses the off-diagonal signs in `(GH9)`.
6. **No unconditional endpoint.**  Finiteness of `(GH2)` for every `sigma>1/2` is RH-equivalent,
   not proved here.

## Corpus and literature boundary

Corpus searches found Mellin--Plancherel infrastructure, finite exponential-pencil Cesaro laws,
Gamma-damped prime covariances, additive Möbius triangle criteria, and critical mass escape.
`GammaSewnMobiusValuationContraction.lean` already proves that its diagonal primewise Gamma
multiplier is boundedly invertible and preserves nonnegative prime-energy summability exactly.
That result and `(GH1)` are complementary: the former excludes free diagonal Hilbertization in
prime coordinates, while `(GH1)` computes the non-diagonal additive-integer Hankel covariance
created by actual Gamma height localization.  The corpus did not contain this Hankel identity
specialized to the Möbius--Laplace source or the full-energy criterion `(GH2)`.

External searches covered mean squares of zeta times Dirichlet polynomials, reciprocal-zeta
Dirichlet series, Hilbert-matrix operators, and Gamma-weighted Dirichlet-polynomial phrases.  No
matching statement was found.  Mellin--Plancherel, Euler's Gamma integral, the beta Fourier kernel,
and Hilbert-matrix theory are classical; therefore the finite transform identity is classified as
standard.  Candidate delta is the exact source specialization, the equivalence `(GH2) <-> RH`, and
the synthesis no-go.  This remains `NOVELTY UNVERIFIED`, not a literature claim.

The sharpened one-sided covariance audit also checked Mangerel, *On a Goldbach-Type Problem for
the Liouville Function* (IMRN 2024), Misra--Saha--Sharma, *On additive convolution sum of
arithmetic functions and related questions* (arXiv:2502.08305), and averaged/logarithmic Chowla
work.  Mangerel proves a qualitative strict improvement over the trivial Liouville antidiagonal
bound, not an aperture-uniform weighted covariance ceiling.  Misra--Saha--Sharma requires
absolutely convergent Ramanujan expansions.  Averaged Chowla controls translation shifts rather
than the growing additive reflection.  None supplies the upper sign in `(MP6)`; no exact published
match was located.

## Lean certificate

Verified declarations:

```text
finiteRealLaplacePencil
finiteGammaHankelEnergy
integral_finiteRealLaplacePencil_sq
finiteGammaHankelEnergy_nonneg
shiftedMobiusRealCoefficient
finiteMobiusLaplacePencil
finiteMobiusGammaHankelEnergy
integral_finiteMobiusLaplacePencil_sq
finiteMobiusGammaHankelEnergy_nonneg
integrableOn_finiteRealLaplacePencil_sq
integral_log_finiteRealLaplacePencil_sq
integrable_log_finiteRealLaplacePencil_sq
integral_log_finiteMobiusLaplacePencil_sq
finiteMobiusGammaHankelDiagonalEnergy
finiteMobiusGammaHankelOffDiagonalCovariance
finiteMobiusGammaHankelEnergy_eq_diagonal_add_offDiagonal
finiteMobiusGammaHankelDiagonalEnergy_le_tsum
finiteMobiusGammaHankelOffDiagonalCovariance_lower_floor
MobiusGammaHankelEnergyUniformlyBounded
MobiusGammaHankelOffDiagonalUpperBounded
mobiusGammaHankelEnergyUniformlyBounded_iff_offDiagonalUpperBounded
```

The formal certificate now covers `(GH3)`, the finite Laplace/Hankel half of `(GH1)`, its exact
log-coordinate form, diagonal/off-diagonal decomposition, unconditional diagonal summability,
automatic lower covariance floor, and one-sided covariance compression.  The separate
Mellin--Plancherel module formalizes the infinite-aperture Hardy--Mellin criterion and the
closed-boundary zero exclusion.  The beta/Fourier equality `(GH4)` remains unnecessary.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/MobiusLaplaceGammaHankelWall.lean  PASS
lake build GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelWall         PASS
```

The four public theorem endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.
Formal lint recognizes this module as reachable from `RHTower.lean`; repository-wide lint still
reports unrelated pre-existing unreachable concurrent modules in RHTower, HTGeometry, and
HilbertMetric.

## Gates

- [x] internal corpus audit
- [x] external adjacent-literature audit
- [x] exact finite Gamma--Hankel law proved on paper
- [x] full-energy `L2` criterion proved on paper
- [x] hostile tests against Bohr mean, Hilbert norm, compact synthesis, and primewise norm
- [x] arbitrary finite real coefficient law formalized
- [x] finite Möbius specialization formalized
- [x] exact log-coordinate finite energy identity formalized
- [x] diagonal p-series ceiling for every `r>1` formalized
- [x] automatic off-diagonal lower floor formalized
- [x] uniform energy iff one-sided off-diagonal upper ceiling formalized
- [ ] formalize beta/Fourier height equality
- [x] formalize infinite-aperture `L2` Mellin continuation theorem
- [ ] prove cofinal one-sided off-diagonal covariance ceiling unconditionally
- [ ] RH

## No-go closure

- **Killed mechanism:** Gamma damping followed by an ordinary scalar norm or long-height Bohr
  averaging cannot supply the missing half-plane estimate.
- **Strongest positive survivor:** exact source-resolved Gamma--Hankel covariance `(GH1)`, cofinal
  energy criterion `(GH2)`, and theorem that all diagonal/lower-sign obligations are automatic.
- **Remaining named core:** one-sided aperture-uniform **upper** control of signed off-diagonal
  Möbius Hankel covariance at exponents cofinal from the right at `1`.

## Log

- 2026-07-22 — Derived finite height/Laplace/Hankel identity, proved `L2` RH equivalence on paper,
  completed hostile audit, and formalized finite Laplace/Hankel identity with Möbius specialization.
- 2026-07-22 — Proved and formalized exact log-coordinate identity, unconditional diagonal
  summability and lower covariance floor, and one-sided off-diagonal covariance compression.
