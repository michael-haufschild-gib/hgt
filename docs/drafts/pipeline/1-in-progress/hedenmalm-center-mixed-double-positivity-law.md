# Hedenmalm center-mixed double-positivity law

- **ID:** `hedenmalm-center-mixed-double-positivity-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM / SOURCE-SIDE HILBERT--POLYA ORIENTATION COORDINATE
- **Scientific status:** `[PROVED ON PAPER] [LEAN PARTIAL] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parent:** `theta-wigner-eisenstein-orientation-current.md`

## Statement

Let `k : R -> R` be even, strictly positive, and rapidly decreasing against every exponential of
rate below `1/2`, and define its Wigner distribution by

```text
W_k(y,b)=integral_R k(y+t)k(y-t)exp(2 i b t)dt.
```

For `0<a<1/2`, define the center-mixed density

```text
M_(k,a)(t)
 =integral_(0,infinity)
    r sinh(a r) k(r/2+t)k(r/2-t)dr.                       (1)
```

Then `M_(k,a)` is strictly positive, even, continuous, and integrable.  Its Fourier transform is
the radial Wigner current:

```text
integral_R M_(k,a)(t) exp(2 i b t)dt
 =integral_(0,infinity) r sinh(a r)W_k(r/2,b)dr.          (2)
```

For Hedenmalm's normalized theta source

```text
k(x)=2 VarTheta_00(i exp(2x)),
X(w)=integral_R k(x)exp(w x)dx=xi(1/2+w),
```

the following are equivalent:

```text
RH;

for every 0<a<1/2 and b in R,
  Fourier(M_(k,a))(2b)>=0;

for every 0<a<1/2,
  M_(k,a) is positive definite on R.                     (3)
```

Thus the source-side orientation carrier is **doubly positive**: `M_(k,a)` is already pointwise
positive unconditionally, while RH is exactly its second positivity, positive definiteness.

## Proof of the transform identity

Absolute convergence follows from the exponential decay of `k` and `a<1/2`.  Fubini gives

```text
integral_R M_(k,a)(t) exp(2 i b t)dt
 =integral_(0,infinity) integral_R
    r sinh(a r) k(r/2+t)k(r/2-t)exp(2 i b t)dt dr.
```

The inner integral is `r sinh(a r)W_k(r/2,b)`, which proves `(2)`.

The two source factors in `(1)` are exchanged by `t -> -t`, so `M_(k,a)` is even.  Every other
factor is positive for `r>0`, and the theta source is strictly positive, so `M_(k,a)(t)>0`.
Continuity follows by dominated convergence.  Integrability follows either by the same exponential
majorant or by Tonelli after integrating the positive kernel in `t`.

For the theta source, the already proved Wigner--Bezoutian identity and Hermitian orientation gate
give the equivalence of RH with the second line of `(3)`.  Since `M_(k,a)` is continuous and
integrable, the classical Bochner theorem identifies nonnegativity of its Fourier transform with
positive definiteness, proving the third equivalence.

## Pure-state tangent interpretation

Put

```text
f_a(x)=exp(a x)k(x),
rho_a=|f_a><f_a|.
```

The full-center form of `(1)` is

```text
M_(k,a)(t)=partial_a R_(f_a)(2t),                         (4)

R_(f_a)(q)=integral_R f_a(x)f_a(x-q)dx.
```

Equivalently, the Fourier transform in `(2)` is the momentum diagonal of the rank-two tangent

```text
partial_a rho_a
 =|x f_a><f_a|+|f_a><x f_a|.                             (5)
```

Unless the source is concentrated at one point, `(5)` is indefinite on the span of `f_a` and
`x f_a`: it has one positive and one negative direction.  Therefore `(3)` does not claim ambient
operator positivity.  It says that the distinguished momentum diagonal of this universal Krein
tangent is nonnegative throughout the critical aperture.

This is the continuous form of the already formalized two-atom Mellin signature.  It also explains
why an ambient Hecke square, a Loewner-monotone density matrix, or a positive Gram factorization on
arbitrary theta coefficients cannot prove orientation.

## Why this survives the previous attacks

1. **Hudson rigidity does not apply.**  Hudson forbids pointwise positivity of every pure-state
   Wigner slice `W_k(y,b)` unless `k` is Gaussian.  The density `(1)` mixes the center variable
   before the Fourier sign is read and is not a pure-state Wigner distribution.
2. **The ambient Krein obstruction is retained.**  Formula `(5)` is indefinite, in agreement with
   the exact negative two-atom determinant.  Only its source-selected momentum diagonal is tested.
3. **No divisor has been inserted.**  The density `(1)` is constructed directly from the theta
   source and the critical aperture parameter `a`.
4. **The remaining theorem is explicit.**  A proof must establish positive definiteness of the
   concrete positive density `(1)`, not positivity of a reconstructed zero measure or an abstract
   Hilbert space.

## Positive carrier obligation

Any successful Hedenmalm--Hilbert--Polya construction in this coordinate must provide one of:

```text
a source factorization of M_(k,a) as a positive mixture of autocorrelations;

a source-preserving operation that places M_(k,a) in the positive-definite cone;

or a direct finite-matrix proof that
  sum_(i,j) c_i conjugate(c_j) M_(k,a)(t_i-t_j)>=0
for every finite packet, uniformly for 0<a<1/2.
```

Pointwise positivity of `M_(k,a)` is only the first half of this obligation.

## Formalization status and open proof obligations

- [x] formalize the actual theta-source center-mixed density and its absolute integrability;
- [x] formalize the center-mixing Fubini identity with the exact Fourier phase normalization;
- [x] formalize strict positivity, evenness, continuity, and integrability of `M_(k,a)`;
- [x] formalize `M_(k,a)(x/2)=partial_a R_(f_a)(x)`, extend integrability and continuity to
      `|a|<1`, and combine strict spatial positivity with the finite differential-frame exclusion;
- [x] formalize the Fourier-sign/RH equivalence in `(3)` without introducing a positivity premise;
- [ ] formalize the rank-two inertia statement `(5)`;
- [ ] audit the exact center-mixed criterion against ambiguity-function, Wigner, and
      positive-definite-function literature;
- [ ] find or refute a source factorization of `M_(k,a)` inside the positive-definite cone.

The completed unconditional analytic layer is in
`formal/GaloisForLFunctions/RHTower/ThetaWignerCenterMix.lean`.  It includes an explicit
two-variable exponential majorant, so absolute integrability is derived for the actual theta
source rather than exposed as a theorem hypothesis.  This does not formalize, assume, or imply the
positive-definiteness assertion in `(3)`.  The exact module build succeeds, and the Fubini,
strict-positivity, integrability, and continuity theorems print only the standard foundations
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.

The exact autocorrelation-path identification and full-aperture regularity are in
`formal/GaloisForLFunctions/RHTower/HedenmalmAutocorrelationPath.lean`; their separate formalized
card is `../3-formalized/not_new_scientific_knowledge/hedenmalm-autocorrelation-path-boundary.md`.

The exact source-to-orientation boundary is in
`formal/GaloisForLFunctions/RHTower/HedenmalmCenterMixedOrientationBoundary.lean`.  It proves that
the actual and pointed-moment Bezoutian diagonals equal the theta-orbit Krein current divided by
`2a`, and that nonnegativity of the corresponding center-mixed Fourier current throughout the
critical aperture is equivalent to RH.  It does not prove that current nonnegative.

The formal theorem surface is:

```text
integral_thetaWignerCenterMixedDensity_mul_phase_thetaCusp
thetaCuspCenterMixedDensity_pos
integrable_thetaCuspCenterMixedDensity
continuous_thetaCuspCenterMixedDensity.
thetaXiHankelOrbitNonnegative_iff_riemannHypothesis
thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis
```

## Parent-theory boundary

The sign in `(3)` is the source-coordinate form of horizontal monotonicity of the modulus of the
Riemann xi function.  Sondow and Dumitrescu proved that horizontal modulus monotonicity in the
zero-free right half-plane is equivalent to RH.  Consequently the RH equivalence itself is a
`[BRIDGE]`, not new scientific knowledge.  Potential novelty can attach only to the explicit
center-mixed positive-density representation or to a genuinely new source factorization proving
its positive definiteness.  No such factorization has yet been proved.

Primary parent: J. Sondow and C. Dumitrescu, *A monotonicity property of Riemann's xi function and
a reformulation of the Riemann Hypothesis*, Period. Math. Hungar. 60 (2010), 37--40,
doi:10.1007/s10998-010-1037-3.

## Publication boundary

The transform identity and criterion are not yet sufficient for a publication-level RH result.
They become significant only if the center-mixed density admits a new source-side
positive-definiteness mechanism, or if the failure of every natural factorization can be classified
by a theorem stronger than the existing two-point Krein obstruction.
