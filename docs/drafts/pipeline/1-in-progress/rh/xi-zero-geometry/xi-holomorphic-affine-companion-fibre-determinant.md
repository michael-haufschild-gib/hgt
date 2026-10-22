# Xi holomorphic affine-companion fibre determinant

- **ID:** `xi-holomorphic-affine-companion-fibre-determinant`
- **Stage:** `1-in-progress`
- **Type:** `[CONJECTURE -> PAPER THEOREM -> LEAN TARGET]`
- **Scientific status:** `[CORPUS-NEW EXACT PHASE CLASSIFICATION] [NOVELTY UNVERIFIED] [NOT 75%]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/XiHolomorphicAffineCompanionFibreDeterminant.lean`,
  `formal/GaloisForLFunctions/RHTower/XiHolomorphicAffineCompanionHeightDephasing.lean`,
  `formal/GaloisForLFunctions/RHTower/XiWardAbelAffineCompanionMultiplicitySeparator.lean`

## Conjecture AHC-Fibre

The prime--Gamma Weil form is holomorphic rather than a positive Hermitian Gram.  Its two-by-two
determinant therefore expands into squared complex minors, not squared norms.  The initial
Cauchy--Binet idea fails globally because unrelated zero pairs carry indefinite phase.

The surviving conjecture was that phase ceases to be an obstruction after two source-native
operations:

1. use an affine companion pair `(H(z), z H(z))`; and
2. dephase in height before aggregating reflection pairs.

For one reflection-complete equal-ordinate fibre, write the strict-right representatives as
`z_j=x+i y_j`, with multiplicity weights `m_j`, and put `P_j=H(z_j)^2`.  Define

```text
A = sum_j m_j Re P_j,
S = sum_j m_j Im P_j y_j,
U = sum_j m_j Re P_j y_j^2.
```

The reflection-paired affine moments are

```text
M0=2A,
M1=2(xA-S),
M2=2(x^2 A-U-2xS).
```

## `[PAPER-PROVED]` Exact phase-safe determinant

Direct expansion gives

```text
M0 M2-M1^2 = -4(AU+S^2).                              (AHC1)
```

This is stronger than the phase-free case.  Envelope phase cannot cancel the transverse charge
inside one equal-height fibre; it adds the further nonpositive square `-4S^2`.  If `A>0` and
`U>0`, the determinant is strictly negative for every nonzero displacement, however small.  If
all `y_j=0`, it is exactly zero.

The existing critical-feature sector theorem supplies `Re(H(z)^2)>0` for
`H(z)=2/(1+(z-t)^2)` throughout the Xi strip, so `(AHC1)` applies to the actual absolute-Euler
critical features without an RH hypothesis.

## Hostile audit

- Generic two-by-two Cauchy--Binet is classical and is not claimed.  Corpus theorem
  `HTGeometry.CommonRealPartTuranDeterminant` already gives the common-real-part sign law for
  **real nonnegative weights**.
- New candidate content is the source-specific affine-companion/equal-height organization and the
  strict complex-weight extension: reflection-conjugate envelope squares need not be real or
  nonnegative, yet their phase becomes `-S^2`, rather than an indefinite remainder.
- `(AHC1)` is qualitative at submicroscopic displacement: `U` still contains `y_j^2`.  It does not
  count multiplicity uniformly and therefore is not a 75% theorem.
- A valid density producer must combine `(AHC1)` with a source-defined Abel/Ward normalization
  whose trace bound is uniform in the normalization parameter.  Inserting `1/y_j` by hand is
  forbidden.

## Next falsifier

Construct the finite height-dephased prime--Gamma determinant for `(H,zH)` and test whether the
regular source Abel weights can normalize `U` to

```text
sum_j m_j * n y_j^2/(1+n y_j^2),
```

without a zero-selected coefficient.  Its monotone limit is strict-right multiplicity.  Failure
of source realization or a nonuniform arithmetic trace bound retires this route.

## `[LEAN TARGET]` Finite source-generated dephasing

For arbitrary complex envelope weights `c_i` and spectral points `z_i`, the ordered-pair identity

```text
2 det[[sum c_i, sum c_i z_i],
      [sum c_i z_i, sum c_i z_i^2]]
  = sum_(i,j) c_i c_j (z_i-z_j)^2                       (AHC2)
```

holds without positivity.  Multiply every pair coefficient by the corpus's source-native
integer-harmonic correlation at ordinate gap `gamma_i-gamma_j`.  Finite-sum convergence gives
the exact equal-ordinate filter.  This closes height dephasing before any sign assertion; `(AHC1)`
then supplies the fibre sign after reflection pairing.

## `[PAPER-PROVED; LEAN TARGET]` Ward--Abel multiplicity saturation

The source-only Ward Abel projector has weight `(1+n y^2)^(-1)`.  Its complement

```text
w_n(y)=n y^2/(1+n y^2)
```

is regular, lies in `[0,1]`, is zero at `y=0`, and tends to one for every `y!=0`.  Put
`Y_n=sqrt(w_n)`.  In `(AHC1)` take the envelope weight `P=1`, one representative from each
reflection pair, and transverse coordinate `Y_n`.  For a finite equal-height packet containing
`M` strict-right divisor copies,

```text
D_n=-4 M sum_j w_n(y_j)  ->  -4 M^2.                   (AHC3)
```

Because `XiZeroCopy` repeats analytic multiplicity, `M` is multiplicity-exact.  Formula `(AHC3)`
separates arbitrarily small positive shifts from diagonal critical-line multiplicity with no
zero-dependent inverse and no minimum displacement.  It is the requested local submicroscopic
separator in determinant form.  Remaining 75% gate is an upper bound for the height-dephased
prime--Gamma four-leg trace, uniform in `n`.

## Gates

- [x] global Hermitian Cauchy--Binet shortcut rejected
- [x] equal-height affine-companion identity proved on paper
- [x] direct Lean check of fibre determinant module
- [ ] umbrella import and targeted build
- [ ] direct Lean check of source-generated height dephasing
- [ ] direct Lean check of Ward--Abel multiplicity saturation
- [ ] Abel-normalized prime--Gamma trace
- [ ] quantitative 75% budget

## Log

- 2026-08-13 — Conjectured affine companions after the holomorphic/Hermitian mismatch.  Exact
  expansion proved `(AHC1)` and showed phase reinforces, rather than cancels, transverse charge.
