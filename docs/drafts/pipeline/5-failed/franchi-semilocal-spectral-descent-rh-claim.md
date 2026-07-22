# Semilocal spectral descent does not prove Weil positivity

- **ID:** `franchi-semilocal-spectral-descent-rh-claim`
- **Stage:** 5-failed
- **Type:** FALSIFIED EXTERNAL PROOF CLAIM / LITERATURE AUDIT
- **Scientific status:** `[CLAIMED RH PROOF REJECTED] [NO COMPUTATION USED]`
- **Claimed source:** C. Franchi Viceré,
  [*A Proof of the Riemann Hypothesis for the Riemann Zeta Function: Weil Positivity via Semilocal
  Spectral Descent*](https://zenodo.org/records/19546495), 12 April 2026
- **Primary comparison source:** A. Connes, C. Consani, H. Moscovici,
  [*Zeta Spectral Triples*](https://arxiv.org/abs/2511.22755), Theorem 1.1 and Section 8
- **Statement audited:** finite self-adjoint semilocal spectral approximants, compact-support form
  stability, and place exhaustion imply global Weil positivity and RH.

## Verdict

The claim fails before any limiting argument.  Its Theorem 1 drops two explicit hypotheses from
CCM Theorem 1.1, and its Theorem 2 invents a positive spectral expansion of the unshifted finite
Weil form that the cited source does not prove.  Compact-support stabilization cannot repair this
missing sign.

## Exact source mismatch

CCM Theorem 1.1 begins:

```text
Let epsilon_N be the smallest eigenvalue of QW^N_lambda assumed simple and xi the
corresponding eigenvector assumed even.
```

It then proves self-adjointness using the inner product induced by

```text
QW^N_lambda - epsilon_N <.|.>.                         (1)
```

The claimed proof states the result as unconditional for every finite truncation and omits both
`simple` and `even`.  CCM itself lists simple-evenness as its first essential missing step in
Section 8.

More decisively, `(1)` is positive semidefinite because the lowest eigenvalue was subtracted.  It
says only

```text
QW^N_lambda(v,v) >= epsilon_N ||v||^2.                 (2)
```

It does not say `QW^N_lambda(v,v)>=0`.  The sign needed by Weil is exactly the missing assertion
`epsilon_N>=0`.

## Failure of the asserted sum of squares

The claimed Theorem 2 writes

```text
QW^N_lambda(g*g#)=sum_k |g_tilde(rho_k)|^2 >= 0.       (3)
```

No such identity for the unshifted restricted Weil form appears in CCM Theorem 1.1, Theorem 3.6,
or its regularized-determinant theorem.  CCM proves that, under simple-evenness, the Fourier
transform of one lowest-eigenvalue eigenvector is entire, has real zeros, and is a regularized
determinant of a self-adjoint rank-one perturbation.  Real zeros of that one transform do not
diagonalize `QW^N_lambda`, remove `epsilon_N`, or turn the original form into `(3)`.

CCM's abstract and Section 8 explicitly state that rigorous convergence of these spectra or
normalized determinants is still missing and would establish RH.  The six-page manuscript does
not supply that convergence or an alternative proof of the finite-form sign.

## Why compact support does not close the gap

For compactly supported multiplicative test data, only finitely many prime powers occur in the
finite-place part of the explicit formula.  Once a place set and geometric aperture contain those
prime powers, those arithmetic summands stabilize exactly.  This valid observation does not imply
any of the following:

```text
epsilon_N >= 0;
simple-evenness of the actual restricted Weil ground state;
convergence in the closed Weil-form topology;
local uniform convergence of the ground-state transforms to Xi;
positivity of an archimedean-plus-polar compressed form.
```

The manuscript's appeal to Fejér convergence is also insufficient: uniform convergence on the
support controls finitely many point samples, not the archimedean distributional form or the
Galerkin ground-state projection.  Its place-exhaustion step merely preserves positivity if each
semilocal form was already positive; that premise is precisely what `(2)` fails to establish.

## No-go closure

- **Exact killing theorem/mechanism:** subtracting the lowest eigenvalue makes a finite Hermitian
  form positive semidefinite without making the original form nonnegative.  Self-adjointness and
  real zeros of the associated ground-state transform therefore carry no sign for the unshifted
  Weil form.  The cited theorem additionally assumes, rather than proves, simple-evenness.
- **Strongest positive survivor:** compact multiplicative support makes every finite-place prime
  contribution eventually exact.  Thus no uniformity over test functions is needed *after* actual
  finite-form nonnegativity has been proved.  The only surviving completion route is a true
  cofinal spectral-floor theorem or divisor-preserving locally uniform determinant convergence.
- **New insight:** “weak pointwise convergence suffices” is logically correct but analytically
  irrelevant until the scalar floor is controlled.  The omitted number `epsilon_N` is not an error
  term; its cofinal nonnegativity/vanishing is the RH-bearing quantity.
- **Status:** source claim falsified by direct comparison with CCM Theorem 1.1 and Section 8.
  Existing Lean theorem `rayleighQuotient_add_real_smul_id` in
  `formal/GaloisForLFunctions/RHTower/RayleighScalarShift.lean` verifies exact scalar-shift
  behavior.  Existing paper theorem `ccm-cofinal-weil-spectral-floor-criterion.md` proves that a
  cofinal true floor tending to zero already implies RH.  No new RH premise is discharged.

## Integrity note

The downloaded PDF's MD5 hash matches the Zenodo file record.  Its SHA-256 hash does not match the
SHA-256 string advertised in the record description.  This metadata discrepancy is independent of
the mathematical rejection above.

## Gates

- [x] primary PDF read in full
- [x] cited CCM theorem checked in primary source
- [x] omitted simple-even assumptions identified
- [x] shifted-versus-unshifted sign error identified
- [x] unsupported sum-of-squares identity identified
- [x] compact-support survivor extracted
- [x] existing Lean scalar-shift theorem located
- [x] route retired

## Log

- 2026-07-21 -- external RH claim audited and rejected; positive finite-place stabilization
  survivor retained, cofinal spectral-floor wall unchanged.
