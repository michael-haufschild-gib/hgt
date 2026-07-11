# The reflected digamma anomaly is real exactly on the critical line

- **ID:** `reflected-digamma-anomaly-reality-selector`
- **Stage:** 3-formalized
- **Type:** THEOREM; archimedean superspace selector
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `GaloisForLFunctions/ReflectedDigammaAnomaly.lean`
- **Statement:** If `0<sigma<1` and `t>0`, then

```text
Im(psi(sigma+it)+psi(1-sigma-it))=0
  iff
sigma=1/2.
```

## Proof

For `sigma>=0` and `t>0`, the digamma recurrence and its far-field anchor give

```text
Im psi(sigma+it)
  = sum_(n>=0) t/((sigma+n)^2+t^2).                    (1)
```

Every summand in `(1)` is strictly decreasing in `sigma`.  More quantitatively, if
`0<=sigma<tau`, every finite partial-sum difference is at most its strictly negative `n=0`
term,

```text
t/(tau^2+t^2)-t/(sigma^2+t^2)<0.
```

Passing to the limit proves

```text
Im psi(tau+it)<Im psi(sigma+it).                       (2)
```

Digamma respects complex conjugation, so

```text
Im(psi(sigma+it)+psi(1-sigma-it))
  = Im psi(sigma+it)-Im psi(1-sigma+it).               (3)
```

Strict injectivity in `(2)` makes `(3)` vanish exactly when `sigma=1-sigma`, equivalently
`sigma=1/2`.  QED.

The negative-height case follows by conjugation.  Height zero is deliberately excluded: digamma is
real across the entire real interval `(0,1)`, so reality does not select the line there.

## Meaning for the reflected bi-heat pairing

The universal finite-part term of the reflected bi-heat pairing contains

```text
-psi(z)-psi(1-z).
```

This theorem proves that at nonzero height its imaginary anomaly vanishes exactly at the
self-dual scale.  The archimedean inner metric therefore has a faithful pointwise critical-line
selector.

It does not prove RH.  Nothing currently forces the finite-part pairing attached to a hypothetical
off-line zeta zero to be real.  Imposing reality at every zero is another RH-equivalent source
condition unless an independent physical or arithmetic constraint produces it.

## Lean surface

The formal module proves, without axioms or analytic placeholders:

- `tendsto_verticalDigammaIm_partialSums`;
- `verticalDigammaIm_strictAnti`;
- `digamma_conj`;
- `anomaly_im_eq_sub`; and
- `anomaly_im_eq_zero_iff`.

The proof reuses the already formalized digamma recurrence and far-field anchor but adds the strict
horizontal monotonicity and exact anomaly-reality selector.  The full reflected bi-heat expansion
is not claimed formalized because the current tree has no polylogarithm boundary finite-part API.

## Novelty verdict

The theorem is a direct consequence of the classical digamma partial-fraction series and strict
termwise monotonicity.  Its superspace interpretation is useful, but the parent mechanism is
routine; Lean verification does not change that classification.

## Gates

- [x] paper proof complete
- [x] strict monotonicity formalized
- [x] digamma conjugation formalized
- [x] critical-line reality equivalence formalized
- [x] no hidden `sorry`, `axiom`, or placeholder analytic interface

