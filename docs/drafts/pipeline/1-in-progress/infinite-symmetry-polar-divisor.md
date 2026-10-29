# Infinite-symmetry continuation in positive genus: is the polar divisor constrained?

- **ID:** ISC-polar
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** docs/reports/review-2910/obstacles-summary.md §2.6 Q3 and §2.7 ("analytic continuation by infinite symmetry"); predecessor [ISC-cal](../5-failed/infinite-symmetry-continuation-calibration.md) (genus zero: blind).
- **Statement:** For affine \(A_1\) Eisenstein data over a curve datum, decide whether any structure available without RH constrains where the zeta-zero hyperplanes of the polar divisor may lie.

## Goal

The route needs a theorem that the polar divisor of the continued affine constant term, in a region reached without RH, contains only hyperplanes of on-line type. Over \(\mathbb F_q\) a yes would re-prove RH for a curve by holomorphy; that is the calibration. A no retires the route with a precise reason.

## Gates
- [x] 0 → 1  in-progress: object fixed (affine \(A_1\) Weyl sum with Gindikin–Karpelevich coefficients over a curve datum, level-four slice, degree rotation), attack = fake-datum calibration plus chamber analysis.
- [ ] 1 → 2  fully-proven: verdict with paper proof.
- [ ] 2 → 3  formalized: survivors in `RHTower/InfiniteSymmetry/`.

## Approach

1. Generalize the corpus's exact pole-survival theorem (actual curve over \(\mathbb F_3\)) to every curve datum with zeros in the open critical strip, including the impure golden datum.
2. Receiver form: the polar divisor of the continued sum in \(-1<\operatorname{Re}s<0\) is exactly the shifted zero set; unitarity of the datum is equivalent to the polar divisor lying on \(\operatorname{Re}s=-1/2\).
3. Chamber law: positive real roots pair with the closed positive chamber in real part \(\ge0\); zero hyperplanes have real part \(\operatorname{Re}\rho-1<0\); the zero-free set certified by holomorphy on the closed chamber is \(\{\operatorname{Re}\rho\ge1\}\).
4. Literature: Garland's minimal-parabolic continuation (meromorphic, wall); Garland–Miller–Patnaik entirety of cuspidal series (arXiv 1304.4913), Braverman–Kazhdan finiteness over function fields; the L-functions sit in the negative series \(E^-\) with \(E=\Xi E^-\), whose continuation is open.

## Log
- 2026-10-29 — created; literature intake (GMP abstract and §1.3); plan fixed.
