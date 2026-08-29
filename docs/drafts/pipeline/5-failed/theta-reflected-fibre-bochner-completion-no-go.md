# Reflected-fibre Bochner completion no-go

- **ID:** S6F-RFPD-NG
- **Stage:** 5-failed
- **Type:** FALSIFIED (diagnostic computation; analytic/Lean no-go open)
- **Source:** `../1-in-progress/theta-rank-three-direct-parabolic-determinant.md`
- **Statement:** Completed-theta reflected fibres are not globally positive definite, so Bochner
  cannot supply an all-order positive moment completion of native D1.

## Goal

Test whether

```text
g_x(t) = Phi(x+t) Phi(x-t) / Phi(x)^2
```

is positive definite for each missing-orbit center. This would imply all signed even local Hankel
determinants and replace direct rank-three analysis by an all-order measure representation.

## Gates

- [x] 0 → 1 in-progress: source-pure reflected fibre and finite Gram falsifier specified
- [ ] 1 → 2 fully-proven: replace high-precision six-point witness by analytic strict sign proof
- [ ] 2 → 3 formalized: unconditional concrete six-point no-go theorem
- [ ] 3 → 4 publication-ready: integrate exact no-go and finite-order survivor

## No-go closure

- **Exact killing mechanism:** Across every one of 142 tested physical centers, the cosine
  transform and an equispaced Toeplitz section become negative. At seam, a six-point section at
  rational spacing `1/50` is negative at 100 digits, while corresponding sizes four and five are
  positive. Report:
  `../2-fully-proven/computations/2026-08-29-reflected-fibre-positive-definite/REPORT.md`.
- **Strongest positive survivor:** `[CONJECTURE]` reflected fibres are positive definite of order
  five on the physical center interval. Two independent arbitrary-packet campaigns totaling
  21.12 million 4/5-point matrices found no high-precision counterexample. This survivor is
  nontrivial because five-point reflection-even coalescence produces native rank-three D1.
- **New insight:** Global translation-invariant measure representation fails one packet order after
  the native rank-three cusp. Direct D1 or finite-order-5 positivity is the correct scope; TP-infinity
  and all-order Bochner completion are too strong.
- **Status:** Full-PD claim is computationally falsified only. No numerical output is admissible in
  Lean. Finite-order survivor has neither paper proof nor Lean theorem, so no formalization is due
  yet under dependency-closure discipline.

## Log

- 2026-08-29 — six-point Toeplitz and negative-transform mechanisms found; order-five survivor
  survived hostile arbitrary-packet search.
