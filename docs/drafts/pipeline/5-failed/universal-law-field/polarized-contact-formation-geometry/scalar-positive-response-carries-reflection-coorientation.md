# Scalar positive response carries reflection coorientation

- **ID:** ULF-PCFG-FAIL-1
- **Stage:** 5-failed
- **Type:** FALSIFIED FIELD MECHANISM / POSITIVE SURVIVOR EXTRACTED
- **Statement:** The conjecture that an analytic scalar square root of every even positive response
  provides a reflection-separating source coordinate is false exactly at odd half-order.

## Failed conjecture

Given an even nonnegative analytic response `I`, take an analytic signed square root `q` and its
primitive

```text
Theta(t)=integral_0^t q(s) ds.
```

It was conjectured that `Theta` always supplies the missing oriented source coordinate while
retaining the scalar positive metric `I=Theta'^2`.

## Exact failure

If `nu(I)=2k`, every analytic square root has parity `(-1)^k`. For odd `k`, every square root is
odd and every primitive is even:

```text
Theta(t)=Theta(-t).
```

The scalar analytic realization therefore folds the two reflection sides. Choosing the unsigned
square root and signed arclength separates them only at the price of losing `C^(k+1)` regularity.
The Wold response has `k=1`, so the failure occurs at the first nontrivial source contact.

## No-go closure

- **Exact killing theorem/mechanism:** Half-order parity controls the parity of every analytic
  scalar square root. Odd half-order forces an even primitive and exact reflection folding.
- **Strongest positive survivor:** Minimal analytic reflection-oriented realization rank is one for
  even half-order and two for odd half-order. The explicit rank-two velocity
  `q(t)(cos t,sin t)` retains the same positive response and separates the source sides. Common
  recovery cannot reduce this minimum or restore a missing sign channel.
- **New insight:** Positive response is not merely phase-blind. Its contact parity determines the
  least symmetry representation needed to lift it without folding. For Wold contact two, the
  functional-equation double is minimal rather than decorative.
- **Status:** Dependency-closed paper theorem ULF-PCFG-2; `[LEAN PENDING]`. The failed route remains
  open at the formal no-go-closure gate until that survivor is Lean-certified.

## Representation lesson

The defect is not repaired by adding a better scalar function. The carrier must change from a
scalar square root to an equivariant vector polarization containing both trivial and sign channels.
This is a change of primitive, not an exception added to the scalar model.

## Log

- 2026-08-12 -- scalar square-root/arclength conjecture frozen.
- 2026-08-12 -- killed by odd half-order parity; exact rank-two survivor promoted to Stage 2.
