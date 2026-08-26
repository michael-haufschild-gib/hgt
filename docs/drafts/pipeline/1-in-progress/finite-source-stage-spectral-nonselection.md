# Finite Source Stage Spectral Nonselection

- **ID:** finite-source-stage-spectral-nonselection
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** actual theta-stage Green-neutrality frontier
- **Statement:** Traceless finite-support kernels with a nonreal ordinary Fredholm divisor are Hilbert--Schmidt dense around every Hilbert--Schmidt source kernel on an infinite coordinate carrier.

## Goal

Decide whether finite support, exact trace cancellation, and Hilbert--Schmidt approximation can
select real finite divisors near nonzero source operators. Door passport: source-pure; no Xi zero,
divisor enumeration, or zero-location premise enters.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, explicit fresh-coordinate microblock attack
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `exists_finiteSupport_traceZero_nonrealDivisor_close`, targeted build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Approximate arbitrary Hilbert--Schmidt target by a traceless kernel on finite support `s`. Choose
two fresh coordinates outside `s`, add isolated diagonal eigenvalues `ia` and `-ia`, and take `a`
small. Disjoint support preserves exact trace zero and factors a nonreal divisor into the enlarged
ordinary determinant, while triangle inequality makes total Hilbert--Schmidt error arbitrary.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** Pending proof of density theorem.
- **Strongest positive survivor:** Pending.
- **New insight:** Pending.
- **Status:** Internal corpus audit found only zero-target microblock theorem, not arbitrary-target density.

## Log

- 2026-08-26 — created in 1-in-progress after trace-zero and fixed-metric conjectures failed.
