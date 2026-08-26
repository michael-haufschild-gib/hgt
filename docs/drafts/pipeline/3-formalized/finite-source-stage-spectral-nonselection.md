# Finite Source Stage Spectral Nonselection

- **ID:** finite-source-stage-spectral-nonselection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** actual theta-stage Green-neutrality frontier
- **Statement:** Traceless finite-support kernels with a nonreal ordinary Fredholm divisor are Hilbert--Schmidt dense around every Hilbert--Schmidt source kernel on an infinite coordinate carrier.

## Goal

Decide whether finite support, exact trace cancellation, and Hilbert--Schmidt approximation can
select real finite divisors near nonzero source operators. Door passport: source-pure; no Xi zero,
divisor enumeration, or zero-location premise enters.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, explicit fresh-coordinate microblock attack
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `exists_finiteSupport_traceZero_nonrealDivisor_close`, targeted build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Approximate arbitrary Hilbert--Schmidt target `K` within `epsilon/2` by a traceless kernel `T`
supported on finite `s`. Choose fresh coordinates `a,b` outside `s` and add the isolated diagonal
pair `ir,-ir`, with `r=epsilon/8`. Disjoint support preserves trace zero. Its Hilbert--Schmidt norm
is `sqrt(2 r^2) <= 2r < epsilon/2`, so the enlarged kernel remains within `epsilon` of `K`.

At `z=-i/r`, the `a` column of `1-zK'` is identically zero: the old block has no `a` coordinate,
the new block is diagonal, and `1-z(ir)=0`. Hence the ordinary determinant vanishes at a point with
nonzero imaginary part.

`[PROVED HERE]` Applying this theorem to `-thetaKernelMatrix` at accuracy `1/(k+1)` proves that every
current `ThetaSourceSignedApproximationProperty k` fibre contains an admissible stage with a
nonreal divisor.

## No-go closure

- **Exact killing theorem/mechanism:** `thetaSourceSignedApproximationProperty_spectrally_nonselective`; finite support, Hilbert--Schmidt regularity, approximation accuracy, and exact trace zero admit a nonreal divisor at every stage accuracy.
- **Strongest positive survivor:** Arbitrary-target density theorem with explicit isolated bad divisor, plus source-specific application to every theta approximation fibre.
- **New insight:** Current stage specification is spectrally nonselective around the actual nonzero theta source, not merely at the zero kernel. Required arithmetic flag or modewise boundary law must be recorded in replacement stage data and proved stable under completion.
- **Status:** Internal corpus had only zero-target microblocks. External Hedenmalm audit supplies fixed source/determinant framework but no arbitrary-target finite-stage selection theorem. Paper proof dependency-closed; Lean modules `GaloisForLFunctions.HTGeometry.TraceZeroNonrealDivisorDensity` and `GaloisForLFunctions.RHTower.HedenmalmThetaAdmissibleStageSpectralNonselection`.

## Log

- 2026-08-26 — trace-zero and fixed-metric conjectures falsified.
- 2026-08-26 — arbitrary-target fresh-coordinate theorem paper-proved and formalized; card advanced to Stage 3.
