# Route T source-ordered Borel--Laplace reconstruction

- **ID:** `T-C5a.5`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/route-t-required-residual-continuation.md · C5a.5
- **Statement:** Source ordering globally continues the local Wold residual Borel germ on its
  safe negative ray and its Laplace transform is exactly the corpus lower-Hardy residual.

## RH dependency chain

```text
source-marked local Borel germ [C5a]
  -> safe negative-ray continuation + exact lower-Hardy reconstruction [THIS CARD]
  -> positive-normal continuation and zero lateral Stokes jump [C5b OPEN]
  -> forced required residual regularity
  -> riemannHypothesis_iff_requiredResidualContinuation_continuousAt
  -> RH.
```

This card closes the Borel-to-physical weld. It does not assert upper continuation or zero Stokes
jump; those are exactly C5b.

## Corpus origin

The conjecture was forced by three existing Lean theorems:

- `summable_abs_xiHeatCassiniOrderedWoldResidual_mul_primeLogGap` supplies finite source
  variation;
- `norm_xiHeatCassiniOrderedPrimeNegativePhase_sub_succ_le` preserves one adjacent prime-log gap
  in the physical phase chord;
- the corpus `J₀/J₁` integral and derivative infrastructure makes the second-factorial kernel
  oscillatory and flat at the origin on the negative ray.

These inputs suggested preserving the source index through Borel continuation instead of taking
coefficientwise absolute values.

## Exact result

For `Phi(z)=sum_k z^k/(k!)^2`, the formalization proves

```text
Phi(-r)=J_0(2 sqrt r),
|Phi(-hs)-Phi(-Hs)| <= 2(H-h)s,
integral_0^infinity exp(-t) Phi(wt) dt = exp(w).
```

Consequently the source-ordered carrier

```text
B^-_x(s)=sum_N R_N
  (exp(-i h_N x) Phi(-h_N s)
   - exp(-i h_(N+1) x) Phi(-h_(N+1) s))
```

is absolutely source-summable for every `s>=0`, agrees with the original two-index Borel germ on
a nonzero initial segment, and satisfies for all `y>=0`

```text
integral_0^infinity exp(-t) B^-_x(yt) dt
  = xiHeatCassiniWoldResidualLowerHardyKernel(x-iy).
```

## Formal certificate

Modules:

- `formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelBessel.lean`
- `formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelLaplace.lean`
- `formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelSourceLaplace.lean`

Principal declarations:

- `secondFactorialBorelKernel_neg_real_eq_besselJ0`
- `norm_secondFactorialBorelKernel_neg_mul_sub_le`
- `integral_secondFactorialBorelKernel_eq_exp`
- `exists_radius_xiHeatCassiniWoldResidualBorelCarrier_lowerRay_eq_sourceCarrier`
- `integral_exp_neg_mul_xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier_eq_lowerHardy`

Direct `lake env lean` checks and targeted module builds pass. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`. Final module is wired into the RHTower umbrella;
no umbrella build was run.

## Novelty status

`[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` Internal corpus and primary-literature audit found no prior
source-ordered Wold prime-edge Borel continuation, Bessel adjacent-height gap law used for this
carrier, or exact Wold lower-Hardy Borel--Laplace reconstruction. External expert review remains
required before publication.

## Remaining open core

C5b: continue the same germ through the positive normal direction, construct both source-faithful
lateral sums, and prove their Stokes jump vanishes. Off line, corpus residue theorems predict a
nonzero jump carrying exact Wold multiplicity, so this is an RH-strength obstruction rather than
missing infrastructure.

## Log

- 2026-08-29 — paper proof completed; three Lean modules, targeted builds, and axiom audit passed
