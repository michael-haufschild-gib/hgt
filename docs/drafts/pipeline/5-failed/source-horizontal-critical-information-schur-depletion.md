# Critical information Schur depletion

- **ID:** source-horizontal-critical-information-schur-depletion
- **Stage:** 5-failed
- **Type:** FAILED CONJECTURE / FORMAL POSITIVE SURVIVOR
- **Source:** `source-horizontal-stokes-conditioned-information-coenergy.md`; P-G71 squared Stokes carrier; P-G72 critical mass no-go
- **Statement:** Subtract the critical information coenergy coefficientwise from P-G71's raw squared Stokes carrier and test whether the residual is the missing positive reduced square-coordinate response.

## Frozen claim

For `pk=(p,e)`, put

```text
kappa(pk) = sourceHorizontalPrimeGeometricKLScaleTerm(p,e,1/4),
w(pk)     = gammaSewnMobiusApertureStokesReflectedWeight(1/2,pk),
d(pk)     = (2-kappa(pk)) w(pk).
```

Then `2w` is P-G71 raw squared mass, `kappa*w` is the new critical coenergy, and `d` is their
coefficient-faithful Schur depletion.  Conjecture C3 has two independent falsifiers:

1. `d(pk)>0` for every prime-power label and is summable;
2. total residual mass no longer violates P-G72's completed seam mass ceiling.

If (1) holds but (2) fails, scalar first-information depletion is formally retired and the
positive survivor is an exact lower bound on additional Gamma/polar Feshbach depletion required.

## Conjecture loop

### C3 — first information coenergy is the missing negative-central correction

**Status: FALSE; RETIRED UNCONDITIONALLY.** Lean proves `0<kappa(pk)<2` globally, hence `d(pk)>0`
on every prime-power label and `sum d(pk)<infinity`. Thus source-horizontal information depletion
is a genuine positive Schur survivor, not a sign error.

Mass adequacy fails sharply. A cubic virial bound gives `kappa<3/10` on `(2,0),(2,1),(3,0),(3,1)`.
Stronger rational contraction estimates prove their raw mass exceeds `63/1000`, so their depleted
mass alone exceeds `29/625`, while the whole completed seam mass is below `29/625`. Therefore even
this coefficient-faithful first negative channel leaves too much central mass.

## Open core

Closed. `GammaSewnMobiusApertureStokesCriticalInformationSchurDepletion.lean` proves both
falsifiers and the positive survivor. Any successful completion needs another strictly negative
central contribution beyond first information depletion. Fitted scaling remains forbidden.

Next route: non-diagonal Gamma Schur/Feshbach coupling acting before scalar label compression;
coefficientwise first-information subtraction is now a fully retired producer class.
