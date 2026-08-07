# Burnol Cartier head-energy Stokes flux

- **ID:** `burnol-cartier-head-energy-stokes-flux`
- **Stage:** 3 — formalized in Lean 4
- **Route:** R
- **Scientific status:** `[PAPER-PROVED SURVIVOR] [LEAN-PROVED]`
- **Open producer:** nonpositivity of one oriented divided-shift head flux from pre-divisor
  Euler--Gamma--Stokes structure.

## Frontier

Current endpoint asks for fixed two-head non-amplification

```text
E_(1/2)(U_rho f0) <= E_(1/2)(f0)
```

at every hypothetical right-half Xi divisor.  Directly proving this after Cartier transfer still
hides source orientation inside a positive quadratic expression.  Exact polarization instead
shows that its defect is horizontal displacement times one signed current formed *before* Cartier
transfer.

Write

```text
T_rho = burnolMellinDividedShift rho
U_rho = 1 - 2 (Re rho - 1/2) T_rho
h(f)   = burnolSoninForwardHeadCoefficient (1/2) f
C      = soninCosineUnitary
J(f)   = |h(f)|^2 - |h(C f)|^2.
```

For the fixed co-Poisson atom `f0`, the already proved divided-shift heads are

```text
h(T_rho f0)   = (1-rho)^(-1),
h(C T_rho f0) = -(log 2)/rho.
```

Hence

```text
J(T_rho f0) = |1-rho|^(-2) - (log 2)^2 |rho|^(-2).
```

## Exact transgression theorem

Let `sigma = Re rho`, `q = |rho|^2`, and `r = |1-rho|^2`.  The Cartier gains give

```text
E(U_rho f0) - E(f0)
  = q/r - 1 + (log 2)^2 (r/q - 1).
```

Since `q-r = 2 sigma - 1`, purely algebraic factorization yields

```text
E(U_rho f0) - E(f0)
  = (q-r) (1/r - (log 2)^2/q)
  = 2 (sigma - 1/2) J(T_rho f0).
```

This is an exact quadratic Stokes transgression, not an implication and not an assumed comparison.

At a right-half Xi divisor, `q > r > 0`.  Also `0 < log 2 < 1`, so

```text
J(T_rho f0)
  > 1/q - (log 2)^2/q
  = (1-(log 2)^2)/q
  > 0.
```

Because `2 (sigma-1/2) > 0`, fixed two-head non-amplification is equivalent, pointwise in the open
right half-plane, to

```text
J(T_rho f0) <= 0.
```

Thus the remaining producer no longer needs to compare `U_rho f0` with `f0`, preserve a full
metric, or conserve either head.  It must derive one oriented signed current inequality from the
Euler--Gamma--Stokes source.

## Conjecture / hostile-attack log

1. **Douglas contraction of co-Poisson channels.** `[FAILED — CIRCULAR]`  Existing Lean proves
   contractive factorization is equivalent to the desired nonpositive compressed holonomy.  It
   cannot independently produce the sign.
2. **Fourier-invariant Stokes trace.** `[FAILED — WRONG CARRIER]`  Existing parity theorem proves
   every Fourier-invariant linear reader annihilates the odd holonomy for all parameters.  It
   erases precisely the orientation needed to distinguish the critical line.
3. **Compact-window co-Poisson seed presentation of `U_rho f0`.** `[FAILED — UNAVAILABLE]`  The
   corpus proves extended-Sonin landing, but not membership in the compact-window source image.
   Assuming that source lift would reinsert the missing globalization theorem.
4. **Oriented pre-transfer head flux.** `[SURVIVES]`  Exact algebra above removes `U_rho` from the
   producer.  The signed difference is orientation-sensitive, fixed-aperture, coefficient-faithful,
   and strictly positive at every hypothetical right-half zero.

## Novelty audit

Internal corpus contains reciprocal Cartier head gains, strict two-head amplification, co-Poisson
reciprocal landing, and parity/Douglas no-go laws.  It does not contain the exact identity expressing
the transferred positive-energy defect as horizontal displacement times the oriented
divided-shift head current.

Burnol's primary co-Poisson and Sonine papers supply the reciprocal-source transform, constant-head
mechanism, and orthogonal-projection framework, but no fixed-atom Cartier energy transgression or
Euler--Gamma sign for this current:

- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, JTNB 16 (2004), DOI `10.5802/jtnb.434`.
- J.-F. Burnol, *Entrelacement de co-Poisson*, AIF 57 (2007), DOI `10.5802/aif.2268`.

## Lean target

New module should provide:

1. `burnolSoninOrientedGammaHeadFlux`;
2. exact divided-shift head and flux values;
3. strict positivity and a quantitative positive floor at right-half Xi divisors;
4. exact head-energy transgression;
5. equivalence between prior non-amplification producer and nonpositivity of this single current;
6. Route R endpoint from the flux producer.

No critical-line placement, RH, source sewing, head conservation, or metric comparison enters
these proofs.

## Lean formalization

Module `RHTower/BurnolCartierHeadEnergyStokesFlux.lean` proves all six targets above.  It is wired
into `GaloisForLFunctions/RHTower.lean`.  Targeted `lake env lean` and module build pass.  Audited
capstones use only the project baseline axioms `[propext, Classical.choice, Quot.sound]`.

## Remaining open core

Derive, before divisor placement, that the Euler--Gamma--Stokes image of the fixed source atom has
nonpositive oriented current

```text
J(T_rho f0) <= 0.
```

The present theorem proves this is exactly sufficient for the requested two-head inequality.  It
does not manufacture the sign from ambient isometry, Fourier parity, compact-window source
membership, or an RH-equivalent sewing assumption.
