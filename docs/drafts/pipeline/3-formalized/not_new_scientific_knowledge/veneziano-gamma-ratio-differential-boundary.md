# Veneziano Gamma-ratio differential boundary

- **ID:** `veneziano-gamma-ratio-differential-boundary`
- **Stage:** 3-formalized
- **Type:** EXACT SCATTERING VALUE RELATION / GAMMA-ORBIT SPECIALIZATION
- **Scientific status:** `[KNOWN CONSEQUENCE] [LEAN-FORMALIZED] [PHYSICS APPLICATION]`
- **Formal module:**
  `formal/GaloisForLFunctions/HTGeometry/VenezianoGammaRatioBoundary.lean`

## Exact theorem

Define the genuine global meromorphic element

```text
V_red(z;a,b) = Gamma(z+a) / Gamma(z+a+b).
```

Then, over the rational differential field `C(z)`, Lean proves

```text
V_red(-;a,b) is differentially algebraic
  <=> exists k in Z, b=k,

V_red(-;a,b) is hypertranscendental
  <=> for every k in Z, b!=k.
```

Declarations:

- `reducedVenezianoAmplitudeMero`;
- `reducedVenezianoAmplitudeMero_natShift`;
- `reducedVenezianoAmplitudeMero_negSuccShift`;
- `differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift`;
- `hypertranscendentalOver_reducedVenezianoAmplitudeMero_iff_nonintegerShift`.

At nonnegative integer separation, the ratio is the inverse Pochhammer rational factor.  At
negative integer separation, it is a Pochhammer rational factor.  At noninteger separation, the
two Gamma factors lie on distinct translation orbits with charges `+1` and `-1`; the existing
meromorphic Gamma superselection theorem forces HT.

## Scattering interpretation

The Euler beta factor is

```text
B(x,b)=Gamma(x) Gamma(b) / Gamma(x+b).
```

For fixed `b` away from a Gamma pole, `Gamma(b)` is a nonzero constant in the variable `x`, so it
does not change the DA/HT classification.  The theorem therefore classifies the variable-channel
beta factor used by Veneziano/open-string four-point amplitudes.

This also applies to beta-function Regge amplitudes used as models of strong-interaction hadron
scattering.  It does not assert that a full interacting QCD amplitude is a beta function.

Physics provenance:

- C. Cheung and G. N. Remmen, *Veneziano Variations: How Unique are String Amplitudes?*,
  arXiv:2210.12163, treats the Veneziano amplitude as the benchmark four-point string amplitude.
- G. Veneziano, S. Yankielowicz, and E. Onofri, *A model for pion-pion scattering in large-N QCD*,
  arXiv:1701.06315, uses Veneziano/Lovelace--Shapiro-type Regge amplitudes as large-`N` QCD models.

## Clock/observability statement

The same two Gamma factors can cancel their HT source only when the observer identifies their
arguments on one integer translation orbit.  The integer channel condition is therefore an
observability congruence.  Generic noninteger separation leaves two visible orbit charges and the
ratio remains HT.  No time evolution is used.

## Positive residue of the cancellation no-go

```text
[NO-GO]
A ratio of two HT Gamma factors is necessarily HT.

[POSITIVE THEOREM]
The ratio is DA exactly when the two factors occupy the same integer orbit; otherwise it is HT.
```

This is more informative than a closure statement because it computes the exact cancellation
locus.

## RH pressure test

The theorem does not constrain zeros of zeta and has no direct RH implication.  It strengthens the
Gamma-facing corpus by giving a concrete two-factor specialization of orbit-charge
superselection.  For completed `L`-function factors, it warns that equal total exponent is not
enough: cancellation is orbitwise.  RHTower still needs an arithmetic source theorem and a
critical-line orientation mechanism.

## Verification

The exact module build and direct Lean check passed.  The exact DA and HT equivalences depend only
on `propext`, `Classical.choice`, and `Quot.sound`.
