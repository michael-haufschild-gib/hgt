# Xi endpoint completed-value bound

- **ID:** `xi-endpoint-completed-value-bound`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / VALUE-RELATION BRIDGE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/XiEndpointCompletedValueBound.lean`
- **Statement:** The endpoint curvature is the explicit completed source value
  \[
  C_\Xi:=\operatorname{xiEndpointCompletedCurvature}
  =2+\gamma-\log(4\pi)<\frac12,
  \]
  so the source-only endpoint norm hypothesis is unconditional and
  \[
  E_\Xi<C_\Xi,
  \qquad
  M_\Xi\le \frac32 C_\Xi.
  \]

## Goal

Remove the scalar hypothesis `xiEndpointCompletedCurvature < 1` from the
endpoint reflection-defect budget.  This is a top-down discharge below the
sharp capstone

\[
M_\Xi\le C_\Xi\iff\mathrm{RH}.
\]

The theorem does not establish the sharp coefficient.  It narrows the
remaining source estimate from an unspecified finite factor to the explicit
gap

\[
M_\Xi\le \frac32 C_\Xi
\quad\longrightarrow\quad
[\text{OPEN: improve }3/2\text{ to }1]
\quad\longrightarrow\quad
\mathrm{RH}.
\]

## Exact value relation

Mathlib proves the pole-subtracted completed-zeta value

\[
\Lambda_0(1)
=1+\frac{\gamma-\log(4\pi)}2.
\]

The completed functional equation `Lambda_0(1-s)=Lambda_0(s)` gives the same
value at zero.  The formal endpoint identity already present in the corpus is

\[
C_\Xi=2\operatorname{Re}\Lambda_0(0).
\]

Combining the two equalities yields

\[
C_\Xi=2+\gamma-\log(4\pi).
\]

This is the classical Laurent constant of the completed zeta function, not a
zero-divisor input.  The Laurent expansion and completed product are standard;
see [DLMF §25.2](https://dlmf.nist.gov/25.2).

## Rational bound

The proof uses only formal inequalities already available in Mathlib:

\[
\gamma<\frac23,
\qquad
e<2.72,
\qquad
3<\pi.
\]

First,

\[
e^2<8,
\qquad
e^{1/6}\le \frac1{1-1/6}=\frac65,
\]

so

\[
e^{13/6}=e^2e^{1/6}<8\cdot\frac65<4\pi.
\]

Hence `13/6 < log(4*pi)`, and therefore

\[
\operatorname{Re}\Lambda_0(0)
=1+\frac{\gamma-\log(4\pi)}2<\frac14,
\qquad
C_\Xi<\frac12.
\]

No decimal evaluation of the completed value occurs in the proof.

## Budget discharge

The existing source-only estimate states

\[
E_\Xi
\le \frac{C_\Xi}{1-C_\Xi}C_\Xi.
\]

The existing infinite-divisor theorem also gives `0 < C_Xi`.  Since
`0 < C_Xi < 1/2`, the prefactor is strictly smaller than one, so

\[
E_\Xi<C_\Xi.
\]

The exact identity

\[
E_\Xi=2(M_\Xi-C_\Xi)
\]

then gives

\[
M_\Xi\le\frac32C_\Xi.
\]

The result is source-pure: it uses the functional equation, the completed
Laurent value, and the already formalized endpoint sum identity.  It assumes
neither RH, Xi zero locations, real-rootedness, nor an RH-equivalent limiting
measure.

## Lean certificate

The public declarations are:

```text
completedRiemannZeta₀_zero_eq_eulerMascheroni_log
completedRiemannZeta₀_zero_re_eq_eulerMascheroni_log
thirteen_div_six_lt_log_four_mul_pi
completedRiemannZeta₀_zero_re_lt_one_fourth
xiEndpointCompletedCurvature_eq_eulerMascheroni_log
xiEndpointCompletedCurvature_lt_one_half
xiEndpointCompletedCurvature_pos
xiEndpointCompletedCurvature_lt_one
xiEndpointDefectEnergy_le_unconditional_source_factor
xiEndpointSourceDefectFactor_lt_one
xiRawMass_le_unconditional_source_only_factor
xiEndpointReflectionDefectEnergy_le_endpointCurvature
xiEndpointReflectionDefectEnergy_lt_endpointCurvature
xiRawReciprocalHermitianMass_le_three_halves_mul_endpointCurvature
```

The module is imported by `GaloisForLFunctions.RHTower` and therefore by the
package root through `GaloisForLFunctions.MainTheorems`.

## Gates

- [x] 0 → 1 in-progress: source-pure value relation and target capstone identified
- [x] 1 → 2 fully-proven: exact proof from the completed functional equation and Laurent constant
- [x] 2 → 3 formalized: Lean module builds without placeholders and is umbrella-wired
- [ ] 3 → 4 publication-ready: not proposed; this is a classical bridge theorem
