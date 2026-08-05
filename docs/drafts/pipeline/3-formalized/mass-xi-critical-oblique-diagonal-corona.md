# Mass-Xi critical oblique diagonal corona

- **Stage:** 3 — formalised in Lean 4
- **Date opened:** 2026-08-05
- **Parent:** `mass-xi-oblique-comoving-phase-transition`
- **Target:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3

## Frozen conjecture C20

Let `F` be an admissible abstract spectral family.  Put `A=a-1/2` and
write an original point as `R+iJ`, with mass image `M+iK`.  On the exact
critical wall

\[
 a\ge2,\qquad v>0,\qquad v|u|\le A,
 \qquad \sigma>0,\qquad 4\sigma v=1,
\]

the lost exponential rate is replaced by a diagonal large-deviation defect:

\[
 M(-\sigma M+uK)
 \le -\sigma\big((A-R)^2+A\big).
\]

Define the finite moving corona

\[
 \mathcal C_a(F)=\{i:A/2\le \operatorname{Re}p_i\le2A\}.
\]

Then the complete mass trace equals its finite corona sum modulo an
exponentially small tail:

\[
 \left\|\Theta_F^{(a)}(\sigma+iu)
       -\sum_{i\in\mathcal C_a(F)}e^{-(\sigma+iu)m_a(p_i)}\right\|
 \le e^{-\sigma A/12}\Theta_F(\sigma/12).
\]

For `a=v|u|+2` in the Xi family, transfer this exact localization through
the Gamma/source identity.  The literal von-Mangoldt source must equal one
finite cofinal Xi-corona observable modulo two explicit exponentially small
remainders.

## Why this is the critical survivor

The open chamber `4 sigma v>1` is exponentially blind.  At equality, only
spectral heights comparable to aperture can avoid exponential absorption.
This is neither a finite jet nor a fixed compact window: it is a moving,
cofinal packet.  The conjecture classifies the first scale on which adaptive
mass can retain information and identifies the exact remaining cancellation
object.

## Proof plan

1. Strengthen mass geometry to
   `A^2 + R^2 + A <= M^2` using `|J|<1/2`.
2. Use `MK=RJ`, the critical identity, and the cone to prove the displayed
   diagonal defect.
3. Outside `[A/2,2A]`, use `M<=R+a` to derive
   `-sigma M+uK <= -(sigma/12)(A+R)`.
4. Split the absolutely convergent trace over the finite corona and its
   complement; sum the tail against `traceReal (sigma/12)`.
5. Apply the exact Xi source identity and Gamma mass-gap law with
   `delta=sigma/2`.

## Hostile checks

- The theorem must retain the finite cofinal corona; deleting it would assert
  critical extinction and is false in the balanced `R~A`, `|J|~1/2` regime.
- No boundedness, RH, zero-free, cancellation, or counting hypothesis may
  enter the Lean proof.
- All tail rates and corona endpoints are explicit.

## Status

Fully proved unconditionally and formalised in Lean 4.

Universal module:

- `formal/GaloisForLFunctions/HTGeometry/AbstractSpectralCriticalDiagonalCorona.lean`

Xi transfer module:

- `formal/GaloisForLFunctions/RHTower/XiMassCriticalDiagonalPrimeCorona.lean`

Principal declarations:

- `sq_sub_half_add_sq_re_add_sub_half_le_sq_mass_re`
- `critical_mass_phase_defect`
- `critical_mass_phase_le_outside_corona`
- `norm_mass_traceC_sub_criticalDiagonalCoronaTraceC_le`
- `norm_xiMassBottomPrimeIntegral_sub_criticalPrimeCoronaModel_le`
- `norm_xiMassBottomPrimeIntegral_critical_le_coronaCard_add_tails`

Verification:

- `lake env lean` passes for both modules;
- targeted builds pass: `2752/2752` and, through the sharp counting successor, `9422/9422`;
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
