# Exact type of the fixed-to-co-moving Xi prime aperture gap

- **ID:** mass-xi-prime-aperture-gap-type
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../../reports/mass-shifted-spectral-trace-route.md · §9.3 Exact open core
- **Statement:** Subtracting the uniformly bounded prime source at mass `|u|+2` from any fixed legal mass source preserves exactly the fixed mass displacement exponent; bounded aperture gap is equivalent to RH.

## Goal

Remove the universal bounded bulk supplied by the co-moving cone and identify the exact transverse
mass-aperture observable that still carries RH-strength growth.  This is a source-side high-pass
classification, not a claim that the remaining gap is bounded.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean capstone, targeted build green, axiom audit PASS
- [ ] 3 → 4  publication-ready

## Exact claim C14

For fixed legal `1/2<c<a`, `sigma>1/2`, and `lambda≥0`, define

`Gap(u) = P_(a,c)(sigma+iu) - P_(|u|+2,1)(sigma+iu)`.

Then

`Gap(u) = O(exp(lambda |u|))`

if and only if

`|Im (xiMassFamily a).pt q| ≤ lambda` for every Xi divisor copy `q`.

At `lambda=0`, boundedness of `Gap` is equivalent to RH.

## Approach

The co-moving theorem supplies an explicit constant `D_sigma` with
`|P_(|u|+2,1)(sigma+iu)|≤D_sigma`.  Since `exp(lambda|u|)≥1`, that term belongs to every
nonnegative exponential growth class.  Triangle inequalities in both directions show that `Gap`
and fixed `P_(a,c)` have the same growth class.  Apply the existing exact fixed-source type law.

## Hostile audit

- No boundedness conclusion is claimed for the gap.
- Subtracted term is a literal legal von-Mangoldt integral with an unconditional explicit bound.
- Result is graded for every nonnegative exponent, not only a renamed Boolean RH equivalence.
- Transverse-shift aperture corpus was audited: it proves prime-jet independence and zero-strip
  threshold laws, but no global Bessel-mass source bound or collision with C14.
- The theorem isolates one new target: arithmetic control of a transverse Bessel aperture
  difference, equivalently a finite mass high-pass.

## Complete paper proof `[PROVED HERE]`

Let

`D_sigma = ‖pi i‖ xiPoissonTraceReal(sigma-1/2) + B(2,sigma)`.

The co-moving prime theorem gives `|P_moving(u)|≤D_sigma` for every real `u`.  If `lambda≥0`, put
`E(u)=exp(lambda|u|)`.  Then `E(u)≥1`, hence `D_sigma≤D_sigma E(u)`.

Suppose first that `|Gap(u)|≤C E(u)`.  Since `P_fixed=Gap+P_moving`,

`|P_fixed(u)|≤|Gap(u)|+|P_moving(u)|`

`≤C E(u)+D_sigma≤(C+D_sigma)E(u)`.

Conversely, if `|P_fixed(u)|≤C E(u)`, then

`|Gap(u)|≤|P_fixed(u)|+|P_moving(u)|≤(C+D_sigma)E(u)`.

Thus the gap and fixed source belong to exactly the same nonnegative exponential growth classes.
The already dependency-closed fixed-source type theorem identifies those classes with the bound
`|Im m_a(q)|≤lambda` for every divisor copy.  Setting `lambda=0` identifies bounded gap with fixed
prime boundedness, which the exact prime open-core theorem identifies with RH. ∎

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.XiMassPrimeApertureGap`.
- Gap definition: `xiMassBottomPrimeApertureGap`.
- Growth preservation:
  `xiMassBottomPrimeApertureGapLineGrowth_iff_primeLineGrowth`.
- Exact graded type:
  `xiMassBottomPrimeApertureGapLineGrowth_iff_mass_displacement_le`.
- RH capstone: `riemannHypothesis_iff_xiMassBottomPrimeApertureGapLineBound`.
- `lake env lean GaloisForLFunctions/RHTower/XiMassPrimeApertureGap.lean` — PASS.
- `lake build GaloisForLFunctions.RHTower.XiMassPrimeApertureGap` — PASS (`9389/9389`).
- `#print axioms` on all capstones — only `propext`, `Classical.choice`, `Quot.sound`.
- Module wired into `GaloisForLFunctions.RHTower` umbrella.

## Log

- 2026-08-05 — C14 frozen after co-moving countermodel and transverse-aperture corpus audit.
- 2026-08-05 — paper proof closed and unconditional Lean module passed direct check, targeted build,
  and axiom audit.
