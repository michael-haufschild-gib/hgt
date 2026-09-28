# HB literal finite-cutoff two-leg action transgression

- **ID:** hb-literal-finite-cutoff-two-leg-current
- **Stage:** 3-formalized
- **Type:** BRIDGE
- **Source:** HB literal cyclic Peierls realization; B2a on `../1-in-progress/hb-source-pole-frequency-defect-cochain.md`

## Exact statement

Fix the actual source `q`, reader `r`, branch, spectral parameter and amplitude
of `D4BMPhysicalModeAction`, a finite radial interval `[s,t]⊂(-∞,0)`, an angular
point `z`, and either original outer leg `o`.  Write

`J_o(u) = physicalProjectedModeAction ... o u z hz 1`,
`K_o(u) = physicalModeSourceContact ... o u`,
`N = modeAngularSquare (physicalModeAngularJet r z)`, and
`I_o = ∫[s,t] tortoiseMode o * continuedAngularSourceProjection`.

With `c = physicalAngularParameter(r)^2 - 1/4 - 2`, the literal
contact-renormalized current `R_o(u)=J_o(u)+K_o(u)N` satisfies

`R_o(t)-R_o(s) = -c I_o N`.

Consequently, for two outer legs `o₁,o₂`, the exact finite two-leg functional
`R_o₁-R_o₂` has increment `-c(I_o₁-I_o₂)N` and changes sign under
`o₁ ↔ o₂`.

## Dependency-closed paper proof

`physicalProjectedModeAction_transport` states directly

`J_o(t)-J_o(s) = (-c I_o-(K_o(t)-K_o(s)))N`.

Adding `(K_o(t)-K_o(s))N` to both sides gives the one-leg identity by ring
algebra.  Subtracting that identity for `o₂` from the identity for `o₁` gives
the two-leg formula.  Interchanging the legs negates both differences.  No
limit, source replacement, frequency continuation, or boundary cancellation
is used.

## Consequence for the full route

`source pole → explicit wave cochain → B1 homogeneous causal difference →
[this B2a finite action transgression] → noncompact causal two-leg limit →
mixedField boundary → cyclic Peierls extinction → RH`.

This closes only the finite-cutoff contact bookkeeping: the contact is an exact
endpoint renormalization, not a discarded term.  It does not identify the two
outer modes with retarded and advanced solutions, take either endpoint to the
physical boundary, or connect the result to the source-pole cochain.  Those
three tasks are the remaining B2 content; a mismatch there kills the literal
distributional/action realization.

## Lean status

The direct source module currently lacks a transitive olean in this checkout.
A targeted Lake attempt was stopped when it expanded into an impermissible
11k-module replay.  The above is therefore paper-closed only.  The independent
finite-interval calculus required for its future source proof is formalized as
`HTGeometry.complex_intervalIntegral_green_two`, source-checked with standard
Lean axioms only.

## Formalized (2026-09-27)

`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFiniteCutoffTwoLegCurrent.lean`
(namespace `RHTower.D4BMPhysicalModeAction`): `contactRenormalizedCurrent`
(`R_o = J_o + K_o N`), `modeSourceIntegral` (`I_o`), `contactRenormalizedCurrent_transport`
(`R_o(t) - R_o(s) = -c I_o N`), `twoLegCurrent`, `twoLegCurrent_transport`
(`-c (I_{o₁} - I_{o₂}) N`), `twoLegCurrent_swap`.  The only hypotheses are the domain conditions
on the spectral parameter carried by `physicalProjectedModeAction` itself.  Axioms
`[propext, Classical.choice, Quot.sound]`.
