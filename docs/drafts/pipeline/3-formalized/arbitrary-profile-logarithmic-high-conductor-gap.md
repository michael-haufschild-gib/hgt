# Arbitrary-profile logarithmic high-conductor gap

- **ID:** arbitrary-profile-logarithmic-high-conductor-gap
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Σ1d; quadratic collar cancellation and conductor-band overlap bounds.
- **Statement:** Every nonzero real `C²` profile supported on `[0,1]` has constants `C,D>0` such that, on normalized packets in `V_R∩V_Q^⊥`,
  `Wφ,c,N ≥ adjunction/8 + (log Q)/4 − log c − C`
  whenever the explicit nine-term error in `exists_profile_completeWeilEnergy_ge_adjunction_and_log` is at most `1/D`, and its stated geometric horizon bounds hold.

## Proof

Quadratic center and separated-cross bounds cost respectively
`Oφ(c(1+log R)/log N)` and `Oφ(c²/log N)`. Pairing the near-cancellation
remainder against the terminal mass of the packet costs
`Oφ(c²(1+log R)(1+log c)/log N + c²R sqrt(log N/N))`.
The exact complete-Weil decomposition therefore gives prime energy minus
the overlap quadratic form, with self-energy loss `log c+Oφ(1)`.
These estimates require only the stated profile regularity, support and
positive mass.

Orthogonality to `V_Q` makes the coefficient prefix through `Q` have norm
at most `54(1+log R)/log N`. Removing it changes the overlap quadratic
form by at most `270 Cφ c(1+log c)(1+log R)/log N`.
For the remaining packet, the cubic lag estimate costs
`Oφ(c²(1+log c)/log N + c⁵log N/N + c³/sqrt Q + c³R⁴/N)`.
The nine-term budget bounds the total overlap cost by five.
Prime adjunction supplies `adjunction/8+(log Q)/4−log 4−4`.
Combining these inequalities proves the claim.

For `Q=(log N)^q`, `R=(log N)^A`, `q>0`, `A≥q`, and
`c≤α log log N`, every error tends to zero while
`log c=o(log Q)`. Thus the high block has a growing positive gap at this
overlap scale; the earlier quadratic-in-overlap loss is avoidable.

## Lean

`CriticalArithmeticCorrelationTheory/EveryProfileHasALogarithmicHighConductorGap.lean`:
`exists_profile_completeWeilEnergy_ge_prime_sub_overlap` and
`exists_profile_completeWeilEnergy_ge_adjunction_and_log` passed direct
Lean checks and transitive axiom audits: only `propext`, `Classical.choice`,
`Quot.sound`. The module is wired into the umbrella.
