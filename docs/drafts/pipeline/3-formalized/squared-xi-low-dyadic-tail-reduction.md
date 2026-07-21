# Squared-Xi low dyadic source and tail-from-32 RH reduction

- **ID:** `squared-xi-low-dyadic-tail-reduction`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH BRIDGE
- **Claim labels:** `[BRIDGE] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** `squared-xi-dyadic-half-plane-rigidity-rh.md`

## Exact claim

For the fixed-shift coordinate

```text
Z(q) = ((A(q) : ℂ) - B(q) I)^(-1),
A(q) = Im(q)^2 - (Re(q)-1/2)^2 + 1,
B(q) = 2 (Re(q)-1/2) Im(q),
```

the dyadic rungs `k = 0,1,2,3,4`, i.e. powers `1,2,4,8,16`, have strictly positive real part
unconditionally for every Xi zero copy `q`.

Define

```text
XiSquaredSeamDyadicTailFromFive :=
  for every q and k, 5 <= k -> 0 <= Re(Z(q)^(2^k)).
```

Then

```text
XiSquaredSeamDyadicTailFromFive <-> RiemannHypothesis.          (T5)
```

Thus the exact first unproved dyadic source rung is power `32`; no positivity at powers below `32`
remains in the RH interface.

## Internal frontier

- `[CORPUS]` `xiZeroCopy_offLine_eightyFive_lt_im_sq`: every off-line Xi zero copy has squared
  height greater than `85`.
- `[CORPUS]` `xiOrderSixteenReciprocalPower_re_pos`: fixed-shift power `16` is strictly positive.
- `[LEAN-PROVED]` `xiSquaredSeamDyadicHalfPlane_iff_riemannHypothesis`: all dyadic signs are
  equivalent to RH.

No low-rung package or tail-from-`k=5` reduction was found in the internal corpus. Per user
direction, no external priority claim is made.

## Paper proof: unconditional sector

Write

```text
u = (Re(q)-1/2)^2,
v = Im(q)^2,
A = v-u+1,
B = 2 (Re(q)-1/2) Im(q).
```

The critical strip gives `u < 1/4`, and always `A > 0`.

If `q` is on the critical line then `B = 0`, so `Z(q)` is positive real and every power is
positive. Suppose `q` is off-line. The unconditional off-line height theorem gives `v > 85`.
Since `4u < 1`,

```text
B^2 = 4uv < v.
```

Also `A = v + (1-u) > v`, hence

```text
A^2 > v^2 > 85v > 85B^2.                                    (1)
```

Put `D=A^2+B^2`, `x=Re Z=A/D`, and `y=Im Z=B/D`. Then `D>0`, `x>0`, and (1) gives

```text
85 y^2 < x^2.                                                  (2)
```

## Paper proof: powers 1, 2, 4, 8

Set `s=x^2>0` and `t=y^2>=0`. From (2), `85t<s`.

The first three relevant real parts are

```text
Re Z     = x,
Re Z^2   = s-t,
Re Z^4   = s^2 - 6st + t^2.
```

They are positive because `s>85t` implies `s>t` and, after multiplication by `s>0`,
`s^2>85st>6st`.

For power eight,

```text
Re Z^8 = s^4 - 28s^3t + 70s^2t^2 - 28st^3 + t^4.             (3)
```

Since `t<s`, one has `t^2<=s^2`, hence `st^3<=s^3t`. Multiplying `85t<s` by `s^3>0` gives
`85s^3t<s^4`; therefore `56s^3t<s^4`. Dropping the nonnegative terms in (3) and using the preceding
comparison gives

```text
Re Z^8 >= s^4 - 56s^3t > 0.
```

This proves strict positivity at dyadic rungs `k=0,1,2,3`. Rung `k=4` is exactly the existing
power-`16` theorem specialized to shift `y=1`.

## Paper proof of (T5)

Assume the tail condition. For any `k`, either `k<5` or `5<=k`. The first case is discharged by
the five unconditional low-rung theorems; the second is the tail hypothesis. Hence the complete
dyadic half-plane condition holds, and the parent rigidity theorem gives RH.

Conversely RH gives the complete dyadic condition, hence its restriction to `k>=5`. This proves
(T5).

## Hostile audit

1. **Tail-only counterexamples are not ignored.** For arbitrary `z`, a nonreal `2^K`-th root of
   unity has positive tail from `K` onward. Here rungs below `5` are separately proved from Xi
   geometry; the implication uses the assembled full sequence.
2. **Off-line height is unconditional.** `v>85` comes from the formalized endpoint-source quartet
   theorem, not a zero table or RH.
3. **No equality leak.** Sector (2) is strict, so powers `1,2,4,8` are strictly positive. Tail uses
   only nonnegativity, matching the parent rigidity theorem.
4. **No missing rung.** Natural numbers below `5` are exactly `0,1,2,3,4`; their exponents are
   `1,2,4,8,16`.
5. **Verdict:** `BRIDGE`. This discharges a finite source prefix and makes power `32` the exact
   rightmost open source atom. It does not produce the infinite tail, which remains equivalent to
   RH after these unconditional discharges.

## Exact open core after this theorem

`[OPEN CORE]` Unconditionally produce the fixed-shift atom signs only at powers
`32,64,128,...`, or find a source law implying them. Any proposed producer must use arithmetic
information beyond the finite low-order sector: arbitrary nonzero transverse phase eventually
crosses the dyadic left half-plane.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.XiSquaredSeamLowDyadicTail`
- Unconditional rungs: `xiSquaredSeamDyadic_rung_zero_pos`,
  `xiSquaredSeamDyadic_rung_one_pos`, `xiSquaredSeamDyadic_rung_two_pos`,
  `xiSquaredSeamDyadic_rung_three_pos`, and imported `xiSquaredSeamDyadic_rung_four_pos`.
- Tail assembly: `xiSquaredSeamDyadicHalfPlane_of_tailFromFive`.
- RH equivalence: `xiSquaredSeamDyadicTailFromFive_iff_riemannHypothesis`.
- Direct `lake env lean` check: passed.
- `#print axioms` for all new capstones: only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint: passed with proof debt `0`.
- Final targeted `lake build GaloisForLFunctions.RHTower.XiSquaredSeamLowDyadicTail`: passed.
- Umbrella import: `GaloisForLFunctions.RHTower`.

## Gates

- [x] Internal corpus audit
- [x] Complete paper proof
- [x] Hostile audit
- [x] Stage-2 promotion: `[PAPER-PROVED]`
- [x] Exact Lean theorem
- [x] Axiom/lint/module audit and Stage-3 promotion
- [ ] Dyadic-tail producer
- [ ] Full RH proof
