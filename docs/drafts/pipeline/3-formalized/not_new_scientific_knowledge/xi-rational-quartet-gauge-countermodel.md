# Xi rational-quartet gauge countermodel

- **ID:** `xi-rational-quartet-gauge-countermodel`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[FORMALIZED] [UNCONDITIONAL] [BRIDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiRationalQuartetGauge.lean`
- **Statement:** There exists an entire function with the completed-xi functional equation and
  Schwarz symmetry, nonvanishing on the real segment `0 < sigma < 1`, but with an explicit zero
  off the critical line.

## Exact theorem

For real `a,b`, Lean defines the centered quartic

`Q_(a,b)(s) = (((s-1/2)-a)^2+b^2) (((s-1/2)+a)^2+b^2)`

and the gauged completed function

`xi_(a,b)(s) = Q_(a,b)(s) xi(s)`.

It proves:

1. `Q_(a,b)(1-s)=Q_(a,b)(s)`;
2. `Q_(a,b)(conj(s))=conj(Q_(a,b)(s))`;
3. `xi_(a,b)` is analytic at every complex point;
4. `xi_(a,b)` has the same functional equation and Schwarz symmetry as `xi`;
5. if `b>0`, then `Q_(a,b)` has positive real part at every real argument and
   `xi_(a,b)(sigma) != 0` for `0<sigma<1`;
6. `rho=1/2+a+b i` is a zero of `xi_(a,b)`;
7. if `a!=0`, then `Re(rho)!=1/2`.

The capstone `RHTower.exists_xi_symmetric_entire_offcritical_countermodel` specializes to
`a=1/4`, `b=1`, proves `0<Re(rho)<1`, and packages all seven facts into one unconditional
existential theorem.  Its selected zero is therefore inside the open critical strip, not merely
off the critical line somewhere in the plane.

## Consequence

Entire analyticity, the xi functional equation, Schwarz symmetry, and real-segment
nonvanishing do not determine critical-line zero location.  Any proposed RH route using only
those properties is formally refuted by this countermodel.

The theorem does not refute divisor-sensitive routes.  It also does not formalize the broader
paper theorem that rational gauges preserve differential-translation matroids.  That claim stays
at stage 2 until its differential-field equalities themselves are represented in Lean.

## Scientific status

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.  The construction is polynomial multiplication and
the proof is elementary.  Its value is as a machine-checked boundary preventing symmetry and
hypertranscendence arguments from silently assuming divisor recovery.

## Verification

- `lake build GaloisForLFunctions.RHTower.XiRationalQuartetGauge` passed.
- Scratch `#print axioms` for the capstone and real-anchor theorem reports only
  `[propext, Classical.choice, Quot.sound]`.
- The project formal lint passes with no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
  declaration.

## Gates

- [x] 0 -> 1: explicit polynomial gauge and exact countermodel statement
- [x] 1 -> 2: complete unconditional paper proof
- [x] 2 -> 3: complete stated claim formalized in Lean; narrow build, axiom audit, and lint pass
- [ ] 3 -> 4: not a standalone publication target

## Log

- 2026-07-11 -- Formalized the quartic gauge, both symmetries, entire analyticity, off-critical
  zero, real-axis gauge positivity, real-segment nonvanishing, and the existential capstone.
