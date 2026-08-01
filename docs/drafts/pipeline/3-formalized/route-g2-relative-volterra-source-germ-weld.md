# Route G2 relative-Volterra source-germ weld — formalized closure

- **ID:** `route-g2-relative-volterra-source-germ-weld-formalized`
- **Stage:** 3-formalized
- **Type:** NO-GO / EXACT RH-EQUIVALENT SOURCE CLASSIFICATION
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Paper proof:** `../2-fully-proven/route-g2-relative-volterra-source-germ-weld.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.SuzukiVolterraSourceGermWeldRigidity`

## Formal theorem surface

1. `suzukiAffineSewnExteriorWeylQuotient_eq_localCorrection_sub_xiMultiplier`
   proves pointwise source transparency at every point where the sewn characteristic is nonzero:

   ```text
   m = odd(local right response)/sewn characteristic - XiC'/(z^2 XiC).
   ```

2. `analyticAt_suzukiAffineSewnExteriorWeylEulerDefect_of_riemannHypothesis`
   proves under RH that the actual quotient's Euler defect is analytic at every nonreal point.

3. `analyticOnNhd_suzukiAffineSewnExteriorWeylEulerDefect_of_riemannHypothesis`
   upgrades the preceding result to the full upper half-plane.

4. `riemannHypothesis_iff_exists_suzukiAffineSewnExteriorWeylEulerDefect_source_germ_weld`
   proves the generic admissible-boundary pointed-germ package is exactly equivalent to RH.

5. `riemannHypothesis_iff_exists_suzukiVolterraPhaseEulerDefect_source_germ_weld`
   substitutes the complete relative-Volterra Euler/Neumann boundary responses and closes Route G2
   without erasing any channel.

## Proof dependencies and unconditionality

Forward direction uses RH only to exclude upper-half-plane Xi zeros, after which the multiplier,
local correction, quotient, and Euler defect are analytic. Reverse direction reuses the previously
proved exact double-pole theorem and meromorphic pointed-germ propagation. No positivity premise,
finite-limit assumption, source postulate, numerical computation, `sorry`, `admit`, custom `axiom`,
`opaque`, or `unsafe` declaration is introduced.

`#print axioms` for all five declarations reports only:

```text
propext
Classical.choice
Quot.sound
```

## Verification

Passed on 2026-08-01:

```text
lake env lean GaloisForLFunctions/RHTower/SuzukiVolterraSourceGermWeldRigidity.lean
python3 scripts/formal_tools.py lint
lake env lean /tmp/SuzukiVolterraSourceGermWeldRigidity.lean   # batched #print axioms
lake build GaloisForLFunctions.RHTower.SuzukiVolterraSourceGermWeldRigidity
```

Module is imported by `GaloisForLFunctions.RHTower`; generated Lean API/overview/gap indexes include
its five declarations and report no forbidden proof debt.

## Closed boundary

Route G2's independent-bypass reading is retired. The formal theorem does not prove RH and does not
claim a literal prime--Gamma source construction. It proves that any such construction satisfying
the proposed single pointed analytic germ is already a complete RH proof. Strongest surviving new
knowledge is exact source transparency and exact pole amplification/classification, not a renamed
conditional connector.

## Gates

- [x] 2 -> 3: exact paper theorem formalized unconditionally and wired into umbrella
- [ ] 3 -> 4: independent mathematical-priority and expert-source review
