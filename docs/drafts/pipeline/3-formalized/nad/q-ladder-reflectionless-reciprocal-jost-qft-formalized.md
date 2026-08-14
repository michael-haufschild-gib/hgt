# q-ladder reflectionless reciprocal Jost QFT — formalized

- **ID:** `q-ladder-reflectionless-reciprocal-jost-qft-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `q-ladder-reflectionless-reciprocal-jost-qft.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/QLadderTransmission.lean` | the transmission germ `(6)`, its normal convergence, the one-shell equation `(7)`, unimodularity on the imaginary axis, the momentum form `(5)`, and the wave-number summability `(2)` |
| `HTGeometry/OpenFamilyCDDShell.lean` | the finite-union multi-ladder shell with multiplicities and its convergence |
| `HTGeometry/GeometricCDDConstraint.lean`, `HTGeometry/GeometricCDDBoundarySelection.lean` | the finite shell algebra, the infinite log-energy delay, and boundary uniqueness |
| `HTGeometry/SourceLogarithmicBoundary.lean` | the logarithmic-derivative HT equivalence `(10)`–`(11)` |
| `HTGeometry/ExponentialObservationHypertranscendence.lean` | HT is unchanged by a nonzero DA factor, giving `(12)` |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `(2)` `summable_qLadderWaveNumbers` — the geometric ladder `κ q^n` is absolutely summable, which is
  the Gesztesy–Karwowski–Zhao admissibility condition;
- `(5)` `qLadderFactor_momentum` — for nonzero momentum the physical product
  `∏ (k + iκq^n)/(k − iκq^n)` is exactly the ladder factor at the crossing coordinate `iκ/k`;
- `(6)` `qLadderFactor`, `qLadderTransmission`, with `qLadderFactor_zero` and `qLadderFactor_succ`;
- **normal convergence**: `multipliable_qLadderFactor` — on the open unit disc the product converges,
  proved by writing each factor as `1 + 2q^ⁿz/(1 − q^ⁿz)` and dominating by a geometric series;
- `(7)` `qLadderTransmission_one_shell` — the exact one-shell `q`-difference equation
  `F_q(z) = ((1+z)/(1−z))·F_q(qz)` for the **infinite** product, not only for truncations;
- reflectionless unitarity: `norm_qLadderFactor_eq_one` and `norm_qLadderTransmission_eq_one` —
  `|T(k)| = 1` for real momentum, obtained by pushing the convergent product through the modulus
  monoid homomorphism;
- supporting estimates `norm_qLadderScale_lt_one`, `one_sub_qLadderScale_ne_zero`,
  `one_sub_norm_le_norm_one_sub`, `qLadderFactor_eq_one_add`;
- `(10)`–`(11)` `hypertranscendentalOver_deriv_div_self_iff` — an element is HT exactly when its
  logarithmic derivative is, which is Claim B's step verbatim;
- `(12)` `hypertranscendentalOver_mul_differentialAlgebraic_iff` — the Wigner delay `−iL/(2k)` is HT
  because `L` is and `−i/(2k)` is a nonzero DA factor.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/QLadderTransmission.lean
lake build GaloisForLFunctions.HTGeometry.QLadderTransmission
```

## What closed last

The infinite product itself.  The corpus had the finite shell algebra and the real log-energy delay
with its boundary-selection uniqueness, but not the complex germ `F_q`, its convergence, or the
one-shell equation for the limit.  The step that makes `(7)` work at the level of the `tprod` is that
the shifted family `n ↦ F-factor at index n+1` is literally the family at the scaled argument `qz`,
so `tprod_eq_zero_mul'` applies once the scaled family is known multipliable — and `‖qz‖ < 1`
whenever `‖q‖, ‖z‖ < 1`.  Unimodularity then follows by transporting the convergent product through
the modulus, since every factor `(1 + w)/(1 − w)` with purely imaginary `w` has modulus one.

## Boundary

The Gesztesy–Karwowski–Zhao infinite-soliton construction of `(3)`–`(4)`, the
Adamczewski–Dreyfus–Hardouin rational-or-HT dichotomy applied to `(7)`, and Lechner's
inverse-scattering QFT reconstruction in Claim D are cited published theorems, as the card states.
The paper card's open gates — an external formula-level novelty audit, a reciprocal Jost map derived
from common physical dynamics, and an admissible cosmological background with a phase-sensitive
reporter — are onward research targets and literature obligations, not formalization gates for the
scattering-germ analysis certified above.
