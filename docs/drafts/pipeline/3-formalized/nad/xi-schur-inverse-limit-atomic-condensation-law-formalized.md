# Xi Schur inverse-limit atomic condensation law — formalized

- **ID:** `xi-schur-inverse-limit-atomic-condensation-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `xi-schur-inverse-limit-atomic-condensation-law.md`
- **Umbrella imports:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `RHTower/XiSchurDiscGerm.lean` | the Xi source trace `H_Ξ`, the Cayley map `χ`, the basepoint `b` with `b > 0`, the germ `F_Ξ` `(1)`–`(4)`, the anti-Herglotz/RH bridge, and the abstract Herglotz measure |
| `RHTower/XiCircleAtomicMeasure.lean` | the atomic Xi circle measure, its probability normalization, singularity, infinite support, the conformal Poisson transfer, the identification with the Herglotz measure of `F_Ξ`, and the condensation capstone |
| `HTGeometry/HerglotzRepresentationDisc.lean` | the Herglotz representation theorem on the unit disc |
| `HTGeometry/HerglotzDiscDilation.lean`, `HTGeometry/HerglotzBoundaryMeasure.lean` | the dilated Poisson representation and the boundary probability family |
| `HTGeometry/SingularSchurDefectCollapse.lean`, `HTGeometry/FAndMRieszSchurConsequences.lean` | the singular Schur-defect collapse and the Bernstein–Szegő cofinal approximation |
| `HTGeometry/BernsteinSzegoProbabilityApproximation.lean`, `HTGeometry/BernsteinSzegoCaratheodoryRational.lean`, `HTGeometry/MomentFiberPickSchurPhase.lean` | the OPUC/Schur-defect and Bernstein–Szegő layers and the generic Xi-facing capstone |
| `HTGeometry/CircleSingularWitness.lean` | singularity of countably carried circle measures |
| `RHTower/CCMCompletedPrimeGammaAccretivityCriterion.lean` | the checked anti-Herglotz/RH criterion |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `(1)` `xiSourceHerglotz`, `cayleyDisc`, with `cayleyDisc_im` and `cayleyDisc_im_pos`;
- **the bridge**: `continuedPrimeArchUpperAntiHerglotz_iff_xiSourceHerglotz_im_nonneg` and
  `riemannHypothesis_iff_xiSourceHerglotz_im_nonneg_strip` — the already checked `RHTower`
  criterion **is** the Herglotz sign of `H_Ξ` on the centered upper half strip, through the proved
  identity `continuedPrimeArchSourceRelativeTrace = -H_Ξ`;
- `(6)` `xiSourceHerglotz_im_nonneg_of_rh` — under RH the trace is Herglotz on the **whole** upper
  half plane, since every centered spectral point is then real;
- `(2)`, `(3)` `xiBasepointSlope`, `xiBasepointSlope_im` (it is real, from Schwarz reality of `ξ`)
  and `xiBasepointSlope_re_pos_of_rh` (`b > 0`, as the convergent positive sum
  `∑_q 1/(t_q²+1)` — the resolvent argument replaces the theta integral and uses no numerics);
- `(4)` `xiCaratheodory`, `xiCaratheodory_zero_of_rh`, `xiCaratheodory_re_nonneg_of_rh`,
  `differentiableOn_xiCaratheodory_of_rh`;
- `exists_xiCircleMeasure_of_rh` — the Herglotz representation applied to `F_Ξ`;
- the **canonical measure, explicitly**: `xiCayleyPoint`, `xiAtomWeight`, `xiCircleAtomicMeasure`,
  `xiCircleAtomicMeasure_univ_of_rh` (a probability measure),
  `mutuallySingular_xiCircleAtomicMeasure` (singular to `circleLebesgue`),
  `xiCircleAtomicMeasure_support_infinite_of_rh` (infinite support);
- `im_cayleyDisc_div_normSq` — the exact conformal Poisson transfer;
- `re_xiCaratheodory_eq_integral_poissonKernel_of_rh` — **the atomic measure is the Herglotz measure
  of `F_Ξ`**: the germ's real part is its Poisson integral;
- `xiSchur_atomicCondensation_of_rh` — the capstone: under RH the canonical Xi circle measure
  carries both `HasSingularSchurDefectCollapse` and `HasBernsteinSzegoCofinalApproximation`.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/XiSchurDiscGerm.lean
lake build GaloisForLFunctions.RHTower.XiCircleAtomicMeasure
```

## What closed last

The canonical measure.  The card's Stage-3 gate asked for a source-faithful construction of the Xi
circle probability measure together with the bridge to the checked anti-Herglotz criterion.  The
bridge came from identifying the continued prime–archimedean relative trace with `-H_Ξ`.  The
measure looked as if it needed Fatou's radial-limit theorem — absent from mathlib — to prove
singularity; instead it was built **atomically** from the centered Xi spectrum, and then *identified*
with the Herglotz measure by computing its Poisson integral.  The identification rests on one exact
conformal identity: for a real ordinate `t` and a disc point `w`,
`Im χ(w)/|t − χ(w)|² = P(0,w,(t−i)/(t+i))/(t²+1)`, which turns the half-plane resolvent expansion of
`H_Ξ` into a weighted sum of disc Poisson kernels.  Singularity is then immediate — the measure is
carried by a countable set — and `b > 0` falls out of the same expansion as the total Cauchy weight.

## Boundary

The RH direction is stated as it is on the card: RH **forces** the atomic condensation.  This is not
a proof of RH; the reverse implication on the card is the separate finite-Pick-positivity criterion,
already formalized in the Schur-defect layer.  The remaining paper gates — an independent specialist
proof audit and a full priority audit — are external obligations.
