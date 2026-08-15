# Route P primitive Burnol / Deninger finite orientation witness

- **ID:** `route-p-primitive-burnol-deninger-finite-orientation-witness`
- **Stage:** 3-formalized
- **Type:** FINITE SOURCE NEGATIVITY REDUCTION
- **Label:** `P-G204`
- **Source:** P-G201 upper secant graph completion, P-G202 conjugate-lower four-leg completion,
  P-G203 collapse rigidity, unconditional Xi Weil Hilbert quadratic
- **Statement:** The difference between the original upper squared-Cauchy graph and P-G202's
  fourth leg is a pure reflection-odd channel with Weil energy equal to minus its Hilbert norm
  square. Explicit finite mixed upper/conjugate-lower prime--Gamma secants converge to this channel.
  Failure of RH therefore produces a finite negative source packet and is equivalent to these
  explicit finite source energies converging to a strictly negative limit.

## Conjecture loop

`C204-A` continued the W-H184 plan by seeking a bounded projection from P-G194's source
colligation onto P-G202's full graph Gram. The `N=1` endpoint exposes why this is the wrong local
object: a strict-right cubic charge is already at least the entire `<2` source capacity. Any such
projection theorem would itself contain the contradiction and cannot arise from generic Hilbert
geometry.

`C204-B` preserves rather than collapses the two graph orientations. Let

```text
x = upperSquare(A,w),
Jx = fourLegMate(A,w),
d = x-Jx.
```

P-G202 gives `J^2=1`, hence Lean proves

```text
Jd = -d,
Q_Weil(d) = Re inner(Jd,d) = -||d||^2.
```

P-G203 makes the sign sharp for every `A != 0` and every upper pole `w`:

```text
d=0       iff RH,
Q_Weil(d)>=0 iff RH,
Q_Weil(d)<0  iff not RH.
```

This is not a positivity assumption. It identifies the exact negative channel that any source
positivity law must eliminate.

`C204-C` asks whether this completed negative channel is merely a target-side closure artifact.
It is not. P-G201 supplies explicit upper two-atom secants and P-G202 supplies explicit
conjugate-lower two-atom secants, all chosen only from `A`, `w`, and `n`. Their difference

```text
d_n = UpperEval(upperSecant(A,w,n))
      - conj(LowerEval(lowerSecant(conj(A),conj(w),n)))
```

converges strongly to `d`. Continuity of the unconditional Weil quadratic gives

```text
Q_Weil(d_n) -> -||d||^2.
```

Thus `not RH` forces `Q_Weil(d_n)<0` for some finite `n`. More exactly,

```text
(exists E<0, Q_Weil(d_n) -> E) iff not RH.
```

The off-critical obstruction is therefore visible at finite prime--Gamma source level; no
divisor-selected approximation or abstract closure witness remains.

## Higher principle

P-G203 showed that four-leg asymmetry stores the critical-line displacement. P-G204 identifies
its correct variational role: asymmetry is a reflection-odd Krein channel, so it carries negative
Weil energy rather than a large positive graph norm. The earlier singular `1/(2a^2)` cost arose
from trying to dominate the entire graph norm. The orientation channel needs no such domination;
it needs a source theorem forbidding negative energy on one explicit finite mixed-sector family.

This reframes Route P's endpoint from

```text
construct target Gram <= source Gram
```

to

```text
prove Q_Weil(d_n)>=0 for the explicit mixed prime--Gamma secants.
```

The latter remains hard but is finite, coefficient-faithful, and directly in Deninger's source
cup. P-G194 may enter by decomposing this signed mixed energy into its conserved positive channels
plus the P-G196 commutator term, rather than by producing a target projection.

## Hostile novelty audit

The corpus contained generic even/odd Krein decompositions and other Cauchy orientation-defect
reconstructions. It did not identify P-G202's actual upper/fourth-leg difference as a pure negative
channel, construct its explicit paired P-G201/P-G202 finite source sequence, or prove that failure
of RH creates a finite negative packet in this coefficient-faithful Route P family. P-G204 closes
the target-versus-source status of the obstruction and supplies a narrower terminal receiver.

No source positivity, Hodge compatibility, target domination, zero location, simplicity, or RH
premise is assumed by the equivalences.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolDeningerFiniteOrientationWitness.lean
```

Capstones:

- `xiWeilLineConj_fourLegOrientationDefectJet`;
- `xiWeilHilbertQuadratic_fourLegOrientationDefectJet`;
- `routePDeningerFourLegOrientationDefectJet_eq_zero_iff_riemannHypothesis`;
- `xiWeilHilbertQuadratic_fourLegOrientationDefectJet_nonneg_iff_riemannHypothesis`;
- `tendsto_routePDeningerFiniteFourLegOrientationDefectJet`;
- `tendsto_xiWeilHilbertQuadratic_finiteFourLegOrientationDefectJet`;
- `exists_finiteFourLegOrientationDefectJet_weil_negative_of_not_riemannHypothesis`;
- `exists_negative_limit_finiteFourLegOrientationDefectJet_iff_not_riemannHypothesis`.

Verification:

- `/tmp/pg204.lean`: `lake env lean /tmp/pg204.lean` passed;
- exact leaf target
  `GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolDeningerFiniteOrientationWitness` built;
- `/tmp/pg204_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- forbidden-declaration scan clean;
- umbrella import wired without building umbrella.

## Gates

- [x] construct upper-minus-fourth-leg orientation channel
- [x] prove exact reflection anti-fixedness
- [x] prove Weil energy equals negative Hilbert norm square
- [x] classify zero, nonnegative, and negative energy by RH
- [x] construct explicit finite mixed upper/conjugate-lower source secants
- [x] prove strong convergence to orientation channel
- [x] prove finite source energy convergence
- [x] prove `not RH` yields a finite negative source packet
- [x] prove negative-limit finite-source criterion iff `not RH`
- [x] scratch verification and exact leaf build only
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [ ] prove nonnegativity of the explicit finite mixed-sector source energies
- [ ] conclude unconditional RH
