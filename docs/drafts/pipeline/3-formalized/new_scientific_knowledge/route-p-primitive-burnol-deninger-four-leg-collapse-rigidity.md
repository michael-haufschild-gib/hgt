# Route P primitive Burnol / Deninger four-leg collapse rigidity

- **ID:** `route-p-primitive-burnol-deninger-four-leg-collapse-rigidity`
- **Stage:** 3-formalized
- **Type:** SHARP RH-EQUIVALENT COLLAPSE NO-GO
- **Label:** `P-G203`
- **Source:** P-G200 squared-Cauchy incidence, P-G201 source graph completion, P-G202 four-leg
  Hodge completion, unconditional critical-line conjugation of the complete Xi divisor
- **Statement:** For every fixed nonzero amplitude and every upper Deninger pole, equality of
  P-G202's positive fourth leg with the original upper squared-Cauchy graph vector is equivalent
  to the Riemann hypothesis. Coordinatewise collapse occurs exactly at critical-line-fixed Xi
  spectral points.

## Conjecture loop

`C203-A` proposed collapsing the four-leg energy back onto a two-leg prime--Gamma trace by
identifying the positive fourth leg with the original upper graph. This would have converted
P-G202's ordinary Hilbert square into a source-looking same-vector pairing.

The hostile test computes the exact coordinate defect. Write

```text
a = xiSpectralPoint(q),
v(q) = A/(a-w)^2,
H4(v)(q) = A/(conj(a)-w)^2.
```

Lean proves

```text
H4(v)(q) - v(q)
  = A (a-conj(a)) (a+conj(a)-2w)
      / ((conj(a)-w)^2 (a-w)^2).
```

The denominator never vanishes: both `a` and `conj(a)` remain in the centered Xi strip, while
the upper Deninger pole lies strictly above it. The apparent second zero mechanism is also
impossible:

```text
a + conj(a) - 2w != 0,
```

because `a+conj(a)` is real and `Im(w)>1/2`. For `A != 0`, only critical-line displacement
remains. Therefore

```text
H4(v)(q) = v(q)  iff  a = conj(a)  iff  Im(a)=0.
```

Function equality for one fixed nonzero amplitude and one arbitrary upper pole is consequently
equivalent to every Xi spectral point being real, hence to RH.

`C203-A` fails as an unconditional construction and survives as an exact rigidity theorem.

## Higher principle

P-G202's four legs are not redundant bookkeeping. Their nonholomorphic separation stores exactly
the off-critical displacement. The difference between line-reflected and original upper graph
jets is a rationally invertible detector of `a-conj(a)`; upper-strip geometry eliminates every
spurious resonance. Thus the fourth leg is a complete orientation observable for RH.

This explains why attempts to scalarize the four-leg metric stall. Same-leg identification does
not transport known positivity—it erases the sole variable measuring failure of RH. Any proof of
that identification must already control every off-line zero. Surviving source transport must
remain asymmetric/nonholomorphic and prove a one-sided contraction or shorting inequality without
equating the two graph legs.

## Hostile novelty audit

The corpus already contained fixed-Cauchy orientation-defect RH equivalences. P-G203 is not a
relabeling of those results: it computes the exact defect of P-G202's newly constructed
source-completed squared-Cauchy Hodge leg, proves the upper-pole resonance factor is universally
nonzero, and quantifies collapse at arbitrary nonzero amplitude and arbitrary upper Deninger pole.
It closes a previously open Route P design choice at the actual P-G200--P-G202 graph object.

No Hodge compatibility, source domination, zero location, simplicity, or RH premise is assumed by
the theorem.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolDeningerFourLegCollapseRigidity.lean
```

Capstones:

- `routePDeningerUpperCollapseResonanceFactor_ne_zero`;
- `routePDeningerFourLegCollapseDefect_factorization`;
- `routePDeningerFourLegCollapseDefect_eq_zero_iff`;
- `routePDeningerFourLegCollapseDefect_eq_zero_iff_im`;
- `routePDeningerUpperFourLegHodgeMate_eq_upperSquaredCauchyJet_iff_riemannHypothesis`.

Verification:

- `/tmp/pg203.lean`: `lake env lean /tmp/pg203.lean` passed;
- exact leaf target
  `GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolDeningerFourLegCollapseRigidity` built;
- `/tmp/pg203_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- forbidden-declaration scan clean;
- umbrella import wired without building umbrella.

## Gates

- [x] factor the exact four-leg collapse defect
- [x] prove both squared-Cauchy denominators are nonzero
- [x] eliminate the apparent upper-pole resonance
- [x] classify coordinate collapse by critical-line fixedness
- [x] classify coordinate collapse by zero imaginary part
- [x] prove global collapse iff RH
- [x] scratch verification and exact leaf build only
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [ ] construct asymmetric coefficient-faithful P-G194-to-four-leg contraction/shorting
- [ ] instantiate W-H184 and prove unconditional RH
