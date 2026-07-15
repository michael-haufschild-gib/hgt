# Library ticket: shifted sector-circle valuation cones

- **Source card:**
  `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/prime-arch-shifted-sector-circle-valuation-cone.md`
- **Destination:** reusable theorem in `formal/GaloisForLFunctions/HTGeometry`, Xi specialization
  and residual Sonin consumer in `formal/GaloisForLFunctions/RHTower`
- **Status:** exact thirteenth-power Xi core formalized in
  `PrimeArchShiftThirteenCircleCone.lean`; reusable circle-density packaging and residual Sonin
  consumer remain

## Reusable HTGeometry layer

Formalize a theorem for a summable family of complex atoms `u_j` satisfying

```text
0 < Re(u_j),  |arg(u_j)| <= alpha,  |u_j| <= R < 1.
```

For a shift `s`, assume

```text
cos((s+1)*alpha) > 2*R/(1-R).
```

Then the real shifted moment sequence

```text
m_(s+n)=Re(sum_j u_j^(s+n+1))
```

has a strictly positive absolutely convergent circle density

```text
w_s(e^(it))=m_s+2*sum_(n>=1)m_(s+n)cos(nt),
```

with explicit two-sided density bounds and the induced reflected coefficient cone.

## RHTower specialization

Use

```text
summable_xiZeroCopyReciprocalSquare_pow
xiCentralReciprocalMoment_im_eq_zero
normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment
xiZeroCopy_fortyOne_div_two_lt_im_sq
xiThermalNode_pos
xiThermalOrientationTerm_le_one_over_eightyFour_node_sq
```

to obtain the rational specialization for `0<=s<=11` with

```text
delta_s=224/(13*(168-(s+1)^2)).
```

The endpoint `s=12` is separately supplied by the formal exact bound
`Re(u^13)>|u|^13/8`.  It gives `delta_12=32/39` and the additional valuation-six cone

```text
32*E_tail(q) <= 7*q(0)^2.
```

Then prove the remaining circle-density packaging for the valuation corollary for `P=X^v q`,
`v<=6`, and define the residual integer test family complementary to the six old cones

```text
224*E_tail(q) <= (1960-13*(2v+1)^2)*q(0)^2.
```

and the new valuation-six cone above.

Finally specialize the proof of
`riemannHypothesis_of_soninCoupledPrimeArchPerTestVariationalUpperBound` so the variational premise
is required only on that residual family.

## Verification requested

- build only the new HTGeometry module and the remaining RHTower specialization;
- inspect axioms from a scratch file;
- run the formal lint gate after the targeted modules pass;
- wire the new modules into the explicit circle-state and coupled-Sonin imports;
- do not launch a whole-project build unless separately requested.
