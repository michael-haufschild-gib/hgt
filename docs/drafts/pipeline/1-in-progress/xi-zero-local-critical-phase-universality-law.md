# Xi-zero local critical-phase universality law

- **ID:** xi-zero-local-critical-phase-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized)
- **Source:** Post-Law-28 terminal inventory of Born, prime-clock, prime-mark, Arakelov, Clifford, and Gamma--Mertens modules
- **Statement:** At each actual Xi zero, critical-line placement is equivalent to eleven local
  realizations: critical Born temperature, reflected phase match, functional-equation fixed point,
  reflected prime-clock Shale summability, perspective-neutral external clocks, unit centered-prime
  mark, unit Arakelov coordinate, finite unitary eigenpacket, real Berry--Keating and weight-one
  Clifford energies, and a finite shift-two Gamma--Mertens coboundary. Off-line placement forces
  simultaneous failure in all eleven charts.

## Gates

- [x] 0 → 1 in-progress: exact Lean declarations and downstream consumers read
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs read

1. `reflectedPhaseMatch_iff`, `fe_reflection_fixed_iff`, and `bornBeta` identify the critical line
   with the fixed temperature `1` and functional-equation--Schwarz fixed locus.
2. `summable_primeClockReflectionEnergy_iff` and `perspectiveNeutralExternalClock_iff` each classify
   the real coordinate `sigma = 1/2`.
3. `centeredPrimeMark_norm_eq_one_iff` classifies the critical line for every integer base `p > 1`.
4. `arakelovW_norm_one_iff_critical` and `finiteUnitaryEigenDatum_iff_norm_eq_one` classify the same
   line through unit-circle geometry and a finite norm-preserving eigenpacket.
5. `berryKeatingU_nonreal_of_offCritical_nonzero_im` shows quadratic reality is faithful away from
   the real axis. An actual Xi zero in the open critical strip cannot lie on the real axis, so its
   quadratic reality is exactly critical placement. Weight-one Clifford energy differs by a real
   affine term and has the same imaginary part up to sign.
6. `mertensPolePair_re_eq_half_of_finiteShiftTwoCoboundary` gives the hard direction of the local
   Gamma--Mertens chart using the HTGeometry principal-part differential operator. On the critical
   line its reflected pole supports coincide, and the zero finite support supplies the converse.

## Internal noncollision audit

`scripts/formal_tools.py research "Born phase prime clock centered prime mark Arakelov unitary
Clifford Berry Keating Mertens coboundary critical line"` found the separate classifiers and
unconditional HTGeometry prime-clock/divisor-phase structure but no common local consumer. Existing
universality laws do not mention these Born, Shale-clock, Arakelov-unitary, quadratic-Clifford, or
Gamma--Mertens coboundary predicates. Bare right-half zero-indexed Arakelov power/collision criteria
were rejected because their reverse RH direction is explicitly audited as vacuous. The survivor is
pointwise at every actual Xi zero and remains informative on either side of the line.

## Paper proof

Fix an Xi zero `rho`, an integer base `p > 1`, and a real Clifford coupling `a`. The zero-strip
theorem gives `0 < rho.re < 1`, hence `rho ≠ 0`. If `rho.re = 1/2`, direct application of the Born,
reflection, both clock, centered-mark, and Arakelov biconditionals supplies the first seven charts;
the unit Arakelov norm supplies a finite unitary eigenpacket. The Berry--Keating imaginary-part
formula vanishes, and the real affine Clifford connector transfers that vanishing. Equality of the
two reflected Mertens pole supports reduces the principal-part pair to zero, realized by the zero
finite support.

Conversely, any faithful chart recovers the line; the implementation uses reflected prime-clock
summability. For the two new local connectors, if quadratic energy were real off the line, the
Berry--Keating formula forces `rho.im = 0`; this contradicts the theorem that Xi has no real zero in
the open strip. For the Gamma--Mertens chart, the existing orbit-coboundary obstruction already
forces the line. Thus critical placement is equivalent to the complete eleven-chart certificate.

Negating each exact local biconditional shows that off-line placement forces all eleven failures.
Conversely, failure of reflected prime-clock summability contradicts its critical-line value, so
the synchronized failure certificate implies off-line placement. Positive and failure certificates
are exact complements at every Xi zero.

## Lean formalization

`RHTower/XiZeroLocalCriticalPhaseUniversalityLaw.lean` proves the two missing local connector
lemmas, defines eleven-field positive and failure structures, and proves critical/off-line
universality plus exact complementarity. Exact direct check:

```text
lake env lean GaloisForLFunctions/RHTower/XiZeroLocalCriticalPhaseUniversalityLaw.lean
```

passed after one batched mechanical correction (point-to-real rewrite and conjugation notation).

## Hostile literature noncollision audit

Exact combined searches found no pointwise Xi-zero classifier joining all eleven charts, and no
Gamma--Mertens finite shift-coboundary analogue. Planat--Solé--Omar formulate an RH-equivalent
inequality in Bost--Connes KMS states ([arXiv:1012.4665](https://arxiv.org/abs/1012.4665)), not a
zero-wise temperature/reflection/clock equivalence. Sierra's Berry--Keating and Rindler--Dirac
models seek spectral realizations of Riemann zeros
([arXiv:0712.0705](https://arxiv.org/abs/0712.0705),
[arXiv:1404.4252](https://arxiv.org/abs/1404.4252)); neither identifies local quadratic reality
with Arakelov unit-circle packets or finite Gamma coboundaries. Connes--Consani relate scaling
Hamiltonians and Weil positivity ([arXiv:1910.14368](https://arxiv.org/abs/1910.14368)), again
without the local eleven-way classifier or synchronized off-line failure. This is a noncollision
audit, not a priority claim.

## Log

- 2026-07-21 — Found bottom-up after Law28. Rejected vacuous global zero-orbit conjunction; retained
  pointwise eleven-chart classifier with a genuine HTGeometry Gamma-coboundary connector. Paper
  proof closed; Lean pending.
- 2026-07-21 — Local quadratic/Clifford and Gamma--Mertens converse connectors plus eleven-chart
  positive/failure laws formalized; exact direct check passed.
- 2026-07-21 — Hostile literature audit found adjacent Bost--Connes and Berry--Keating/Dirac
  programs but no pointwise eleven-chart or Gamma-coboundary law. Marked no-priority noncollision.
