# Theta C5 cofinal functional absorption

- **ID:** `theta-c5-cofinal-functional-absorption`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE with dependency-closed structural theorems
- **Source:** literal completed-theta product fibres, higher/first atom likelihood ratio, and exact source C5 numerator
- **Conjecture label:** `C5-RB1`
- **Statement:** The surviving modular-center statement is a source-specific upper envelope for
  normalized Riccati growth at negative intrinsic C5 minima. Put

  ```text
  IntrinsicC5(t) := sourceC5(0,t) / sourceDrop(0,t)^2
                  = 4 * cumulativeEndpointMassElasticityBalance(0,t).
  r   := exp(q(t)) - 1,
  s   := t*q1(t)/r,
  b   := t^2*(q2(t)-q1(t)^2)/r,
  rho := t^3*(2*q1(t)*q2(t)-q3(t))/r,
  P0  := 99*s - 123*s^2 + 24*s^4 - 51*b + 36*s*b + 16*s^2*b - 65*b^2.

  at every negative local minimum of IntrinsicC5,
    P0 + 100*s*r*rho - 8000*t^4/r - 25*r*(b + 2*s^2*r)^2 <= 0.
  ```

  Lean proves this statement is equivalent to source `C5(0,t) >= 0` at every positive radius.
  The exact second-order identity removes the fourth source jet using the corpus strict
  fourth-Turan theorem and exposes two costs: `8000*t^4/r` and the displayed perfect square. Every
  intrinsic local minimum unconditionally forces the opposite strict inequality, so a C5 failure
  must make normalized Riccati growth overpay both costs. The remaining research problem is an
  upper, not lower, control of this literal completed-theta Riccati margin in the negative-minimum
  chamber.

## Corpus derivation

This conjecture was frozen only after corpus search exposed all of its terms:

1. `thetaCuspCompletedProductFiberAmplitude_one_add_higherTail` gives the exact completed
   product-fibre split `source = first fibre + cofinal higher tail`.
2. `exists_thetaCuspCompletedProductFiberAmplitude_one_rise` proves that the first-fibre-rise
   chamber is nonempty.
3. `thetaCuspReflectedSourceFirstDrop_pos` forces the cofinal higher-tail drop to be strictly
   positive in that chamber.
4. `thetaCuspHigherToFirstAtomLikelihoodRatio_antitoneOn` and the exact derivative chain through
   the higher likelihood jets provide the source-specific variables for attacking the sign.
5. The new unconditional total-variance identity proves

   ```text
   A1*A2*C5(A1+A2,D1+D2,J1+J2)
     = A2*(A1+A2)*C5(A1,D1,J1)
       + A1*(A1+A2)*C5(A2,D2,J2)
       + 4*t^2*(A1*D2-A2*D1)^2.
   ```

6. At modular center the infinite cofinal tail is literal, not a formal residual:

   ```text
   higherTail(t) = firstFiber(t) * R(t) * (2 + R(t)),
   R = higherAtomTail / firstAtom.
   ```

   Lean proves both tail derivative identities through order two and identifies the residual
   curvature with the functional fifth-root numerator of the actual infinite tail.
7. `exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_pos_right` supplies strict C5 at
   the coalesced boundary.
8. `tendsto_pow_mul_iteratedDeriv_thetaCuspFullSource_atTop_zero` and the resulting exact C5 limit
   supply strict C5 on a cofinal tail.
9. Differentiating the corpus C5 numerator gives the explicit third-jet velocity

   ```text
   39*A*D + t*A*J - 17*t*D^2 + t^2*(5*A*K - 3*D*J),
   K = dJ/dt.
   ```

   Compact minimization then proves every negative C5 value forces a positive-radius stationary
   negative witness. Differentiating once more and applying the local-minimum second-derivative
   test sharpens the live statement to `C5-SA1`.
10. The corpus identity

    ```text
    sourceC5 = 4 * sourceDrop^2 * cumulativeEndpointMassElasticityBalance
    ```

    makes `IntrinsicC5 := sourceC5/sourceDrop^2` exactly four times a bounded dimensionless
    balance. A second compact minimization proves every failure has a negative local minimum of
    `IntrinsicC5`. Quotient differentiation gives the exact critical law

    ```text
    C5Velocity * sourceDrop = 2 * sourceC5 * sourceFlux,
    ```

    so its raw C5 velocity is strictly negative. At a negative raw-C5 stationary point the
    derivative of `IntrinsicC5` is strictly positive. Hence the two critical witnesses are
    necessarily distinct. This corpus-derived reduction sharpens the live statement to
    `C5-ILM1`.
11. Corpus search then combined the intrinsic stationary law with
    `thetaCuspReflectedLogRiccatiMargin_nonneg` and the strict fourth-Turan ceiling. Exact
    normalization removes the fourth jet and proves

    ```text
    5*t^2*IntrinsicSecondOrderTuranCeiling
      = sourceDrop^4 *
          (P0 + 100*s*r*rho - 8000*t^4/r - 25*r*(b + 2*s^2*r)^2).
    ```

    At every intrinsic local minimum the left side is strictly positive. Thus every hypothetical
    failure must force strict Riccati overcompensation after paying one fourth-Turan cost and one
    perfect-square cost. This exact corpus-derived reduction sharpens the live statement to
    `C5-RB1`. The earlier likelihood third-cumulant sign gives no upper bound for `rho`; the
    formal atom/likelihood Riccati no-go prevents promoting that local sign architecture again.

Therefore, in the rise chamber, the product of first and tail drops is negative and Lean proves

```text
source C5(0,t) >= 0
  iff cofinalFunctionalAbsorptionBudgetAtZero(t) <= 0.
```

This is not generic positive-mixture closure. The first component has negative accumulated drop;
the higher tail must absorb the first-fibre curvature and the strictly nonnegative projective-flux
mismatch square.

## Attack

The first structural attack is now closed in Lean. Differentiating the exact factorization

```text
higherTail = firstFiber * R * (2 + R)
```

twice gives the literal infinite-tail laws

```text
D_tail = D_first * L - F_first * L',
J_tail = J_first * L + 2 * D_first * L' - F_first * L'',
L = R * (2 + R).
```

Substitution exposes an exact likelihood-convexity tax. In every first-fibre-rise chamber it is
strictly positive:

```text
tax = -5*t^2*A_first*A_source*A_tail*F_first*L'' > 0.
```

Hence `L >= 0`, `L' <= 0`, and `L'' > 0` alone point in the wrong direction and cannot close
the conjecture. Corpus antitonicity together with strict positivity of the second likelihood jet
also forces `L' < 0`. Expanding its square exposes a second strictly positive tax:

```text
baseBudget = driftBudget + slopeSquareTax,
slopeSquareTax = -4*t^2*A_first*A_tail*F_first^2*(L')^2 > 0,
functionalBudget = driftBudget + slopeSquareTax + convexityTax,
functionalBudget <= 0
  iff driftBudget <= -(slopeSquareTax + convexityTax).
```

The second structural attack is also closed. The first fibre has an absolute-value seam, so Lean
constructs its smooth right-chamber flux representative and proves exact fundamental-theorem laws:

```text
firstDrop(t) = integral_0^t firstRightFlux(s) ds,
sourceDrop(t) = integral_0^t sourceFlux(s) ds,
tailDrop(t) = integral_0^t tailRightFlux(s) ds.
```

After substitution, all first/tail component drops cancel from the sign criterion. The drift budget
factors as `firstDrop * tailDrop * chordReserve`, while the two positive taxes factor as
`-(firstDrop * tailDrop) * taxDensity`. More strongly, for every `t > 0`:

```text
sourceC5(0,t) = integralChordReserve(t) - taxDensity(t),
taxDensity(t) > 0,
sourceC5(0,t) >= 0 iff taxDensity(t) <= integralChordReserve(t).
```

Thus no componentwise sign or local likelihood/Riccati argument can finish the proof: the sole
positive producer must be the accumulated full-source chord. Corpus exponential derivative decay
then proves

```text
sourceC5(0,t) -> 24 * sourceProduct(0,0)^2 > 0
```

as `t -> +infinity`. Together with the corpus strict coalesced chamber, modular-center C5 first
reduces to one compact annulus. A new exact minimum principle removes the annulus quantifier:

```text
global center C5
  iff every positive-radius stationary C5 point is nonnegative
  iff taxDensity <= integralChordReserve at every C5Velocity-zero point.
```

Differentiating once more gives the exact fourth-flux acceleration. Any failure witness is a
negative local minimum, hence has zero C5 velocity and nonnegative C5 acceleration. The strict
source fourth-Turan law simultaneously gives the native center ceiling

```text
reflectedLogJetFour(0,t) + 320 < 2*reflectedLogJetTwo(0,t)^2.
```

The further intrinsic normalization first gave `C5-ILM1`. Differentiating it and applying strict
fourth-Turan now eliminates the fourth jet entirely. The sharpened live attack is `C5-RB1`: prove
the displayed Riccati compensation budget nonpositive only at negative local minima of
`sourceC5/sourceDrop^2`. This is an exact iff, not an added hypothesis. The generic local
atom/likelihood Riccati architecture remains retired by
`atomLikelihoodRiccatiSignArchitecture_with_localC5_does_not_force_globalC5`; the required upper
envelope must use the literal completed-theta action or its nonlocal likelihood representation.

Failure criterion: an exact theta-derived sign reversal of this budget. If found, retain the
sharp scale chamber or equality classification and retire only the modular-center cofinal
absorption subroute.

## RH proof chain and uncovered joins

This conjecture contributes to the following explicit corpus chain:

1. **Negative-minimum Riccati-budget upper envelope `C5-RB1`** (this card) gives source `C5 >= 0`
   at every modular-center positive scale by
   `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_negativeIntrinsicMin_riccatiBudget_nonpos`.
2. Combine modular-center C5 with still-open off-center/complement transport to obtain global
   `thetaCuspReflectedSourceFifthRootCurvatureNumerator >= 0`.
3. `thetaCuspReflectedSourceOddParityWall_or_exists_fifthRootCurvatureNumeratorFailure` then rules
   out every negative literal source rank-four odd wall.
4. `thetaCuspCenterMixedOddParityWall_nonneg_of_sourceFibres`, followed by
   `thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_oddParityWall`, lands this at physical
   center-mixed rank four.
5. Rank four is not RH. Still-open higher-packet positivity and a cofinal no-escape theorem must
   upgrade the finite-rank source orientation to the universal theta packet/tilt-flux sign.
6. `riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg` then identifies that universal sign
   with RH (equivalently use `riemannHypothesis_iff_xiWeilPolarization_nonneg`).

Thus this conjecture closes one genuine C5 chamber in the first rank-four arrow; it does not hide
the later all-rank and source-to-Weil joins.

## Novelty / hostile audit

- Corpus had no fifth-root mixture law, no cofinal C5 budget, no likelihood factorization of the
  completed product-fibre tail, no exact seam-safe drop integral laws, and no
  chord-reserve-minus-tax identity before this card's Lean modules. It also had no theorem reducing
  a global theta C5 failure to a stationary strict reserve overspend.
- Planat--Solé, *Second-Level Concavity of the Riemann Xi Kernel* (arXiv:2608.19160), proves a
  different Laguerre-expression log-concavity theorem and makes no RH claim; it contains neither
  this `C5` total-variance identity nor the cofinal budget.
- Michałowski, *On the Pólya Frequency Order of the de Bruijn--Newman Kernel* (arXiv:2602.20313),
  leaves global `PF4` open and studies a different Toeplitz threshold; it contains no product-fibre
  likelihood absorption law.
- Exact August 2026 searches found no external statement of the algebraic total-variance identity,
  literal cofinal-tail curvature split, seam-safe integral laws, or chord-reserve/tax
  factorization. This is a literature-search conclusion, not a Lean theorem.

## Lean artifacts

- `GaloisForLFunctions.HilbertMetric.FifthRootCurvatureMixture`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureTotalVariance`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureLikelihoodTax`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureLikelihoodSlopeTax`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureCofinalChordReserve`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureCompactCore`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureStationaryLocus`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureStationaryAcceleration`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicBalance`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicAcceleration`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicFourthTuran`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicRiccatiBudget`
- `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureRiccatiBackwardDrift`
- `GaloisForLFunctions.HilbertMetric.RiccatiChargeFifthRootNoGo`
- Main exact hard core:
  `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_cofinalFunctionalBudget_nonpos`
- Likelihood factorization:
  `thetaCuspCompletedProductFiberHigherTail_zero_eq_firstFiber_mul_likelihoodFactor`
- Sharp replacement:
  `thetaCuspCompletedProductFiberCofinalFunctionalBudget_nonpos_iff_drift_le_neg_twoTaxes`
- All-radius nonlocal hard core:
  `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_iff_taxDensity_le_integralReserve`
- Cofinal limit and compact reduction:
  `tendsto_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_atTop` and
  `exists_thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_compactCore`
- Stationary-locus reduction and exact surviving burden:
  `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_stationary_taxOverspend`
  and
  `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_stationary_taxReserve`
- Stationary-acceleration/fourth-Turan reduction and sharpened exact surviving burden:
  `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_acceleration_taxOverspend`
  and
  `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_stationary_acceleration_taxReserve`
- Intrinsic-balance critical law, two-critical-point failure classification, and live exact burden:
  `thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_isLocalMin_velocity`,
  `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_two_distinct_critical_taxOverspends`,
  and
  `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_intrinsicBalance_localMin_taxReserve`
- Fourth-Turan/Riccati compensation identity and sharpened live exact burden:
  `thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderTuranCeilingAtZero_eq_riccatiBudget`,
  `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_failure_forces_intrinsicRiccatiCompensation`,
  and
  `thetaCuspReflectedSourceFifthRootCurvatureNumerator_zero_nonneg_all_iff_negativeIntrinsicMin_riccatiBudget_nonpos`

## Gates

- [x] corpus-derived statement and exact source coordinates
- [x] explicit downstream RH chain with uncovered joins named
- [x] total-variance identity, literal tail jets, chamber nonemptiness, and exact iff formalized
- [x] infinite-tail product jets and strict likelihood-convexity tax formalized
- [x] strict likelihood decrease and positive slope-square tax formalized
- [x] monotone/convex sign-only subroute retired with a formal sharp replacement hypothesis
- [x] seam-safe first/source/tail drop integral identities formalized
- [x] exact all-radius chord-reserve-minus-strict-tax identity formalized
- [x] unconditional cofinal C5 positivity and compact-core reduction formalized
- [x] every possible center-C5 failure localized to a stationary strict tax overspend
- [x] every failure localized further to nonnegative C5 acceleration under the strict native
  fourth-Turan jet ceiling
- [x] intrinsic drop-square normalization and two-distinct-critical-overspend law formalized
- [x] fourth jet eliminated at intrinsic minima; exact Riccati compensation and perfect-square
  cost law formalized
- [x] lower-drift/charge-positivity/charge-monotonicity closure mechanism retired with a smooth
  analytic countermodel; exact nonlocal theta charge envelope retained
- [x] August 2026 primary-literature collision audit
- [ ] prove or refute negative-minimum Riccati-budget upper envelope `C5-RB1` from literal theta
  action/likelihood structure
- [ ] extend surviving sign mechanism off modular center and across complement chamber
- [ ] close global source C5 and physical rank-four wall
- [ ] build higher packets and cofinal source-to-Weil no-escape

## Log

- 2026-08-29 — Opened after corpus search and exact Lean reduction. No computation entered the
  proof or the conjecture.
- 2026-08-29 — Proved both cofinal product-jet laws and the exact positive convexity-tax
  decomposition. Reduced the conjecture to a strict negative base reserve; no computation used.
- 2026-08-29 — Proved strict negativity of the cofinal likelihood slope and split a second
  positive slope-square tax. Remaining hard core is the drift reserve paying both taxes.
- 2026-08-29 — Proved seam-safe exact drop integrals, cancellation of component drops, and the
  all-radius identity `source C5 = integral chord reserve - strictly positive tax density`.
- 2026-08-29 — Proved `source C5(0,t) -> 24*sourceProduct(0,0)^2 > 0`; combined with strict
  coalesced positivity to reduce the full modular-center problem to one qualitative compact annulus.
- 2026-08-29 — Differentiated the exact C5 numerator and proved every failure attains a negative
  stationary minimum. The full center problem is now exactly `C5-SL1`: reserve dominance only on
  the zero locus of the explicit third-jet C5 velocity.
- 2026-08-29 — Differentiated through the fourth source-flux jet. Every failure now forces one
  stationary strict tax overspend with nonnegative C5 acceleration and the strict center
  fourth-Turan ceiling `q4 + 320 < 2*q2^2`. The exact live burden is `C5-SA1`, restricted to
  stationary points with nonnegative acceleration. No computation enters the proof.
- 2026-08-29 — Removed the positive accumulated-drop square from C5. The intrinsic quotient is
  exactly four times the bounded cumulative mass/elasticity balance. Every failure forces a
  negative intrinsic local minimum with raw C5 velocity strictly negative and a distinct raw-C5
  stationary minimum with nonnegative acceleration; both strictly overspend the exact reserve.
  The exact live burden is now `C5-ILM1`. No computation enters the proof.
- 2026-08-29 — Eliminated the fourth jet at every intrinsic local minimum using the corpus strict
  fourth-Turan law. Proved an exact normalized identity in which Riccati growth must pay
  `8000*t^4/r` and `25*r*(b+2*s^2*r)^2`. Every C5 failure therefore forces strict Riccati
  overcompensation plus likelihood-tax overspend. The exact live burden is `C5-RB1`, with the full
  downstream rank-four, higher-packet, TTF/Weil, and RH joins unchanged. No computation enters the
  proof.
- 2026-08-29 — Hostile-tested the corpus-derived backward-normalized-Riccati attack. Its exact
  integrating factor is `r*(r+1)^2/t^3`; the conjugated charge is `exp(2q)*(2*q1*q2-q3)`, starts at
  zero, and is strictly increasing. Thus normalized cofinal decay cannot provide a terminal-zero
  upper bound: it is caused by collapse of the inverse factor, not decay of charge. This retires
  the local backward-drift subroute without changing conjecture `C5-RB1` or its RH chain.
- 2026-08-29 — Formalized the strongest positive survivor. The charge is exactly the raw
  source-product flux Wronskian
  `P(0)^2/P(t)^4 * -(P*K + D*J)`, with `P*K + D*J < 0`, and global modular-center C5 is exactly
  equivalent to a division-free charge-envelope inequality at negative intrinsic minima. The
  remaining attack must upper-control this literal source Wronskian using nonlocal chord,
  likelihood, or modular-ODE structure; local Riccati/fourth-Turan signs alone have wrong
  orientation. No new conjecture was introduced and no computation entered any proof.
- 2026-08-29 — Killed the last lower-drift shortcut. The corpus sextic countermodel has its
  conjugated Riccati charge strictly increasing from zero on the whole physical ray, global
  nonnegative Riccati margin, seam-positive C5, and the previously formalized six-jet
  atom/likelihood architecture, yet later C5 is strictly negative. Therefore charge positivity or
  monotonicity cannot imply the stationary envelope. The live `C5-RB1` burden is now exclusively a
  theta-specific nonlocal upper comparison. No computation entered any proof.
- 2026-08-29 — Froze `C5-FLC1`, a corpus-derived stationary flux-curvature classification.  Write
  `A` for accumulated source drop, `D=A'`, `J=D'`, `K=J'`, and
  `x=t*D/A`, `y=t*J/D`.  Corpus angle concavity gives `0 < x <= 2`.  At a negative local minimum of
  `C5/A^2`, the exact intrinsic stationary law eliminates `K`.  The proposed exact certificate is

  ```text
  d := -(24 - 9*x + 5*x*y - 4*x^2) > 0,
  125*x^2 * (t^2*(D*K-J^2)-t*D*J+2*D^2)/D^2
    = -20*(x-2)^2*(x^2+36)
      -5*d*(5*x^2-24*x+48) - 5*d^2 < 0.
  ```

  The left side is the division-free logarithmic curvature of the positive normalized squared
  flux `D(t)/t` in `t^2`.  Thus every hypothetical center-C5 failure is forced into strict local
  flux log-concavity at its canonical negative intrinsic witness.  This kills any attempt to
  obtain the missing `C5-RB1` upper envelope from local flux log-convexity, even after restricting
  to the exact stationary failure locus; the surviving proof must compare this quantified
  negative local curvature with cumulative earlier theta flux.  RH chain remains
  `C5-FLC1 classification -> nonlocal exclusion of its strict-negative chamber -> modular-center
  C5 -> off-center/rank-four -> higher packets/no-escape -> CLG/TTF or Weil -> RH`.
  Falsifier: failure of the displayed polynomial identity after substituting corpus definitions
  and the exact intrinsic stationary law.  August 2026 searches found reverse-hazard elasticity
  and generic log-concavity literature, but no stationary fifth-root certificate or theta-source
  analogue.  No computation enters the conjecture.
