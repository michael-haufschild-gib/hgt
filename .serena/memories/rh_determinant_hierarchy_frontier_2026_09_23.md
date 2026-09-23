# The Hankel determinant hierarchy is a RECEIVER — and how I mis-ranked it

`primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis` makes RH EQUIVALENT to
positivity of every leading Hankel determinant of `normalizedPrimeArchMoment n`.

**Why it cannot produce RH.** `normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment`
(`PrimeArchScaledHausdorffDivisorValueRelation`) gives
`m_n = Re Σ_ρ mult(ρ) · xiCentralReciprocalSquare(ρ)^(n+1)` — a power sum over the Xi DIVISOR.
Hankel positivity of `(m_n)` is exactly "every `xiCentralReciprocalSquare ρ` is a nonnegative real",
i.e. RH itself. The "source-side" framing (`PrimeArchSourceTraceHankelIntNonnegative`, whose
definition mentions no zeros) is a change of coordinates, not elimination of zero data. Also:
certifying sizes 3, 4, 5, … one at a time can never finish — the reduction
`riemannHypothesis_of_primeArchSourceMomentHankelDeterminantTailFromThree` needs ALL sizes ≥ 3.

**My ranking error.** I ranked the 645 `riemannHypothesis_of_*` hypotheses by how many theorems
CONCLUDE them vs assume them, and `PrimeArchSourceTraceHankelIntNonnegative` won 41:2. That metric
selects receivers: an RH-equivalent statement attracts many downstream reformulations. A zero-free
DEFINITION is not evidence either. The correct filter is the old one from
`rh-chain-closability-audit-2026-09-05`: check whether the hypothesis is provably equal to a
statement about the Xi divisor; if so it is a receiver whatever the counts say. That audit's
details are stale but its conclusion was right.

**AXIOM TRAP (independently valuable).** Two moment-bound machineries, different axiom status:
- `ThetaGibbsSteinSourceMinor` (Bernstein/Stein certificates, Ward 0–3): AXIOM-CLEAN.
- `PrimeArchThetaFirstAtomHighOrderMomentBounds` (64-interval rational quadrature, r ≤ 3):
  `thetaRationalQuadrature_firstAtom_bounds` uses `native_decide`, so it and
  `thetaCuspFirstAtom_highOrder_five_bounds` carry `…_native.native_decide.ax_1_1`.
60 RHTower modules use `native_decide`; the lint gate misses it (no `axiom` is declared).
ALWAYS `#print axioms` before building on a moment bound.
Also `ThetaCuspFirstAtomSingleGibbsRationalMomentBounds` (Gibbs 0–8 enclosures, consumed by several
modules) is NEVER constructed — a hypothesis class, not data.

**Clean theorems added 2026-09-23** (correct, but receiver-side; do not mistake for progress on RH):
`det_primeArchSourceMomentHankelMatrix_two_pos`,
`riemannHypothesis_of_primeArchSourceMomentHankelDeterminantTailFromThree`,
`det_primeArchSourceMomentHankelMatrix_three` + Schur form,
`normalizedPrimeArchMoment_{three,four}_eq_thetaCuspNormalizedEvenMoment` (index-7/9 recurrences),
`thetaCuspFirstAtom_tail_density_le_exp_majorant_order` (removes the `r ≤ 3` tail cap at every
order, rate `83/2 − 2r`; the original `37/2, 71/2` are its `r = 3` instance).
