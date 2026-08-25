# CCM First-Clock Reduced Mass-Deficit Floor

- **ID:** ccm-first-clock-reduced-mass-deficit-floor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** rh-current-frontier-map.md · endpoints.md · direct lower-floor attack
- **Statement:** After prime-power tower collapse, the literal CCM lower floor is exactly a uniform upper bound on one explicit positive reduced mass deficit.

## Goal

Control cancellation between positive archimedean/good-tower mass and positive residual bad-tower
mass without importing Xi-zero location.  Isolate the strongest exact source-only invariant before
attempting any new positivity mechanism.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `ccmFirstClockReducedMassDeficitEventuallyBoundedAbove_iff_rh`, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact source data

For physical aperture `L ≥ π/2`, write

`S(L) = ccmPublishedSourceSineCoefficient (L/2) (2π/L)`,

`A(L) = ccmFirstClockContinuousHalfWaveBudget L (2π/L)`,

`G(L) = ccmFirstClockReducedGoodTowerMass L`, and

`B(L) = ccmFirstClockReducedBadTowerResidual L`.

`[CORPUS]` Existing exact theorems give

`π S(L) = A(L) + G(L) - B(L)`,

with `A(L), G(L), B(L) ≥ 0`.  `B` contains only one-mode outer primes plus negative parts of the
two exceptional two-mode towers at `p = 2,3`; all other complete prime-power towers lie in `G`.

Define reduced mass deficit

`Δ(L) := B(L) - (A(L) + G(L))`.

## Conjecture loop and hostile audit

1. `[FALSIFIED]` Completed coherent barycenter energy should bound outgoing CCM charge by incoming
   arithmetic bulk.  Exact Pythagorean identity gives `total = incoming + outgoing`; without an
   independent total-energy ceiling this is tautological and supplies no upper bound on outgoing
   charge.
2. `[FALSIFIED]` Atomwise phase-disk Schur completion should orient the signed logarithmic reporter.
   Completion reserve is nonnegative but nonsummable, so infinite completion destroys the required
   cancellation.
3. `[FALSIFIED]` Positive Markov density and a zero-mean wavelet should force the required source
   lower bound.  Zero mean alone fixes no sign for pairing with the signed Möbius causal complement;
   source-specific arithmetic control is still exactly missing.
4. `[PAPER-PROVED]` The strongest dependency-closed survivor is the exact deficit identity and its
   sharp tail classification:

   `Δ(L) = -π S(L)`, hence for every `C ≥ 0`,

   `S(L) ≥ -C ↔ Δ(L) ≤ π C`.

   Consequently, `Δ` is eventually bounded above on some physical tail iff RH.  Under `¬RH`, `Δ`
   exceeds every nonnegative level `π C` on every physical tail.

## Paper proof

`[PROVED HERE]` Existing half-wave reflection gives `πS=A+P`, where `P` is literal prime sine mass.
Prime-power tower collapse gives `P=G-B`.  Substitution yields `πS=A+G-B=-Δ`, proving the identity.
Since `π>0`, multiplication by `π` preserves order and gives
`S≥-C ↔ πS≥-πC ↔ -Δ≥-πC ↔ Δ≤πC`.  Quantifying over one tail gives equivalence with existing exact
tail-floor criterion `CCMFirstClockPublishedSourceEventuallyBoundedBelow ↔ RiemannHypothesis`.
Negating the quantified statement gives unboundedness on every tail under `¬RH`.

## External SOTA audit

- Connes–Consani, *The Scaling Hamiltonian* (2019), arXiv:1910.14368: semilocal operator framework,
  no all-prime lower-floor theorem.
- Connes–Consani, *Weil positivity and Trace formula, the archimedean place* (2020),
  arXiv:2006.13771: archimedean positivity, not prime/archimedean cancellation at uniform `O(1)`.
- Connes–Consani–Moscovici, *Zeta Spectral Triples* (2025), arXiv:2511.22755: finite spectral
  approximants; convergence needed for RH remains open.
- Suzuki, *Weil's quadratic form via the screw function* (2026), arXiv:2606.09096: unconditional
  finite-interval self-adjoint structures; limiting realization remains conjectural.

## No-go closure

- **Exact killing theorem/mechanism:** Positivity wrappers either leave signed reporter unoriented or
  pay nonsummable scalar reserve; energy conservation alone has wrong inequality direction.
- **Strongest positive survivor:** Exact positive-mass deficit `Δ`, with pointwise and uniform-tail
  classification and explicit `¬RH` blow-up law.
- **New insight:** Literal lower-floor problem is not control of all prime oscillation.  After local
  tower geometry, only excess of outer-prime/exceptional residual over archimedean plus stable-tower
  mass remains.  Required control is `O(1)`, not relative or averaged domination.
- **Status:** Paper proof dependency-closed and formalized in
  `CCMFirstClockReducedMassDeficitFloor.lean`.  Exact Lean endpoints are
  `pi_mul_ccmPublishedSourceSineCoefficient_eq_neg_reducedMassDeficit`,
  `ccmPublishedSourceSineCoefficient_lowerBound_iff_reducedMassDeficit_upperBound`,
  `ccmFirstClockReducedMassDeficitEventuallyBoundedAbove_iff_rh`, and
  `not_rh_implies_ccmFirstClockReducedMassDeficit_unboundedAbove_on_every_tail`.  `[OPEN CORE]`
  Unconditional proof of eventual upper boundedness of `Δ`; this is exactly RH, so no claimed
  solution.

## Log

- 2026-08-25 — created in 1-in-progress; three mechanisms falsified; exact deficit survivor paper-proved.
- 2026-08-25 — formalized, wired into `RHTower.lean`, targeted build green; axiom audit shows only standard Lean axioms.
