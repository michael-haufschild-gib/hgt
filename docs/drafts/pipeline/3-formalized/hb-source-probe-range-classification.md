# HB source-probe range and nonlinear response boundary

- **ID:** HB-SOURCE-PROBE-RANGE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Goal:** unconditional Lean proof or falsification of RH through HB. This card closes a source-readout obstruction; it does not claim RH.

## Proof chain and current obligation

Literal theta-cusp source → Xi occurrence → completed spin-two angular source → physical
radial/left-QNM response and nonlinear causal cut → source-derived extinction on the fixed
Hawking clock → RH. The last source-derived extinction law remains open.

The static alternative is a coefficient-faithful phase-sensitive theta–Hawking KMS law →
noncentral resonance-centralizer exclusion → RH; its source law also remains open.

## Corpus audit

- `ThetaCuspHawkingBMCanonicalSchwarzTransportExtinctionClassification` proves both old BM
  source axes vanish exactly at critical copies, for a nonzero seed.
- `ThetaCuspHawkingDiagonalPeierlsSourceIncidenceRigidity` evaluates a weighted response as
  `w(q) * normSq(sourceAmplitude(q))`.
- `ThetaCuspHawkingAIMEBMGlobalSourceIncompatibility` proves full incidence on a critical copy
  requires the negative nonzero AIME numerator.
- `ThetaCuspHawkingBMCompletedBalancedSpinTwoFirstLiveJet` proves the multiplicity-matched
  angular jet is nonzero on every Xi copy. It is a different, non-extinct source datum.
- Whole-corpus research queries: `theta hawking centralizer`, `hawking nonlinear source`,
  `nonlinear peierls`, `conservation source cubic`, `peierls defect`, `peierls hermitian`,
  `peierls nonlinear reciprocal`, `nonlinear reciprocity linear`, `reciprocal linearity`,
  `adjoint nonlinear`, `peierls source zero`, `response profile critical line`.
- Serena cannot retrieve Lean symbols: the active Python project reports Lean paths ignored.
  Exact Lean definitions were read with `rg` and bounded file reads.

## Exact theorem

Set `p_q = hbXiPeierlsPlusSource 1 q`, `m_q = hbXiPeierlsMinusSource 1 q`, and let `B`
be the literal carrier pairing. For every profile `t : XiZeroCopy → ℂ`, these are equivalent:

1. `t(q)=B(F(p_q),m_q)` for one arbitrary function `F` on the full carrier.
2. The same holds for a weighted complex-linear skew Peierls propagator.
3. `t(q)=0` on every critical copy.

Necessity uses only `m_q=0`, not linearity, continuity, vacuum preservation, boundedness,
reciprocity, Schwarz exchange, or locality. Sufficiency sets
`w(q)=t(q)/normSq(sourceAmplitude(q))`, with Lean's total division giving zero at zero.
The weight is forced off the critical line and free on it. Thus nonlinear response enlarges
neither this source-probe range nor its critical nullspace.

Even a copy-dependent arbitrary returned vector cannot change the zero-probe conclusion.
Hardy's unconditional critical copy then excludes both full nonzero-seed AIME incidence
and recovery of the nonzero first-live angular jet through this old pairing.

## Dependency-closed paper proof

[PROVED HERE] Write `a_q` for the unit BM source amplitude and `N_q=normSq(a_q)`.
The corpus proves `a_q=0` exactly on the critical line. Hence `m_q=0` there and
`B(v_q,m_q)=0` for every returned vector `v_q`. This proves necessity even when each
`v_q` is chosen independently, without a common response map.

For sufficiency choose `w_q=t_q/N_q` and the already-constructed global weighted skew
propagator `Delta_w`. Its measured value is exactly `w_q N_q`. Off line, `N_q` is nonzero,
so this equals `t_q`. On line it is zero, and equals `t_q` exactly when the required
compatibility condition holds. No infinite sum is needed: the carrier consists of finite
packets, and a diagonal map preserves finite support for every weight profile. Thus the
same single linear map realizes every compatible profile simultaneously. Applying this
construction to the measured profile of any nonlinear map reproduces all its measurements.

If two weight profiles give the same measurements, cancellation of `N_q` proves equality
of the weights off line. On line `N_q=0`, so all weights give the same value. This proves
both directions of the complete freedom classification.

At each critical copy and every nonzero AIME seed, the existing exact residue formula
requires a nonzero same-pole remainder. The preceding zero measurement contradicts it.
The existing first-live angular-jet theorem likewise gives a nonzero value at that copy.
Hardy's theorem supplies a critical copy unconditionally, so neither universal incidence
nor universal first-live-jet reconstruction exists through this testing leg.

No RH premise or source regularity premise occurs in these global exclusions. The range
construction depends on the desired target and is not a causal PDE solution or RH producer.
The algebra is elementary bilinear annihilation and diagonal interpolation; no external
novelty is asserted.

## No-go closure

- **Exact killing mechanism:** the original complementary testing leg is zero on critical
  copies, whereas full AIME incidence and the first-live angular coefficient require a
  nonzero value there. The response can be arbitrary and copy-dependent.
- **Strongest positive survivor:** exact range, explicit simultaneous linear skew realization,
  and complete classification of the invisible weight freedom.
- **New insight:** the original probe loses the coefficient before dynamics is read. Breaking
  linearity, reciprocity, regularity, or Schwarz exchange only in the response cannot repair
  that source-readout mismatch.
- **Status:** paper proof dependency-closed; all eleven theorems pass scratch, direct
  target Lean checking, final leaf Lake build, and individual axiom audit.

This retires changing only the response while retaining the extinct BM testing leg. It does
not retire HB, nonlinear Einstein dynamics, cross-pole source replacements, or a pairing
defined on jets/distributions that no longer factors through the old zero probe.

The positive survivor is the exact range, canonical realization, and complete freedom of its
weights. A viable source-semantic repair must retain the already-proved nonzero first-live
angular jet before this scalar pairing. Its causal landing and extinction are still unproved.

Finite nonlinear response must not be confused with a linearized Green operator:
[Esposito–Marmo–Stornaiolo, equations (1.9)–(1.18)](https://arxiv.org/pdf/hep-th/0209147)
derive reciprocity for infinitesimal response. No finite nonlinear reciprocity law is imported.

## Verification plan

- [x] Recover HB chain and audit exact source definitions.
- [x] Prove exact range, canonical realization, and weight classification in scratch.
- [x] Prove full AIME and first-live-jet source-probe exclusions.
- [x] Check leaf with `lake env lean`; wire umbrella; final leaf-only `lake build`.
- [x] Audit all new theorem axioms in scratch; run formal lint; update current ledgers.

No computations supply proof evidence. No RH, positivity, or extinction premise is added.

## Verification record

Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSourceProbeRangeClassification.lean`.
Imported by `formal/GaloisForLFunctions/RHTower.lean`; generated indexes refreshed.

- Scratch `lake env lean /tmp/hb-source-probe.NT73vA/SourceProbeRange.lean`: passed, no warnings.
- `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSourceProbeRangeClassification.lean`:
  passed, no warnings.
- `lake --old build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceProbeRangeClassification`:
  passed; exactly one module compiled, in 23 seconds. Existing dependency artifacts were used.
  The ordinary no-build preflight reports 39 stale transitive targets; `--old` skips transitive
  invalidation. No full/umbrella build or dependency rebuild ran. Cached dependency warnings
  were replayed; the new leaf emitted none.
- Scratch `#print axioms` for every new theorem: all eleven use only `propext`,
  `Classical.choice`, and `Quot.sound`. No `Lean.ofReduceBool`, additional axiom, or proof debt.
- `scripts/formal_tools.py lint --check-generated`: the final snapshot reports only two
  unrelated unreachable modules, `RHTower.ThetaCuspModularCompactTube` and
  `HTGeometry.PolynomialODEJetRankThreeCompactExpansion`. These concurrent files were not
  modified. The new HB module is reachable; generated-file and proof-debt checks report no error.
- `git diff --check` passed for the edited shared ledgers and umbrella.
- No owned Lean process remains running. No commit or push.

## Exact remaining RH obligation

The proven range theorem does not supply a new causal law or make the old probe faithful.
Starting from the already-nonzero multiplicity-matched completed spin-two jet, a physical
construction must retain that coefficient in its source/testing domain before scalarization,
derive its radial/left-QNM action and causal discontinuity before divisor selection, and
prove extinction on the fixed Hawking clock. The older linear reciprocal Schwarz-exchanged
first-live radial obstruction still applies in its stated class. No such source-derived
extinction theorem, static centralizer producer, RH proof, or RH falsification is established.
