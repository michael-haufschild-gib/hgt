# Compact logarithmic states from compensated physical producers

- **ID:** compact-physical-box-producers
- **Stage:** 2-fully-proven
- **Type:** PROVEN_ON_PAPER
- **Status:** Paper proof complete; restriction foundation formally certified. Further formalization is inactive after the user cleared the research goal.
- **Source:** continuum-coprime-shear; physical-box-average-affine-regularity
- **Statement:** Construct compact logarithmic primitive states from arbitrary physical velocities using interval truncation, explicit zero-integral compensation and box smoothing, with quantitative errors and compact-source form convergence.

## Paper theorem

Proof: docs/reports/BiScaleUncertainty/CompactLogarithmicPhysicalProducers.md.
The complete paper proof preceded new field Lean.

For n∈ℕ set r=n+1, α=exp(−r), β=exp(r), L=exp(2r), h=exp(−2r).
For arbitrary q∈L²(ℝ), put q_n=1_(α,β]q, m_n=∫_α^βq,
c_n=(m_n/L)1_(β,β+L], v_n=q_n−c_n and w_n=M_(−2r)v_n.
The exact identities ‖c_n‖²=m_n²/L and
‖v_n‖²=‖q_n‖²+m_n²/L give ‖c_n‖≤exp(−r/2)‖q‖ and
‖v_n‖²≤(1+exp(−r))‖q‖². Zero total integral removes the primitive tail.
The smoothed logarithmic state F_(w_n)∘exp is compact C¹, with support
inside [log(α−h),log(β+L)] and exact weighted Dirichlet energy.

The paper proves convergence w_n→P₊q in physical L², uniform compact
logarithmic trace convergence, explicit affine commutator bounds, and
convergence in every constructed compact source-mass-plus-jump form.
Its explicit source coefficient is K(ψ)=∫ψ(x)²exp(x)dx.
Negative physical velocity is invisible to the logarithmic state; the
physical limit is P₊q, not the full q. No independently added constants,
full uncut SourceGraph closure or divisor-domain invariance are claimed.

## Completed formal foundation

PhysicalIntervalRestriction.lean constructs actual bounded linear maps
R_(a,b)q=1_(a,b]q and P₊q=1_(0,∞)q. It proves exact squared norm integrals,
contraction, P₊q=q−negativePhysicalVelocity(q), idempotence, primitive
preservation for t≥0, and exact equality of logarithmic primitives.
Interval restrictions are integrable, have their expected integral, and
have explicit zero-left and constant-right primitive tails.

The leaf has 171 lines, two public definitions and fourteen public theorems.
Its direct `lake --old env lean -j 1 -o ...` check has an empty log and a
current normal olean. All16 public axiom audits use only propext,
Classical.choice and Quot.sound. All16 signatures and24 mathlib API probes
pass. One unique umbrella import and16 exact API catalog locations were
verified. This supporting foundation does not increment the count19/100.

Compensation, compact smoothing, approximation and form convergence are
paper-proved future formalization work; no partial modules for them exist.
The user ended the research goal and requested code closure. No work is
running on those phases and no autonomous continuation is authorized.

## Corpus and source audit

Two initial hybrid queries each inspected20 candidate statements and20
source-argument statements. Their results were partial: first deadline /
reranking unfinished, generation1447717 pending; second semantic coverage
incomplete, inventory73830 complete, snapshot1447809/current1447810,
retrieval1447801, compiler mostly pending/source-only, refresh incomplete.
Evidence: /tmp/physical-box-next-search.json and
/tmp/compact-log-primitive-next-search.json.

The focused positive-half-line/compensator query returned no candidates or
source arguments; partial deadline/vector-statement coverage,
generation1447962 pending, refresh incomplete. A lexical fallback returned
14 declarations out of36 total lexical matches under the default module
cap; all14 returned declarations were inspected. Existing negative
restriction, physical box/profile and compact graph bounds are parents.
Evidence: /tmp/compact-physical-current-search.json and
/tmp/compact-physical-lexical-search.json. No absence or novelty inference.

Primary mathlib indicator documentation and Demkowicz translation /
regularization arguments are linked in the paper. Local toolchain APIs
were checked directly. The construction applies Trap10 through actual
producers and unconditional errors. No receiver-only equivalence,
pre-floor subtraction, RH work or numerical experiment is introduced.

## Closure audit

The field README was read in full and left unchanged, SHA256
`dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933`.
No full or umbrella build, heartbeat increase, proof admission or new axiom.
The leaf is wired and indexed; no unfinished field code remains from this work.

Global lint result: 1. Existing large-file warnings: 381.
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.AnnularCoherentEnergyBounds
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.ConcentratedPairedCollarPenalty
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.FourthRootCutoffNormalization
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.PairedArrayRadialGeometry
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.SharpPairedCollarAsymptotics
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.SharpPairedCollarComparison
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.SharpProductCoupledAsymptotics
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarClampedPrimeSum
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialAtomicPacket
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialLocalCertificate
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialLocalEnergy
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialPacketEnvelope
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialPolarPacket
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarLocalizedPacket
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarRealFactorialStencil
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.BiScaleUncertainty: GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarReflectedTentPacket

No repository-wide green claim is made when unrelated lint errors remain.
Evidence: /tmp/physical-interval-restriction-build.log,
/tmp/physical_restriction_axioms.lean, /tmp/physical-restriction-axioms.log,
/tmp/physical-restriction-audit-names.json,
/tmp/physical-restriction-api-entries.txt,
/tmp/physical-restriction-index.log and /tmp/physical-restriction-lint.log.
