# Cubic two-branch contact-threshold classification (2026-08-25)

Formalized exact first-multibranch inverse landing classification in `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicTwoBranchContactThresholdClassification.lean`.

Setting: genus-zero sphere, one puncture, one Stokes orbit, exactly two distinct coefficient-generated Puiseux branches, unit Rees scale. Let `c = contactNumerator(0,1)/N`, `r` common physical rank, and `R_Xi = normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0^3/4 < 0`.

[LEAN-PROVED]:
- Exact contact law: `4 W_unit = (5 - 2c) r^2`.
- Landing fibre nonempty iff `5/2 < c`.
- Converse is constructive: choose unique orbit charge `u = sqrt((-R_Xi)/(2c-5))`.
- Every landing obeys `(2c-5)r^2 = -4R_Xi`.
- Integral threshold: nonempty iff `5N < 2 contactNumerator(0,1)`; every landing forces declared ceiling `5N < 2K`.

Mechanism: terminal energy `u^2`, physical rank `2u`, zero diagonal self-contact, two equal off-diagonal contact terms `c u^2`, and zero genus-zero one-puncture fusion. Thus local/global unit form is `(5-2c)u^2`.

This resolves the abstract minimal multibranch landing problem: below/at `5/2` impossible; above it explicit landing exists. It does not construct arithmetic source-to-charge map or meromorphic connection. Parent Euler/index mechanism is a BRIDGE; completed-Xi sharp iff is NOVELTY UNVERIFIED.

Public declarations (5) all audited with only `[propext, Classical.choice, Quot.sound]`. Targeted direct module elaboration and explicit olean emission passed. No umbrella build/full build/global lint. Scratch and generated raw/signature/new `.olean` files removed. Umbrella import added. Card: `docs/drafts/pipeline/3-formalized/route-p-cubic-two-branch-contact-threshold-classification.md`. Frontier map remained read-only.