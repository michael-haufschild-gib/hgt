# GTA theta-stage Schur quartic charge flag (2026-08-27)

## Result
New module:
formal/GaloisForLFunctions/RHTower/HedenmalmThetaSchurQuarticChargeFlag.lean

For each actual signed theta source stage k:
- ThetaSourceStageSchurPacket k packages any unitary Schur triangulation U,T of thetaSourceSignedStageFinMatrix k.
- thetaSourceStageSchurPositiveQuarticCharge S applies finite-packet positive charge to diagonal nodes T_ii.

Lean proves for every Schur packet S:
Q(S)=0 iff ThetaSourceArithmeticHermiteStageProperty k
iff ThetaSourceSignedStageRealDivisor k
iff ThetaSourceArithmeticGreenStageProperty k.

Global flag quantifying over every k and every Schur packet is equivalent to:
- ThetaSourceArithmeticHermiteFlag
- ThetaSourceArithmeticGreenFlag
- ThetaSourceSignedAllStagesRealDivisor
and therefore implies RiemannHypothesis.

Nonunique Schur bases and repeated roots cause no ambiguity because the equivalence holds for every Schur packet, not only a chosen one.

## Verification
- exact /tmp scratch passed
- direct tree lake env lean passed
- targeted module build passed
- axiom audit only propext, Classical.choice, Quot.sound
- umbrella import added to formal/GaloisForLFunctions/RHTower.lean
- global formal lint was temporarily blocked by unrelated concurrently added un-wired modules; keep card at Stage 2 until lint rerun passes.

## Route impact
GTA finite spectral assembly and actual-stage transport are now closed. Remaining burden is a single source-side theorem forcing ThetaSourceSchurQuarticChargeFlag, equivalently all actual stage quartic charges vanish. This burden is RH-strength; do not present existing equivalence as unconditional RH progress by itself.

See `mem:rh/gta_finite_packet_schwarz_doubled_positive_quartic_2026_08_27`.

Novelty remains [NOVELTY UNVERIFIED].