# C5 velocity Bregman cone transfer no-go (2026-08-29)

Route: CLG/TTF modular-center C5, C5-VP1/C5-VP2.

Formal module: `formal/GaloisForLFunctions/RHTower/ThetaCuspFifthRootCurvatureVelocityLikelihoodBregmanCone.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean`.

Exact decomposition: center action/slope `A=Q-D`, `a=p-E`; strict likelihood Bregman cone `0<D<tE`. New theta-specific anti-collapse: `E<1`, `D<t`. First-atom strong convexity: `38t≤p`, `19t²≤Q`. Thus literal source has `38t-1<a`, `19t²-t<A`.

Killed branch: `not_C5VelocityStrongTangentBregmanConeTransfer`. Strict cone + tangent floors + positive q2/q3 + positive action/slope do not force C5 core; negative cores persist near zero positive action for every third jet when q1²<q2.

Positive survivor: `c5VelocityActionCore_nonneg_iff_drive_pos_and_reserve`. In curvature-dominant chamber,
`core≥0 ↔ drive>0 ∧ tax/drive≤exp(A)-1`,
with `drive=39q1+t(q2-q1²)+5t²(q3-3q1q2+q1³)`,
`tax=17tq1²+3t²q1(q2-q1²)`.

Remaining C5-VP1 burden: theta-specific drive/action-reserve coupling, split when slope square crosses first-atom curvature. Generic convex/Bregman proof is dead.

Audit: direct Lean check and targeted lake build passed. Selected axioms only propext, Classical.choice, Quot.sound. Repository lint failure was unrelated unreachable concurrent modules plus existing sorry in Sieve/KubalalikaPowerEnvelope.