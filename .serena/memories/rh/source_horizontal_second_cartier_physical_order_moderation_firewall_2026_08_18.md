# Second-Cartier physical order/moderation firewall (2026-08-18)

Formalized module: `formal/GaloisForLFunctions/RHTower/SourceHorizontalSecondCartierPhysicalOrderModerationNoGo.lean`.
Card: `docs/drafts/pipeline/3-formalized/source-horizontal-second-cartier-physical-order-moderation-firewall.md`.
Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`; umbrella not built.

Exact source setup in `Q = Z[q,q^-1]/(q-1)^3`: forward `F`, inverse `R`, quadratic `G`; existing `F+R=G`, `G != 0`. New exact laws: `F^3=0`, `R^3=0`, `G^2=0`, `F^2=G`, `F*R=-G`.

Sharp results:
1. Any multiplicative map from Q to a reduced commutative ring kills F, R, G, and the entire integral rank-two source lattice. No such map is injective.
2. Reducedness is not needed for the order collision. In any partially ordered additive commutative ring, a multiplicative receiver declaring both the forward-square channel G and Gamma-Hermitian channel -G nonnegative must kill G. A receiver retaining G must reject one positivity.
3. Any additive D from the literal source lattice to Z→C mapping F and R to the same nonzero coefficient times exact Hardy positive/negative halves is forced to map G to the scaled bilateral eigenfamily. This is moderate iff character norm is 1. For any strict-right Xi copy and prime, norm 1 contradicts strict-rightness; therefore no such coefficient-faithful moderate D exists.

Capstones:
- `sourceHorizontalSecondCartierPhysicalOrderModeration_orderFirewall`
- `sourceHorizontalSecondCartierPhysicalOrderModeration_firewall`
- `sourceHorizontalStrictRightXi_no_coefficientFaithful_secondCartier_moderation`

Verdict: ordinary source-derived physical order/moderation is impossible for this nonzero quadratic class. Exact escape class must be nonmultiplicative/relation- or Krein-jet-valued and avoid the exact Hardy additive horn; merely choosing a nonreduced ordered target does not evade the G/-G sign collision.

Verification: direct `lake env lean` PASS; exact leaf `lake build GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierPhysicalOrderModerationNoGo` PASS; capstones depend only on `propext`, `Classical.choice`, `Quot.sound`. Global lint reached this module through umbrella but exits nonzero due unrelated pre-existing unreachable modules (HellingerCurvature and several HTGeometry leaves).