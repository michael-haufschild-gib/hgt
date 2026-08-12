# Projective nodal all-grade arithmetic contact cascade (2026-08-12)

Formal module: `formal/GaloisForLFunctions/RHTower/XiShiftedProjectiveNodalContactCascade.lean`.
Card: `docs/drafts/pipeline/3-formalized/mass-shifted-projective-nodal-contact-cascade.md`.
Report: §9.3 equations (9.3.674)–(9.3.682).

For `M_k=L_y(X^k p^2)` and projective Möbius tangent `V=X^2p'-nXp+ap`, the complete covariant rate is `M_k^dot=2a M_k-(2n+k+1)M_(k+1)`. Hence for `D_k=M_kM_(k+2)-M_(k+1)^2` and `J_k=M_kM_(k+3)-M_(k+1)M_(k+2)`, `D_k^dot=4aD_k-(2n+k+3)J_k`. With division-free `Q_k=M_kXp-M_(k+1)p`, `J_k=L_y(pX^(k+2)Q_k)`. At `y=w^2`, this is exactly literal completed rational-Gamma-minus-von-Mangoldt packet of `(p,X^(k+1)Q_k)`, one common kernel before aggregation. At contact `D_k=0`, derivative is negative coefficient times that packet.

Hostile no-go: coefficient growth does not imply nonsummable source work. Positive two-atom model `M_k=Ar^k+Bs^k` has `D_k=AB(rs)^k(r-s)^2>0` and `J_k=AB(rs)^k(r+s)(r-s)^2>0`, yet `sum (c+k)J_k` is summable for `|rs|<1`. Remaining open core: Xi-specific normalization against geometric moment contraction, nongeometric terminal tail from off-line divisor, or mass-grade synchronization. Nodal refinement monotonicity, sector transfer, and positive-measure/Toda routes are dead.

Verification: direct `lake env lean` pass warning-free; targeted `lake build GaloisForLFunctions.RHTower.XiShiftedProjectiveNodalContactCascade` pass; capstone axioms only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired; API indexes regenerated. Full lint remains red only on concurrent unrelated umbrella reachability/staleness during refactor.