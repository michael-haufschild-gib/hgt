# RN: global canonical coordinate-current sign

Status: formalized and directly audited. RH remains open.

For the literal theta source k, set p=−(log k)', c=p',
C(t,y)=t[p(t+y)−p(t)]/y−p(t), and
λ(t,y)=[p(t+y)−p(y)]/[p(t)+p(t+y)]. Then

    C_y−λ C_t−λ_t C < 0   for every t>0, y>0.

The theorem is `RHTower.ThetaCoordinate.canonicalCurrent_neg` in
`ThetaCoordinateCanonicalGlobal.lean`. Its only parameters are the two
positive real arguments; no RH, source-sign, spectral or integral premise
is assumed.

The actual subleading tail S(2c−c')→24 and the curvature defect propagate
2c−c'>0 from infinity. Consequently cc''−c'²>0. This proves increasing
slope elasticity tc/p and the positive two-point cross margin. Separately,
the actual projective reserve cc'−pc''>0 makes c concave in U=−log k.
The current 3tc²−3pc−tpc' has positive derivative and makes t/p convex in U.
Their strict trapezoid gaps pay the canonical base margin. The exact
base-plus-cross decomposition therefore gives the full three-point margin
positive and the canonical differential current negative.

Validation on 2026-10-02:

- Targeted `lake --old build` passed for all four changed/new proof leaves.
- Final `lake env lean GaloisForLFunctions/RHTower/<leaf>.lean` passed without
  diagnostics for ThetaCuspCurvatureLogConvex, ThetaConfluentCoordinateCurrent,
  ThetaCoordinateCrossCurrent and ThetaCoordinateCanonicalGlobal.
- All 24 public theorems were audited with `#print axioms` in a /tmp file:
  only propext, Classical.choice and Quot.sound occur.
- All new completed leaves are wired into RHTower. No full or umbrella build,
  numerical experiment, admitted proof or heartbeat increase was used.

The weighted-integral transfer and global confluent coordinate residual
are now formalized: see `rn-global-confluent-coordinate-residual.md`.
The repository lint gate reports 11 unrelated unreachable modules; no
violation names an owned leaf. Finite-pair Schur
compensation and propagation, arbitrary-rank positivity, and the retained
arithmetic RH transfer remain open. Matching kernel diagonals supplies no
off-diagonal identification.
