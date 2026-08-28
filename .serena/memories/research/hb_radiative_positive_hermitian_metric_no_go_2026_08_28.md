HC90 formalized and promoted.

Module: formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMRadiativeSourceFEPositiveHermitianMetricNoGo.lean
Card: docs/drafts/pipeline/3-formalized/hb-radiative-antilinear-positive-hermitian-metric-no-go.md
Umbrella: formal/GaloisForLFunctions/RHTower.lean imports module after HC89.

New result:
- Actual HC89 Green/source-FE cocycle lifts to conjugate-linear finite-packet transport T_rad with coefficient/singleton formulas and T_rad²=id.
- Base finite Hermitian form H0(x,y)=dot(conj x,y) is proved sesquilinear, conjugate symmetric, with diagonal equal finite sum of normSq; energy nonnegative and zero iff x=0.
- H_rad(x,y)=H0(x,y)+H0(T_rad y,T_rad x) is a genuine positive-definite Hermitian form and T_rad is exactly antiunitary: H_rad(Tx,Ty)=conj(H_rad(x,y)).
- h(q)=norm(kappa_rad(q)) is strictly positive and obeys h(Rq)*normSq(kappa_rad(q))=h(q).
- Closed theorem hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveHermitianBrightCancellation packages these facts together with HC89 off-line bright cancellation.
- This kills positivity/Hermiticity as standalone HB selector. Surviving burden: fixed/source-independent metric selection or reflection-real coordinate weights from local detector/source algebra.

Audit:
- lake env lean source passed.
- targeted lake build module passed 12019/12019.
- #print axioms main/antiunitary/orbit balance: propext, Classical.choice, Quot.sound only.
- formal lint has only unrelated pre-existing unreachable modules; no HC90 finding.
- /tmp scratch files removed; no HC90 Lean process remains. One unrelated /tmp/SCScaled.lean process existed and was not touched.
- Frontier map remained read-only.