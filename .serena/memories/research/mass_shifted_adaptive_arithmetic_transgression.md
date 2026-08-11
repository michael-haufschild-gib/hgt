# Adaptive arithmetic transgression (2026-08-11)

Formal module: `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionArithmeticTransgression.lean`.

For literal completed adaptive rational–Gamma/von Mangoldt source (Q_w(A)) and bilinear source (B_w(P,D)), define
(T_w(P,A)=2B_w(P,A-P)+Q_w(A-P)).

Kernel-checked unconditional results:
- (Q_w(A)=Q_w(P)+T_w(P,A)).
- (T_w(P,A)=Q_w(A)-Q_w(P)).
- (T_w(A,B)+T_w(B,C)=T_w(A,C)), hence diagonal zero and antisymmetry.
- Mixed source-mass rectangle:
  (T_w(P,A)-T_v(P,A)=[Q_w(A)-Q_v(A)]-[Q_w(P)-Q_v(P)]).
- For current canonical admission (P_{n,w}) and admission frozen at (a):
  (Q_w(P_{n,a})=2h_n(w)E_n(w)+T_w(P_{n,w},P_{n,a})).
- Exact negativity threshold:
  (Q_w(P_{n,a})<0) iff (T_w(P_{n,w},P_{n,a})<-2h_n(w)E_n(w)).

Scientific consequence: fixed-source-mass admission mismatch is an exact path-independent transgression, so it is not genuine holonomy. Only mixed mass–admission curvature (rectangle) can obstruct positivity transport. Next theorem must bound/sign that rectangle along the selected bounded-scale/hard-edge branch; orientation maps, root division, and fixed linear reporters cannot supply this.

Verification passed:
- `lake env lean GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionArithmeticTransgression.lean`
- `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionArithmeticTransgression`
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- forbidden-token and `git diff --check` clean.

Paper card: `docs/drafts/pipeline/3-formalized/mass-shifted-canonical-admission-arithmetic-transgression.md`.
Report addendum: equations (9.3.441)–(9.3.447) in `docs/reports/mass-shifted-spectral-trace-route.md`.
Frontier map item 51 records alternate current-admission producer refinement.
