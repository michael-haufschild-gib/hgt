# HC51 — HB source-FE packet Peierls classification (2026-08-28)

Formal module:
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceFEPacketPeierlsClassification.lean
- imported by formal/GaloisForLFunctions/RHTower.lean

Formalized card:
- docs/drafts/pipeline/3-formalized/hb-source-fe-cocycle-packet-peierls-classification.md

New result:
- Literal BM unit-source FE cocycle extends to an anti-linear involution T on every finite Xi packet:
  T(single q c) = single (Rq) (kappa(q) * conj(c)).
- For diagonal complex-bilinear Peierls form B_w(x,y)=sum_q w(q)x(q)y(q), full packet Ward covariance is exactly:
  B_w(Tx,Ty)=conj(B_w(x,y)) for all x,y iff
  w(Rq)*kappa(q)^2=conj(w(q)) for every q.
- Necessity on a single basis vector rules out cross-fibre/reflection cancellation.
- Canonical transported weight w_source(q)=conj(kappa(q)) satisfies the Ward equation unconditionally.
- B_source=B_fixed on all packets iff RH.
- Fixed B_1 is packet-Ward covariant iff RH.
- Any everywhere-nonzero reflection-real fixed diagonal weight is packet-Ward covariant iff RH. No positive/nondegenerate fixed diagonal renormalization evades obstruction.

Verification:
- direct lake env lean passed.
- targeted leaf build passed 11919/11919; no full/umbrella build.
- 19 public theorem axiom audits: only propext, Classical.choice, Quot.sound.
- lint: no HC51 error; unrelated repository-wide unreachable-module errors remain.
- scratch files removed; no HC51 Lean processes remain.

Bounded primary-source audit:
- arXiv:2210.15935 (Teukolsky conserved bilinear reflection form)
- arXiv:2305.19332 (literal nonlinear Teukolsky source)
- arXiv:2606.09096 (Suzuki screw/Weil quadratic form, cofinal limit conjectural)
- arXiv:2511.22755 (CCM zeta spectral triples, convergence conjectural)
No audited source states HC51 classification; novelty claim remains bounded/project-specific.

Remaining hard producer:
Derive from literal augmented Einstein–Teukolsky source/constraints/corners that fixed physical Peierls form obeys HC51 Ward equation. Transported-form covariance alone is automatic and insufficient. Same fixed-vs-transported reflected-wall obstruction is shared by HB/FZZ-P/RBH/PW-B.
