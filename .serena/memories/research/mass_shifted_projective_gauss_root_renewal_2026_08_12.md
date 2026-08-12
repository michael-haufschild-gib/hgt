# Projective Gauss-root renewal (2026-08-12)

Created `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionProjectiveGaussRootRenewal.lean`, wired in `RHTower.lean`.

Exact findings:
- For roots (r_{n,k}) of current monic admission:
  [
  \sum r_{n,k}=A_n=\sum_{j<n}\alpha_j,qquad
  \sum r_{n,k}^2=Q_n+2\sum_{j<n}\beta_j.
  ]
- Centered root spread
  [
  \mathcal G_n=\sum r^2-(\sum r)^2/n
  =Q_n-A_n^2/n+2\sum_{j<n}\beta_j>0
  ]
  on finite positive blocks for (n\ge2).
- Retained projective inventory:
  [
  \mathcal R_n=2(2n+1)\mathcal G_n+(2/n)(A_n-n\alpha_n)^2
    +2(2n+1)(n+1)\beta_n.
  ]
- Complete surplus:
  [
  \mathfrak S_n=2(2n+1)(n+1)\beta_{n+1}
    +2(2n+1)\mathcal G_n+(2/n)(A_n-n\alpha_n)^2
    +2(2n+1)(n+1)\beta_n.
  ]
- Literal source work:
  [
  c_n[S_n^\sharp-h_n(\alpha_nF_n+2n\alpha_n^2)]-h_nF_n^2
  =2c_n(n+1)h_{n+1}+h_n\mathcal R_n.
  ]
- Under hard-edge affine coordinate (z=2yX-1), centered root spread scales exactly:
  [
  \mathcal G_n^{hard}(y)=4y^2\mathcal G_n(y).
  ]

Thus projective-renewal collapse is exactly empirical hard-edge root concentration plus terminal mismatch and boundary-edge collapse; vague “Jacobi shape escape” is eliminated.

Verification:
- direct `lake env lean GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionProjectiveGaussRootRenewal.lean` passed.
- targeted `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveGaussRootRenewal` passed, 11790 jobs.
- nine axiom audits show only `propext`, `Classical.choice`, `Quot.sound`.
- forbidden declaration scan and diff check passed.

Docs:
- report equations (9.3.628)–(9.3.633).
- Stage3 card `docs/drafts/pipeline/3-formalized/mass-shifted-projective-gauss-root-renewal.md`.

Next open theorem:
At parabolic first contacts (n\asymp a=\sqrt y), completed source gives a nonzero strong L2 Paley–Wiener limit. Prove such phase-space tight packets cannot coexist with empirical hard-edge root spread / n -> 0 and both boundary accounts collapsing. Candidate route: root concentration should force normalized Cayley angular derivative energy subquadratic; a nonzero L2 limit forces positive physical derivative energy, hence quadratic angular energy. Must rigorously control sublinear root outliers and does not currently have an interval-root premise pre-RH.

`docs/notes.md` correctly warns estimate chains are RH walls; this result is exact identity plus positivity, but final incompatibility is still open. Do not claim RH.