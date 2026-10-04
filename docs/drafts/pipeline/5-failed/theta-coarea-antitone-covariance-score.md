# RN: separate antitone coarea covariance score — refuted

2026-10-04. Paper and Lean closure complete; route RN remains active.

Retired conjecture: the actual score B_y=A_y-y*partial_y A_y is antitone in
coarea mass for every y>0. ThetaGaussianCoareaScore.covarianceScore_not_antitone
refutes it for every positive endpoint. The actual covariance kernel has an
adverse two-mass pair for every x,y>0. This is not a sign theorem for the
integrated covariance and not an RH falsification.

Strongest positive survivor: exact positive score-defect quadrature
q+c(y)-2*p(y)/y=(1/y)*integral_0^y s*(y-s)*c''(s) ds>0,
identified with the limit of the literal score's mass derivative at u=z^2,
z->0+. Paper proof and all9 Lean theorem audits are complete. Certificate:
../3-formalized/theta/rn-coarea-covariance-score-defect.md.

Both positive potential excess and covariance were needed in the original
Schur cross theorem. Their differentiated contributions require an actual
coupled inequality; separate monotonicity cannot supply it. The global finite-
pair comparison, general anchors, arbitrary rank and RH transfer remain open.
