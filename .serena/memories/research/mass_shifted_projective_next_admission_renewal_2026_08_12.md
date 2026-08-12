# Mass-shifted projective next-admission renewal (2026-08-12)

Created and verified `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionProjectiveNextAdmissionRenewal.lean`, wired through `formal/GaloisForLFunctions/RHTower.lean`.

Main source-first identity, on every positive shifted-Xi `(n+2)` moment block with `w>1/2`, `n>0`:
[
h_n \mathfrak S_n = 2(2n+1)(n+1)h_{n+1}+h_n\mathcal R_n,
qquad \mathcal R_n>0.
]
Here `\mathfrak S_n=(2n+1)D_n-F_n^2` is the literal adaptive mixed/completed arithmetic surplus after admission-specific drift and projective flux cost, and
[
\mathcal R_n=V_n+(2n+1)(4\sum_{j<n}\beta_j+2(n+1)\beta_n).
]
Thus current arithmetic work exactly capitalizes complete next admitted norm; this is not an orientation map or fixed linear reporter.

Exact alpha-shape decomposition:
[
V_n=2(2n+1)(Q_n-A_n^2/n)+(2/n)(A_n-n\alpha_n)^2.
]
So renewal collapse requires simultaneous lower-alpha dispersion collapse, terminal-to-lower-mean mismatch collapse, and beta-inventory collapse after normalization.

Killed conjectures:
1. Adjacent projective clock ordering: exact difference numerator `2F_n-(2n+1)(alpha_n+alpha_(n+1))` has uncontrolled sign.
2. Generic uniform next-edge fraction: positive Jacobi shapes allow beta coordinates arbitrarily small relative to nonzero diagonal mean.

Verification:
- direct `lake env lean GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionProjectiveNextAdmissionRenewal.lean` passed.
- final `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveNextAdmissionRenewal` passed.
- eight capstone `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound`.
- forbidden declaration scan and scoped `git diff --check` passed.

Documentation:
- report addendum equations (9.3.623)–(9.3.627) in `docs/reports/mass-shifted-spectral-trace-route.md`.
- Stage3 card `docs/drafts/pipeline/3-formalized/mass-shifted-projective-next-admission-renewal.md`.

Remaining exact open core:
At parabolic first contact (`n asymp sqrt y`), prove nonzero strong Paley–Wiener hard-edge compactified limits are incompatible with normalized Jacobi point-mass concentration. Need bridge from collapse of alpha dispersion/mismatch and beta inventory to degeneration/non-L2 behavior of hard-edge Cayley orthogonal polynomials. Do not claim RH.