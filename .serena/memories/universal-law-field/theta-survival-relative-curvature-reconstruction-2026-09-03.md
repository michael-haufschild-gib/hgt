# ULF-TSRC-001 — theta-survival relative curvature reconstruction

Paper card:
`docs/drafts/pipeline/2-fully-proven/universal-law-field/restricted-grassmannian-formation-geometry/theta-survival-relative-curvature-reconstruction.md`

Inputs:
- `ULF-TM6H-001`: literal theta Mellin-six holonomy gives `m_n=105/((2n+3)(2n+5)(2n+7))`.
- `ULF-PHSF-001`: forced shift `C e_n=sqrt(r_n)e_(n+1)`, `r_n=m_(n+1)/m_n=(2n+3)/(2n+9)`, `ind C=-1`.
- `ULF-PHIN-001`: prime-mixed integral-nuclear `T=Phi tensor A_form`, `Phi=diag(w_n)`, `w_n=m_n-m_(n+1)`, trace one.

New dependency-closed paper theorem:
- `A_minus=I-C*C`, `A_plus=I-CC*`.
- Both positive compact but non-Schatten-one.
- `K=A_plus-A_minus=C*C-CC*=[C*,C]` is positive Schatten-one.
- Diagonal: `kappa_0=1/3`; `kappa_n=12/((2n+7)(2n+9))` for `n>=1`.
- `Tr K=||K||_1=1`, `||K||=1/3`, `Tr K=-ind C=Tr T`.
- Exit and curvature laws reconstruct exactly:
  - `m_n=sum_(j>=n)w_j`, `r_n=m_(n+1)/m_n`, `kappa_0=r_0`, `kappa_n=r_n-r_(n-1)`.
  - `r_n=sum_(j<=n)kappa_j`, `m_n=prod_(j<n)r_j`, `w_n=m_n(1-r_n)`.
- Prime lift `mathcal K=K tensor A_form` is prime-mixed positive S1, trace one, norm <=1/3; raw lifted defects are compact non-S1. `mathcal K <-> T` via history reconstruction.

Interpretation:
Universal metric anomaly is a canonical pair of non-nuclear incoming/outgoing metrics whose relative curvature is nuclear/integral. It is not a scalar counterterm. This solves source-side relative subtraction and fixes full filtration that completion must preserve.

Hostile limit:
- Weighted-shift self-commutator trace and homological-index language are classical (arXiv:2508.02896; arXiv:1402.0475).
- Generic cyclic pairing, total trace preservation, or scalar capacity do not close RH. Corpus proves route-P collision trace-capacity law is RH-equivalent.
- Remaining theorem: pre-divisor same-boundary morphism from literal integer/Poisson self-duality carrying full filtered prime-mixed relative pair into completed pair, plus exhaustion. If completed reporters exhaust any strict-right rank-one horizon, filtered preservation contradicts the added reporter mass.

Updated:
- `euler-theta-relative-superconnection.md`: counterterm construction removed from open core; now asks for source-defined filtered same-boundary morphism and bivariant boundary.
- `STATUS.md`: F531, F532, MUST-163; stays below 5000 lines.

Formal status:
Not yet Lean-certified. No Lean files or builds were run in this research loop. Existing Lean certifies inputs only.