# Observer-dimension replica-action crowding frontier correction (2026-08-08)

## Mission context
Static-local Brown--Susskind master card: `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`.
Lean corpus under active refactor. This advance is paper-only; no Lean source/build/process was touched.

## New Stage-2 theorem
Card: `docs/drafts/pipeline/2-fully-proven/observer-dimension-replica-action-crowding-law.md`.

For `N=binom(D+r-1,r)` multiplicity sums `G_p=sum p_j v_j` with `||v_j||<=L` in `R^d`,
`min_{p!=q} ||G_p-G_q|| <= 2rL/(N^(1/d)-1)`.
For fixed-shell spectral velocities, `d=12n-10`, `L=sqrt(12n-9)`; at `r=Theta(D)` the worst action gradient is at most `exp(-Omega(D/n))`.

Amplitude-weighted crowding: for iid multiplicity sums `S,S'`,
`Pr(P!=P', ||S-S'||<=delta) >= (9/16)(1+8L sqrt(r)/delta)^(-d)-C_r(lambda)`.
For the collision-good filtered seed and `delta=D^-1`, the absolute off-diagonal coefficient mass in this gradient sector is at least
`(9/16)^r exp(-O(n^2))`; relative to capture `(a/4)^r`, it is at least `(9/(4a))^r exp(-O(n^2))`.
Thus a positive first-gradient unresolved-sector majorant cannot close the circuit union.

Independent route killer: the prior onset formula
`T_tr=2BN_s/[q(a/4)^r]*(g^-1+g^-2)`
has `T_tr >= (2/q)(4/a)^r` for fixed `0<q<=1`. At `r=Theta(D)`, it is `exp(Theta(D))`; no improvements to `Q_r`, `B`, gaps, or semialgebraic exponents can make that proof Brown-time.

## Exact signed lift
For `mu_1=sum_j c_j delta_(e_j,v_j,E_j)`, conjugate reflection `star`, and `nu_1=mu_1*mu_1^star`,
`nu_r=nu_1^{*r}`.
Equal-multiplicity return is exactly hidden lattice sector `k=0`, so correct source-first excision is one final projection
`nu_r^off=P_(k!=0)(nu_1^{*r})`
before observer/incidence pushforward.
Fourier character:
`hat nu_r(xi,t)=|sum_j c_j exp(-i(tE_j+<xi,v_j>))|^(2r)`;
off-return subtracts diagonal multinomial mass `sum_p |a_p|^2`.

Two exact failures:
1. Total-variation contraction is false. For uniform positive seed law and `r=floor(cD)`, `||nu_r^off||TV=1-C_r(p)>=1-c^r`.
2. Stepwise killed transfer changes process:
`Pperp(nu_1^2)-Pperp((Pperp nu_1)^2)=2Pperp((P0 nu_1)*(Pperp nu_1))`.
It deletes paths that return at intermediate replica order and later leave.

## Surviving conjecture
Card: `docs/drafts/pipeline/1-in-progress/scale-matched-signed-action-packet-law.md`.
Construct duplication/refinement-invariant occupied-incidence quotient norm after:
full convolution -> one final return projection -> observer-action pushforward -> Fourier evaluation -> quotient norm.
Prove/falsify scale-matched contraction through `r=Theta(D)`.
Signed cancellation is current candidate, not proved necessary among all conceivable higher-order methods.

## Parent correction
`fixed-shell-transversality-onset-hardening-cone-law.md` remains valid finite-size Stage 2, but status now marks Brown-scale first-order route retired. Master log corrected. No paper may claim Brown growth from this onset theorem.
