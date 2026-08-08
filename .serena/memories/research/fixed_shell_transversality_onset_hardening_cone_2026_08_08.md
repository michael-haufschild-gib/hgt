# Fixed-shell transversality onset and hardening cone (2026-08-08)

## Result
Stage-2 card: `docs/drafts/pipeline/2-fully-proven/fixed-shell-transversality-onset-hardening-cone-law.md`.
Master log: `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`.

Conjecture/fail loop established a capacity-clock-speed decomposition for the static-local recurrence route:
- spectral collision controls plateau capacity and logarithmic lifetime;
- worst balanced-action gradient tail `Q_r(zeta,g)` plus derivative constant `B` controls common fixed-time onset;
- local simulation complexity `S_H(u,delta)` controls a deterministic backward hardening cone.

Key exact coefficient identity:
`sum_(alpha,beta)|A|=(sum_j |<z,Pi_j chi>|)^(2r)<=1`.
Generic paired-replica equality already exists in Lean as
`HTGeometry/TracelessReplicaDyadicActionShellLaw.lean:complexReplicaPairTotalVariation_eq_pow`.
Projection contraction/filter specialization are not yet formalized.

Raw full-overlap moments only give collision scale `C^(r/2)`, too weak. Correct repair is one common smooth light-sector filter:
`tau=4C/a`, weights `f(p_j/tau)`.
Removed norm is at most `sqrt(a)/2`; capture forces filtered squared overlap at least `a/4`.
On support, `p_j<8C/a`, and exact Steinhaus diagonal moment is at most
`r!(8C/a)^r`.
With collision cutoff support `C<=4L/(D+1)`, dividing by `(a/4)^r` gives
`r!(128L/(a^2(D+1)))^r`.
Choose `r=floor(a^2(D+1)/(256L))`; after `N_s<=2^(r/2)` circuit union, completed shortcut probability is at most `2^(-r/2)`.

For finite `n,r`, fixed-shell nowhere-flatness plus Nash/semialgebraic Lojasiewicz and tube volume proves
`Q_r(zeta,g)<=A_0 zeta^alpha_0 + A_(r,zeta) g^alpha_(r,zeta)`.
Nonstationary phase with `X=grad(phi)/|grad(phi)|^2` gives defect
`Q_r+B |t|^-1(g^-1+g^-2)`.
This yields an all-future finite onset
`T_tr=2 B N_s/[q(a/4)^r]*(g^-1+g^-2)`
once `Q_r<=q(a/4)^r/(2N_s)`.

Existing read-only Lean module
`HTGeometry/AutonomousWordComplexityConeLaw.lean` proves the abstract backward cone.
State specialization:
`C_epsMinus(psi_(T-u)) > s-S_H(u,epsPlus-epsMinus)`.
Nearly linear nearest-neighbor simulation turns plateau depth `Omega(2^n/(L log n))` into an exponential `2^(n(1-o(1)))` hardening shoulder. This is not monotone growth from t=0.

## Falsified routes
- Collision alone cannot control onset: spectra `(0,1,2+eta)` retain collision 1/3 but have height-2 action eta.
- Minimum nonzero action is wrong because negligible-weight levels can generate irrelevant tiny actions.
- Random radial scale quantifies onset but cancels under interaction-normalized time.
- A local plateau cannot jump arbitrarily fast: backward composition cone forbids it.

## Exact remaining frontier
1. Growing-replica large-n control of `Q_r` and `B` at `r=Theta(2^n/L)` strong enough for `T_tr<=2^O(n)`.
2. Weighted action/coarea profile avoiding the worst-character union without losing adaptive circuit targets.
3. Initial pointwise ramp or classification/removal of pre-cone delay.
4. Formalize after corpus refactor; no Lean files were written or built in this turn.

Do not claim full Brown--Susskind growth law or Nature readiness yet.