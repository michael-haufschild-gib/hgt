# Radial--Krylov projected incidence frontier (2026-08-08)

User requires heavy conjecture/proof/failure loop and forbids Lean writes/builds during corpus refactor.

## New Stage-2 theorem

Card: `docs/drafts/pipeline/2-fully-proven/radial-krylov-projected-complete-incidence-law.md`.

For bounded self-adjoint H, seed psi0, Krylov projection P_K, finite target image Z, and replica order r:

- `||psi(t)-P_K psi(t)|| <= eta_K(T)=(BT)^(K+1)/(K+1)!`.
- Tensor telescoping gives distance at most `r eta_K`.
- If `q_r` is original occupied-Veronese projection action and `q_{K,r}` is formed after projecting orbit and occupied targets by P_K, then
  `q_r(t) <= q_{K,r}(t)+2r eta_K(T)`.
- Exact image identity:
  `span{(P_K z)^tensor r}=P_K^tensor r span{z^tensor r}`.
- Rank cap:
  `h_{K,Z}(r)<=min(h_Z(r),binom(dim K_K+r-1,r))`.
- For any target-independent return set R, complete capture measure is bounded by R once plus either the threshold form with `(sqrt(a)-eta)^(-2r)` or additive `a^(-r)(integral q_K+2r eta)`.
- Source fibre sheets remain integrated separately; duplicate target labels and zero returns do not change action.

For homogeneous linear ensembles H(x)=sum x_j A_j and c != 0:
`K_K(H(cx))=K_K(H(x))`, projected target image unchanged, and
`q_{K,r,cx}(t)=q_{K,r,x}(ct)`.
Gaussian disorder therefore disintegrates exactly as a positive radial time mixture of fixed-shell carrier incidence actions.

Proof hostile-checked. Key projection inequality: for y in C=K_K^tensor r and S'=P_C S, `dist(y,S')<=dist(y,S)`; causal projection may enlarge action, so decay is not automatic.

## Conjecture loop

- Full signed packet quotient: underdefined/circular.
- Targetwise moment stability: true but loses target count.
- Projection before replicas: proved; preserves complete union.
- Dimension/rank-only decay: false (one target parallel to carrier gives rank-one action near one).
- Radial randomness creating new carrier geometry: false by scale rigidity.
- Radial Fourier alone: insufficient due nonnegative incidence, returns, growing-replica crowding.

## Exact live core

Card: `docs/drafts/pipeline/1-in-progress/quenched-krylov-circuit-incidence-front-law.md`.

Prove growing-K,r decay of the positive carrier action for actual projected shallow-circuit occupied image in ordinary fixed-strength local Pauli shell, strong enough to beat capture threshold. Conditional covariance target:
`Proj_S E[|phi_K^r><phi_K^r| | K_K] Proj_S`.
Operator norm over full carrier generally too strong (=1); HS/rank alone too weak. Need local Pauli word geometry and actual circuit-image incidence.

Historical signed packet card marked superseded:
`docs/drafts/pipeline/1-in-progress/scale-matched-signed-action-packet-law.md`.

Master updated:
`docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`.

External search found no exact theorem. Distinguish Lv--Zhang--Zhou arXiv:2303.07343 (Krylov complexity from circuit geometry), Ippoliti arXiv:2606.30635 (static spectral ramp only), and 2026 multi-quench temporal-design results arXiv:2604.04205 / 2604.10122.

No Lean file edited; no Lean command/build/process started.