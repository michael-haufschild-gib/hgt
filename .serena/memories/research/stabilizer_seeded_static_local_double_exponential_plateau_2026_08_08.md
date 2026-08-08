# Stabilizer-seeded static-local double-exponential plateau (2026-08-08)

Stage-2 card: `docs/drafts/pipeline/2-fully-proven/stabilizer-seeded-static-local-double-exponential-plateau-law.md`.

For the fixed-strength full one-site + nearest-neighbour two-site Pauli sphere on n qubits (D=2^n, m=12n-9), independently seed by one uniformly sampled efficiently-preparable stabilizer state. Exact stabilizer 2-design identity gives mean spectral collision 2/(D+1) against every eigenbasis. On the collision-good pair set C_H(chi)<=2L/(D+1), heavy-sector replica incidence at
r=floor((1-epsilon_+^2)^2(D+1)/(64L))
bounds the complete depth-s phase shortcut mass by 2^(-r/2) when s+1<=r log2/(2 log M_n).

Fixed-shell angular dephasing restricted to the good pair set gives the same 2^(-r/2) bound at every sufficiently late common time. Bad collision mass 1/L is pair-level and paid once. A grid of N<=2^(r/4) times survives the temporal union; ||H||op<=sqrt(12n-9) and trace-distance Lipschitz motion fill gaps. Thus for every sufficiently late block origin A, with probability >=1-1/L-2^(-r/4)-q, the same fixed H,chi has C_epsilon_->s at every instant of a block of length
W=(epsilon_+-epsilon_-)(2^(r/4)-2)/sqrt(12n-9).
Fixed L: s=Omega(2^n/log n), W=2^Omega(2^n). Slowly growing L yields probability 1-o(1).

Generic cyclicity for every stabilizer plus maximal projective rank gives a later recurrence to the easy seed, so W is a post-plateau recurrence-gap lower bound. Existing local two-query separator remains at every time.

Quantifier: successful pair set may depend on block origin A; recurrence forbids one conull set hard for all late blocks. Remaining hard core: quantitative first onset and initial linear lower ramp. No Lean written/built during corpus refactor.

Related: `mem:research/fixed_shell_angular_dephasing_static_local_plateau_2026_08_08`, `mem:research/local_clifford_return_excised_phase_incidence_2026_08_08`.