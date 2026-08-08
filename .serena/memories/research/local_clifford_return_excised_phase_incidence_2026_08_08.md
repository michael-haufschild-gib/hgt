# Local-Clifford return-excised phase-incidence advance (2026-08-08)

Card: docs/drafts/pipeline/2-fully-proven/local-clifford-return-excised-phase-incidence-law.md
Master: docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md
Status: PAPER-PROVED, NOVELTY UNVERIFIED, LEAN DEFERRED by explicit user instruction during corpus refactor.

Main abstract law. For fixed H/input spectral probabilities p_j, collision C_H=sum p_j^2, finite residual targets Z, replica r, independent return set R, and original event Q with Q\\R inside target capture at squared fidelity a, remove heavy spectral indices p_j>4C_H/a. Let Phi_L be light phase orbit and U^L_(r,R) the least span of P_(S_r(Z)) Phi_L(zeta)^tensor r over zeta outside R, with iota=dim U. Then
m_H(Q) <= m_H(R) + iota r! (16 C_H/a^2)^r,
iota<=h_r(Z).
All phase-source sheets remain integrated; only reporter space is compressed. Duplicate target labels and zero residuals do not change the invariant.

New key lemma: for every general symmetric tensor w,
int |<Phi_L(zeta)^tensor r,w>|^2 dm <= r! tau^r ||w||^2,
tau=4C_H/a,
by exact torus-character orthogonality. This survives projecting target tensors into minimal incidence carrier and is what improves h_r to iota.

Ordinary local ensemble. For support-isotropic Gaussian Pauli Hamiltonians on a graph containing a spanning path (including nearest-neighbor open chain), product-local-Clifford invariance and the six-state one-qubit 2-design give E_H C_H(|0^n>) <= (2/3)^n, hence P(C_H>L(2/3)^n)<=1/L. Generic path-local spectral maximality plus Krylov witness H0=sum 3^j X_j gives maximal projective rank and full product-input spectral support a.s.

Circuit corollary. Choose r=floor((1-epsilon^2)^2(3/2)^n/(32L)). For finite local gate alphabet, completed-time low-complexity density is at most return density + exp(-Omega((3/2)^n/L)) up to depth Omega((3/2)^n/(L log n)), with Hamiltonian probability >=1-1/L.

Boundary: genuinely new completed-time quenched incidence/plateau advance, but not Brown O4. No effective equidistribution, first-hard-time, linear growth, plateau onset, or first recurrence time. No Lean processes/files were started/changed by this work; shared repo had an unrelated active build from another actor.