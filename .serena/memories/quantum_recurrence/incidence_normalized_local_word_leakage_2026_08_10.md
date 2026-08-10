# Quantitative local-word leakage frontier — 2026-08-10

New Stage-2 card:
`docs/drafts/pipeline/2-fully-proven/all-replica-incidence-normalized-local-word-leakage-law.md`.

## Proved no-go
For 0<eps<=1, symmetric 3x3 matrices
A1=[[eps,0,1],[0,0,0],[1,0,0]],
A2=[[0,0,0],[0,eps,1],[0,1,0]]
satisfy:
- A1+A2 invertible (det=-2eps), hence exact Hall;
- (1/2)I <= A1^2+A2^2 <=4I;
- Gurvits CP capacity lies in [eps^2/2,2eps^2].
Upper uses X_t=diag(t,t,t^-2), det eta(X_t)=2(eps^2+t^-3).
Lower is general invertible-pencil certificate cap(eta)>=|det(sum c_iA_i)|^2/||c||^(2d).
Therefore uniform vector Casimir gap + Hall does not control one-step operator capacity. Scaled-commutator gap proposal is retired as unsupported.

## Positive survivor
For full replicated Pauli commutators A_q on n qubits, D=2^n:
- full Casimir K=sum_q A_q^2 is central;
- on global collective-commutant complement Q, 2D^2 I <=K<=4r^2(D^2-1)I (root-lattice SU(D) Casimir minimum and norm ceiling);
- B_q=K^-1/2 A_q is exactly bi-tight;
- every bi-tight tuple obeys sharp leakage sum ||(I-P_V)B_qP_U||_HS^2 >=dimU-dimV.
Thus raw full-Pauli leakage is >=2D^2(dimU-dimV).

Every full Pauli commutator has a depth<=n synthesis from all-to-all physical weight-one/two commutators with coefficient l1 mass exactly one: normalized Pauli brackets divide two product branches by a structure coefficient of modulus 2, preserving l1 mass inductively. Weighted Cauchy then gives incidence-normalized local-word leakage
(1/(D^2-1)) sum_q sum_w |c_qw| ||(I-P_V)W_wP_U||_HS^2
>= 2D^2/(D^2-1)(dimU-dimV)>2(dim loss),
uniform at every finite replica order, retaining each synthesis sheet.

## Hostile boundary
This is all-to-all two-local word depth <=n, not one-step and not yet graph-geometric. It controls dimension-losing linear incidence cuts. A shallow circuit endpoint union may have full span, so no Brown/circuit-union result follows. No static-ensemble probability is proved. Lean must remain read-only during active corpus refactor.

## Next conjecture loop
Naive first-order Bellman carré-du-champ transfer is false. Binomial threshold reporter B_{r,k} has
1-B_{r,k}(u)=C(r,k-1)(1-u)^(r-k+1)+higher,
and along a state displacement 1-u=O(delta^2), so all derivatives below 2(r-k+1) vanish at an exact shortcut. Correct frozen target: contact-order-matched Bellman coarea using order ell=2(r-k+1), or exact beta boundary integral, and prove transfer from antisymmetric local commutator sheets to symmetric Fréchet jets of one static coefficient pencil. Static crossing-memory no-go forbids free-word substitution.

Master and one-step cards were appended with correction. No Lean edits/processes.