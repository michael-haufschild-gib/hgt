# Static-local O4 Pauli cut-rank advance (2026-08-02)

Master card: `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`, equations O4.12q--O4.12z0.

New exact single-backbone theorem:
- For bipartite crossing matrix A over F2, rank rho, nonzero Pauli-letter kernel on 3-letter alphabets has normalized L2 norm <= 2^(l+r-rho)/3^((l+r)/2), uniformly under arbitrary row/column sign functions.
- For a random chord pairing, semicircle bridge chords form a Ferrers cut. After fixed-q support restriction, site-summed cut rank has asymptotic density 1/4.
- Full nested-commutator admissibility survives: Eulerian Walsh bits split into two color-induced Ferrers matrices; first-occurrence Walsh bits add rank <=1 per physical site. For bq/n>=256, full effective rank >=15Q/64 except exp(-c b) mass. Since 15/64 > log2(2/sqrt3), full admissible signed angular coefficient contracts exponentially.
- With b>=k/3 whp and k>=768n/q, contraction is 2^(-eta qk/3), eta=15/64-log2(2/sqrt3)>0.
- A two-qubit gate Pauli transfer column has l1 <=4; an s-gate fixed boundary costs <=4^s. Thus each fixed circuit paired factor is <=4^s(2^(-eta qk/3)+O(e^-ck)).
- Exact angular Wick prefactor a_mk=m^k(2k-1)!!/[m(m+2)...(m+2k-2)] remains; no false normalization.

Honest remaining gaps:
1. Norm-stable spherical/time resummation; absolute Taylor sum is invalid.
2. Hamiltonian-dependent circuit supremum inside expectation (Bellman nonlinearity); fixed-word uniformity is not aggregate O4.12z0.
3. Globally shared exceptional recurrence-tube mass t^(-cm), not multiplied circuitwise.

Replica cross-pairings are multi-backbone diagrams and not covered. They are optional: r=1 first-moment Bellman bound O4.12z0 would already imply O4.3 by Markov. No Lean work authorized until paper proof closes these gaps.