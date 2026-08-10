# Gate-walk Green--Bellman tropicalization law (2026-08-09)

New Stage-2 paper proof: `docs/drafts/pipeline/2-fully-proven/gate-walk-green-bellman-tropicalization-law.md`.

For finite gate dictionary G, |G|=M, seed chi, robust word complexity C_epsilon(v), backward one-gate Markov operator P, and 0<a<1, define normalized killed gate-walk Green mass

G_(a,epsilon)(v)=(1-a) sum_(ell>=0) a^ell P^ell 1_(B_epsilon(chi))(v).

Exact sandwich:
(1-a)(a/M)^C <= G <= a^C.
Therefore C=lim_(a->0) -log G/log(1/a): approximate circuit complexity is exactly the zero-fugacity/tropical exponent of a local gate-walk resolvent.

Soft kernel exp(-beta(d-epsilon)_+) gives an external, noncircular calibration Phi=(log(1-a)-log G_tilde)/log(M/a) with Phi<=C, Phi(gv)<=Phi(v)+1, and Lipschitz beta/log(M/a). For random endpoint V and retained event R,
Pr(R and C<=s) <= E[1_R G_tilde(V)]/((1-a)(a/M)^s).
This replaces complete circuit union by one collision probability between static endpoint and geometrically killed local random circuit.

Hostile no-go: normalized L^p linearization of max over M^ell words loses exactly M^(-ell/p), sharply. To preserve max within exp(-kappa r) with degree-r reporter forces total linear moment order rp >= ell log M/kappa = Omega(D) at Brown depth ell=Theta(D/log M). Thus low replicas survive only in genuinely nonlinear max-plus formulation; every positive finite-temperature/Markov linearization recreates dimension-scale replicas.

Exact surviving open core: zero-temperature quenched gate-transfer estimate at O(n) geometric Brown-skeleton times after one common return/fast-forwardable-carrier excision. Need exponential suppression of shadowing between static endpoint and killed local random circuit, or a quenched free-energy estimate uniform enough for p->infinity. Linear Green route alone does not close Brown growth.

Master `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md` appended. No Lean due explicit corpus refactor instruction. External search found no direct circuit theorem, but ingredients are standard and priority remains unverified.