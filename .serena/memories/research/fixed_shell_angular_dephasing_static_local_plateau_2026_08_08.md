# Fixed-shell angular dephasing static-local plateau (2026-08-08)

Stage-2 paper proof: `docs/drafts/pipeline/2-fully-proven/fixed-shell-angular-dephasing-static-local-plateau-law.md`.
Master updated: `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`.

## Advance
For full one-site + nearest-neighbour two-site Pauli Hamiltonians on the unit coefficient sphere, prove no nonzero integer projective spectral action is constant on any open simple-spectrum shell patch. Hence angular disorder itself yields joint weak convergence
[
(\theta,t\omega(\theta))_*\sigma \to \sigma\otimes \mathrm{Haar}
]
without Gaussian radial scale mixing.

Compose with local-Clifford collision + completed-phase heavy-sector incidence:
[
\limsup_{t\to\infty}P_\theta\{C_\epsilon(e^{-itH(\theta)}\Omega)\le s\}
\le 1/L+2^{-r_n/2},
quad
r_n=\lfloor (1-\epsilon^2)^2(3/2)^n/(32L)\rfloor,
]
when (s+1\le r_n\log2/(2\log M_n)). Thus every sufficiently late common time has high probability of exponential state complexity at fixed coefficient/HS interaction rate. At same times local two-query witness keeps evolution distinguishable from Haar.

## New proof mechanism
1. Strengthen path-local witness to complete endpoint transition graph.
2. Rule out branch identity ((\sum c_jE_j)^2=\kappa D^{-1}\mathrm{Tr}H^2): attach qubit, use cross-block (A\otimes X), differentiate twice, obtain (L_0(z)L_{xx}(z,0)=\kappa Q(V)). Unique gaps isolate residues. Since affine (L_0) has at most one zero, complete bipartite equality graph minus one edge forces all zero-sum coefficients to vanish.
3. Symmetrize over eigenvalue labels to globalize and exclude local shell flatness.
4. Nonflat analytic actions have null critical set; coarea gives absolutely continuous pushforward; Riemann–Lebesgue/Weyl gives angular phase dephasing.

## Failed conjectures retained
- Periodic FK clock transfers spectra, not ordinary circuit lower bounds; postselected branch hardness is insufficient.
- Gaussian radial dephasing is a true scale-mixture statement but invalid as fixed-rate O4 closure.
- Pointwise maximal projective rank alone does not imply angular decay; anticommuting Clifford pencils have radius-only spectra.
- Same H cannot remain hard at all late times because recurrence.

## Honest remaining O4
No quantitative onset (T_n), no initial linear growth, no Brown scale, no control of large-(n)/large-(t) limit order. Need quantitative lower-tail/oscillatory estimate for relevant local spectral actions strong enough for complete circuit tube. Lean was read-only and no Lean build/write was started because corpus refactor is active.
