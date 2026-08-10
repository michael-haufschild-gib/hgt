# Centralizer phase bandwidth and path-local tangent rigidity (2026-08-10)

## Context
Active Brown–Susskind frontier for ordinary time-independent local Hamiltonians. Lean intentionally untouched during shared corpus refactor.

## Conjecture loop
1. **Failed:** every shallow shortcut lies near a fast-forwardable orbit carrier. Counterexample: efficiently compiled Hamiltonian functions such as \(e^{-icH^2}\), which are exact centralizer elements but transverse to the linear orbit.
2. **Failed:** polynomial interpolation degree measures shortcut cost. \(e^{-itH}\) has degree-one exponent for arbitrary time; a shallow fixed operator can have degree \(D-1\) when interpolated in a generic energy coordinate.
3. **Survived/proved:** minimal Lipschitz bandwidth of a real spectral-phase lift.
4. **Failed:** bandwidth universally lower-bounds arbitrary circuit depth. One-qubit diagonal \(H=\mathrm{diag}(0,\delta)\), \(Z=\mathrm{diag}(1,-1)\) has one-gate cost but bandwidth \(\pi/\delta\).
5. **Survived:** quenched finite-scale undistortion of the entire moving centralizer torus in local circuit metric. This is stronger than the orbit-only Brown law and automatically treats recurrence via robust-bandwidth collapse.

## Paper-proved theorem 1
Card:
`docs/drafts/pipeline/2-fully-proven/centralizer-phase-bandwidth-shortcut-extraction-law.md`

For simple \(H\) with ordered energies \(E_j\), centralizer phase \(Z=\sum\zeta_jP_j\):
\[
\mathrm{bw}_H(Z)=\max_j \frac{d_{S^1}(\zeta_{j+1},\zeta_j)}{E_{j+1}-E_j}.
\]
Bandwidth is subadditive, inversion/global-phase invariant. For \(U_H(t)=e^{-itH}\):
\[
\mathrm{bw}_H(U_H(t))=\max_j \frac{\mathrm{dist}(t\delta_j,2\pi\mathbb Z)}{\delta_j}.
\]
It equals \(|t|\) whenever \(|t|\delta_{\min}\le\pi\), hence unconditionally through
\(|t|\le\pi(D-1)/(E_D-E_1)\). Exact/projective recurrence gives bandwidth zero; an \(\eta\)-return gives robust bandwidth zero.

If arbitrary unitary \(W\) satisfies \(\|W-U_H(t)\|_{op}\le\epsilon<1\), normalize its spectral diagonal:
\[
Z_H(W)=\sum_j \frac{\langle e_j,We_j\rangle}{|\langle e_j,We_j\rangle|}P_j.
\]
Then \(Z_H(W)\in\mathbb T_H\), \(\|Z_H(W)-U_H(t)\|\le2\epsilon\), \(\|W-Z_H(W)\|\le3\epsilon\), and
\[
\mathrm{bw}_H(Z_H(W))\ge
\max_{j<k}\frac{(\mathrm{dist}(t(E_k-E_j),2\pi\mathbb Z)-4\arcsin\epsilon)_+}{E_k-E_j}.
\]
Thus every adaptive shortcut yields an exact high-bandwidth moving-centralizer witness without a minimum-gap inverse.

For circuits constrained to the centralizer, bandwidth gives an exact complexity lower bound. A near-centralizer word obeys an intrinsic/transverse budget split. Missing mechanism is finite transverse holonomy.

Exact open conjecture: with probability \(1-\delta_n\), \(\delta_n\to0\), simultaneously for every centralizer phase,
\[
C_\epsilon(Z)\ge
\min\{cD/\log M_n,\ \mathrm{bw}_{H,2\epsilon}(Z)/v_n-v_n\}
\]
for polynomial gate rate \(v_n\). This pays all high-bandwidth carrier tubes in one failure probability and removes time-grid union.

## Paper-proved theorem 2
Card:
`docs/drafts/pipeline/2-fully-proven/path-local-centralizer-tangent-rigidity-law.md`

For open qubit path \(n\ge3\), Hamiltonian with every 3x3 edge coupling matrix \(J_v\) invertible and at least one field-rigid edge:
\[
\{K\in\mathcal L_n:[H,K]=0\}=\mathrm{span}_\mathbb R\{I,H\}.
\]
Mechanism:
- consecutive-edge three-body coefficients yield
  \(x\times By=Ax\times y\);
- tensor contraction proves \(A=B=\lambda I\);
- all two-site couplings of \(K\) synchronize to one scalar multiple of those of \(H\);
- subtracting that multiple leaves only one-site fields;
- one field-rigid edge kills both endpoint fields, and invertible edges propagate zero along path.

Field rigidity is open dense; diagonal \(J=\mathrm{diag}(d_1,d_2,d_3)\) with nonzero pairwise distinct \(d_i^2\) is a witness.

Quantitative corollary:
\[
\mathrm{dist}_{HS}(A,\mathrm{span}\{I,H\})\le \|[H,A]\|_{HS}/\gamma_H
\]
with \(\gamma_H>0\) for each retained H and uniformly on compact sets away from determinant/rigidity failure loci.

Interpretation: the cheap two-local tangent cone intersects the moving centralizer only in physical time plus scalar phase. Remaining Brown obstruction is genuinely finite transverse circuit holonomy, not a hidden local conserved flow.

## External boundary
- Low–Chuang QSP gives t-linear query complexity, not arbitrary nonuniform local-circuit lower bounds.
- Kotowski–Oszmaniec–Horodecki prove GUE/Haar-conjugated complexity jumps, not fixed local shells.
- Hamiltonian-learning literature proves generic recovery up to scale from state data; current tangent theorem is a direct operator classification.
- Novelty remains unverified; exact elementary compositions are proved, no final-paper claim.

## Next hard move
Track local-control word logarithmic increments in a moving frame and split them by projection onto \(\mathrm{span}\{I,H\}\). Tangent theorem makes projected part literal time reparametrization. Prove that a word returning near \(\mathbb T_H\) cannot create \(\Omega(s)\) resolved phase bandwidth unless transverse Magnus-bracket cost is \(\Omega(s)\). This finite holonomy theorem is the live core.

No Lean file/process touched.