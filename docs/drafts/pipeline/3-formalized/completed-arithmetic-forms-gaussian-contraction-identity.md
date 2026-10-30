# Exact Gaussian contraction of source jets

**ID:** completed-arithmetic-forms-gaussian-contraction-identity  
**Stage:** Formalized  
**Type:** Complete-source coefficient identity

For every entire $h:\mathbb C\to\mathbb C$,
$$\partial_z^i\partial_w^j(e^{8zw}h(z+w))_{(0,0)}
=\sum_{r\le\min(i,j)}\binom ir\binom jr8^rr!\,h^{(i+j-2r)}(0).$$
The shared index $r$ retains every Gaussian contraction. The formula follows
from the first-variable Leibniz expansion and the exact monomial jet at zero.

For the literal first-atom source, set $h_q=e^{-4z^2}F_q(z)-1$.
Then its complete mixed error kernel is exactly $e^{8zw}h_q(z+w)$.
For $R\ge1$ and $q\ge\max(3,4R^2,R^4)$,
$$|h_q^{(k)}(0)|\le k!\frac{DR^4}{qR^k},\qquad D=50e\exp(2e).$$

Lean: `CompletedArithmeticForms/GaussianJetConvolution.lean`.
Capstones: `mixedKernelJet_gaussianMultiplier`,
`firstAtomWickError_eq_gaussianMultiplier`, and `gaussianProfileError_jet_le`.
All three audited axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.
