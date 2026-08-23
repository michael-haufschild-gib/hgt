# What this paper says, without the mathematics

A finite, perfectly isolated quantum system never forgets forever. Given enough time, its many internal phases can line up again and bring it close to an earlier state. Classic recurrence theorems guarantee this return but do not tell us how severe the waiting problem becomes in a real many-body system.

Paper identifies what controls that problem: exact arithmetic relationships among energy levels. Each independent relationship removes one phase direction that would otherwise need to line up. No hidden relationships means hardest possible alignment problem for that Hilbert-space size.

Surprising part concerns locality. A chain with only nearest-neighbour interactions looks highly constrained: number of tunable couplings grows only with chain length, while number of quantum energy levels grows exponentially. One might therefore expect locality to force many hidden energy relationships and make recurrence lower-dimensional.

Paper proves opposite for ordinary static one-dimensional chains. For almost every choice of coefficients in full nearest-neighbour qubit Hamiltonian family, energy levels have maximum possible projective independence. Same Hamiltonian then has:

- sharp return exponent using all relative energy phases;
- sharp clock-normalized winding exponent;
- no exact nonzero global return, only arbitrarily close returns;
- smallest possible value of every long-time full-support return moment, at every order.

This is one result, not collection of examples. All conclusions come from one invariant: balanced spectral relation lattice.

Thermodynamic consequence is exact. At any fixed tolerance, long-time fraction spent near a global return is

\[
\left(\frac{2\arcsin(\varepsilon/2)}{\pi}\right)^{q^n-1}.
\]

Since Hilbert dimension is `q^n`, this fraction falls doubly exponentially with number of sites.

Novel scientific contribution is not recurrence itself, torus equidistribution, or moment algebra. Those are known. New result proves that a full deterministic, interacting, static, bounded-degree one-dimensional local family generically reaches maximum recurrence dimension, and that same local Hamiltonian simultaneously saturates sharp return and all-order collision laws. It answers a concrete question experts care about: whether spatial locality necessarily discounts recurrence complexity. For this canonical family, it does not.
