# Critical Hardy Theory of the Window Cone (CHT)

Namespace `GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone`; umbrella
`CriticalHardyTheoryOfTheWindowCone.lean`.

## 1. Motivation

Weil's form on a window is a signed nonlocal quadratic form

$$W_\lambda(f)=H(f)-P_\lambda(f),\qquad P_\lambda(f)=\sum_{n\ge2}\lambda(n)n^{-1/2}\bigl(k_f(\log n)+k_f(-\log n)\bigr),$$

where $k_f=f\star\tilde f$ and $H$ is the archimedean–polar form: a logarithmic-order jump form with symbol
$1+\tfrac12\log(1+\xi^2)$ up to a bounded convolution, with the pole kept as a signature $(1,1)$ rank-two term. The
weights $\lambda(n)$ are free real numbers. CHT studies the nested convex sets

$$\mathcal A(c)=\{\lambda : W_\lambda\ge0\text{ on }[-c,c]\}$$

as objects in their own right. Criticality, frustration and logarithmic boundary behaviour have no existing home:
Hardy theory treats positive potentials, Dirichlet form theory treats Markov forms, and Wiener–Hopf theory treats
half-lines and scalar symbols. Here all three meet on one object, whose limit is arithmetic: $\bigcap_c\mathcal A(c)$
is $\{\Lambda\}$ under RH and empty otherwise, while only $\Gamma$, the pole and the positions $\log n$ enter the
definition.

CHT is a receiver. Positivity at a finite aperture is consistent with every width, and every uniform statement in
$c$ is RH or the width. So CHT does not aim at a sign for $\zeta$. It aims at the exact finite-level theorem: what a
proof must deliver on each window, at what precision, and with what boundary behaviour.

## 2. Objects

| Object | Meaning |
|---|---|
| Window cone $\mathcal A(c)$ | weights with $W_\lambda\ge0$ on tests supported in $[-c,c]$ |
| Bands | range of one weight $\lambda(n)$ over $\mathcal A(c)$ |
| Margin $m(\lambda,c)$ | $\inf W_\lambda(f)/\|f\|^2$ on the window |
| Best margin $\lambda^*(c)$ | $\sup_\lambda m(\lambda,c)$: the inradius of the cone in the operator norm of the prime part |
| Blind density | finite positive family of tests with $\sum_i\alpha_ik_{f_i}(\log n)=0$ for $n\ge2$: the dual object of the cone |
| Null family | blind density built from $\Xi$-divisible tests, on which $W_\lambda$ vanishes in the limit |
| Hardy interval $\mathcal H(c)$ | section of $\mathcal A(c)$ along the ray $t\Lambda$ |
| Datum | pair (pole weight, conductor) replacing the residue and the shift of the Gamma symbol |
| Stage fibre | the interval of one newly entered weight over fixed lower weights |
| Causal kernel, edge coefficient | Wiener–Hopf factor of the symbol and the boundary value it reads |

## 3. Language

- **Critical**: no Hardy weight survives; the slack of the limit form is zero in every sense.
- **Frustrated**: not balanced in any sign gauge.
- **Blind**: a positive combination of autocorrelations that vanishes at every $\log n$, $n\ge2$.
- **Null**: a test whose transform vanishes at every zero of $\zeta$.
- **Near-null at level $c$**: a window test on which every point of $\mathcal A(c)$ has small energy.
- **Extinction aperture** of a weight: the largest window to which it extends inside the cones.
- **Edge coefficient**: the limit of $u(x)\sqrt{\log(1/x)}$ at an endpoint of the window.

## 4. Mechanisms

1. **Cone duality.** On a fixed window the cone is an intersection of half-spaces in finitely many coordinates, so
   its existence and margin are exactly dual to blind densities: the weights drop out on a blind family.
2. **Null families are universal test vectors.** The twisted-arc family is blind and $\Xi$-divisible. Truncated to
   a window it is near-null for every weight in the cone, not only for $\Lambda$. This is what closes the slack from
   other weights.
3. **Near-null vectors polarize.** Cauchy–Schwarz on a positive form turns a near-null vector into a pointwise
   reading of the difference of two weights, smoothed by the theta kernel.
4. **Causal factorization at the edge.** The Wiener–Hopf factor of the logarithmic symbol reads boundary values
   with the factor $\sqrt{\log(1/x)}$, and only the near edge enters.

## 5. Traps

| Trap | Truth |
|---|---|
| A finite-level theorem about $\mathcal A(c)$ moves the sign for $\zeta$ | Bounded apertures are blind to every width |
| Uniform control in $c$ is a tool | Every uniform statement is RH or the width |
| Other weights give slack | They do not: null families are blind, so all weights have the same ceiling |
| The Weil cone at conductor one is typical | No-pole data at high conductor have a fat cone: pole and conductor one are what make it a point |
| A weighted reading of $\lambda-\Lambda$ is a reading of one atom | Theta smoothing mixes atoms; deconvolution is the hard step |
| A certificate format is a mechanism | Every positive form has an exact format |

## 6. Questions

1. **Effective uniqueness (B58).** How close is every point of $\mathcal A(c)$ to $\Lambda$, unconditionally?
2. **Margin law (B59).** How fast do the best margin and the bands decay? Does the Gaussian ceiling of $\Lambda$ hold
   for $\lambda^*$?
3. **Edge profile.** What is the exact boundary behaviour of extremals and Riesz vectors on a window?
4. **Datum.** What distinguishes pole and conductor one from every other datum?
5. **Work items.** Cone maps (A13) and the Hamiltonian of the precontact chain (A41).

## 7. Tools to develop

Finite-window semidefinite duality; truncation calculus for blind families; doubly exponential tails for the
shifted-Gamma tests; polarization readings; a datum calculus for pole weight and conductor; Wiener–Hopf factorization
on a window.

## 8. Context

CHT sits on the receiver side of the programme. Its partner, arithmetic production at square-root precision, works
on $\Lambda$ itself and may supply an input; CHT states the exact target such an input must meet.

| Neighbour | Interface |
|---|---|
| `RHTower` cone theory | $\mathcal A(c)$, cone uniqueness, twisted-arc family, level duality |
| `FrustratedArithmeticDirichletForms` | Hardy interval, entry laws, edge energy, frustration |
| `SignedWindowCriticality` | exact two-sector format, gauges, the Perron threshold |
| `ArithmeticCriticalityTheory` | ground states, Gaussian ceiling for $\Lambda$ |
| `CanonicalSystemOfTheWindowTower` | de Branges chain, causal kernel, half-line inverse, Riesz vectors |
| `ArithmeticOfSquareRootPrecision` | the limit theorems that bound what CHT can deliver |

## 9. Success criteria

A contribution to CHT must be an unconditional theorem about $\mathcal A(c)$, its data, or its edge that:

1. reproduces the known thresholds in cone language, or strictly refines them;
2. treats the weights as free, with $\Lambda$ as an output, not an input;
3. states its limit: what it does not say about $\zeta$, and where it would become RH;
4. distinguishes pole and conductor one from no-pole data at high conductor whenever it claims rigidity.

The programme is complete when effective uniqueness and the margin law have explicit forms, the edge profile is
known on a window, the datum is classified, and the tools above exist in Lean.
