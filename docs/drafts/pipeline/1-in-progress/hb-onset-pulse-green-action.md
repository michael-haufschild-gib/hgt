# HB: original onset-pulse Green action

Status: analytical conjecture/proof loop in progress. Complete physical cancellation and RH remain unproved.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The full incoming wave-image current is [formalized](../3-formalized/hb-full-incoming-current.md). The hard target is its signed combination with the original pulse response, both cross terms and all other physical faces. The pulse is fixed by `fullSourceOnsetPulse_transition`; it cannot be chosen to cancel a current.

First test: recover an explicit wave image by integrating its actual wave operator against the original causal kernel, retaining all characteristic data. Broad concomitant/method searches recover existing projected concomitants and general source equations, but no supplied boundary equality is usable as a premise for extinction.

Second test: for `nu=2s+1`, the two angular inverse parameters are `nu(nu+1)` and `(nu+3)(nu+4)`. Test a three-step differential ladder against the literal forcing and unchanged physical operator. Parameter similarity alone does not identify a physical intertwiner.

A direct Green mechanism to test in parallel: the circular mean of the constructed full angular response satisfies a forced Darboux equation. Its initial value is the full response and its forcing is the literal half-square mean. Derive a finite-radius variation-of-constants identity, then carry it into the original radial/onset integral. This could evaluate the pulse's response contribution without assigning any angular or incoming datum to zero. The finite Green-current identity now has a dependency-closed paper proof; Lean verification is in progress. Its use in the physical pairing remains open.

## Finite angular transfer

Put `s = physicalRate q branch`, `alpha = (2s+1)(2s+2)`, `nu = 2s+1`. Let `h(d)` be the literal circular average of the constructed full angular response `H`, and let `m(d)` be the existing circle average of `Q = scalar²/2`. The polar metric identity, averaging of the periodic angular second derivative, and the already proved full equation `Delta H = alpha(H+Q)` give

`(sinh d)² h″ + sinh d cosh d h′ = alpha (sinh d)² (h+m)`.

For the existing original Legendre kernel `p(d) = legendreKernel nu (cosh d)`, its actual differential equation gives

`sinh d p″ + cosh d p′ = alpha sinh d p`.

Consequently the actual current `W(d) = sinh d (p(d) h′(d) - p′(d) h(d))` obeys, for positive radius,

`W′(d) = alpha sinh d p(d) m(d)`.

Both factors and their first derivatives are continuous at zero; hence `W(0)=0`. The fundamental theorem on `[0,D]`, requiring the derivative only on its interior, proves

`W(D) = alpha integral(0,D) sinh d p(d) m(d) dd`.

This retains `h(0)=H(z)` and requires no inverse of `p`, no zero of an unevaluated remainder, and no altered source. It evaluates a full-response boundary current directly in the literal theta half-square. It does not yet evaluate the full pulse convolution or its physical mixed pairing.

The next dependent test is to insert this transfer into the unchanged causal circle kernel for the onset source `2(b′ H + ell′ Q) chi′ exp(2s v)`, preserving both direct and reflected kernels. The homogeneous angular datum and the other physical faces must be carried through that insertion before any extinction claim.

## Search applicability

Broad corpus searches used `concomitant`, `ladder`, `Legendre`, and a mechanism query about causal Green recovery. Declaration, candidate, method/source-argument and ingredient-group results were inspected. The cached index reported partial/pending coverage and source-only compiler metadata; generated ingredient groups were not accepted as proofs. The usable ingredients are the existing circle-chart polar identities, differentiation of compact circle averages, full angular forcing equation and actual Legendre differential equation. Polynomial-degree recurrences do not yet supply the required physical complex-degree intertwiner.

Independent arXiv searches used `homotopy`, `transgression`, `intertwining` and `caustic`, including June–September 2026 filters. [Caustic beamforming (10 June 2026)](https://arxiv.org/abs/2606.12321) concerns shaped wireless propagation and supplies no proved transfer for this operator. The older [Kerr conserved-current paper (2022; revised 2024)](https://arxiv.org/abs/2210.15935) gives a metric/Weyl symmetry-operator mechanism, but its homogeneous equations and renormalized mode pairing have not been identified with this forced physical action. [The charged two-dimensional black-hole paper (August 2026)](https://arxiv.org/abs/2608.21406) likewise does not supply the present full angular identity. These are analytical leads, not proof dependencies.

## Original pulse substitution

Write the already fixed pulse exactly as `C_H H + C_Q Q`, where

`C_H = -2 sourceSeedFieldFirst(s,0,a,1,alpha,t) chi′(tau+t) exp(2s(tau+t))`,

`C_Q = 2 alpha radialLiftFirst(s,0,a,1,t) chi′(tau+t) exp(2s(tau+t))`.

Linearity of the actual circular average gives `pulseMean = C_H h + C_Q m`. Its actual radial derivative follows from smoothness, so the finite transfer above yields

`W_p(pulseMean)(D) = C_H alpha integral(0,D) sinh d p(d) m(d) dd + C_Q sinh D (p(D)m′(D)-p′(D)m(D))`.

The response channel is therefore replaced by a literal-source integral in this pulse current. The half-square current remains explicit, with both original coefficients and the original onset derivative. This identity is paper-proved and included in the current Lean scratch check. It is a circular transfer identity, not yet an evaluation of the complete causal convolution or its SS/SV/VV pairing.
