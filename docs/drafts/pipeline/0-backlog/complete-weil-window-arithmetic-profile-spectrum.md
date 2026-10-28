# Arithmetic and profile spectrum of the complete Weil window form

- **ID:** complete-weil-window-arithmetic-profile-spectrum
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** actual profile-free logarithmic windows; Ramanujan prime spectrum; arithmetic compactness; atom Robin form
- **Statement:** At a sufficiently small fixed width ratio, the bounded spectrum on all window profiles converges to arithmetic excitation sectors coupled to an interval logarithmic Laplacian.
- **Count:** uncounted; no proof or Lean realization

## Goal

Identify the actual complete Weil form when every logarithmic atom has its own
profile. This enlarges the common-profile finite matrices of the in-progress
full-Weil candidate to an infinite-dimensional space at each horizon. The
intended new result is spectral identification and compactness of this actual
space. Existing profile-free positivity, generic logarithmic-Laplacian theory,
and finite-profile polarization consequences do not count as new results.
No positivity outside these shrinking windows, unbounded overlap, or RH follows.

## Gates

- [ ] Exact closed form, carrier, source-pure statement, and novelty audit
- [ ] Dependency-closed paper proof, including both arithmetic and profile compactness
- [ ] Lean realization, individual foreground checks, transitive axioms, umbrella wiring

## Proposed actual carrier

Fix c>0 small and w=c/N. On the dense core of
`H_N=direct_sum_(1<=n<=N) L2(0,1)`, synthesize

`F_N(u)=w^(-1/2)*sum_n f_n((u-log(n))/w)`,

with profiles extended by zero. Separated windows make this an isometry into
L2(R). The source quadratic form is exactly `weilQuad(F_N)`. Its closure,
semiboundedness, compact resolvent at each N, and the form core must be proved.
The source module
`ArithmeticLorentzianGeometry/WeilsFormIsPositiveOnEveryTestNearTheLogarithms.lean`
was inspected at its introduction, window definitions, and final support
representation and positivity statements. Those statements supply the actual
window geometry, not the proposed limiting spectral decomposition. Their
independent compilation/axiom status has not been audited here.

## Proposed limiting sectors

For a zero-extended profile phi on (0,1), let

`beta(phi)=integral_(0<y<=1) norm(phi-translate_y(phi))^2/(2*y) dy`,

the exact existing `bumpRobin(phi,1)`. Write B for the positive operator of its
closed form, after constructing and identifying it. The proposed limit on
`ell2(positive integers) tensor L2(0,1)` has form

`sum_m [beta(phi_m)+(log(m)+tameDifferent(m)-log(2*pi*c))*norm(phi_m)^2]`
` + c*(integral(phi_1))^2`.

Thus every m>=2 carries `B+log(m)+tameDifferent(m)-log(2*pi*c)`. The m=1
sector carries `B+c*|1><1|-log(2*pi*c)`, with 1 the constant unit vector of
L2(0,1). The last term is a bounded rank-one profile operator, not a scalar
shift on arbitrary profiles. For a single normalized common profile it reduces
to the earlier alpha=c*(integral phi)^2/norm(phi)^2.

The conjectured spectral endpoint is eventual exact eigenvalue counts below
every threshold outside this discrete sector spectrum, retaining multiplicity,
and convergence of isolated spectral clusters under the physical Ramanujan
profile maps. Simplicity of sums of arithmetic and profile energies is not
assumed or asserted.

## Exact shape normalization to verify

Splitting the zero-extension difference integral into its interior and two
boundary strips suggests

`beta(phi)=1/4*double_integral_(0,1)^2 (phi(x)-phi(y))^2/abs(x-y)`
` -1/2*integral_0^1 log(x*(1-x))*phi(x)^2 dx`.

Both singular integrability and the change-of-variables argument remain Lean
obligations. For the conventional Dirichlet logarithmic Laplacian L_Delta on
(0,1), the proposed operator identity is `B=(1/2)*L_Delta+gamma I`.
This is inferred from the one-dimensional singular-integral normalization;
it is not yet a proved corpus identity. With the arithmetic adjunction
operator A, the sector sum would be `A tensor I+I tensor (L_Delta/2)
-log(2*pi*c) I`, plus the displayed ground-sector rank-one term.

## Compactness mechanism to audit

The exact prime term for window profiles is the Weil prime kernel paired with
their L2 Gram. Its ground transform should therefore be the Hilbert-valued
prime defect, not merely the defect of the profile norms. Integrating the
existing scalar sharp-counterterm inequality pointwise in the profile variable
can retain that vector defect. The pole estimate applies to the profile norms,
whose defect is bounded by the vector defect by the norm contraction inequality.

Retain the positive sum of profile Robin energies in the self-energy estimate.
At small c this suggests a uniform lower bound by a fixed scalar mass plus
positive multiples of the vector prime defect and the sum of Robin energies.
Scalar rough-fibre and valuation-tail arguments should extend to Hilbert-valued
profiles. They would approximate bounded-defect vectors by finitely many
Ramanujan modes with profile coefficients. Compactness of the Robin form then
reduces those coefficients to finitely many shape modes. Neither extension is
currently proved, and no compactness premise may replace them.

The common-profile cancellation must also be extended to mixed profiles and
the actual operator/form core. Pointwise form limits alone do not establish
bounded-spectrum exhaustion. Closure, lower-limit control, and recovery of the
actual spectral projections remain substantive obligations.

## Existing external baseline

Chen--Weth's [Dirichlet logarithmic Laplacian paper](https://arxiv.org/html/1710.03416v6),
introduction through Theorem 1.4, was inspected. It gives the singular-integral
normalization, a compact energy-space embedding on bounded domains, and a
complete discrete Dirichlet spectrum. These analytic facts are established
baseline, not proposed novelty. Their constants give the indicated comparison
with beta in dimension one; the corpus still needs its own exact proof.
Chen--Veron's [eigenvalue bounds](https://arxiv.org/abs/2011.05692) were inspected
at the abstract only and likewise exclude generic logarithmic spectral bounds
from novelty. No numerical evidence is used.

Initial corpus searches returned generic compact-resolvent and logarithmic
resolvent tools, the existing geometric prime carrier, and unrelated Weil
profile constructions. No matching full window-sector spectrum was identified
among the inspected statements. This is not an exhaustive novelty claim.
