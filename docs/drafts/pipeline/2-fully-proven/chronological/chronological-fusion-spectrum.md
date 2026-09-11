# Curvature, fusion capacity, and the zeta divisor

**Status:** the capacity/finite-face/Euler-heat/continuous-reference/Mellin-divisor construction is fully formalized and audited; see [the exact result](../3-formalized/chronological-fusion-zeta-response.md). The sphere-homotopy interpretation of arbitrary join powers below remains a paper interpretation; the formal Euler proof does not require it. No new-field or priority claim is established.

## Geometry supplies the energy spacing

For the cubic seed P=27ace+S(b+c+d)c, both displayed diagram terms individually have capacity one. Their sum has exact capacity K=`sixCapacity`>1, attained on the curved response arc. The coefficient normalization is fixed by these unit-capacity diagram terms.

For n independent copies under one variation budget, use the already proved normalization `P_n=n^(3n) ∏P(block_i)`. Finite AM–GM and the repeated maximizing probe give the exact capacity `C_n=K^n`; this is `fused_sharp_bound` plus `fused_attained`. The n=0 empty product has capacity one. Thus the logarithmic capacity increments give

`E_n = log C_n = n a`, where `a=log K>0`.

This spacing is derived from the fusion capacity law, rather than assigned as an arithmetic spectrum. Logarithm converts multiplicative capacity into an additive quantity. Here “energy” is a mathematical grading by logarithmic norm; no physical Hamiltonian is claimed. A merely renamed arbitrary sequence would not establish this construction.

## The cubic ring supplies the sign

The cubic physical sparse unit complex is K_3=Ind(P_5), a triangle with three further edges, with the explicit ring retraction in the coalescence paper. Independent block supports, with separating gaps held at zero, form joins. The n-fold join of K_3 is homotopy equivalent to S^(2n−1), so its reduced Euler characteristic is −1 for every n≥1.

The Euler-weighted heat trace of this repeated-seed tower is therefore

`H_a(t)=−Σ_(n≥1) exp(−E_n t)=−1/(exp(a t)−1)`, t>0.

The zero-energy empty product is omitted. On Re s>1, the spectral trace is `−Σ E_n^(−s)=−a^(−s)ζ(s)`. Both the geometric progression and the zeta identity are classical; the geometric obligations are the capacity-derived spacing and the actual join/Euler classification.

## A convergent response at the nontrivial zeros

The continuous interpolation of the linear fusion spectrum has density 1/a and heat trace `−∫₀∞ exp(−a t u)du=−1/(a t)`. Subtract this continuous reference from H_a:

`B_a(t)=1/(a t)−1/(exp(a t)−1)`.

Its Mellin transform converges as an ordinary integral throughout 0<Re s<1. Indeed 0≤B_1(t)≤min(1,1/t). Nonnegativity follows from exp(t)≥1+t. The bound B_1≤1 is equivalent, after multiplying positive denominators, to `(1−t)exp(t)≤1`, which follows from exp(−t)≥1−t. The 1/t bound is immediate. Scaling gives the corresponding bounds for B_a.

The exact identity is

`∫₀∞ t^(s−1) B_a(t) dt = −a^(−s) Γ(s) ζ(s)`.

For a direct proof on this strip, let F(t)=1/(exp(t)+1). Elementary algebra gives `2B_1(2t)−B_1(t)=F(t)`. Taking the convergent Mellin transforms gives `(2^(1−s)−1) M(B_1)(s)=M(F)(s)`. The classical Fermi identity is `M(F)(s)=Γ(s)(1−2^(1−s))ζ(s)`, recorded in [NIST DLMF 25.5.3](https://dlmf.nist.gov/25.5.E3). The prefactor is nonzero in the open strip because |2^(1−s)|>1. Cancellation and scaling prove the displayed formula. The unregularized Bose identity on Re s>1 is [DLMF 25.5.1](https://dlmf.nist.gov/25.5.E1).

Since a^(−s) and Γ(s) are nonzero on this strip, this **actual convergent geometric response vanishes exactly at the zeta zeros there**, with the same multiplicities. The interpretation is cancellation of the Mellin response of the discrete fusion tower against its continuous interpolation. No assertion about the real parts of the zeros is used or implied.

## Observation loss under the ring retraction

The cubic retraction sets the middle gap to zero, so both seed diagram responses ace and S(b+c+d)c vanish on its image. Hence the entire amplification seed vanishes there. Its original positive capacity K>1 cannot be recovered from the homotopy-equivalent ring by restricting this observation. The proposed spectral construction therefore needs the pair consisting of probe geometry and observation, not its bare homotopy type. The ring supplies a topological sign; the uncollapsed observation supplies the nonzero logarithmic scale. CubicObservation now proves this seed annihilation, preservation of B,C,D throughout the homotopy, and the exact restriction kernel B=C=D=0.

## Relation to the other topological trace

This construction repeats one cubic seed and weights by its logarithmic capacity. It differs from the all-pairing-degree tower, which weights by homological occupation and yields eta. Joining two copies of that entire tower yields `η(s−1)−η(s)` and has no common strip zero with eta. Those are different indexing operations; do not claim that arbitrary fusion either preserves or removes zeta zeros.

For a general spherical seed with positive logarithmic capacity, join parity selects a Bose-type or Fermi-type geometric series. For a seed with several homology generators, multiplicities change the trace and need not give zeta. These extensions are useful classification questions, not formalized results here.

## Novelty boundary and next steps

The logarithm law, join homology, Bose/Fermi series, spectral zeta, and Mellin sum-minus-integral identity are classical mechanisms. The proposed contribution is their concrete coupling to the proved chronological capacity amplification and sparse observation geometry. This coupling has not yet passed a sufficient novelty audit; absence of an exact search hit would not establish priority.

Next: audit the novelty of this coupling and classify more general graded seeds. The actual geometric Euler trace and its continuous-reference subtraction are now connected in Lean to the analytic zero-locus and multiplicity theorems. The full five-generator cubic norm remains separate paper work.
