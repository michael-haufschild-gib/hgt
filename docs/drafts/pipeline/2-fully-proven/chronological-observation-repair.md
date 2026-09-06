# Observation repair and the finite precursors of the zeta response

**Status:** eleven CubicRepair leaves built and axiom-audited: 93 declarations. The intermediate-algebra classification, normalization, arbitrary-observation repair closure, finite quotient flow, finite heat/reference formula, and Mellin convergence and limit are formal. The explicit finite Gamma/power-sum formula remains paper-only. Candidate contribution is the classification within this chronological construction; the commutative algebra and Mellin ingredients are classical. Priority remains unestablished.

## All intermediate observation algebras

Write B=ℝ[u,c] and A=ℝ[u,c²,c³], with physical pullback T_q sending both u and c to q times themselves. Faithful evaluation on the physical section is already proved. Every P∈B has a unique decomposition

`P=a+c p(u)`, where a∈A and p∈ℝ[u].

For any unital real subalgebra S with A⊆S⊆B, define

`I_S={p∈ℝ[u] : c p(u)∈S}`.

This is an ideal: addition follows from linear closure, and multiplication by r(u) follows because r(u)∈A. Subtracting a in the displayed decomposition shows that P∈S exactly when p∈I_S. Conversely, for every ideal I⊆ℝ[u],

`S_I={a+c p(u) : a∈A, p∈I}`

is a unital algebra. In a product, the coefficient of c is a₀(u)p₂(u)+a₂₀(u)p₁(u), which belongs to I; all other powers belong to A. These two constructions are inverse and preserve inclusion. Thus the whole intermediate-algebra lattice is the ideal lattice of ℝ[u]. Moreover,

`B/S_I ≅ ℝ[u]/I`

as real vector spaces, with an additional factor c accounting for the grading shift. The full algebra B is the integral closure of every S_I in their common fraction field: B is already integral over A, hence over S_I, and A⊆S_I⊆B already forces equality of fraction fields.

## Flow invariance forces a discrete classification

Suppose S_I is preserved by every T_q with 0≤q≤1. Then p(u)∈I implies q p(qu)∈I. For 0<q<1, division by the nonzero real scalar q gives p(qu)∈I.

Every monomial occurring in p lies in I. Indeed, if deg p=d, choose d+1 distinct numbers q₀,…,q_d in (0,1). The coefficient vectors of p(q_i u) are related to the monomial components of p by the square Vandermonde matrix (q_i^j). Its determinant is the product of the nonzero differences q_j−q_i, so it is invertible. Each monomial component is therefore a real linear combination of elements of I.

If I≠0, choose the smallest exponent k occurring with nonzero coefficient in any member of I. The preceding argument gives u^k∈I, so (u^k)⊆I. Minimality of k says every polynomial in I has all lower coefficients zero, hence is divisible by u^k. Therefore I=(u^k). The zero ideal is the remaining possibility. Conversely, (u^k) and zero are preserved by scaling.

In fact, preservation under the single half-retraction T_(1/2) suffices. Its iterates give T_(2^(−j)) for every j≥0. Use d+1 distinct positive numbers from this sequence in the same Vandermonde argument. Conversely, the resulting ideals (u^k) are invariant under every scaling. Thus single-half invariance and full-flow invariance are equivalent for all these intermediate algebras. This is a concrete instance of the classical separation of polynomial weights by a nonresonant dilation; it is not claimed as a new general invariant-theory principle.

The Lean proof uses a shorter equivalent route. Every nonzero ideal of ℝ[u] has a monic generator p. Half-stability makes p divide p(u/2), whose degree is at most deg p; hence p(u/2) is a constant multiple of p. Comparing the leading-degree coefficient identifies the multiplier as 2^(−deg p). Comparing every other coefficient, and using distinctness of the powers of 1/2, forces p=u^(deg p). This proves the single-half classification without constructing a Vandermonde inverse.

Consequently, the complete list of intermediate flow-invariant observation algebras is

`A` and `A_k=ℝ[u,c²,c³,u^k c]`, k=0,1,2,… .

Here A₀=B and A_(k+1)⊂A_k. Their intersection is A, since a nonzero polynomial cannot be divisible by every power of u. The actual defect quotient B/A_k has basis

`[c],[uc],…,[u^(k−1)c]`,

and dimension k. Every displayed inclusion is strict: the class of u^k c distinguishes A_k from A_(k+1). The classification covers the entire physical flow, even though one half-retraction suffices to force it.

If one adds an arbitrary nonzero observation p(u)c and then closes under the flow and algebra operations, the resulting algebra is A_k, where k is the smallest exponent occurring in p. The Vandermonde argument extracts u^k c, and A_k already contains every term of p(u)c. Thus the higher coefficients of the new observation do not affect the surviving defect.

## Finite response and its limit

On B/A_k the physical flow has weights 1,…,k. For k≥1 and τ>0 its heat and matching finite continuum reference are

`H_k(τ)=Σ_(n=1)^k exp(−nτ)=(1−exp(−kτ))/(exp τ−1)`,

`C_k(τ)=∫_0^k exp(−xτ) dx=(1−exp(−kτ))/τ`.

Thus b_k=C_k−H_k=(1−exp(−kτ))b(τ), where the already audited b(τ)=1/τ−1/(exp τ−1). Set b₀=0. For 0<Re s<1, the Mellin integral is absolutely convergent and

`R_k(s)=Γ(s)[k^(1−s)/(1−s)−Σ_(n=1)^k n^(−s)]`.

To justify the reference term, Tonelli applied to absolute values gives finiteness from ∫_0^k x^(−Re s)dx<∞. Fubini and the Gamma integral then give Γ(s)∫_0^k x^(−s)dx. The finite heat sum may be integrated termwise by the same Gamma integral. Their difference gives the formula.

As k→∞, b_k(τ)→b(τ), and |τ^(s−1)b_k(τ)|≤τ^(Re s−1)b(τ). The bound b(τ)≤min(1,1/τ), already proved in Lean, makes this dominating function integrable exactly on the stated strip. Dominated convergence therefore gives

`lim_(k→∞) R_k(s)=−Γ(s)ζ(s)`.

The infinite zeta response is thus the limit of responses of the classified finite normalization defects. No claim is made that the individual finite responses have the same zeros as zeta.

## Formalization and novelty targets

CubicRepairAlgebra/Quotient/Power prove the order isomorphism and actual quotient descriptions. Basis/Rigidity/Classification prove the finite bases and single-half rigidity. Normalization/Flow/Heat/Limit prove the common integral closure, actual finite operators, continuous-reference integrals, and dominated Mellin limit. Closure proves the least invariant algebra generated by every polynomial observation, including its zero-coefficient case. All names have prefix CubicRepair. The finite Gamma/power-sum formula above remains to formalize; it is not used in the audited limit proof.

Relevant existing comparisons remain Koopman invariant spaces, cusp normalization and conductor theory, and the Hilbert-series/Dirichlet transform in He–McKay (arXiv:1308.5233, §5). The whole classification and response limit need a focused literature audit before any novelty claim. The corpus search also found `HTGeometry/DaiYoshikawa/NormalizationEulerDefect.lean`; it proves only the arithmetic positivity of a delta-invariant curvature correction, with the geometric formulas supplied as premises. It does not establish a curvature bridge for this construction.

[Vitulli, Definitions 2.6–2.8 and Theorem 2.9](https://pages.uoregon.edu/vitulli/WeakAndSeminormality.pdf) place adjoining an element whose square and cube already lie in the ring within classical elementary subintegral extensions. Our adjoining c fits that pattern. [Reinhart, Lemmas 2.1–2.2](https://imsc.uni-graz.at/reinhart/cond.pdf) treat conductors of intermediate rings. These are additional boundaries on any novelty claim.

A separate [uniform-recovery stress test](chronological-observation-recovery.md) asks what remains after completing in the uniform observation norm. An algebraic normalization defect must not automatically be interpreted as a nondegenerate normed defect.
