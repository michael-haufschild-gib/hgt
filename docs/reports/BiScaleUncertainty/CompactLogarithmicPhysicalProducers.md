# Compact logarithmic states from compensated physical producers

Status: dependency-closed paper proof before field Lean. Proposed connected
contribution20; uncounted until formal certification. Topic: continuum
coprime shear, physical Dirichlet energy and actual compact source forms.

## Visible physical velocity and interval restriction

Let V=L²(ℝ,dt), F_q(t)=∫₀ᵗq and f_q(x)=F_q(exp x). Use the already
constructed physical translations τ_u and box operators M_s. All vectors
below are actual elements of V. For arbitrary real a,b define

    R_(a,b)q=1_(a,b]q,      P₊q=1_(0,∞)q.                  (1)

The sets are measurable; multiplying an L² representative by their
indicators preserves L² membership. The resulting class is independent of
representative. Pointwise indicator algebra proves linearity, while

    ‖R_(a,b)q‖²=∫_(a,b]q²≤‖q‖²,
    ‖P₊q‖²=∫_(0,∞)q²≤‖q‖².                               (2)

Thus these operations are bounded linear contractions. P₊q also equals
q−negativePhysicalVelocity(q). For t≥0, restriction does not change the
integral on (0,t], so F_(P₊q)(t)=F_q(t). In particular

    f_(P₊q)=f_q.                                           (3)

Every logarithmic edge jump, hence its integral against any constructed
edge measure, is identical for q and P₊q. The same is true of sourceMass
for every compact source and fixed anchor. This identity includes extended
energies; it requires no finiteness premise. The negative physical
half-line is an exact invisible component of this logarithmic calculus.

## An explicit compensator with exact energy

For n∈ℕ put r=n+1 and construct

    α=exp(−r), β=exp(r), L=exp(2r), h=exp(−2r), B=β+L.

All are positive, α<β and h<α. Define the actual vectors and scalar

    q_n=R_(α,β)q,   m_n=∫_α^βq,
    k_n=1_(β,B],    c_n=(m_n/L)k_n,
    v_n=q_n−c_n.                                           (4)

The indicator k_n has finite measure L and belongs to V. Its squared norm
is L. The input restriction and compensator have disjoint supports, giving

    ∫c_n=m_n,       ‖c_n‖²=m_n²/L,
    ‖v_n‖²=‖q_n‖²+m_n²/L.                                (5)

These are exact identities, not separate bounds on signed summands.
Cauchy–Schwarz on (α,β] gives

    m_n²≤(β−α)∫_(α,β]q²≤β‖q‖².

Since β/L=exp(−r), (5) proves the quantitative bounds

    ‖c_n‖≤exp(−r/2)‖q‖,
    ‖v_n‖²≤(1+exp(−r))‖q‖²,
    ‖v_n‖≤sqrt(1+exp(−r))‖q‖
          ≤(1+exp(−r/2))‖q‖.                              (6)

All integrals in (5) are legitimate: each vector has bounded support and
is L², hence L¹ on that support. Restriction integrates to m_n and the
constant tail to (m_n/L)L. Consequently ∫v_n=0. Its representative vanishes
off (α,B]. For every real t≤α, the oriented primitive integral is zero.
For t≥B it is the total integral, also zero. Therefore

    F_(v_n)(t)=0 for t≤α or B≤t.                           (7)

This is the exact missing condition in a mere compact-velocity argument:
without zero integral, a constant primitive tail remains.

## Produce an actual compact C¹ logarithmic state

Define w_n=M_(−2r)v_n. This is an actual L² vector. Let p_n denote its
already proved continuous representative, so

    p_n(t)=h⁻¹(F_(v_n)(t+h)−F_(v_n)(t)),
    w_n=p_n almost everywhere,
    p_n'=h⁻¹(τ_hv_n−v_n) almost everywhere.                (8)

Both p_n and this derivative are L², and p_n is locally absolutely
continuous. Formula (7) makes p_n(t)=0 for t≤α−h and for B≤t.
Thus it has actual compact support bounded away from zero.

Compact support of the primitive follows directly from the certified
primitive formula for M_s. Put H(t)=∫₀ᵗF_(v_n)(u)du. Then

    F_(w_n)(t)=h⁻¹(H(t+h)−H(t)−H(h)).                     (9)

Because h<α, (7) gives H(h)=0. If t≤α−h, both H(t+h) and H(t) vanish;
this includes negative t since F_(v_n) vanishes on the entire half-line
ending at α. If B≤t, their difference is ∫_t^(t+h)F_(v_n)=0. Hence

    F_(w_n)(t)=0 for t≤α−h or B≤t.                        (10)

This also proves the smoothed zero-integral property without assuming a
global Fubini identity. Define the concrete source

    g_n(q)(x)=F_(w_n)(exp x).                              (11)

It is continuous. Since α−h>0, (10) puts its support in the finite interval
[log(α−h),log B]. Taking closure preserves this containment, so g_n(q) is
an actual element of C_c(ℝ,ℝ), not an uninstantiated regularity interface.

The primitive of w_n has derivative p_n at every point. The chain rule
therefore gives the everywhere derivative

    g_n(q)'(x)=exp(x)p_n(exp x).                           (12)

The right-hand side is continuous; g_n(q) is C¹. Substitution t=exp x
and the a.e. representative identity give, for every real a≤b,

    ∫_a^b exp(−x)|g_n(q)'(x)|²dx
       =∫_(exp a)^(exp b)|w_n(t)|²dt.                     (13)

The same equality holds for oriented intervals. Thus the constructed
compact source has exactly the physical velocity w_n in the established
weighted logarithmic Dirichlet calculus. No unweighted logarithmic H¹
identification is used.

## Quantitative approximation and its limits

Let e_n=‖q_n−P₊q‖. Indicator algebra gives

    e_n²=∫_(0,α]q²+∫_(β,∞)q².                            (14)

Endpoint choices do not matter for Lebesgue measure. As n→∞, α→0 and
β→∞. The residual squared integrand tends pointwise to zero and is bounded
by q². It is measurable up to the usual null set of an L² representative;
q² is integrable. Dominated convergence gives e_n²→0, hence e_n→0.
The two displayed tail norms separately tend to zero by the same argument.

The triangle inequality and (6) imply

    ‖v_n−P₊q‖≤e_n+exp(−r/2)‖q‖.                         (15)

Box contraction and linearity give the actual producer error

    ‖w_n−P₊q‖≤e_n+exp(−r/2)‖q‖
                 +‖M_(−2r)(P₊q)−P₊q‖.                  (16)

Also e_n is at most the sum of the two tail norms in (14), recovering the
separate-tail bound stated on the candidate card. The last term in (16)
tends to zero by the certified strong approximation M_su→u as s→−∞.
The exponential coefficient tends to zero as well. Consequently

    v_n→P₊q,                 w_n→P₊q in V.                (17)

These are strong limits for every input. All maps are explicit; no input
smoothness, decay rate or compact-support premise is assumed. The uniform
energy bound (6) and contraction give

    ‖w_n‖²≤(1+exp(−r))‖q‖².                              (18)

For any positive t, Cauchy–Schwarz also gives
|F_(w_n)(t)−F_q(t)|²≤t‖w_n−P₊q‖², by (3). Thus primitive traces converge
uniformly on each bounded positive physical interval, and logarithmic
states converge uniformly on each compact logarithmic interval.

## Explicit affine control

For arbitrary real a,b, put d=b(a−1), and let C_(a,b)=A_aτ_b−τ_bA_a.
The certified box-producer estimate applied to the actual v_n gives

    ‖C_(a,b)w_n‖²
      ≤4|a|min(1,|d|/h)²(1+exp(−r))‖q‖².                (19)

Taking the nonnegative square root gives the corresponding norm bound
2sqrt(|a|)min(1,|d|/h)sqrt(1+exp(−r))‖q‖. Zero and negative affine
parameters are included. The derivative in (8) has norm at most
2h⁻¹sqrt(1+exp(−r))‖q‖. These quantitative bounds are constructed together
with compact support and approximation; they are not receiver conditions.

## Source mass and compact graph-form convergence

For a concrete compact source ψ, define the actual finite coefficient

    K(ψ)=∫_ℝ ψ(x)²exp(x)dx.                              (20)

The integrand is continuous, nonnegative and supported inside the compact
support of ψ. Thus it is integrable and K(ψ)≥0. For every u∈V,
Cauchy–Schwarz on (0,exp x] gives |F_u(exp x)|²≤exp(x)‖u‖².
Multiplying by ψ² and integrating proves, in the extended nonnegative reals,

    sourceMass(ψ,u,0)≤ofReal(K(ψ)‖u‖²).                   (21)

Every coefficient is finite by construction. For the existing compact
mixed graph and its finite resistance R(ψ,weights), package19 supplies

    jumpEnergy(ψ,weights,u)≤R(ψ,weights)ofReal(‖u‖²).

Combining with (21), the whole source-mass plus jump form is bounded by

    (ofReal(K(ψ))+R(ψ,weights))ofReal(‖u‖²).              (22)

This is a bound for every actual input and arbitrary nonnegative line
weights of the constructed compact mixture. No form-domain assumption is
introduced. Apply it to u=w_n−P₊q. By (3) and primitive linearity, this u
and w_n−q have identical logarithmic primitives, hence identical source
masses and jumps. The coefficient in (22) is finite and (17) makes its
norm factor tend to zero. Nonnegativity and the squeeze theorem prove

    sourceMass(ψ,w_n−q,0)
       +jumpEnergy(ψ,weights,w_n−q)→0.                    (23)

Both summands consequently tend to zero. Substituting the real error bound
in (16) into (22) supplies a fully explicit nonnegative upper bound on the
form error at each n. Substituting (19) similarly gives a finite explicit
bound on the compact graph form of the affine commutator producer.

The source is zero-anchored, g_n=F_(w_n)∘exp. This theorem does not assert
global physical-energy approximation of independently added constants.
It also does not identify a full uncut SourceGraph closure or preserve
completed arithmetic divisor domains. Its precise positive conclusion is
an actual sequence of compact C¹ logarithmic states approximating every
zero-anchored physical primitive in the visible physical energy and every
constructed compact source form, with explicit compensation and affine costs.

## Parents, corpus evidence and certification boundary

Classical measurable truncation, Cauchy–Schwarz, dominated convergence and
Steklov regularization are parent mechanisms. Primary sources inspected:
[mathlib indicator Lp seminorms](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/LpSeminorm/Indicator.html)
and [Demkowicz, Energy Spaces, §§2.1–2.3](https://users.ices.utexas.edu/~leszek/classes/CSE393/book.pdf).
The book's regularization and translation arguments are parents, not a
citation for this exact compensated logarithmic source theorem. The local
toolchain source, rather than online signatures, governs Lean APIs.

Two preceding corpus queries inspected20 candidates and20 source arguments
each; coverage limits are on the pipeline card. Current semantic query
returned no candidates, partial deadline/vector-statement coverage,
generation1447962 pending and refresh incomplete. A lexical query of known
parents was then run. No absence or external novelty claim is inferred.
The new insight is the exact zero-integral compensation cost and its coupling
to actual compact logarithmic support and source-mass-plus-jump convergence.

All displayed claims have dependency-closed paper proofs above. Formal
certification is pending; no contribution increment yet. No field Lean was
written before this proof. Field README is read-only; no RH work, numerical
experiment, analytic admission premise or pre-floor counterterm subtraction.
