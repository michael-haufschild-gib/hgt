# Sublinear residual mass: paper proof of G

Status: dependency-closed paper argument; **G passed its final direct Lean leaf audit without warnings; all thirty-two new declarations passed their axiom audits**, with only the three standard Lean axioms. Scientific novelty remains provisional. The statement extends the inspected atomic and continuous-edge parents to the actual canonical measure with arbitrary singular-continuous or accumulating fractional remainder. It does not supply a sublinear residual bound from the source.

Let hW be any specified full-cone positive input, μ its canonical measure, κ its integer atomic floor, and ν=μ−κ. Write R for λ(n)=Λ(n) for n≥2 together with RH. We prove

`R ∨ ∀ α<1, ∀ K∈ℝ, ∃ T≥1, K T^α < ν.real([-T,T])`.

All notation and finite-interval decompositions come from the finished integer-floor and residual-phase leaves. The proof below assumes a bound only inside a proof by contradiction of the second alternative; the final statement has hW as its only substantive input.

## Cumulative phase

Suppose ν.real([-T,T])≤K T^α for T≥1 and α<1. Replace α by max(α,1/2) and K by |K|+1, obtaining 0<α<1 and K>0 with the same bound. Define C(x)=ν.real((0,2x]); this is zero for x≤0. Every interval involved has finite measure because ν≤μ and μ is locally finite. Thus C is a nonnegative monotone measurable function on ℝ and, for x≥1,

`C(x) ≤ ν.real([-2x,2x]) ≤ K 2^α x^α`.

At almost every positive y, μ({y})=0. On such intervals the compiled integer floor decomposition removes an integer from μ((0,y)), so the compiled zero-safe radial phase identity gives

`G₀(y) = exp(iπ μ({0})) exp(2πi ν((0,y])) G₀(-y)`.

Set c=exp(iπ μ({0})), Φ(t)=F₀(2t) and Ψ(t)=G₀(-2t)/D(2t), where D(y)=s_y(s_y−1)Γ_R(s_y), s_y=1/2+iy. Then |c|=1 and, almost everywhere on t<0,

`Ψ(t)=c exp(2πi C(-t)) Φ(t)`.

This identity does not divide by G₀ and remains valid at trace zeros. It uses no total mass or limiting phase for ν.

## Refined radial remainder, without a continuous edge

Fix integer m≥1, τ=ε+im, 0<ε≤1, δ=ε/|τ| and M=m+1. Let a_n be the actual Dirichlet coefficients of F, a₁=1. Use the compiled offKernel, rhoMain and edgeTerm definitions in `HamburgerAbelianTwistContour`; write k for pairKernel. For 0<p≤1 the completed SUBPOLYNOMIAL proof gives a uniform constant A_p with |F(x+iy)|≤A_p(1+|y|)^p on 1/2<x≤3/2, |y|≥2.

For Y≤B≤−2, apply Cauchy's rectangle identity on [σ,3/2]×[Y,B], with σ>1/2. Subtract the right vertical integral. The norm of the difference is bounded by the sum of the two horizontal edge norms. The existing offKernel bound makes each horizontal edge at height y at most

`H(y)=A_p (1+|y|)^p 4π^(3/4)|τ| exp(-|y|δ)`.

The width is at most one; the bound holds uniformly in σ. Let σ decrease to 1/2. The already compiled compact radial product convergence passes the left vertical integral to F₀(y)k(y,τ). The right integral and H are independent of σ, so the inequality survives. No horizontal boundary integral is introduced.

For fixed τ, both vertical integrals on (-∞,B] are absolutely integrable: the right edge has its Dirichlet bound times exponential decay; the radial trace has its polynomial bound times the same exponential decay. Also H(Y)→0 as Y→−∞. Passing to this limit gives

`|∫_{t≤b} Φ(t)k(2t,τ)dt − (1/2)∫_{y≤2b} F(3/2+iy)offKernel(τ,3/2+iy)dy| ≤ H(2b)/2`

for b≤−1. The factor 1/2 is the change of variable y=2t.

The compiled `hasSum_edgeTerm` identifies the right integral from the actual arithmetic continuation; it requires no critical-edge continuity. Split off n=m. The compiled `edgeTerm_resonant` makes its contribution exactly 2a_m∫_{t≤b}rhoMain(m,τ,t)dt. The compiled off-resonant estimate bounds the other terms by

`S |τ|^(1/2) (8m+4/π) exp(2bδ)`,

where S=Σ_n |LSeries.term(a,3/2,n)|<∞. Triangle inequality therefore bounds the remainder d_m(t)=Φ(t)k(2t,τ)−a_m rhoMain(m,τ,t) by

`|ε∫_{t≤b} d_m(t)dt| ≤ K_m,p ε^(1−p) exp(bδ)`.

To verify the uniform dependence, use |τ|≤M, ε≤ε^(1−p), exp(2bδ)≤exp(bδ), and the compiled elementary estimate

`ε (1+2|b|)^p exp(2bδ) ≤ ε^(1−p)(1+2M)exp(bδ)`.

These give precisely K_m,p=(S M^(1/2)(8m+4/π)+A_p·4π^(3/4)M(1+2M))/2. No limit is taken uniformly in m; each positive integer is fixed.

## The unbounded monotone twist

Choose p=(1−α)/2>0. Apply the already compiled generic `norm_setIntegral_twist_le_pow` to d=ε d_m and C. Its premises are all paid: d is measurable and integrable; (C(-t)−C(1))|d(t)| is integrable on t≤−1 because C grows at most linearly there, while d has polynomial times exponential decay. Its cumulative bound is the preceding display. With β₀=2π the result is

`|ε∫_{t≤−1} exp(2πi C(-t))d_m(t)dt| ≤ A ε^(1−p)+B ε^(1−p−α)`.

The constants may depend on hW,m,α,K but not ε. Both exponents are positive. Hence the twisted remainder tends to zero. This use of layer cake permits atoms and singular-continuous mass; differentiability of C is unnecessary.

## Arithmetic residue and coefficient comparison

Let β=G(1)/2, which is nonzero: the canonical completion is a nonzero normalization times an exponential in the open half-plane. Its nonzero normalization is the compiled arithmetic nonvanishing at 2. The two finished actual Hamburger identities and linearity of defectLaplace give, for Re τ>0,

`JΨ(τ)=S_a(τ)−β/(πτ)`,

where S_a(τ)=Σ_{n≥1} a_n exp(-2πnτ). All linearity operations are justified by the finished polynomial trace bounds and absolute kernel integrability. The generic base limit gives εJΨ(ε)→0, hence εS_a(ε)→β/π. Integer support gives S_a(ε+im)=S_a(ε) for every integer m. Consequently εJΨ(ε+im)→β/π for each m≥1. The upper-half-line contribution tends to zero by the compiled upper radial estimate; the singleton at zero has zero volume. Therefore

`ε∫_{t<0} Ψ(t)k(2t,ε+im)dt → 2β`.

Insert the almost-everywhere cumulative phase. The portion −1<t<0 tends to zero after multiplication by ε, by its compact trace bound, unit phase norm and bounded kernel for fixed m≥1. Remove the twisted remainder proved above. This yields

`c a_m M_C(ε/m) → 2β`,

where M_C(r)=r∫_{t≤−1}exp(2πi C(-t))rhoMain(1,r+i,t)dt. The exact rescaling is the compiled `mainTwist_scale`, an algebraic identity independent of G or boundary continuity.

For m=1 and a₁=1, cM_C(ε)→2β. Rescaling ε↦ε/m gives cM_C(ε/m)→2β; multiplying by a_m and comparing with the preceding limit gives 2β a_m=2β. Since β≠0, a_m=1 for every m≥1. The compiled `vonMangoldt_and_RH_of_coeff_eq_one` applies to the actual open-half-plane continuation and yields R. This receiver requires no critical-edge continuity.

Thus any failure of the stated quantitative alternative forces R, proving G. The exact formal conclusion is `quantization_rigidity_or_residual_power_obstruction`. Excluding the super-sublinear residual alternative remains a separate source problem for WP04.

## Compiled dependency map

- `WeilWorkQuantizationRadialRemainder`: finite rectangle, compact radial limit, lower-height limit, arithmetic resonance subtraction and refined epsilon estimate.
- `WeilWorkQuantizationRadialPower`: weighted integrability and unbounded monotone phase layer cake.
- `WeilWorkQuantizationCumulativePhase`: local finite residual counts and zero-safe almost-everywhere reflection.
- `WeilWorkQuantizationReflectedResidue`: actual reflected transform, periodic residue and lower-half-line residue.
- `WeilWorkQuantizationPowerRigidity`: main-term scaling, coefficient comparison, growth normalization and the intrinsic source-only alternative.

Each dependency passed its direct leaf check. Final axiom-audit results are recorded in EVIDENCE.md and power-residual-lean-audit.txt.
