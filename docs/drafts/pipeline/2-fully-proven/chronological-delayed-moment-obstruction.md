# Arbitrarily delayed moment obstruction in semialgebraic recovery geometries

**Status:** the geometric negative-square theorem is now formalized: actual planar domains, faithful polynomial evaluation, attained geometric quotient norms, exact protected costs and first-drop bounds, strict adjacent log-convexity, exact first negative-square degree, absence of a representing measure, Hankel inertia, and Hausdorff convergence. Individual leaf checks pass; the full new axiom audit remains pending. The actual graded completion is formalized; its radial-flow trace/Mellin identification and the base wedge's explicit representing measure are in scratch. No numerical input. The original cubic numerical sign problem and novelty/priority remain open.

## Statement

Keep the actual polynomial observation algebra `A=ℝ[u,c²,c³]⊂B=ℝ[u,c]`. For a compact radial geometry K with interior, let Δ_k(K) be the least uniform norm on K of a homogeneous degree-(k+1) polynomial whose coefficient of u^k c is one. These are the actual graded quotient norms of B/A, not prescribed sequence values.

Let `K₀={(u,c):0≤c≤1, c≤u≤3c}` and `β_k=1/((k+1)2^(k+1))`. For every j≥0, put `N=2^(j+4)` and `m=N+1`. The construction below gives an explicit compact semialgebraic radial set K_m⊂K₀ with interior such that:

1. `Δ_k(K_m)=β_k` for every `0≤k<N`.
2. The prefix through Δ_N is strictly log-convex: `Δ_(k+1)²<Δ_k Δ_(k+2)` for `0≤k≤N−2`.
3. The squared normalized costs `γ_k=(Δ_k/Δ_0)²` are not moments of any positive measure, even on ℝ. The least degree of a polynomial P with `L_γ(P²)<0` is exactly `d=N/2`. The first failing Hankel matrix, of size d+1, has precisely one negative eigenvalue and d positive eigenvalues.
4. `K_m→K₀` in Hausdorff distance. The unchanged cusp algebra and radial flow give the same graded flow trace `q/(1−q)` and hence the same reference-subtracted Mellin response `−Γ(s)ζ(s)` on `0<Re(s)<1`.

Thus arbitrarily many initial recovery costs and adjacent curvature tests can agree with a positive-moment model while a later moment obstruction is forced by the geometry. For j=0, m=17: the first 16 costs are unchanged, the next cost forces a degree-eight polynomial-square obstruction, and all adjacent log-convexity inequalities within that prefix remain strict.

## Base costs and a controlled polynomial perturbation

Write T_ℓ for the ordinary Chebyshev polynomial, with `T_ℓ(cos θ)=cos(ℓθ)`. A degree-ℓ homogeneous polynomial is `c^ℓ R(u/c)` (homogenization, including c=0), and its norm on K₀ is `max_[1,3]|R|`. The coefficient of r^(ℓ−1) in T_ℓ(r−2) is `−ℓ2^ℓ`. Therefore

`R_ℓ(r)=−T_ℓ(r−2)/(ℓ2^ℓ)`

has the required coefficient and norm β_(ℓ−1). It is optimal: interpolate at the ℓ+1 nodes `2+cos(iπ/ℓ)`. All nodes are positive. The penultimate-coefficient signs of their Lagrange cardinal polynomials alternate oppositely to the values of T_ℓ. Consequently the sum of the absolute coefficient weights is ℓ2^ℓ, and interpolation bounds every admissible R below by β_(ℓ−1). This is the elementary coefficient-duality argument; no weighted asymptotic theorem is needed here.

Now fix m=N+1. Set `x_i=cos(iπ/m)`, `ξ=x_1`, and let ℓ₁(x) be the Lagrange cardinal polynomial at ξ for the m+1 nodes x_i. Define

`α=−2m²/(2m−ξ)`, `ε=1/(16m³)`, `h=1−ε/2`,

`V_m(x)=(1−ε)T_m(x)+εαℓ₁(x)`, `L=4m+1`.

The coefficient of r^(m−1) in ℓ₁(r−2) is `(2m−ξ)2^(m−1)/m`. Hence V_m(r−2) has the same required coefficient `−m2^m` as T_m(r−2). Also `|α|≤2m` and `‖ℓ₁‖_[−1,1]≤2`, so

`‖V_m−T_m‖≤εL`, `‖V_m‖≤1+εL`.

Both the bound and coefficient formula follow from the finite cosine expansion, with θ₀=π/m:

`ℓ₁(x)=[1+2Σ_(k=1)^(m−1) cos(kθ₀)T_k(x)−T_m(x)]/m`.

To verify it, put `D_m(t)=Σ_(k=0)^(m−1)cos(kt)+(cos(mt)−1)/2`. Telescoping the sine addition formula gives `2sin(t/2)D_m(t)=sin(mt)cos(t/2)`. Hence D_m(0)=m, D_m is even, and D_m(qπ/m)=0 for integers 0<q<2m. At x=cos t the displayed polynomial is `[D_m(t−θ₀)+D_m(t+θ₀)]/m`. Its values on the m+1 nodes are one at ξ and zero elsewhere, so finite interpolation identifies it with ℓ₁. The triangle inequality gives its norm at most `[1+2(m−1)+1]/m=2`.

Its two highest coefficients are `−2^(m−1)/m` and `−ξ2^(m−1)/m`, respectively: only T_m and T_(m−1) contribute, and `cos((m−1)θ₀)=−ξ`. Substitution x=r−2 gives the stated penultimate coefficient `(2m−ξ)2^(m−1)/m`. This finite expansion avoids estimates of a derivative quotient near ξ.

## Every lower-degree alternation set is protected

Take any node `x=cos(iπ/ℓ)` with `1≤ℓ<m`. It cannot equal ξ. If it is also an mth-degree alternation node, then ℓ₁(x)=0, giving `|V_m(x)|=1−ε<h`.

Otherwise mi/ℓ is not an integer. Its distance to the nearest integer is at least 1/ℓ. Hence

`|T_m(x)|≤cos(π/ℓ)≤1−2/ℓ²≤1−2/m²`.

Here ℓ≥2 in the nonshared case, and the sine chord inequality gives `1−cos(π/ℓ)≥2/ℓ²`. Since L≤5m,

`|V_m(x)|≤1−2/m²+5/(16m²)=1−27/(16m²)<h`.

This uniform arithmetic separation of different alternation grids is what makes the perturbation polynomially, rather than exponentially, small.

## The geometry enforces the change in the actual cost

Let F_m(u,c) be the homogeneous degree-m polynomial represented, for c≠0, by `c^m V_m(u/c−2)`. Define

`K_m={(u,c):0≤c≤1, c≤u≤3c, |F_m(u,c)|≤h}`.

This is a closed bounded semialgebraic set, invariant under multiplication of both coordinates by q∈[0,1]. Set `a=h/(1+εL)` and `q₀=a^(1/m)`. Then `0<q₀<1` and

`q₀ K₀ ⊂ K_m ⊂ K₀`.

The first inclusion follows from homogeneity and the bound on ‖V_m‖. It supplies interior and convergence K_m→K₀, since a→1 and q₀≥a. In particular the polynomial norm is faithful and every normalized finite-dimensional homogeneous affine class has a positive attained minimum.

Every protected lower-degree node `(u,c)=(2+x,1)` belongs to K_m. The original lower-degree optimal residuals still give the upper bounds because K_m⊂K₀; interpolation on the protected nodes gives the matching lower bounds. This proves Δ_k=β_k for k<N.

At degree m, `−F_m/(m2^m)` is an admissible residual and has norm at most hβ_N by the defining inequality of K_m. The inclusion q₀K₀⊂K_m gives the lower bound for every admissible degree-m residual. Therefore

`aβ_N ≤ Δ_N(K_m) ≤ hβ_N`.

Moreover

`1−a = ε(L+1/2)/(1+εL) ≤11/(32m²)<1/(m−1)²`.

The only newly affected adjacent log-convexity inequality requires `Δ_N/β_N > (m−2)m/(m−1)² =1−1/(m−1)²`, which follows. Every earlier inequality is unchanged from the strictly log-convex base sequence.

## An exact negative square functional

The base normalized moments are `b_k=(β_k/β_0)²=4^(−k)/(k+1)²`. They have the elementary representation

`b_k=∫₀¹∫₀¹ (st/4)^k ds dt`.

Let `d=N/2` and choose the monic polynomial

`Q_d(x)=2·16^(−d) T_d(8x−1)`.

On [0,1/4], its squared norm is at most `4·16^(−N)`. Thus the base moment functional obeys `L_b(Q_d²)≤4·16^(−N)`.

The new moments γ_k agree with b_k for k<N, and γ_N≤h²b_N. Since Q_d² is monic of degree N,

`L_γ(Q_d²)=L_b(Q_d²)+γ_N−b_N`

`≤4·16^(−N)−(ε/2)b_N`

`=4·16^(−N)−4^(−N)/(32m⁵)<0`.

The penultimate inequality uses `1−h²≥ε/2`. For the final strict sign, write k=j+4≥4, so N=2^k and m=2^k+1<2^(k+1). Induction gives `2^(k+1)≥5k+12`: equality at k=4, and doubling preserves the inequality. Consequently

`4^N=2^(2^(k+1)) ≥2^(5k+12) >128m⁵`.

For the first example m=17, this is simply `128·17⁵<2^7·32⁵=2^32=4^16`. No numerical minimax result or approximate constant enters the proof. A positive representing measure would make the integral of Q_d² nonnegative, so none exists.

This is the **first possible square obstruction**, not just a late witness. If P is nonzero and deg P<d, then deg P²<N, so `L_γ(P²)=L_b(P²)>0`. The last strict inequality follows from the displayed double integral: a nonzero polynomial cannot vanish on the whole interval (0,1/4), and a small open rectangle around a point with P(st/4)≠0 contributes strictly positively. More generally every nonzero polynomial nonnegative on [0,1/4] and of degree less than N has strictly positive γ-functional value.

For the inertia assertion let `H_d=(γ_(i+j))_(0≤i,j≤d)`. It differs from its positive-definite base matrix only in its bottom-right entry. Its restriction to polynomials of degree at most d−1 is positive definite, a subspace of dimension d. The exhibited negative square supplies a negative direction. Therefore H_d has exactly d positive and one negative eigenvalue, with no zero eigenvalues. Its determinant is negative; every smaller leading Hankel matrix, and the shifted d-by-d matrix using moments through N−1, is positive definite. These claims concern the indicated finite matrices, not all translated matrices in the infinite tail.

Thus the integer `ν(K)=min{deg P : L_γ(P²)<0}`, with value ∞ when there is no such P, satisfies `ν(K_m)=2^(j+3)` and `ν(K₀)=∞`. Within this fixed algebra and identical thermal response, the first detectable failure degree is unbounded. In particular the property of having a positive moment representation is not open at K₀ in Hausdorff topology on compact radial domains with interior.

The domains are explicitly nonconvex. Both (1,1) and (3,1) are protected nodes, while their intermediate point (2+ξ,1) is excluded: the cardinal value there is one and `V_m(ξ)=−1+ε(1+α)<−1`, since α<−1. No convex-domain counterexample is asserted.

## The zeta response survives

K_m has interior, so polynomial observations remain faithful. The quotient B/A still has one homogeneous line in each positive degree, represented by u^k c. Its norm is Δ_k by definition. Complete their orthogonal sum using these actual positive quotient norms. The physical radial flow acts on its orthonormal basis as `b_k↦q^(k+1)b_k`; for 0<q<1 it is a positive trace-class operator with trace q/(1−q).

Thus the same continuum-reference subtraction used in the original construction has Mellin transform −Γ(s)ζ(s) on 0<Re(s)<1. The nontrivial zero divisor in that strip is unchanged. This statement uses the established classical Mellin identity; it does not assert new facts about zeta zeros or RH. What changes is the geometry of the actual recovery costs, including failure of positive moment representation.

## Proof scope and formal target

The new contribution candidate is the realization by explicit semialgebraic recovery geometries, with an exactly preserved prefix and a quantitative high-degree obstruction. The abstract existence of weighted shifts with finite positivity and later failure is not claimed as new. The construction is independent of the numerical candidate in [the original hard-target card](../1-in-progress/chronological-recovery-moment-problem.md).

Classical inputs are finite Lagrange interpolation, the elementary Chebyshev identities (see [DLMF 18.5.1](https://dlmf.nist.gov/18.5.E1)), and elementary polynomial integration. The proof includes the estimates needed for the special perturbation; it uses neither weighted potential theory nor a numerical certificate.

Lean's `RecoverySurgery` leaves now connect the exact cardinal perturbation to actual geometry and actual quotient norms. The unconditional capstones `recoverySurgery_dyadic_first_failure`, `recoverySurgery_dyadic_no_measure`, and `recoverySurgery_dyadic_inertia` prove the obstruction and its precise first occurrence. `recoverySurgeryGap_prefix_strict_logconvex` and `recoverySurgeryDomain_hausdorff_tendsto` prove the geometric stability assertions. Remaining finalization is recorded in the status above; no cost sequence or trace is assigned by fiat.
