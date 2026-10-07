# Overlap obstruction and the exact primitive penalty

Status: overlap no-go proved on paper; finite-packet and full smooth compact survivors pass exact-source scratch Lean/axiom audits and final target-file audit. EVIDENCE.md records commands and scope. WP02 remains open.

## Failed conjecture

Conjecture: every finite sum of translates of the same narrow polar bump g_w satisfies E(F)>=(log(1/w)-C)M(F), with C independent of width, centers, coefficients and number of terms. Here E is the actual archimedean energy and M is Fourier squared mass. This drops the separation condition from the proved packet theorem.

Verdict: FALSE on paper. Let G=Psi be the fixed nonzero smooth compact profile, and F=G''-G/4. F is nonzero: G is identically one near zero, where F=-1/4. Normalize Psi(x/w) by its positive integral to a smooth approximate identity rho_w. Then

    F_w = F*rho_w = (G''-G/4)*rho_w
        = integral G(y) g_w(x-y)/(w*integral Psi) dy.

Approximation of G and its first three derivatives gives F_w -> F in H1. For fixed w, the integrand is continuous in H1 as a function of y, on a compact y interval. Finite Riemann sums approximate this integral in H1. Choosing their error tending to zero produces actual finite overlapping packets P_w -> F in H1.

The corpus's upper and lower digamma estimates imply |A(tau/(2*pi))| <= C0(1+tau^2). Hence H1 convergence gives convergence of Fourier mass and actual archimedean energy: use Cauchy–Schwarz on the difference of squared Fourier norms with weight 1+tau^2. Thus M(P_w)->M(F)>0 and E(P_w)->E(F), both finite. The conjectured lower bound would diverge, contradiction.

The existing weighted-form mollifier convergence in `SuzukiHlogMollifiedFormCore.suzukiHlogMollifiedFormVector_tendsto_inward` confirms that energy topology, not pointwise convergence, is the appropriate corpus interface. The finite-Riemann-sum no-go argument above is a paper proof, not a claimed Lean theorem. No numerical Riemann sum was evaluated.

## Positive survivor

For arbitrary finite centers x_m and complex coefficients c_m, any width w>0, define

    G = sum c_m Psi((x-x_m)/w),
    F = sum c_m g_w(x-x_m).

Let C_a=digammaVerticalCoercivityConst(1/4)+log(2)+log(pi). For every real b,

    (b-C_a) M(F) <= E(F) + exp(b)^4 M(G)/4.             (1)

This is an unconditional source inequality for every such packet; it imposes no separation, positivity or arithmetic assumption. Width can be parameterized as exp(-s), s real, removing even a width-sign premise from the final statement.

Proof: Fhat=-(tau^2+1/4)Ghat. The scalar inequalities established in PACKET-PROOF give

    b-C_a <= A(tau/(2*pi)) + exp(b)^4/[4(2+|tau|)^4].

Multiply by |Fhat|^2 and use (tau^2+1/4)^2 <= (2+|tau|)^4. Integrate. Every packet and primitive is smooth and compactly supported, so all three integrands are integrable by existing corpus theorems. All Fourier cross terms are retained. This proves (1).

For the disjoint integer-log packet, M(G)<=R*w^4*M(F), recovering the earlier coercivity result by b=log(1/w). For overlapping approximants to a fixed broad G, the primitive mass does not shrink by w^4. Formula (1) therefore remains valid without predicting divergent energy.

## Additional audit

The Gauss series also suggests convexity of A in v=1/(tau^2+1/4). Each summand is constant minus (4n+1)v/(1+n(4n+2)v), with nonnegative second derivative. This is a Stieltjes/reciprocal-convexity mechanism. Merkle, *Reciprocally convex functions* (2004), explicitly treats negative Stieltjes transforms as a parent class; publisher search abstract inspected, full open returned 403. Do not claim this general convexity mechanism as novel. No separate Lean wrapper is planned for it.

Neither the overlap obstruction nor (1) controls M(G) from the exact exposing trace. That source estimate remains unpaid. A pure bound by the ray multiplier alone cannot hold because prime-blind polar packets may be added with arbitrary nonnegative mixture weight. Any useful bound must account for their mass or energy as well.

## Full smooth compact source extension

No finite-packet hypothesis is needed in (1). For every existing `CCMComplexSmoothInteriorSource a` primitive G, the corpus defines `G.polarMultiplier = G''-G/4`, proves smooth compact support and both polar constraints. Two integrations by parts give the same Fourier multiplier. Therefore the identical pointwise argument and integrability proof yield (1) for every such G. This is the strongest survivor selected for this cycle. No decomposition, density assertion or unproved estimate on G is used. Every smooth compact G fits this interface after choosing an aperture larger than its support; extension to the original C² full matched cone is not claimed by this theorem.
