# Hard target: the recovery-gap sequence

**Priority:** attack this mathematical problem, following the user's correction on 6 September 2026. Further formalization of standard operator consequences is not progress on this target.

For m≥1, W(r)=1−√(1−4r) on [0,1/4]. The actual gap δ_(m−1) is the minimum of max W(r)^m|R(r)| over degree ≤m polynomials with coeff_(m−1)R=1. Positive attainment is formal. Weighted alternation and interpolation give a paper-only unique optimizer: the monic weighted Chebyshev polynomial divided by its penultimate coefficient.

**Unresolved target:** prove or disprove δ_(k+1)²≤δ_kδ_(k+2) for every k. The stronger conjecture that γ_n=(δ_n/δ_0)² is a probability moment sequence now has a reproducible numerical counterexample candidate. Priority: prove its exact sign, rather than continue looking for a positive representing measure. The operator interpretation is already available; do not replace the target with more infrastructure.

**Exact reduction for exploration:** put x=4r=c(2−c). If Q is the degree-m weighted monic Chebyshev polynomial in x, then δ_(m−1)=max_(0≤c≤1)c^m|Q(c(2−c))| /(4^(m−1)|coeff_(m−1)Q|). A common scaling of Q cancels. In shifted Chebyshev coordinates Q=Σa_j T_j(2x−1), fixing a_m=1 gives penultimate coefficient 2^(2m−3)a_(m−1)−m2^(2m−2) for m≥2; for m=1, the constant coefficient is a_0−a_1.

The c-polynomial has degree 3m, a zero of order ≥m at 0, and its quotient by c^m is symmetric under c↦2−c. This does not give an ordinary Chebyshev composition: composition destroys the required zero multiplicity. No general formula obtained from this route.

Numerical minimax exploration is justified to decide which of the two competing conjectures to attack. Run only on the authorized Runpod; retain code, output, and a short report under computations. Numerical values will not enter Lean proofs.

**Operator checkpoint:** five operator leaves passed final individual builds and declaration axiom audits: CubicRecoveryMultiplier, CubicCuspMultiplier, CubicHilbertShift, CubicRecoveryCommutator, CubicRecoveryPositivity (45 declarations). At that checkpoint global lint passed, with 106 leaves/1094 declarations. The later protected-grid construction adds 40 audited declarations; see [current working notes](../../cross-disciplinary/universal-laws-and-structures/excursion-intervention-geometry.md). CubicRecoveryMoments is only an unfinished /tmp scratch and was stopped after the user's correction; it is not exported or counted.

**Actual progress on the hard problem:** [paper proof of the exact exponential rate](../../../2-fully-proven/chronological-recovery-exponential-rate.md): lim δ_k^(1/k)=ρ, where ρ≈0.01736004210 comes from a fixed even convex external potential. Any representing probability measure must have support endpoint ρ². The transformed weighted Chebyshev problem has potential −½log(1−|t|); extend it quadratically outside any a between its equilibrium support and 1 to justify the whole-line support formula, then compare weighted energies. A simple endpoint product estimate proves the root-sum normalization is subexponential. No root-distribution theorem is needed.

[Runpod results](../../../2-fully-proven/computations/chronological-recovery-gaps/REPORT.md): degrees 1–64; the 18×18 unshifted Hankel matrix for γ has a negative eigenvalue. All 2080 available Hausdorff differences still pass: this finite-difference truncation is weaker than positivity on polynomial squares of the same available degree. A second calculation in coefficient coordinates at 230 digits independently checks the first 35 gaps and the following witness. No computed number has entered a Lean proof.

**Concrete hard inequality, not yet proved:** set s=3/10000 and

`p(x)=Σ_(j=0)^17 c_j x^j`, `c_j=(-1)^j binom(17,j) binom(18+j,j)/(j+1)`.

This is the canonical normalized Jacobi polynomial P_17^(1,0)(1−2x)/18. The candidate is

`Σ_(i,j=0)^17 c_i c_j s^(−i−j) δ_(i+j)² < 0`.

Its numerical value is approximately −0.00000398195275827, or −0.00024340009021827 after division by δ_0². If proved exactly, it excludes every positive moment measure: the left side would be the integral of a polynomial square, multiplied by δ_0². The rational scale s makes this test independent of the potential-theory constant ρ. The witness formula is exact; the negative evaluation is exploratory. Do not claim non-subnormality as proved or import decimal bounds as proof certificates.

**Positive survivor, paper proved:** [uniform block growth and the exact spectral disc](../../../2-fully-proven/chronological-recovery-uniform-spectrum.md). Repair the forbidden penultimate coefficient of H_d=c^dT_d(u/c) by adding S_d cH_(d−1). The result is an available observation acting as U^d and yields δ_(k+d)≤[t_d+(d/4)t_(d−1)]δ_k uniformly in k. Thus lim(sup_k δ_(k+d)/δ_k)^(1/d)=ρ, and the complexified recovery shift has spectrum the closed disc of radius ρ. No moment assumption is used. Lean status: paper only, including the earlier Chebyshev/rate dependencies.

**Rejected routes / remaining uncertainty:** fixed-degree Fenton intertwining does not compare different degrees. Unsquared gaps already fail a numerical 10×10 moment test; squaring postpones the obstruction. Logarithmic finite differences also reject the infinite-divisibility route. These numerical failures are not exact no-go theorems. The shifted unsquared sequence also fails at larger matrix size, so a model with only a negative atom at zero is unsupported. The equilibrium measure in the rate proof is not a representing measure for gaps. General novelty remains unestablished.

**Structural obstruction now proved on paper:** [delayed moment obstruction](../../../2-fully-proven/chronological-delayed-moment-obstruction.md) constructs actual compact semialgebraic radial domains for the same cusp algebra, preserving any prescribed finite prefix of base recovery costs and forcing the first negative square at an explicitly arbitrarily high degree. The first failing Hankel matrix has inertia (d,1,0); the thermal zeta response is unchanged. The proof is analytic, using arithmetic separation of Chebyshev grids and a coefficient-preserving cardinal perturbation. It establishes that neither the cusp algebra, the heat trace, nor finite curvature tests force a moment representation. These domains are nonconvex and differ from the original cubic probe section. It does not settle the exact Jacobi witness above or global log-convexity. Full geometric Lean formalization remains open.
