# Exact matched-ray mass and the zero-margin boundary

Cycle17. Paper proof and Lean audits closed in WeilWorkExposingRayMassMargin.lean: six public theorems, final source audit and standard-axiom audits pass. Classification: source-specific BRIDGE / precision boundary, not a new general uncertainty principle or an RH proof.

## Exact conjecture and useful survivor

Let M(f)=integral |f(u)|^2 du. There are fixed m0>0 and C such that, for every sufficiently large N, an actual finite nonnegative polar C2 family has aperture at most log(N)/2+C, all integer traces exactly w_N (including the zero tail), total mass at least m0, and energy at most T+2*tau_N.

Consequently, for EVERY epsilon>0 and EVERY fixed real c, all sufficiently large N admit such a family with

    total_energy - epsilon*total_mass < T-c*tau_N.

Thus adding any fixed positive physical-mass margin to the universal lower bound fails, even with an arbitrary fixed multiple of the box-tail slack. Equivalently, uniformly lowering the Fourier symbol by a positive constant cannot preserve the original endpoint inequality (with the corresponding Plancherel normalization). No claim about a nonuniform spectral debit is made yet.

The positive survivor is the exact matched family with a cutoff-independent mass floor and a vanishing energy excess bound. This concerns the actual full ray constraints, not a toy null family. The lower sign of its energy excess remains unproved and is not needed.

## Dependency-closed proof

1. For every continuous compactly supported complex f and real y, norm(Corr(f,f)(y)) <= M(f). Indeed, norm of the integral is bounded by the integral of |f(u)| |f(u-y)|. Pointwise 2ab<=a^2+b^2, followed by translation invariance of Lebesgue integration, gives the claim. All majorants are integrable by continuous compact support. Hence |atomCoeff(f,n)|<=2*M(f), with both signed logarithmic samples retained.
2. For any nonnegative finite mixture and any matched atom n, triangle inequality gives |w_N(n)| <= 4*pi*sum alpha_i M(f_i). This holds for all complex tests and all finite index sets.
3. The formal theorem exposingWeight_eventually_pos supplies an actual integer n0>=2 with w(n0)>0. For every N>=n0, w_N(n0)=w(n0). Put m0=w(n0)/(4*pi)>0. Every unit-ray matched mixture then has mass at least m0; this is independent of its construction and aperture.
4. Apply the already compiled natural_aperture theorem with its approximation parameter equal to one. It constructs the exact families in the first statement, with energy <= T+2*tau_N. Combine with step3. This uses neither RH nor Weil positivity nor a lower-energy hypothesis.
5. Since tau_N tends to zero, (c+2)*tau_N eventually lies below epsilon*m0, for any real c. Subtract epsilon times the actual mass from the energy bound to obtain the strict displayed failure. Every omitted atom remains zero by the exact construction. No numerical estimate is used.
6. For any 0<r<2*pi*exp(-2), the compiled exponential tail bound gives tau_N<=B*exp(-r*N). Since total_mass>=m0>0, the same families satisfy total_energy-T <= (2*B/m0)*exp(-r*N)*total_mass. This is a quantitative, mass-normalized upper bound; it still supplies no lower sign or absolute-value convergence.

## Hostile, utility and novelty audits

The argument does NOT bound energy below, prove prime-blind positivity, prove cone nonemptiness, or show E-T tends to zero in absolute value. An upper bound tending to zero is not a two-sided limit. It rules out a uniform positive mass margin only; it does not rule out retaining the complete signed gamma symbol or using a debit that vanishes on the limiting exposing density.

Fresh deep searches of the actual corpus inspected all returned candidate lemmas, source arguments and proposed ingredient sets. Existing near-radical margin laws concern unconstrained test families; finite realization supplies the extra all-integer matching here. Returned primitive coercivity leaves its primitive penalty, and the proposed search proof sets do not supply an endpoint sign. No absence-of-literature claim follows from retrieval.

Primary-source comparison checked 7 October 2026: Connes–Consani, https://arxiv.org/abs/2006.13771, treats the single-place trace mechanism; Zhu, https://arxiv.org/abs/2608.24827v2, discusses fixed-window bounds and collapsing spectral margins. The latter abstract explicitly distinguishes unconditional finite-window estimates from an RH-conditional asymptotic upper bound. Neither abstract establishes the present exact matched-ray statement. General zero-margin reasoning is classical; scientific novelty beyond this corpus synthesis is unestablished. No computational claims from those papers are imported.

## Next substantive gate

The mass argument alone does not classify nonuniform symbol approximations. Test the stronger concrete conjecture that exact repaired finite-ray families retain the complete limiting real-axis spectral density of the canonical polar Riemann mixture, in L1. That would locate every surviving spectral debit, rather than assert another scalar margin obstruction. It needs an actual retained-source/repair-mass estimate and a full density convergence proof before Lean, and must be compared with existing corpus source limits. Universal WP02 remains the objective.
