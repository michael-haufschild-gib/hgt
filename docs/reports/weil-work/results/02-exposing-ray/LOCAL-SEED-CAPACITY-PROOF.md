# Capacity floor for local-seed variance completion

Status: dependency-closed paper proof, now formalized in WeilWorkExposingRayLocalCapacity.lean; complete scratch and final leaf/cache audits pass. Its generic ingredients are classical. The new source application concerns the literal truncated Riemann family, not arbitrary repairs. Full WP02 remains OPEN.

Let a=log(2)/2 and kappa=pi/(5*log(2)). Let g_j be finitely many actual compact C2 polar tests supported in [-a,a], let alpha_j>=0, M=sum alpha_j>0, and let x_j be arbitrary real translations. Define h_j(u)=g_j(u-x_j), F=sum alpha_j*h_j, and R_j=M*h_j-F. These are actual compact C2 polar tests at some common finite aperture: translations multiply each polar moment by a scalar, and finite linear combinations preserve their vanishing.

## Exact signed energy identity

For arbitrary complex numbers z_j and z=sum alpha_j*z_j, expansion of the squared norms gives

    |z|^2 + sum_j (alpha_j/M)*|M*z_j-z|^2
       = M*sum_j alpha_j*|z_j|^2.

No equal-modulus assumption is needed. Substitute z_j=paperFT(h_j)(tau). Real-frequency translation changes only a unit-modulus phase, hence |z_j|=|paperFT(g_j)(tau)|. Multiply by the actual archimedean symbol A(tau/(2*pi)) and integrate. Every term is integrable by compact C2 regularity, so this remains an equality even though the symbol changes sign:

    archEnergy(F)+sum_j (alpha_j/M)*archEnergy(R_j)
       = M*sum_j alpha_j*archEnergy(g_j).

## Fourier evaluation capacity

The new C2 admission theorem transfers the existing one-tenth ground gap exactly:

    archEnergy(g_j)>=(pi/5)*integral |g_j|^2.

At every real frequency t, the corpus's `norm_paperFT_real_le` bounds the Fourier value by the L1 norm. Cauchy–Schwarz on support interval [-a,a], whose measure is log(2), gives

    |paperFT(g_j)(t)|^2 <= log(2)*integral |g_j|^2.

Thus E(g_j)>=kappa*|paperFT(g_j)(t)|^2. Weighted Cauchy–Schwarz for the finite translated Fourier values gives

    |paperFT(F)(t)|^2 <= M*sum_j alpha_j*|paperFT(g_j)(t)|^2.

Combining these inequalities with the exact energy identity proves, for every real t,

    kappa*|paperFT(F)(t)|^2
      <= archEnergy(F)+sum_j (alpha_j/M)*archEnergy(R_j).

This is a quantitative positive survivor for the whole local-seed variance class. It neither supposes nor proves that an arbitrary repair admits such a representation.

## Literal truncated Riemann source

Take F_L=polarRiemannDifference(L,1), equivalently the complex lift of `polarRiemannDifferenceReal L 1`. The source identity `paperFT_polarRiemannDifference` evaluated at zero gives

    paperFT(F_L)(0) = (1-2*polarWeight(1))*integral Phi(u)*bulkCutoff(L,u) du.

Put b=1-2*polarWeight(1). Its actual denominator is exp(1/2)+exp(-1/2)=2*cosh(1/2), so b>0 analytically. Let m=integral over [-1/2,1/2] of Phi. Continuity and strict positivity of the actual Riemann kernel imply m>0. For L>=2 the actual cutoff is one throughout that interval and nonnegative everywhere. Hence |paperFT(F_L)(0)|>=b*m. Every local-seed variance completion of F_L has total energy at least

    delta = kappa*b^2*m^2 > 0,

uniformly in L, seed count, weights, translations, and profiles. The exposing finite mixture retains this source as its k=0 term with energy weight 1/(2*pi). If each source is completed through this class, all completion energies are nonnegative and that first term alone gives delta/(2*pi).

## Scope and attack verdict

The zero-total-energy endpoint is unavailable to this whole local-seed mechanism for the actual exposing source. This is broader than the fixed-profile geometric gap. The generic capacity inequality is a direct ground-gap/Cauchy–Schwarz bridge; external scientific novelty is not established. The specific source exclusion is the reason to formalize it, if the subsequent source/novelty audit confirms its utility.

An arbitrary opposite-ray mixture need not come from a local-seed variance completion. Furthermore, passing from the literal finite Riemann mixture to an exactly repaired truncated exposing trace requires retaining every integer residual and its energy. No such passage is asserted here. A successful opposite-ray producer must address those obligations, and the original universal lower inequality remains unchanged.


## Formal closure, cycle 12

The module proves the exact signed identity and capacity for every real frequency, not only zero. All translated means and variance residuals are admitted as actual C2 polar tests within the explicit common aperture log(2)/2+sum|x_j|. The central mass is `riemannMass`; `riemannMass_pos` and `riemannCapacity_pos` prove strict positivity. The literal source theorem is `riemann_local_completion_floor`. `exposing_mixture_local_completion_floor` allows a different finite seed type for every source k, retains all source terms, and proves the exact lower bound riemannCapacity/(2*pi).

This closes the stated local-seed conjecture and its stronger all-frequency/whole-mixture survivor. It supplies neither arbitrary-repair representation nor the universal exposing-ray lower estimate. Final verification details and the prior-source audit are in EVIDENCE.md.
