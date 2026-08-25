# Hawking–Teukolsky mediator holonomy route (2026-08-25)

New source-specific chain, after rejecting KMS half-density as imaginary-frequency translation.

Files:
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyMediatorHorizonHolonomy.lean
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyMediatorHorizonMonodromy.lean
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyMediatorSourceIncidence.lean
- imports added to formal/GaloisForLFunctions/RHTower.lean

Exact results:
1. Existing two virtual BM mediator clocks satisfy
   omega_R - omega_F = I*(Re rho - 1/2).
2. Analytically continued exponential-peeling Hawking kernel at two distinct log incoming frequencies has rectangle holonomy
   exp(kappa^{-1}*(Re rho-1/2)*(ell1-ell2)).
   Its 2x2 determinant vanishes iff Re rho=1/2 for nonzero inverse surface gravity and ell1 != ell2.
3. Nonzero separated row/column factors (Gamma/Jost residue, angular/radial normalization) only rescale determinant and cannot change vanishing.
4. Both mediator angular channels have a common bright completed-Eisenstein input by countable avoidance.
5. In BM unit-surface-gravity normalization, relative incoming-frequency monodromy is
   exp(2*pi*I*(Re rho-1/2)).
   Critical-strip confinement removes nonzero integer aliases. It is 1 iff critical.
   A tilted nonzero relative amplitude cannot be single-valued; any closing calibration has unique nontrivial monodromy.
6. Exact fundamental chiral radial kernel -3/[Q(Q+2)] is nonzero in both mediator rows (Q=-3/4 and -2<Q<0). Combining it with common bright angular incidence and Hawking kernel gives a factorized EKG–Teukolsky source determinant nonzero for some bright input at every tilted divisor.
7. Global rank-one/monodromy-trivial/bright-source confluence variants are each equivalent to RH; these are endpoints, not proof of their dynamical premise.

Hostile limitation:
- Monodromy blocks single-valued sector identification but does not prevent same-character full Teukolsky source terms from canceling a row.
- Controlled factorized AIME/EKG component is nonzero. Full reduced second-order Einstein–Teukolsky remainder could still supply exact opposite same-pole numerator.
- Remaining precise PDE problem: prove full remainder cannot equal negative controlled row as a function/operator over continuum inputs, or show cancellation necessarily introduces another nontrivial branch/channel.
- Likely useful discriminator: angular-continuum dependence/principal symbol or helicity/Weyl parity, not KMS/passivity/CCR.

Verification:
- Each new module passed targeted lake env lean.
- New theorems use only propext, Classical.choice, Quot.sound.
- Lint shows only unrelated pre-existing unreachable HTGeometry modules HardyOperatorGramRankProfile and SecondOrderConstraintDescent.
- All /tmp scratch and temporary .olean files removed.
- No git used.
