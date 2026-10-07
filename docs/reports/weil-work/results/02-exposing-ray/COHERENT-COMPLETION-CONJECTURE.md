# Next primary conjecture: bounded coherent completion of far-polar sources

Status: OPEN source-production conjecture. Do not assume the factorization below; audit corpus and primary sources before Lean work. LATTICE-REPAIR-CONJECTURE.md remains a narrower secondary diagnostic.

## Exact target

There exist constants C,B such that for every X>=4 there is an actual complex C2 polar test h_X at aperture <=X+B for which, for every integer n>=2,

atomCoeff(farPolarTest X,n)+atomCoeff(h_X,n)=0,

and archEnergy(h_X)<=C. Stronger candidate: the sum of the two spectral densities equals that of one fixed compact polar test g supported inside (-log(2)/2,log(2)/2), so their total energy is exactly archEnergy(g), independent of X.

No RH, PBAP, global positivity, or assumed source existence is permitted. This produces a bounded-energy coherent completion; it would NOT prove that its total energy vanishes or is negative.

## Mechanism to audit

Let psi be the corpus Fejer profile and P(z)=z^2+1/4. Put c=1/cosh(X/2), m_X(z)=1-c cos(Xz), and g=8(D^2-1/4)psi. Formally g-hat=-8P psi-hat; g is polar and remains supported below the first integer lag if the actual profile has the required smoothness.

For real t, 0<c<=1 and |m_X(t)|<=2, while 64P(t)^2>=4. Hence

S_X(t)=|psi-hat(t)|^2(64P(t)^2-m_X(t)^2)>=0.

Because m_X vanishes at both z=+i/2 and z=-i/2, T_X=m_X/P extends to an entire function. The proposed residual primitive density is

H_X(z)=psi-hat(z)^2(64-T_X(z)^2).

It is nonnegative on the real axis (psi is real/even), has finite exponential type, and the proposed smooth decay comes from the actual profile. A compact smooth spectral factor q_X with |q_X-hat(t)|^2=H_X(t) would give h_X=(D^2-1/4)q_X, hence a polar compact test and

|farPolarTest(X)-hat(t)|^2+|h_X-hat(t)|^2=|g-hat(t)|^2.

Fourier inversion then cancels EVERY integer coefficient, including all high atoms. Energy additivity gives E(h_X)=E(g)-E(f_X); the existing real multiplier estimate bounds E(f_X) uniformly, so completion cost stays bounded.

[OPEN CORE] Prove the precise compact spectral factorization and regularity for this literal entire function; verify complex reflection convention, real-axis nonnegativity, exponential-type bound after removable division, actual psi smoothness, both polar zeros, and energy integrability. A measurable square root is insufficient. No factorization hypothesis is allowed in the final theorem.

## Why this matters and what it cannot prove

The completed leakage theorem only shows that independent-atom repair has a divergent certified budget. This conjecture tests whether coherent repair removes that divergence. A fixed positive total energy E(g) does not attain the zero-trace endpoint or the exposing-ray threshold. If the completion exists, the next question is whether its fixed total cost can be lowered to zero by a genuinely broader source family; short-window positivity must be checked before proposing such a limit.

## Cycle 9 update: explicit finite mixture

The actual profile is built from Real.smoothTransition, so C2 is not its intrinsic regularity limit. A more direct finite construction now avoids spectral factorization entirely: with Ns=X, the two geometric factors of the far-polar multiplier express f_X as a positive weighted sum of translates of f_s. Choose 1/201<=s<=1/200; those short polar tests are exactly blind at every integer atom. Uniformly bounded total filter weight plus weighted variance gives an explicit finite opposite-trace mixture at the original aperture with uniformly bounded energy. Complete paper proof: COHERENT-COMPLETION-PROOF.md. Finite-mixture version now fully formalized as `RHTower.ExposingRayCompletion.bounded_coherent_completion`; final installed leaf and axiom audits passed. The single-test statement remains stronger and unproved; no silent replacement of that statement or the main WP02 goal is intended.
