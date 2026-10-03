# Route PM: actual normalized bands cannot converge to a fixed Mellin profile

- **ID:** pm-ramanujan-band-no-fixed-profile
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, fully audited)
- **Continuation:** `../1-in-progress/pm-ramanujan-band-spectral-escape.md`.

## Exact statements

For every epsilon>0 and every fixed critical-frequency L2 vector F, the actual normalized complete-band vectors F_X do not converge to F as real X tends to infinity. In fact, for each epsilon>0 there is one c>0 such that for every F and every real cutoff B there is X>=B with ||F_X-F||>=c.

The separation constant is independent of F. Transfer to the original physical Hilbert carrier and integer/dyadic cutoff variants are not claimed here. The frequency-space fixed-profile candidate is falsified, with a uniform positive separation theorem as its survivor. The original physical-carrier transfer is under verification.

## Dependency-closed paper proof

Assume F_X tends strongly to F. Hardy's unconditional dyadic critical-zero theorem supplies rho with Re(rho)=1/2, Im(rho)>0 and zeta(rho)=0. The actual complete-residue test supplies [a,b] strictly above Im(rho), an L2 test h supported there, a positive frequency gap, and a strictly positive real pairing with the complete residue numerator A_rho.

The audited continuation theorem identifies zeta(rho+delta) times the actual tested scale transform Q(delta) with the compactly tested complete arithmetic kernel for every delta>0. That kernel is holomorphic on a neighborhood of rho; hence its tested value tends to the positive residue pairing as delta decreases to0.

The audited actual Abel theorem gives delta*Q(delta)->0. Ordinary differentiability of zeta at rho gives zeta(rho+delta)/delta -> zeta'(rho), by restricting the complex derivative to a real increment and using the right-hand slope limit. No assumption about zeta'(rho) being nonzero is needed. Multiplying these two limits shows zeta(rho+delta)*Q(delta)->0. Uniqueness of limits forces the strictly positive real residue pairing to vanish, a contradiction.

Completeness of the actual L2 space strengthens nonconvergence to a uniform separation radius. Otherwise, arbitrarily small balls around possibly different centers would contain whole tails. Taking radius eta/2 and using the triangle inequality would make F_X Cauchy. Completeness would then give a fixed strong limit, contradicting the scalar argument. Equivalently, failure of the metric Cauchy criterion gives a positive tail-diameter lower bound eta; each tail has two vectors separated by eta, and at least one lies eta/2 away from any prescribed F. All arithmetic terms were retained in the continued identity and in its positive residue test; divergence of a selected sector is not used.

## Scope and verification

This rejects the proposed fixed normalized-profile limit. It does not reject a bounded oscillating family or the weaker energy control sufficient for RH. The complete small-positive-damping signed-energy ceiling remains open; RH is neither proved nor falsified here.

All four exports in `PMRamanujanBandSpectralEscape.lean` passed targeted old-mode leaf build (144 seconds), mandatory final actual-file `lake env lean` with no diagnostics, and individual axiom queries showing only propext, Classical.choice and Quot.sound. Umbrella wired once. Global lint has thirteen unrelated unreachable modules, no own finding. The stronger common-radius theorem is proved; no arithmetic, convergence, zero-simplicity or RH premise is left in its statement beyond positive damping and the universally quantified physical parameters.
