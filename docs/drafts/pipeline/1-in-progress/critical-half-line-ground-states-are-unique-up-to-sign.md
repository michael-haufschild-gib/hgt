# Critical half-line ground states are unique up to sign

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** B104; rigidity of the actual critical state.
- **Statement:** At a finite global window threshold, any two actual normalized critical half-line ground states agree almost everywhere up to sign.
- **Status:** Laplace-zero exclusion and weak equation verified. Uniqueness module written, unchecked.

## Argument

Fix `s>0`. Zero energy and endpoint nonnegativity make the full mixed form
of a critical state vanish against every admissible test. Hence every
linear combination of two critical states has zero full energy.

If F and G are critical states, `L_G(s)≠0`. The combination
`H=F−(L_F(s)/L_G(s))G` remains in the actual energy domain, has zero energy
and has `L_H(s)=0`. The reflection argument forces H to vanish almost
everywhere. Unit norms then force the scalar to be `1` or `−1`.

No positivity of either state, polar-threshold equality, smoothness, or
spectral simplicity assumption enters this argument.

## Lean

Verified input: `criticalHalfLineMixedEnergy_groundState_eq_zero`,
`CriticalHalfLineEnergyDomain.add_const_mul`, and
`criticalHalfLineFullEnergy_add_const_mul`.

Verified input:
`ae_eq_zero_of_criticalHalfLineFullEnergy_eq_zero_of_laplace_zero` in
`TheCriticalHalfLineStateHasNoPositiveLaplaceZero`.

Written, unchecked: `TheCriticalHalfLineStateIsUniqueUpToSign`, including
the exact Laplace-ratio formula and unconditional existence/uniqueness dichotomy.

The arithmetic polar pairing can still vanish on this single line; B104
is not thereby closed.
