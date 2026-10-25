# Product-horizon centered Vaughan Gram at the trivial exponent

- **ID:** vaughan-product-horizon-centred-gram-has-zero-trivial-density
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** For `0<ε<1/2`, after subtracting the cutoff-dependent linear means, every Vaughan Gram entry at `T=UV` is `o(T^(1-2ε))` whenever both cutoffs diverge, with arbitrary aspect ratio.
- **Novelty status:** New proposed Vaughan specialization of existing mean-zero and floor-atom estimates; no external novelty claim.

## Dependency-closed proof

Let `e_i(n;U,V)=p_i(n;U,V)-c_i(U,V)n`, `q=1/2-ε>0`, and `T=UV`.
Assume both cutoff schedules tend to infinity; no bound on their aspect ratio is needed.
The two small legs are finite sums of centered floor errors. The existing atom estimate
`‖floor(n/d)-n/d‖_T≤sqrt(2)d^(-1/2)` therefore gives
`‖e_0‖_T≤sqrt(2)W_ε(U)=O(U^q)` and `‖e_1‖_T≤sqrt(2)W_ε(V)=O(V^q)`.
Dividing by `T^q=U^q V^q` gives bounds tending to zero, respectively as `V^(-q)`
and `U^(-q)`. The atom theorem is `pronicNorm_sawtooth_le`; the absolute mass estimate
is `pmVaughanAtomicAbsoluteMass_le`.
The pole-centered component has bounded norm.

The both-large piece vanishes exactly throughout this horizon. Its centered version is
`e_3(n;U,V)=-c_3(U,V)n`, where the proved mean factorization gives
`c_3(U,V)=Z(A_U-ρ)(A_V-ρ)`. The linear sequence has norm at most `sqrt(T)`:
each summand `n²/(n(n+1))≤1`. Therefore

`‖e_3‖_T/T^q≤Z |U^ε(A_U-ρ)| |V^ε(A_V-ρ)|→0`.

The signed reciprocal-tail input is now checked. Given `η>0`, mean-zero Möbius
(`hasMeanValue_moebiusReal`) supplies `|M(x)|≤Lx` for all sufficiently large `x`, with
`L=η/(2+1/ε)`. The proved Abel-tail estimate
`abs_tsum_tail_rpow_le_of_linear` gives

`|Σ_(d>N) μ(d)d^(-1-ε)|≤(2+1/ε)L N^(-ε)=η N^(-ε)`.

The absolute reciprocal sum equals `ρ`, so its signed tail is `ρ-A_N`. This proves
`N^ε(A_N-ρ)→0` for every `ε>0`, with no rate inferred from little-o. Both cited inputs
have been checked in Lean source. The older absolute half-exponent tail estimate would
not suffice for this step.

The exact sum of the centered components is the interior prefix. Its norm is
`o(T^q)` by the existing actual-source energy theorem. Subtracting the other four
pieces proves the same for `e_2`. Cauchy–Schwarz gives the centered Gram claim.
The product horizon tends to infinity because both cutoffs do. This closes every
dependency of the paper proof.

Equivalently, every component norm divided by `T^q` tends to zero, the entire centered
diagonal divided by `T^(1-2ε)` tends to zero, and every fixed coefficient packet formed
from these centered pieces has the same zero density. The square-root case `U=V=N`
is an immediate specialization.

## Meaning and limits

At fixed positive cutoffs the centered Gram instead has a nonzero rank-one density
at this exponent, from the finite harmonic pole factors. The two limiting regimes
therefore differ even after subtracting their explicit linear means. The candidate
product-horizon law is a selective little-o estimate using actual Möbius cancellation;
it contains no fixed power saving and does not close Q-I.

## Gates and checks

- [x] Exact square-root vanishing, uniform mean factorization, and absolute `W_ε` bound are proved.
- [x] Existing corpus supplies the centered floor atom norm and interior little-o energy.
- [x] Check the scaled reciprocal-tail input and its proof dependencies in source.
- [x] Close the paper proof. Existing horizon-row results provide related tail bounds;
  no new general Abel theorem or analytic source estimate is claimed.
- [x] Check the exact centered matrix law and its square-cutoff corollaries in Lean.
- [x] Complete the repository final direct audits.

The signed-tail input and its actual Möbius specialization passed eight scratch axiom
audits. Their repository module is `SignedVaughanTailsVanishAtTheirAbsoluteScale.lean`.
The uniform small-leg atom estimate is checked in the fixed-packet module. The stronger
uniform product-horizon theorem and its two-divergent-cutoff corollary passed all fifteen
scratch axiom audits in `ProductHorizonVaughanGramsHaveZeroTrivialDensity.lean`.
Both producing and final direct `lake --old env lean` checks passed. The stronger result
is tracked in `uniform-product-horizon-vaughan-second-scale.md`.

## Log

- 2026-10-25 — Extracted a possible second-scale distinction from the fixed and moving Gram laws.
