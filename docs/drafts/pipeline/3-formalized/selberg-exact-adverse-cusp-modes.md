# Exact adverse integer modes of the critical cusp seam

- **ID:** SELBERG-EXACT-ADVERSE-CUSP-MODES
- **Stage:** 3-formalized
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 15.
- **Scope:** Actual critical Bessel response at integer Fourier frequencies and finite compact mode packets. No infinite Fourier assembly or core response is assumed.

## Exact theorem

For period `w=exp(b)`, height `Y=exp(T)`, and the proved critical Bessel transition `tau`, put

`R=exp(tau)*w/(2*pi*Y)`, `M=ceil(R)-1`.

For each nonzero integer `n`, the actual frequency is `2*pi*|n|/w`. Its outgoing seam coefficient is negative exactly when `0<|n|<R`. The complete adverse set is therefore

`A={-M,...,-1,1,...,M}`, with `card(A)=2*M`.

All other nonzero coefficients are nonnegative. The zero channel is omitted explicitly; it is not a Bessel mode of positive frequency. The adverse set is empty exactly when `R<=1`.

For any finite set of integer modes `S` and arbitrary real traces `c_n`, the complete seam form has the exact decomposition

`sum_(n in S) B_n*c_n^2 = sum_(n in S) max(B_n,0)*c_n^2 - D_S(c)`,

`D_S(c)=sum_(n in S intersection A) (-B_n)*c_n^2 >= 0`.

The cost is strictly positive exactly when a trace is nonzero on an adverse mode of the packet. For arbitrary compact real C¹ profiles in each mode, summing the actual critical energy identities gives

`sum excess = sum square-remainders + positive seam form - D_(S without 0)(trace)`.

Thus the explicit adverse trace cost bounds all possible negative finite-packet excess from below. No claim that every adverse trace gives a negative total energy is made.

## Dependency-closed paper proof

The critical coefficient is `(Q(log(k)+T)-1/2)/exp(T)`, and the already-proved strict sign classification says it is negative exactly when `log(k)+T<tau`. Substitute `k=2*pi*|n|/w` and exponentiate. Positivity of width, height, and nonzero frequency gives `|n|<R`. For natural `|n|`, the ceiling characterization converts this into `|n|<=ceil(R)-1`. Erasing zero from the symmetric integer interval gives its exact cardinality.

Split each coefficient into `max(B_n,0)-max(-B_n,0)`. The negative part is supported exactly on the explicit adverse set, which proves the finite form decomposition. Each retained cost coefficient is strictly positive; a sum of nonnegative weighted squares is positive exactly when at least one associated trace is nonzero. Finally sum the already-proved compact-profile Bessel identity over `S` with zero erased. Each integrand has already been proved integrable, and every square integral is nonnegative.

At fixed `T`, choosing

`b=log(2*pi)+T-tau+log(m+1)`

gives `R=m+1`, hence `M=m` and exactly `2*m` adverse signed modes. Unboundedness persists along positive integer periods: choose a natural `N` larger than `(m+1)*2*pi*exp(T)/exp(tau)`. Then period `N+1` gives `R>m+1`, so its cutoff exceeds `m`.

## Lean implementation and audit

Module: `GaloisForLFunctions.RHTower.SelbergBesselAdverseModes`, namespace `GaloisForLFunctions.RHTower.SelbergBesselModes`.

Capstones: `mode_frequency`, `mem_adverse_iff`, `card_adverse`, `radius_width_height`, `adverse_empty_iff`, `card_adverse_tuned_width`, `integer_width_cutoff_unbounded`, `seam_form_decomposition`, `debtForm_pos_iff`, `finite_packet_energy_identity`, and `finite_packet_debt_bound`.

Complete scratch and final direct checks passed without warnings. The targeted final build passed, rebuilding only this module (`/tmp/selberg_bessel_modes_build.log`). Eleven capstone axiom checks in `/tmp/selberg_bessel_modes_axioms.lean` report only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into the RHTower umbrella. Final index refresh, repository-wide formal lint, and whitespace checks passed, with existing large-file lint warnings. No Lean or Lake process remained. Detailed logs are recorded on the parent card.

## Consequence for the Selberg route

The seam obstruction has an explicit finite support at every fixed width and height, but its size is not bounded uniformly in integer period at fixed height. A successful core argument must use the width/height scaling or control growing blocks. Finiteness alone proves no core Schur positivity. Infinite Fourier/Parseval passage, energy closure, and the actual congruence core estimate remain absent.
