# Delayed Hawking–Teukolsky pump–probe producer (2026-08-25)

## New mechanism

Use independent pump amplitude ε and delayed probe amplitude λ. Pump absorption leaves stationary mass completion δM ∂_M g. After factoring probe time translation, ε²λ AIME term is delay-independent. Local radiative overlap terms decay as pump–probe delay T→∞ once stationary completion is split off. Therefore full co-moving source/residue equals nonzero AIME term plus r(T), with r(T)→0. Exact same-pole cancellation cannot persist at all large T.

This is source-specific horizon memory/redshift, not generic KMS/passivity/CCR.

## Formalization

Added:
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyDelayedPumpProbe.lean`
- import in `formal/GaloisForLFunctions/RHTower.lean`

Main theorems:
- `eventually_const_add_ne_zero_of_tendsto_zero`
- `eventually_d4DelayedPumpProbeCrossBranchPole_order_qnmMinus_xi`: for nonzero pump and decaying projected radiative remainder, delayed full response eventually retains exact simple pole at negative BM QNM.
- `exists_eventually_d4DelayedPumpProbeMediatorDeterminant_ne_zero_of_tilt`: every tilted Xi divisor has common bright angular input such that any decaying correction leaves full delayed two-channel determinant eventually nonzero.

Targeted module build passed. New theorem axioms only `[propext, Classical.choice, Quot.sound]`. Lint shows unrelated unreachable umbrella modules only; new module reachable.

## Exact remaining PDE estimate

Prove, on massless d=4 topological AdS black hole, after decomposition into stationary mass completion plus radiative part, the co-moving projected ε²λ reduced Einstein–Teukolsky remainder tends to zero as pump–probe delay→∞. Expected inputs: locality of δ²G, BM QNM/redshift gap, no-hair/completion classification, integrable continuum bound. Must control direct and continuum pieces uniformly.

## Hostile audit

- Completion-mode orthogonality alone fails: nonlinear radiative harmonics can return to same output.
- Scalar mass parameter does not force mediator rank one.
- APS eta is coarse; reflected pair cancels globally.
- Real-QNM conjugation already exists and does not identify virtual multi-sector mediator clocks.
- Rees superselection forbids exact profile sewing, not arbitrary nonzero mixing; no bridge from Teukolsky mixing alone.
