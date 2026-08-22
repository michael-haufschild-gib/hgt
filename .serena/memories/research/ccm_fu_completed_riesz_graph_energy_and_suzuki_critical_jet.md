# CCM-FU completed Riesz graph energy and Suzuki critical jet (2026-08-22)

New module: `formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCompletedRieszGraphEnergy.lean`.
Umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`. Route map was not edited.

Closed unconditional Lean results:
- exact completed-prefix successor/mesh flux for `mobiusDivisorSquareRootAbelMoment`
- square-summability of singular graph increments, using `summable_psi_error_weight`
- exact absolutely summable completed harmonic charge with total zero (Mertens tail -2γ cancels Gamma +2γ)
- harmonic-to-square-root clock transmutation and signed Abel prefix/clock-acceleration law
- fixed-aperture right-critical Suzuki coupled-error jet lands on literal completed Riesz moment and normalized unit-aperture window
- exists positive schedule omega_N -> 0 tracking actual completed Riesz moments with vanishing error, and same for unit-aperture windows.

Scientific frontier:
- convergence/identification, including source-selected cofinal diagonal convergence, is unconditional and does not imply RH.
- hard datum is uniform bound for normalized finite Suzuki critical jets along a coefficient-faithful critical/cofinal schedule, preserving shifted-Euler atomic/main cancellation through omega -> 0+. Since tracking error is o(1), this is RH-equivalent.
- harmonic total charge and ℓ² graph energy lack needed rate against clock ratio ~ k^(3/2).
- no corpus theorem gives a bound for suzukiCoupledError uniform as omega downarrow 0; fixed-omega positivity loses critical cancellation.
Novelty remains [NOVELTY UNVERIFIED].

Verification:
- `lake env lean GaloisForLFunctions/RHTower/CCMFUSuzukiCompletedRieszGraphEnergy.lean` passed.
- targeted `lake build GaloisForLFunctions.RHTower.CCMFUSuzukiCompletedRieszGraphEnergy` passed.
- #print axioms on major theorems: only propext, Classical.choice, Quot.sound.
- global formal lint was run but fails on unrelated concurrent un-wired modules; forbidden declaration scan on new module is clean.
- do not kill concurrent builds owned by other agents.
Card: `docs/drafts/pipeline/1-in-progress/ccm-fu-completed-riesz-graph-energy.md`.