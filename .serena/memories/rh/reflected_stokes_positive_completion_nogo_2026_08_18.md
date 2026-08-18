# Reflected Stokes positive completion no-go (2026-08-18)

The prior claim that reflected/Hermitian Stokes carrier was the only surviving C1 architecture was stale. Lean corpus already contained:
- `GammaSewnMobiusApertureStokesCriticalMassNoGo.not_gammaSewnMobiusApertureStokesCriticalMomentIdentification`: raw critical squared carrier cannot equal completed seam germ; four atoms exceed completed zeroth moment.
- first prime-two atom also exceeds completed first moment.
- any scalar repair requires negative zeroth and first corrections.

New module:
`formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPositiveCompletionNoGo.lean`

New formal classification:
- `not_completedSeamMomentGerm_eq_compactMarkov_of_criticalStokes_le`: any finite positive measure dominating raw critical Stokes carrier cannot represent completed germ.
- `criticalStokes_not_le_of_completedSeamMomentGerm_eq_compactMarkov`: exact representing carrier must fail domination, so must omit/reweight raw mass.
- closed `not_gammaSewnMobiusApertureStokesCriticalPositiveSupercarrierCompletion`: no finite positive Hermitian supercarrier completion exists.

Proof: raw mass > completed m0; domination increases mass; germ equality at zero forces total mass=m0, contradiction.

Targeted source check/build pass. Axiom audit: only propext, Classical.choice, Quot.sound. Wired into RHTower umbrella. Global lint still fails only on unrelated unreachable modules, no proof-debt error. No stale owned Lean processes.

Conclusion: reflected/Hermitian Stokes carrier is dead as canonical positive/passive C1 extension. Any repair must use deletion/reweighting or signed negative correction and therefore is a different architecture.
