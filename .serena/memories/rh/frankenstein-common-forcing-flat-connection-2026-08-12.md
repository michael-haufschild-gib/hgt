# Frankenstein common-forcing flat connection (2026-08-12)

Exact module: `formal/GaloisForLFunctions/RHTower/FrankensteinThetaPrimeTranslationCommonForcing.lean`.

Proved unconditionally:
- `thetaPrimeTranslatedSourceResidual_eq_integerAnomaly`: for every theta-source zero z, `(B + z⁻¹) T_n f_z = r_n`, coefficient exactly 1 from canonical mass.
- `thetaIntegerCovariantSourceInverse_integerShift`: rank-one connection `K_n` satisfies `K_n(T_n f)=T_n(Bf)` for every integrable f and n>0.
- `thetaIntegerCovariantSourceInverse_flat`: multiplicative flatness under mn.
- `thetaIntegerCovariantSourceInverse_thetaXi_both_eigen`: q and lineConj(q) are eigenmodes of same literal covariant operator, labels/multiplicity preserved.
- `thetaXiPrimeTranslatedSourceMode_eq_lineConj_iff`: response equality iff horizontal spectral coordinate vanishes.
- `riemannHypothesis_of_thetaXiPrimeTranslatedSourceMode_eq_lineConj`: all-q equality at any one positive integer label implies RH.
- prime residual is nonzero, yet every Xi conormal character annihilates it.

Verification:
- `lake env lean GaloisForLFunctions/RHTower/FrankensteinThetaPrimeTranslationCommonForcing.lean` passed.
- exact leaf `lake build GaloisForLFunctions.RHTower.FrankensteinThetaPrimeTranslationCommonForcing` passed.
- axiom audit only propext/Classical.choice/Quot.sound.
- forbidden scan empty; no stale Lean/lake process.
- module wired into RHTower umbrella; no umbrella build.

Heavy-loop failures after survivor:
- common forcing permits distinct resolvent parameters.
- flat covariance permits conjugate eigenvalues.
- sesquilinear Weil pairing is automatically compatible with conjugation.
- theta Green commutator records horizontal flux rather than kills it.
- every Xi conormal kills the nonzero common residual.
- centered positive prime channel / Hardy contractivity supplies only receiver/RH-equivalent saturation.

Precise remaining producer: independent arithmetic fixed-frame law forcing q/ref translated response equality (equivalently reflection-invariant covariant defect) at one positive integer label. Must act before quotient/conormal evaluation.

Research card and frontier map were appended with C9/C10 and seam status. Global `scripts/formal_tools.py lint` found no forbidden declarations but exits on many pre-existing umbrella-unreachable Route-T/Suzuki/etc modules; exact leaf is clean.