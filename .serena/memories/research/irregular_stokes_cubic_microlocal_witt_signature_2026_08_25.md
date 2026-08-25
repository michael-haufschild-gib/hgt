# Cubic wall–Xi microlocal Witt, slope, cancellation, and corrected Rees status (2026-08-25)

Module: `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicMicrolocalWittSignatureRigidity.lean`.

Every landing under nonnegative Rees parameters has nonzero charge/common physical rank, negative `globalRankCoefficient`, strict rank-debt domination, exact `sigNeg = 1`, radical finrank zero, and `fusionCoefficient < Σ(root - 1)`. On genus-zero one-puncture data, landing forces normalized Puiseux root `(K+1)/N > 1`; slope-at-most-one fiber is empty.

At one fixed scale, raw Euler/global Lorentz specialization gives
`globalReesPositiveForm = S + cubicResidual`,
hence `(1999/2000)S < globalReesPositiveForm < S`.

Conditional two-scale theorem in this module: landing at Rees parameters zero and one annihilates all threshold cut charges and extends landing to every parameter. Raw-Euler terminal-energy bounds were derived conditionally on that subtype.

CORRECTION/FOLLOW-UP: `mem:research/irregular_stokes_cubic_diagonal_rees_transversality_2026_08_25` proves the two-scale subtype empty. Pendant singleton cuts make threshold coarea faithful, so annihilating every cut charge annihilates full orbit charge, contradicting negative Xi landing. Therefore conditional terminal-energy branch is logically valid but vacuous. Strong positive survivor is strict Rees transversality: every contracted landing has positive unit drift equal to total block coarea.

Original module targeted check and all thirty-one declaration axiom audits passed with only `propext`, `Classical.choice`, `Quot.sound`. Card corrected to record vacuity. Frontier map untouched.