# Mass-shifted external-clock gauge and exact zero-frontier phase (2026-08-12)

## Arithmetic producer
Exact admission-sensitive, source-first bilinear arithmetic landing is in `formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryAdaptiveArithmeticSourceLaw.lean`.
`xiShiftedAdaptiveMixedCompletedArithmeticSource` is archimedean + continuum Gamma formation minus labelwise von Mangoldt formation using the same amplitude-selected mixed kernel.
Capstones land admitted null-gauge and lower-memory-corrected source series into this arithmetic source, and `two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource` identifies actual bilinear shear. It is formed before reflection aggregation and contains no fixed reporter/orientation map.

## External schedule gauge no-go
Module `XiShiftedCanonicalAdmissionCofinalScheduleNoGo.lean` proves:
- fixed-degree positive limits do not control a degree diagonal;
- unconditional actual shifted-Xi positive schedules exist above arbitrary lower mass floors;
- projective spread diverges and harmonic source work holds along such a schedule;
- even arbitrary externally prescribed spread floors can be beaten after cofinal reindexing.
Higher principle: external observation index has a cofinal reparametrization gauge. Lower mass growth, external spread growth, cofinal positivity, and harmonic work are RH-blind. Only an intrinsic upper mass–degree–source-price relation survives.

## Exact RH phase classification
Module `XiShiftedTerminalFrontierZeroPhaseLaw.lean` proves occupied shifted reciprocal-square support remains infinite; under RH every nonzero finite Hankel vector has strictly positive energy at every nonnegative shift; hence all shifted blocks are PosDef and all terminal failure frontiers vanish. Existing false-RH renewal supplies positive frontiers. Capstone:
`RHTower.riemannHypothesis_iff_forall_xiShiftedHigherBlockTerminalFrontier_eq_zero`.

This is not an RH proof. Remaining exact open core: derive terminal frontier zero from the arithmetic producer, equivalently exclude false-RH cofinal positive-frontier phase through intrinsic mass–degree–source-price/admission effectivity. External rate or fixed reporting cannot do it.

## Verification
Direct `lake env lean` passed warning-free for new modules. Targeted module builds passed. `#print axioms` for capstones reports only `propext`, `Classical.choice`, `Quot.sound`. Modules wired into `RHTower.lean`.