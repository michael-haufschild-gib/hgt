# The critical trace and logarithmic translation boundary

- **ID:** xi-theta-critical-log-translation-seam
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), [PROVED]
- **Date:** 2026-07-10
- **Modules:** GaloisForLFunctions.RHTower.XiThetaCriticalTrace,
  GaloisForLFunctions.RHTower.XiThetaLogTranslationSeam
- **Paper proof:** ../../2-fully-proven/new/xi-theta-critical-log-translation-seam.md

## Formal surface: critical trace

- criticalMellinPullback_eq: the critical Mellin pullback is xiThetaLogSource.
- completedRiemannZeta₀_critical_eq_fourier_xiThetaLogSource: exact critical Fourier trace.
- integrable_logMellinPullback_of_mellinConvergent: Mellin convergence discharges logarithmic
  pullback integrability.
- xiThetaLogSource_integrable, xiThetaPositiveSource_integrable,
  xiThetaReflectedSource_integrable: concrete source hypotheses.
- fourier_xiThetaReflectedSource: reflection becomes frequency negation.
- fourier_xiThetaLogSource_split: exact positive/reflected Fourier split.
- conj_fourier_xiThetaPositiveSource: the real positive source has conjugate-symmetric Fourier
  trace.
- completedRiemannZeta₀_critical_eq_re_positiveFourier: the completed critical trace is the positive
  cosine trace.

## Formal surface: logarithmic translation seam

- thetaLogMother: common heat profile in log coordinates.
- thetaSquareLogAtom: square-rate logarithmic atom.
- thetaSquareLogAtom_eq_shifted_mother: exact weight m^(-1/2), shift 2 log m.
- positiveLogTruncation: the strict positive-half interface.
- forwardTranslationBoundary: the interval swept across zero.
- positiveLogTruncation_translate_add_boundary: exact truncation/translation commutator.
- squareTranslationBoundary_length: boundary length 2 log m.
- positiveThetaSquareLogAtom_translation_seam: combined square-atom boundary charge.
- forwardTranslationWindow: the boundary in translated mother coordinates.
- forwardTranslationBoundary_eq_window_translate: exact finite-window representation.
- fourier_forwardTranslationBoundary: phase times the finite-window Fourier transform.

## Certificate

- Both source files pass targeted Lean checks.
- Targeted CriticalTrace build passed through job 8601 of 8601; the final TranslationSeam build
  passed through job 8600 of 8600.
- Full and umbrella builds were deliberately not run.
- Active sorry, admit, axiom, opaque, unsafe: none.
- Axiom audit: propext, Classical.choice, Quot.sound only.
- Generated API refreshed; formal lint passed.

## Scope

The formal result adjudicates the transform and isolates the moving boundary charge. Stable
finite-sample and L1 readers are subsequently ruled out in XiThetaReaderConditioning. It does not
yet supply the stronger intrinsic topology, a Perron contradiction, or RH.
