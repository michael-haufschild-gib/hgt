# Nonreciprocal Wilson source firewall and EWQ orientation lift

- **ID:** NW-EWQ
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** arXiv:2607.18215 · whole-corpus route audit
- **Statement:** Passive reverse-adjoint link systems have zero real directional Wilson contrast, while an active Pauli link word gives a coefficient-faithful linear orientation lift whose square is the EWQ--Hedenmalm reflected crossing.

## Goal

Determine whether directional non-Hermitian Wilson transport supplies the missing source-native
orientation law for any live RH route.  Separate an unconditional active-link source theorem from a
receiver that merely reports the centered Xi grade after divisor selection.

## Gates

- [x] 0 → 1  in-progress: paper mechanism is well-posed; passive-source obstruction and active Pauli attack are explicit
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: direct Lean checks green; new-declaration axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

1. Prove reverse-adjoint Wilson reciprocity: reverse trace is the conjugate of forward trace, so
   real and absolute directional contrasts vanish for every passive Hermitian/Gram carrier.
2. Build the minimal active non-Hermitian Pauli word modeled on the paper's ordered plaquette and
   prove its signed contrast is linear in the source amplitude while magnitude contrast is blind.
3. Weld that contrast to the exact EWQ--Hedenmalm crossing and test whether the completed EWQ jet
   supplies a pre-divisor, independent source law or only a nowhere-zero auxiliary carrier.
4. Audit implications for every route family using the source/receiver firewall.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** `normalizedBlockKernel_reverseDirectionalWilson_re_eq`
  and `normalizedBlockKernel_reverseDirectionalWilson_norm_eq` force both paper observables to be
  orientation-blind for every passive PSD block source.  In the active Pauli transplant,
  `ewqDirectionalWilsonMagnitudeContrast_eq_zero` kills the magnitude protocol, while global
  signed-contrast annihilation is equivalent to RH rather than unconditional.
- **Strongest positive survivor:** The active signed contrast is exactly `4z`; the EWQ reflected
  crossing is `-(log p / 4)` times its square; the full pre-divisor completed EWQ jet family erases
  no nonzero contrast.  Noncommuting Wilson loops coexist with passive directional reciprocity.
- **New insight:** Non-Abelianity, nonreciprocity, and source production are three independent
  layers.  Existing Hilbert/Gram route landings cannot manufacture the paper's active orientation;
  a surviving Frankenstein route needs an arithmetic law that breaks reverse-adjoint reciprocity.
- **Status:** `[PROVED HERE]`; formalized in
  `HTGeometry/DirectionalWilsonReciprocity.lean` and
  `RHTower/EulerSquarefreeWickNonreciprocalWilsonOrientation.lean`; direct checks green; axiom set
  only `propext`, `Classical.choice`, `Quot.sound`.

## Log

- 2026-08-22 — created directly in 1-in-progress after paper extraction and whole-corpus novelty search
- 2026-08-22 — producer conjecture falsified; positive survivor paper-proved and formalized
