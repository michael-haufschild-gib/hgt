# Kapustin--horizontal--Hedenmalm--bosonic universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL CROSS-CHART EQUIVALENCE; LITERATURE AUDITED]`

## Lean-derived law

Three closures are formalized.

1. Analytic order one at every zero of uncentered `xi` is exactly `XiZerosSimple` in centered
   Hedenmalm coordinates.
2. Every exact-height Xi-zero fiber having total multiplicity one is unconditionally equivalent
   to the complete Hedenmalm RH-and-simplicity certificate.
3. If one symmetric Hilbert-space operator carries every Kapustin Xi-divisor spectral value,
   that hypothesis already supplies RH. In this setting horizontal mass one is equivalent to the
   Hedenmalm simplicity certificate alone, and also to the enlarged package consisting of:

   - the full RH-and-simplicity Hedenmalm certificate;
   - a unit local Xi factor at every zero;
   - unit small-circle winding at every zero;
   - every normalized bosonic jet residue for that unit factor.

Lean declarations:

- `RHTower.xiOrderOne_iff_xiZerosSimple`
- `RHTower.XiUnitHorizontalWindingBosonicFingerprint`
- `RHTower.xiHorizontalFibersMultiplicityOne_iff_hendenmalmRHSimplicityUniversalCertificate`
- `RHTower.kapustin_symmetricPointSpectrum_horizontalMultiplicityOne_iff_hendenmalmSimplicity`
- `RHTower.kapustin_horizontalHedenmalmBosonicUniversality`

## Corpus inputs

- `RHTower.riemannHypothesis_of_kapustin_symmetric_pointSpectrum`
- `RHTower.kapustin_symmetricPointSpectrum_horizontalWindingBosonicFingerprint`
- `RHTower.xiHorizontalFibersMultiplicityOne_iff_rh_and_orderOne`
- `RHTower.riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate`
- `RHTower.xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate`
- `RHTower.deriv_XiC_eq_deriv_xi_mul_I`
- Mathlib analytic-order derivative laws

## New mathematical connector

The terminal Kapustin and horizontal-multiplicity modules shared the horizontal divisor census,
while the Hedenmalm terminal module used centered derivative simplicity. The corpus lacked the
coordinate-exact equivalence between global uncentered analytic order one and centered derivative
simplicity. Proving that equivalence closes the three classifications.

The symmetric Kapustin point-spectrum assumption then discharges the RH component globally.
Consequently one simplicity bit controls the horizontal census, eight Hedenmalm simplicity
charts, the enlarged RH certificate, local factor order, winding, and all normalized bosonic
residues.

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof searches covered Kapustin's Hilbert-space models and zeta-zero point spectra,
Hilbert--Pólya spectral interpretations, Hedenmalm's theta/differential spectral problem,
de Branges/Weil Hilbert spaces, zero multiplicity, and the argument principle.

Nearest sources:

- Kapustin, *Five Hilbert space models related to the Riemann zeta function*, Zap. Nauchn. Sem.
  POMI 503 (2021), studies Hilbert-space models tied to zeta:
  <https://www.mathnet.ru/eng/znsl7101>
- Kapustin, *The set of zeros of the Riemann zeta function as the point spectrum of an operator*,
  St. Petersburg Math. J. 33 (2022), constructs operator point spectra from zeta zeros:
  <https://www.mathnet.ru/php/archive.phtml?jrnid=aa&option_lang=eng&paperid=1771&wshow=paper>
- Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  arXiv:math/0412277, realizes nontrivial zeros spectrally on a nuclear Fréchet space:
  <https://arxiv.org/abs/math/0412277>
- Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494, constructs a
  theta-based differential eigenvalue problem and studies self-adjointness; its
  one-dimensional eigenspaces are noted only as weak support for simple real Xi zeros:
  <https://arxiv.org/abs/2606.17494>
- Suzuki, *On the Hilbert space derived from the Weil distribution*, Canadian Journal of
  Mathematics, develops a de Branges/Weil Hilbert--Pólya space under RH:
  <https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/on-the-hilbert-space-derived-from-the-weil-distribution/FD33EBD117A6B448053450DD8D62ADB6>

No source found states the exact equivalence joining Kapustin symmetric point spectrum,
exact-height divisor mass one, the complete Hedenmalm RH/simplicity certificate, unit local
factorization, unit winding, and all normalized bosonic jet residues. Novelty claim is restricted
to this joint cross-chart law.

## Lean target

`formal/GaloisForLFunctions/RHTower/KapustinHorizontalHedenmalmBosonicUniversalityLaw.lean`

## Verification

- source proof exact and warning-free:
  `lake env lean GaloisForLFunctions/RHTower/KapustinHorizontalHedenmalmBosonicUniversalityLaw.lean`
- imported by `formal/GaloisForLFunctions/RHTower.lean`
- final module and umbrella builds deferred to terminal audit
