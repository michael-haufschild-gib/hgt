# Arithmetic Resonance Theory (ART): programme development

- **ID:** art-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — programme of theorems
- **Source:** docs/reports/review-3010/fable.md §7 (the field that would supply the missing tools)
- **Statement:** Develop the field "RH is about resonances; every positive object sees spectra": realizations of the
  primes as dynamical zetas, oscillation (resonance gaps), non-envelope amplifiers, the resonance–spectrum dictionary.

## Goal
Lean programme `formal/GaloisForLFunctions/ArithmeticResonanceTheory/` with umbrella and README; answer the field's
questions by theorems (classifications, sharp boundaries, no-gos with positive survivors).

## Work plan (modules)
1. TheTwoRealizationsOfThePrimes — commutative realization (Euler product, diagonal transfer, pole = nuclearity
   breakdown, spectral radius ≤ 2^{-σ}); free realization (renewal zeta 1/(1−P), entropy σ* ∈ (1,2), spectral pole).
2. PrimesObeyNoAffineRecurrence — Cunningham lemma: primes with p_{n+1} = a p_n + m eventually is impossible;
   eventually periodic defect impossible.
3. IntegralityForbidsSuperConformalDistortion — Pisot obstruction: p_n = C a^n e^{ε_n}, a^n ε_n convergent ⇒ ⊥.
4. TheHolderModulusOfARealizationOfThePrimes — symbolic: θ-Hölder potential, fixed point a, word a^n b;
   realization ⇒ θ·e^{φ(a^∞)} ≥ 1.
5. AdditiveRealizationsAreCommutative — weighted digraph, first-return loops: two distinct ⇒ ⊥.
6. EvenRealizationsHaveNoZeros — finite graph locally constant roof: zeta = 1/det, zero-free; curves g ≥ 1 need odd part.
7. AHolderRealizationIsAZeroFreeStrip — Pollicott corollary.
8. OscillationFailsOnAdditiveRealizations — Dirichlet simultaneous approximation: twisted sums return to the
   untwisted value at arbitrarily large t; Dolgopyat modulus = 1 at the abscissa; free prime realization.
9. TheAmplifierTheorem — rate = depth for finite exponential sums; positivity + fixed loss ⇒ sharp; graded loss ⇒ strip.
10. OrthogonalityAmplifiersAreTrivial — Brauer at level k on r primes ⇒ |X| ≥ C(r+k−1,k) ⇒ amplified bound ≥ trivial;
    finite rank (F_q) ⇒ loss → 0.

## Status (modules compiled with `lake --old env lean`)
Done: PrimesObeyNoAffineRecurrence, IntegralityForbidsSuperConformalDistortion,
TheHolderModulusOfAPrimeLengthSystem, TheTwoRealizationsOfThePrimes,
OscillationFailsOnAdditiveRealizations, TheAmplifierLaw, OrthogonalityAmplifiersAreTrivial,
EvenRealizationsHaveNoZeros, AHolderRealizationIsAZeroFreeStrip, AdditiveRealizationsAreCommutative,
TheArchimedeanPlaceForbidsFiniteVirtualRealizations, OverFiniteFieldsTheOddPartIsSpectral,
GeneralizedDirichletSeriesAreDeterminedByTheirValues, ARealizationOfZetaIsPrimeLength,
TheHolderModulusAlongEveryCycle (all in umbrella).
README rewritten with Lean names and the answers to the five questions.
Open topics (README §9): Mills boundary, sub-conformal realizations, countable alphabets,
infinite-rank odd parts, identity amplifiers, CGL loss audit.

## Log
- 2026-10-30 — created; README first draft.
