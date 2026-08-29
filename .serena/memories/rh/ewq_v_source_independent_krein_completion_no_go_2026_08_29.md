# EWQ-V source-independent diagonal Krein completion no-go (2026-08-29)

Route EWQ-V is retired within its declared unequal/mixed/indefinite diagonal completed-matrix/jet chamber.

Formal module: `GaloisForLFunctions.RHTower.EulerSquarefreeWickSourceIndependentKreinCompletionNoGo`.

Core result: for arbitrary finite auxiliary type, arbitrary other matrix entries and diagonal masses, and any fixed real diagonal metric with one nonzero paired weight, coefficient-faithful entries `(deltaS p rho, (deltaS p rho)⁻¹)` plus weighted self-adjointness on every Xi fibre imply RH. Pointwise, one completion forces `‖w_reverse‖ = ‖w_forward‖ * ‖deltaS p rho‖²`; Xi line reflection reciprocates the character norm, so the same fixed metric cannot complete both members of an off-line orbit.

Key theorems:
- `ewqKrein_reverseWeightNorm_eq_forwardWeightNorm_mul_characterNormSq`
- `norm_ewqKreinXiPrimeCharacter_eq_one_of_reflectionPair_kreinCompletions`
- `riemannHypothesis_of_everyXiEWQSourceIndependentDiagonalKreinCompletion`
- `not_reflectionPair_ewqSourceIndependentDiagonalKreinCompletions_of_re_ne_half`

Positive survivor: the unique single-fibre metric magnitude repair is modular counterweight `‖chi‖²`; a divisor-dependent metric is an RH receiver because it imports horizontal Xi coordinate, not an independent vacuum.

Verification: direct `lake env lean` PASS; targeted `lake build` PASS in 6.3s after reducing imports to `PrimeTranslationKoszulOffLine` and `XiCriticalLineIntegrality`; axioms only `propext`, `Classical.choice`, `Quot.sound`. Full formal lint still fails only on unrelated pre-existing umbrella reachability omissions. Module wired into `RHTower.lean`. Cards: `docs/drafts/pipeline/3-formalized/ewq-v-source-independent-krein-completion-no-go.md` and `docs/drafts/pipeline/5-failed/ewq-v-source-independent-krein-completion.md`.