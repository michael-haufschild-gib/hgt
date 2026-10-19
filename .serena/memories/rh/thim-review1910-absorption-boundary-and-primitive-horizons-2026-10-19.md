# THIM review §5: verified absorption obstruction and primitive horizon bounds

Two new leaves in `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/`:
- `OddPolarAbsorptionBoundaryAndCompensatedHorizon.lean`
- `CanonicalOddPrimitiveHorizonBounds.lean`

For `0<a≤log(2)/2`, the literal odd-polar cosh/sinh ratio is at least `π exp(2x−5log(2)/4)` for `x≥log 2`. Every legitimate derivative coefficient exceeds one at radius `R≥log 2`, even with varying a and M. Smooth compact even localization disproves every fixed universal integrated coefficient (`oddPolar_integrated_absorption_counterexample`).

Positive survivors: exponential sinh-tail confinement; exact least continuous even nonnegative local MASS correction `[Θ ψ_a² cosh−θ m_a sinh]_+`; complete compensated energy identity. This local correction is not proved paid by jump energy on arbitrary profiles.

Actual primitive producer: apply SAME cutoff χ_n to theta BEFORE translating. Let f_a,n=((Θχ_n)(x−a)−(Θχ_n)(x+a))/(2sinh(a/2)); g_a,b,n=f_a,n−f_b,n. Ordinary mean zero alone is insufficient: each f has sinh moment coshHalfMoment(Θχ_n), so shared-cutoff pairing is essential. Both hyperbolic moments of g vanish exactly. Its complete graph limit is the previously proved signed-radical difference; that cancels linear polarization error.

Full edge displacement and admitted translated-source moments give `|E(g_a,b,n)|≤2(L_a+L_b)/(n+1)²`. Constants depend on fixed admitted shifts; all primes, moving mass errors and original cosh subtraction are retained. `canonicalCriticalCutoff_source_class` and `canonicalCriticalCutoff_inverse_square_bound` specialize to explicit shifts, taking only natural indices as inputs. `canonicalPrimitiveCutoff_eventually_nonzero` excludes a vacuous zero family. No finite-horizon sign, full primitive-sector density, Nyman approximation or RH conclusion follows.

Four named source audits passed without warnings. All 84 public declarations in the two new leaves were checked with #print axioms from /tmp; only propext, Classical.choice and Quot.sound. No additional axiom/sorryAx. Both leaves are wired through THIM. Global lint must be rerun in the changing shared checkout; concurrent unrelated modules affected its last result.

Paper proof and exact T1–T4 scope: `docs/drafts/pipeline/3-formalized/thim-review1910-complete-absorption.md`. Failed-route closure with positive survivors: `docs/drafts/pipeline/5-failed/thim-uniform-sinh-absorption.md`. Knowledge ledger: `logs/thim-review1910-knowledge.md`.

Novelty is source-specific. Kernel slope, graph admission, radical pairing, localization and weighted cutoff arguments are prior or standard. Do not represent this as universal primitive coercivity or a new RH proof mechanism.