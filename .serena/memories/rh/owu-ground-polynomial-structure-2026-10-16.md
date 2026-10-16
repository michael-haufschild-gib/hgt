# OWU: canonical corrected odd ground factor (2026-10-16)

New modules: `formal/GaloisForLFunctions/RHTower/OddSectorPairedGroundDivision.lean` and `OddSectorGroundPolynomialStructure.lean`, wired into `RHTower.lean`.

Unconditional at every positive aperture: the odd part S of the exact arithmetic-corrected ground eigenspace is nonzero and finite-dimensional. Its entire Fourier–Laplace transforms are exactly `{P(w²) F_G(w) : deg P < dim S}`, with unique P and actual form-domain realization in both directions. G is an actual nonzero odd ground vector; F_G has zeros only on the real or imaginary axis. Among actual ground generators, its line is unique up to a unique nonzero scalar. Every attained blind minimizer belongs to this representation.

Main namespace `RHTower.OddSector`: `exists_oddArithmeticGround_div`, `exists_oddArithmeticGround_generator`, `exists_canonical_oddArithmeticGround_generator`, `exists_blind_optimizer_common_factor`.

Mechanism: pair division at z,-z to preserve oddness; the Hermitian polynomial splitting in w² preserves the full signed pole term, all finite arithmetic corrections, and mass. Nonnegative shifted odd form forces the quotient back into S. A kernel of dim(S)-1 evaluations plus paired division provides a polynomial-degree basis. An off-axis generator zero would give `(X-z²)P=1`. Mutual generator representations force constant factors.

Do NOT infer: the quotient/G is blind, the blind minimum is nonnegative, a positive arithmetic weight exists, or RH. This is not a polynomial module closed under arbitrary multiplication: degrees are truncated below dim(S). Existing full-space and even-polar root-division theorems do not directly supply this corrected odd signed-pole result. No simplicity premise is needed. No external novelty claim was made.

Paper proof, conjecture loop, limitations and audit: `docs/drafts/pipeline/3-formalized/owu-ground-obstruction-removal-2026-10-16.md`. OWU entry in `docs/reports/rh-current-frontier-map.md` updated.

Both leaf modules compile warning-free via `lake --old env lean -j 1`; no full/umbrella build, heartbeat increases or numerical certificates. All twelve public declarations were checked with #print axioms in /tmp: only propext, Classical.choice, Quot.sound. Index refresh succeeded. Global lint had ten unrelated concurrent unwired-module errors, listed in the card; no new OWU lint errors. Owned scratch files cleaned. Other agents' work preserved.