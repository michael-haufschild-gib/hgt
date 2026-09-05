# Strict decrease of constrained Weil ground energy

**Status:** formalized in four wired Lean leaves; all named leaf builds and all 24 public-theorem axiom checks pass. Global lint currently reports three unrelated unwired Bellman modules, listed below.

**Proof chain:** literal constrained Weil form → exclude its unique possible zero ground → positive ground at every finite aperture → existing weighted pole-exclusion theorem → RH. Strict decrease and the exact failure classification are proved; exclusion of the zero ground remains open. RH is neither proved nor disproved here.

## Exact results

- `RHTower.strictAnti_ccmRestrictedWeilPolarGroundEnergy`: for every `a<b`, `μ₀(b)<μ₀(a)`, unconditionally for the actual arithmetic source.
- `RHTower.riemannHypothesis_iff_polarGroundEnergy_pos`: RH is equivalent to strict positive constrained ground at every finite aperture.
- `RHTower.riemannHypothesis_or_unique_polarGroundZero`: either RH, or exactly one zero aperture, with positive floors below and strictly negative floors above. No branch is selected.
- `RHTower.polarSmoothSource_strict_ground_floor`: every nonzero smooth strict-interior constrained test has Rayleigh quotient strictly above `μ₀(a)`, at every aperture and energy. Smooth density cannot supply an interior ground minimizer.
- Full weighted Fourier-domain translation preserves physical norm, aperture support admission, the two exponential constraints, and the complete constrained prime–Gamma quadratic.
- Equally spaced translates of every nonzero complex L² function are linearly independent, with no regularity or compact-support assumption.
- The constrained radical of an identity-minus-compact operator on a closed Hilbert subspace is finite-dimensional. Null vectors enter this radical when the restricted Hermitian form is nonnegative.

## Dependency-closed paper proof

Assume `a<b` and the ground energies agree at `E`. Take an attained normalized constrained ground vector `u` at `a`. The shifted form `Q-E‖·‖²` is nonnegative on the constrained sector at `b`.

For `|h|≤b-a`, translation `T_h u` belongs to the larger form domain. Its Fourier multiplier is unimodular, preserving the weighted norm and physical L² norm; its translated support remains in `[-b,b]`. A pole coordinate with exponent `s` gains exactly `exp(-sh)`, so both constraints persist. Prime translation pairings commute with translation, Gamma energy is invariant, and the extra prime indices at the larger aperture vanish by the existing exact aperture-extension theorem. Thus `Q(T_h u)=E‖T_h u‖²`.

Semidefinite Hermitian polarization puts every such translate in the constrained radical of the shifted form. The exact actual-pencil identity is `Q-E mass = I-K(b,E)`. For every radical vector `v`, its diagonal identity gives `‖v‖²=Re⟨v,Kv⟩≤‖v‖‖Kv‖`, hence `‖v‖≤‖Kv‖`. The radical is a closed intersection of linear kernels and the pole constraints. Compactness of `K` therefore forces finite dimension.

For any finite size choose distinct equally spaced shifts inside the support margin. A relation becomes `p(exp(2πihξ))*Fourier(u)(ξ)=0` almost everywhere. A nonzero polynomial has finitely many roots; their exponential preimages are countable, and the nonzero-frequency real-line parametrization is injective. The multiplier is nonzero almost everywhere, so the relation would force `u=0`. Arbitrarily large independent families cannot fit the finite-dimensional radical. This proves strict decrease at every energy.

Small-aperture positivity, continuity, and strict decrease give the unique-zero sign profile. All-aperture nonnegativity is already RH-equivalent; applying strict decrease between any finite aperture and a larger one upgrades nonnegativity everywhere to positivity at each finite aperture. Finally, any smooth strict-interior test fits a smaller aperture, whose ground is strictly higher, proving strict nonattainment by such tests.

## Conjecture refinement and corpus audit

The initial target was strict negativity above a null aperture. The energy-shifted identity exposed the stronger theorem: strict decrease at every energy. The proof requires no regularity of a ground vector. The earlier compact pointwise shift-independence result did not cover arbitrary L² ground vectors; Fourier polynomial independence closes that exact gap.

Corpus searches `research 'radical compact'` and `research 'ground strict aperture'`, together with statement searches, located the compact bounded-below theorem, Hermitian radical lemma, exact shifted pencil identity, aperture extension, and ground attainment. They did not locate the assembled strict-decrease theorem. This is a corpus novelty check, not a claim of literature priority.

Inputs include `L2MellinUnitary`, `LpBoundedMultiplier`, `CCMArchimedeanHilbertFormDomain`, `CCMRestrictedWeilApertureMonotonicity`, `CCMRestrictedWeilCanonicalGroundHeadEnergy`, `CCMRestrictedWeilPolarGroundState`, `CompactOperatorBoundedBelow`, and `CapocasaCatanesePositivity`. Mathlib supplies polynomial root finiteness and `Set.Countable.preimage_cexp`.

## Lean and validation

| Leaf under `formal/GaloisForLFunctions/` | Public theorems | Named build |
|---|---:|---|
| `RHTower/CCMRestrictedWeilFormTranslation.lean` | 11 | Pass |
| `HTGeometry/L2TranslationPolynomialIndependence.lean` | 2 | Pass |
| `HTGeometry/CompactConstrainedRadical.lean` | 4 | Pass |
| `RHTower/CCMRestrictedWeilPolarStrictDomain.lean` | 7 | Pass |

All four leaves are imported by their theorem-area umbrellas. Foreground scratch checks used `lake env lean <file>`; final audits used named `lake --old --log-level=error build <module>` calls, with no full or umbrella build. The 24 public theorem axiom audits report only `[propext, Classical.choice, Quot.sound]`; the actual target remains mathlib's zeta-zero `RiemannHypothesis`. No added axiom, admission, or computational proof oracle occurs. No mathematical numerical experiment was used.

`git diff --check` passes. The repository-wide formal lint has unrelated reachability errors for `HTGeometry.Arxiv2608BellmanShorelineAlgebra`, `HTGeometry.Arxiv2608BellmanShorelineApplications`, and `HTGeometry.Arxiv2608BellmanShorelineConvex`, created concurrently outside this work. This prevents claiming a clean global lint at this audit.

Scratch proofs and axiom audit: `/tmp/hgt-weil-translate.etUC0A`. All owned Lean/build sessions completed.
