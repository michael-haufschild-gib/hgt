# Card `quasi-abelian-facet-palette-necessity` — **STAGE 3, LEAN GATE CLOSED** (2026-08-08)

Card moved to `docs/drafts/pipeline/3-formalized/quasi-abelian-facet-palette-necessity.md`.
Only gate left: independent specialist proof / novelty audit — **not a Lean obligation**.

The gate was *"construct full-period extraction and the Capocasa–Catanese necessary direction in
Lean"*.  Both are now unconditional theorem chains, and `QuasiAbelianFacetCertificate` /
`QuasiAbelianFacetPaletteInput` are **constructed** from them rather than assumed.  21 new modules,
all axiom-clean, all wired into `GaloisForLFunctions.HTGeometry`.

## The lesson that drove the whole build

Packaging a conclusion in a structure field is **not** proving it.  Before this work,
`quotient_noncompact`, `gammaClosed`, `gammaDiscrete`, `H_positive`, `H_integral_imaginary` existed
in the tree *only* as hypothesis fields of two structures — the card read as "formalized" but the
analytic content was assumed.  Grep for a field name before trusting a card's Lean status.

## Capstone

`exists_quasiAbelianFacetCertificate_of_realization` (`QuasiAbelianFacetRealization.lean`):
from (i) translation by `a v` fixes `G` exactly for `v ∉ A`, (ii) distinct integral facet exponents
translate `G` to distinct functions, plus the period-geometric data, produce a certificate with an
injective integral lattice class.

## Module map (all under `HTGeometry/`)

* `ClosedSubgroupLineStructure` — closed subgroups of a f.d. real space; `lineDirections`;
  **not in mathlib**.  Trick: complement `F`, `P ⊓ F` has no line, transport along the projection —
  no quotient topology, no induction on dimension.
* `FullPeriodExtraction` — `translationPeriods` (generalizes the corpus's 1-variable
  `periodSubgroup`, bridged by `rfl`); complex-linear line directions via the identity theorem.
* `NoncompactPeriodQuotient` — `span ℝ Γ ≠ ⊤ ⟹ W ⧸ Γ` noncompact (one dual vector).
* `GeneralizedRiemannRelations` / `RankTwoRiemannRelations` / `PlaneRiemannRelations` — property 6
  for ℂ-independent lattices, for rank ≤ 2 in any dimension, and hence for *all* of dimension 1.
* `CocycleCommutatorPairing` — commutator of a 2-cocycle is alternating + biadditive (`T = K1+K2−K3`).
* `AlternatingHermitianDictionary` — `H(x,y) = E(ix,y) + iE(x,y)`; `Im H = E` on the nose.
* `AutomorphyFactorCocycle` / `AutomorphyLogarithmDefect` — ℤ-valued defect
  (`Complex.exp_eq_one_iff`), constant by continuity + connectedness; logarithm from
  `Complex.exists_continuousOn_eqOn_exp_comp`.
* `AppellHumbertFactor` — the normal form; `thetaNorm` is Γ-invariant.
* `GaussianDecayVanishing` / `AffineGaussianSemidefinite` / `PeriodicBoundedThetaNorm` —
  semi-definiteness from one nonzero value (complete the square on affine lines).
* `HermitianRadicalPositivity` / `CapocasaCatanesePositivity` — degenerate Cauchy–Schwarz
  (`symmBilin_eq_zero_of_self_eq_zero`, no limits), radical, positive definiteness.
* `StanleyReisnerExponentDetector` — `x_v q_A ∈ I_Δ ↔ v ∉ A` (card (9), both directions).
* `DomainLinearIndependentMul` / `FacetQuotientDomain` — card (12)–(13).
* `TranslationOperatorIncidence` — card (11); axioms `[propext, Quot.sound]` only.
* `QuasiAbelianFacetCertificateOfTheta` / `QuasiAbelianFacetRealization` — the constructors.

## Corpus facts found mid-build (do not rebuild)

* `StanleyReisnerFacetSeparator.exists_facetSeparator` already proves card (7)–(9) **without** the
  per-facet vertex choice — the facet monomial itself is the separator.
* `FacetRestrictionEmbedding.linearIndependent_localizedStanleyReisnerFacetEmbedding_iff` already
  gives "restrict to the A-facet quotient".
* `FacetPolynomialQuotient.facetPolynomialQuotientEquiv` identifies the facet quotient with a
  polynomial ring.
* mathlib **has** `Complex.exists_continuousOn_eqOn_exp_comp` (Analysis/Complex/BranchLogRoot).

## Lean traps (recurring)

* **`Basis` is now `Module.Basis`** — without `open Module` it becomes an autoImplicit variable.
* `AddSubgroup.closure_induction` cases are `mem`, `zero`, `add`, `neg`.
* `AddMonoidAlgebra k G` is *not* reducibly `G →₀ k`.
* `IsDomain` transfer: use `Function.Injective.isDomain`, **not** `Equiv.isDomain` (the latter
  transports the ring *structure* and the instance stops matching `Ideal.Quotient`'s).
* `Finset.sum_subtype` needs an α-indexed summand; for a genuinely subtype-indexed one use
  `Finset.sum_attach`.
* `have h : A →+ B := …` forgets the body — use `closure_induction` instead of comap subgroups.
* `rcases ... with rfl|rfl` on `a = ω₁ ∨ a = ω₂` may substitute **ω₁ := a**, renaming outer vars.
* `RCLike.re/im` ≠ `Complex.re/im` syntactically — bridge with `RCLike.re_to_complex`.
* `Submodule.linearProjOfIsCompl` → `Submodule.projectionOnto` / `Submodule.projection`.
* `push_neg` → `push Not at h`.
* A `cd` inside a compound Bash command leaves the shell at that directory — heredocs then write to
  the wrong place or fail outright.  Use absolute paths for `cat >`.
