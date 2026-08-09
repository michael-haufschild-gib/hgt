# Bipolar provenance and dagger reduction — Lean certificate

- **ID:** `bipolar-provenance-dagger-reduction-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `bipolar-provenance-dagger-reduction.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Modules

| File | Contents |
|---|---|
| `HTGeometry/ExactnessFlagDaggerDuality.lean` | §1: the dagger, its perfect pairing, and involutivity |
| `HTGeometry/ExactnessFlagBipolarTopology.lean` | §2–3: dagger discontinuity and the bipolar refinement |
| `HTGeometry/ExactnessFlagPhaseCertificate.lean` | §4: continuous phase certificates |
| `HTGeometry/ExactnessFlagGreenReduction.lean` | §5: Green reduction and the positivity no-go |

All four are in namespace `GaloisForLFunctions.HTGeometry`.

## Card statement to Lean name

| Card | Lean |
|---|---|
| `(2)`: the dagger of a flag | `ExFlag.dagger` |
| `(3)`: the canonical pairing `(Z/B) × (B°/Z°) → k` | `ExFlag.daggerEval`, `ExFlag.daggerEval_homologyClass` |
| `(5)`: restriction is surjective onto the quotient dual | `ExFlag.surjective_daggerEval` |
| kernel of `(5)` is `Z°` | `ExFlag.ker_daggerEval` |
| `(4)`: `(Z/B)ᵛ ≅ B°/Z°` | `ExFlag.daggerHomologyEquiv` |
| perfection of the pairing | `ExFlag.eq_zero_of_forall_daggerEval_eq_zero` |
| involutivity of `(2)` | `ExFlag.dagger_dagger`, `ExFlag.daggerEquiv` |
| `(6)`–`(7)`: the dagger pullback of a dual cycle test | `ExFlag.dagger_preimage_cycleTest` |
| the dagger pullback of a dual boundary test is a union of source cycle tests | `ExFlag.dagger_preimage_boundaryTest` |
| §2: dagger is not provenance continuous | `ExFlag.not_continuous_dagger_of_exists`, `ExFlag.not_continuous_dagger` |
| `(8)`: the bipolar topology | `ExFlag.biTopology` |
| `(8)`: coarsest refinement making the dagger continuous | `ExFlag.biTopology_le_prov`, `ExFlag.continuous_dagger_bi`, `ExFlag.le_biTopology` |
| `(10)`: the phase test is the only new generator | `ExFlag.biTopology_eq_generateFrom` |
| `(9)`: dagger is a bipolar homeomorphism | `ExFlag.induced_dagger_biTopology`, `ExFlag.daggerBiHomeomorph` |
| `(11)`: specialization order unchanged | `ExFlag.bi_specializes_iff` |
| `(13)`: continuous phase certificate | `ExFlag.exists_phase_certificate` (real case `ExFlag.exists_real_phase_certificate`) |
| `(13)` read on the flag | `ExFlag.mem_survival_iff_exists_phase_certificate` |
| `(14)`: Green self-duality | `ExFlag.IsGreenSelfDual` |
| `(14)`: the boundary space is isotropic | `ExFlag.IsGreenSelfDual.isotropic` |
| `(15)`: the form descends to `Z/B` | `ExFlag.greenQuotForm`, `ExFlag.greenQuotForm_mk` |
| `(17)`: the descended form is nondegenerate | `ExFlag.nondegenerate_greenQuotForm` |
| `(16)`: positive definiteness forces `(0, ⊤)` | `ExFlag.IsGreenSelfDual.eq_trivial_of_anisotropic`, `ExFlag.eq_trivial_of_orthogonal_selfDual` |
| no nonzero boundary survives | `ExFlag.IsGreenSelfDual.boundary_eq_bot_of_anisotropic` |
| `(18)`: the hyperbolic plane realizes the off-horizon flag | `ExFlag.hyperbolicForm_orthogonal_line`, `ExFlag.isGreenSelfDual_hyperbolic_offHorizon` |
| the horizon flag is Green self-dual for every form | `ExFlag.isGreenSelfDual_horizon` |

## Generality actually proved

- §1 needs no finite-dimensionality: the perfect pairing and the isomorphism `(Z/B)ᵛ ≅ B°/Z°` are
  proved for an arbitrary vector space, using algebraic extension of functionals.  Only
  involutivity and the flag bijection use `FiniteDimensional`.
- §2 is proved for any nonzero covector with nonzero kernel over an infinite field, and then
  specialized to `1 < Module.rank`, which is the card's `dim V ≥ 2`.
- §4 is proved for any Hausdorff locally convex space over an arbitrary `RCLike` field — the card's
  "real or complex" — by upgrading the real geometric Hahn–Banach separation through
  `StrongDual.extendRCLike`.
- §5 splits the card's "bilinear, alternating, or Hermitian" into an explicitly reflexive bilinear
  form (descent and nondegeneracy) and an anisotropic form or a genuine inner product (the no-go).

## Reusable infrastructure added

- `ExFlag.quotBilin` — descent of a bilinear form through a submodule contained in both radicals,
  built from `Submodule.dualQuotEquivDualAnnihilator`.  Mathlib has no such construction.
- `ExFlag.congr` — transport of exactness flags along a linear equivalence as a homeomorphism, and
  `ExFlag.induced_pushforward_equiv`, which is what makes the bipolar topology dagger-stable.

## Scope of the Meyer–Poisson remark in §4

The card's closing paragraph applies `(13)` to the pair `(𝓑_P, Γ_sec)`.  That instantiation needs
closedness of `𝓑_P` inside `Γ_sec`, an input of `deninger-cofinal-floquet-secondary-poisson-graph.md`
and not of this card; the transferable statement `(13)` itself is proved here for every closed
boundary subspace.

## Axiom audit

`[propext, Classical.choice, Quot.sound]` for every declaration listed above.
