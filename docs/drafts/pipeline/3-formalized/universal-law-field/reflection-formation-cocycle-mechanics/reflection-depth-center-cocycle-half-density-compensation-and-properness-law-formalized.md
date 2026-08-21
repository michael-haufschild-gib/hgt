# ULF-RFCM-1 — Lean formalization record

**Card:** `reflection-depth-center-cocycle-half-density-compensation-and-properness-law.md`
**Module:** `formal/GaloisForLFunctions/HTGeometry/ReflectionDepthCenterCocycle.lean`
**Namespace:** `GaloisForLFunctions.HTGeometry`
**Umbrellas:** `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Card result → Lean declaration

| Card | Lean |
|---|---|
| **Theorem 1.1**, (RFC.4)–(RFC.5) | `exists_unique_formationCenter` |
| `F_λ`, (RFC.2) | `dilate`, `dilate_one`, `dilate_dilate`, `dilate_affine` |
| `R_c`, (RFC.6) | `reflect`, `reflect_reflect` |
| **Theorem 2.1**, (RFC.7) | `dilate_reflect` |
| **(RFC.8)** | `exchange_word` |
| the three-way equivalence | `dilate_reflect_comm_iff` |
| **(RFC.9)** | `exchange_iterate` |
| **Corollary 3.1**, (RFC.10) | `affine_comm_reflect_iff` |
| **(RFC.11)** | `dilate_dilate`, `dilate_center_comm` |
| `R`, (RFC.12) | `dirichletReflect`, `dirichletReflect_eq` |
| **(RFC.13)** | `rawDepth_reflect`, `rawDepth_exchange_word` |
| **(RFC.14)** | `compensatedDepth`, `compensatedDepth_eq_dilate`, `compensatedDepth_reflect` |
| **(RFC.15)** half-density coefficient law | `dirichletWeight_compensatedDepth` |
| **§4**, (RFC.16) | `step_le_of_forall_mem` |
| **§5**, (RFC.17) | `tendsto_properWork_atTop` |
| **§6**, (RFC.19)–(RFC.20) | `formationJeffreys_translationOrbit` (on the corpus `formationJeffreys_splitFormation`) |
| **§7**, (RFC.22) lift side | `not_isBounded_translation_orbit` |
| **§7**, (RFC.22) observer side | `isCompact_closure_projected_orbit` |
| **§7** rational increment | `projected_orbit_periodic` |
| **§7** irrational increment | `denseRange_projected_increment` |

## Method notes

* Theorem 1.1 is stated for an arbitrary subset `M ⊆ ℝ` closed under the cocycle identity with one
  element `ρ ≠ 1`; no monoid or positivity structure is needed for the conclusion.
* The three-way equivalence of Theorem 2.1 is derived from the single value at `x = 0`, so no
  invertibility of `F_λ` is used there; `exchange_word` supplies the invertible form separately.
* (RFC.15) is the pure `rpow` identity `n^{-(mσ-(m-1)/2)} = n^{(m-1)/2}(n^{-σ})^m`, valid for every
  real slope `m`, not only integers.
* §6 needed no new mathematics: the corpus already owns
  `ConstitutiveFunctionalEquationPacketLift.formationJeffreys_splitFormation`; the card's statement
  is its specialization to the translation orbit.
* §7 uses mathlib's `AddCircle.denseRange_zsmul_coe_iff` for the irrational case and an explicit
  period argument for the rational case.

## Verification

* `lake env lean` on the module: 0 errors, 0 warnings.
* Axiom audit: 24 public declarations, only `propext`, `Classical.choice`, `Quot.sound`.
