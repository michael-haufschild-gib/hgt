# Route R: comparison obligation reduced to two intertwining identities

Formalized 2026-08-05, same session as `route_r/phase_defect_character_blindness_no_go_2026_08_05`.

## Universal law (HTGeometry, reusable)

`GaloisForLFunctions/HTGeometry/TraceDerivationCyclicCocycleLaw.lean`.
For a non-unital associative ring `A`, abelian group `K`, `τ : A →+ K`, `D : A →+ A`, put
`φ(a,b) = τ(a · D b)`.

- `traceDerivCocycle_boundary`: if τ is a trace and D a derivation then
  `φ(ab,c) − φ(a,bc) + φ(ca,b) = 0`. **τ∘D = 0 is NOT needed for this.**
- `traceDerivCocycle_antisymm_iff`: `φ antisymmetric ⟺ τ(D(ab)) = 0 ∀ a,b`. So KCC-1's
  annihilation hypothesis is exactly cyclicity.
- `traceDerivCocycle_comp`: `f` additive + multiplicative + `D_B∘f = f∘D_A` + `τ_B∘f = τ_A`
  ⟹ `φ_B(fa,fb) = φ_A(a,b)`.
- `ne_zero_of_traceDerivCocycle_ne_zero_left/right`, `traceDerivCocycle_image_ne_zero`:
  `φ_A(a,b) ≠ 0` ⟹ `f a ≠ 0`, `f b ≠ 0`, `φ_B(fa,fb) ≠ 0`.

## Route R instantiation

`GaloisForLFunctions/RHTower/RouteRCocycleTransportNonErasure.lean`.
`(ε₀, ∂_ℓ)` on `CCMRationalAdelicCyclicSourceAlgebra` is an instance; KCC-1/KCC-2 are corollaries.
`ccmKummerTraceDerivCocycle_primeAtom` = `−log p ≠ 0` on the retained ordinary-prime atom.

`primeAtom_not_erased`: for ANY `(B, τ_B, D_B)` and any additive multiplicative `f` with
`D_B∘f = f∘∂_ℓ` and `τ_B∘f = ε₀`, both legs survive and the transported value is `−log p`.

**Gate collapse**: "coefficient-faithful on the ordinary-prime top atom" (gate 3 of
POLARIZED_ADELIC_STOKES) is NOT an independent requirement — it follows from the two intertwining
identities. Remaining producer: exhibit `(B, τ_B, D_B)` reading the fixed Xi physical residue plus
`f` satisfying those two identities.

Card: `docs/drafts/pipeline/3-formalized/trace-derivation-cyclic-cocycle-transport-law.md`.

## Lean gotchas

- `ccmRationalAdelicCyclicSource_mul_smul` in the Kummer module is `private`; `mul_smul_comm` fails
  on `CCMRationalAdelicCyclicSourceAlgebra` (no `SMulCommClass ℂ S S` instance). Route around by
  reusing the public `ccmRationalAdelicKummerCyclicOneCocycle_primeAtom` +
  `..._tprod` and reducing `Fin.cases _ _ (1 : Fin 2)` with
  `rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ]`.
- `Mathlib.Algebra.GroupPower.Basic` no longer exists on this toolchain.
