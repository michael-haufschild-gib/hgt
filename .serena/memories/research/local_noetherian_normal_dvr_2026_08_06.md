# Local DVR criterion + normal scheme stalks (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Modules **18 and 19**; continues
[[research/coframe_scheme_morphism_pullback_2026_08_06]].

## `LocalNoetherianNormalDVR.lean` (18) — pure commutative algebra, no AG imports

- `not_isField_of_ringKrullDim_eq_one`
- `dimensionLEOne_of_ringKrullDim_eq_one`
- **`isDiscreteValuationRing_of_ringKrullDim_eq_one`** — `[IsLocalRing] [IsDomain]
  [IsNoetherianRing] [IsIntegrallyClosed]` + `ringKrullDim R = 1` ⟹ `IsDiscreteValuationRing R`.

mathlib has this **only** through the Dedekind-ring interface (`IsDiscreteValuationRing.TFAE`
needs `IsDedekindDomain`), so the purely local form had to be built.

**`LocalizationAtPrimeDivisorDVR.lean` was refactored to delegate to it** — the three theorems
`not_isField_/dimensionLEOne_/isDiscreteValuationRing_localizationAtPrime` are now one-liners.
Keeping the criterion in a module with **no AlgebraicGeometry imports** was essential: otherwise
the whole prime-divisor chain (PrimeDivisorOrder → capstone) would inherit an AG dependency.

## `SchemeNormalStalkDVR.lean` (19)

- **`isDiscreteValuationRing_stalk`** — `coheight z = 1` + `IsIntegrallyClosed (stalk z)` ⟹ DVR,
  via `ringKrullDim_stalk_eq_coheight`.
- `isIntegrallyClosed_stalk_of_isAffineOpen` — `IsIntegrallyClosed Γ(X,U)` transfers to the stalk
  by `isIntegrallyClosed_of_isLocalization` + `IsAffineOpen.isLocalization_stalk`.
- **`isDiscreteValuationRing_stalk_of_isAffineOpen`** — the instance the scheme-level pullback law
  needs.

**mathlib has no normality class for schemes** (no `AlgebraicGeometry.IsNormal`), so normality is
stated as `[IsIntegrallyClosed Γ(X, U)]` on an affine chart.

## Remaining for Theorem A at scheme level

1. Assemble: instantiate `EigenvolumeRamificationSystem` on codimension-one points of `X` with
   `Scheme.ord` as the order function, using `finite_ord_support` for `hfin` and
   `ord_functionFieldMap_eq_mul_ramification` for the `e` half of the law.
2. Different exponent `e − 1` beyond the Eisenstein presentation — still the algebraic gap.
3. Step 4's `e > 1` needs N¹ / int-amplification (not started).

## Repo hazard (ongoing)

Concurrent agent keeps adding unwired untracked modules; this round
`HTGeometry.GeneralScaleStabilizer`.  Index staleness in `lint --check-generated` is that race.
