# Coframe card: eigenvolume condition derived + scheme layer opened (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(stage 2).  Modules **14 and 15** of the lineage (see
[[research/eigenvolume_horizon_capstone_2026_08_06]] for 12–13).

## `EigenvolumeUnitInvariance.lean` (14) — `heig` discharged

- `formOrder_eq_of_cross` — the order depends only on the fraction, not the chosen `a`, `b`.
- `orderAt_unit`, `formOrder_unit_mul` — a unit factor changes nothing.
- `eigenvolume_condition_of_unit` — if `(φ a · J) · b = (u · a) · φ b` for `u : Bˣ`, the pullback
  has the same divisor as the form.  This is Step 1 of Theorem A: the top wedge of an invariant
  coframe pulls back to `det(A)` times itself, and `det(A)` is a unit.
- `unitEigenvolume_formOrder_eq_neg_one` / `_ne_zero_iff` /
  `unitEigenvolume_ramificationIndex_eq_one_off_horizon` — the horizon theorem with the
  eigenvolume condition replaced by the unit identity.

## `SchemeOrderSupportFinite.lean` (15) — the scheme layer

Dictionary (needs neither `IsIntegral` nor `IsLocallyNoetherian`):
- `coheight_eq_height_primeIdealOf` — via `ringKrullDim_stalk_eq_coheight` +
  `IsLocalization.AtPrime.ringKrullDim_eq_height` + `IsAffineOpen.isLocalization_stalk`.
- `isUnit_germ_iff_notMem_primeIdealOf` — `IsLocalization.AtPrime.isUnit_to_map_iff`;
  `algebraMap Γ(X,U) (stalk x) = germ` is **`rfl`**.
- `primeIdealOf_injective` — free from `IsAffineOpen.fromSpec_primeIdealOf` (a left inverse).

Order lemmas: `ord_algebraMap_stalk_eq_zero` (`Ring.ordFrac_of_isUnit` proves
`X.ordHom z hz (algebraMap …) = 1` **directly**, no unfolding needed),
`ord_germToFunctionField_eq_zero_of_isUnit_germ`.

**`finite_ord_support_of_isAffineOpen`** — on an affine open of an integral locally Noetherian
scheme, `{x : U | Scheme.ord f x ≠ 0}` is finite when `f · b = a` for nonzero sections `a, b`.
Proof: transport to `PrimeSpectrum Γ(X,U)` and apply `finite_heightOneSupport_frac`.

## mathlib state (checked 2026-08-06, v4.32.2)

- `AlgebraicGeometry.Scheme.ord` / `ordHom` exist (`Mathlib/AlgebraicGeometry/OrderOfVanishing.lean`)
  with `ord_mul`, `ord_of_isUnit`, `ord_add`, `ord_le_smul`.  **No divisor of a rational function,
  no support finiteness.**  `AlgebraicCycle/Basic.lean` is 79 lines — still no principal divisor.
- `Ring.ord` = `Module.length R (R ⧸ span {x})`; `Ring.ord_eq_addVal` bridges to DVRs.
  **No `ord = 0 → IsUnit`.**
- Different ideal: `pow_sub_one_dvd_differentIdeal` gives `P^(e−1) ∣ 𝔡` (Dedekind, separable);
  `not_dvd_differentIdeal_of_isCoprime` needs `IsCoprime P Q`, so it does **not** cover the
  totally ramified local case.  Exact `= e−1` there is still only our Eisenstein module.
- `AlgebraicGeometry.StructureSheaf.isUnit_toStalk` is **not public** (module system, after
  `end Public`) — use `Scheme.mem_basicOpen` / `IsAffineOpen.isLocalization_stalk` instead.
  `StructureSheaf.stalkIso` *is* accessible but there is no `Algebra R (stalk z)` instance.

## Repo hazard

Two collisions from another agent's untracked modules this session:
`TorusDerivationJets.fderiv_apply_eq_sum` clashed with the tracked
`ClockFlatFrameCovariance.fderiv_apply_eq_sum` — renamed the newcomer to
`fderiv_apply_eq_sum_complexJets` to unbreak the shared umbrella.  `TorusDerivationLeibniz` is
untracked and unwired, so `lint --check-generated` flaps.
