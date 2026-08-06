# Coframe card: scheme-level finiteness globalised + pullback law (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(stage 2).  Modules **15 (extended) and 16**.  See
[[research/coframe_scheme_layer_opened_2026_08_06]] and
[[research/eigenvolume_horizon_capstone_2026_08_06]].

## `SchemeOrderSupportFinite.lean` — globalised

- `exists_num_den_of_isAffineOpen` — on an affine open, `f · b = a` for sections `a`, `b`;
  from `functionField_isFractionRing_of_isAffineOpen` + `IsFractionRing.div_surjective`.
  **`algebraMap Γ(X,U) X.functionField = X.germToFunctionField U` is `rfl`** (but `field_simp`
  will not see through it — rewrite with an explicit `rfl`-`have` first).
- `finite_ord_support_inter_affineOpen`
- **`finite_ord_support`** — `[IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]`:
  `{z | Scheme.ord f z ≠ 0}.Finite`.  Finite affine subcover via
  `isCompact_univ.elim_finite_subcover`; each point sits in
  `(X.affineCover.f (X.affineCover.idx x)).opensRange`.

## `SchemeOrderPullbackLaw.lean` (16)

- `algebraMap_stalk_ne_zero`, `exists_natCast_addVal`
- **`ord_algebraMap_stalk_eq_addVal`** — the bridge: mathlib's `Scheme.ord` (module length) equals
  `IsDiscreteValuationRing.addVal` at a codimension-one point with DVR stalk.  Route:
  `Scheme.ord_eq_iff` → `Ring.ordFrac_eq_ord` → `Ring.ordMonoidWithZeroHom_eq_coe` →
  `Ring.ord_eq_addVal`.
- **`ord_pullback_eq_mul_ramification`** — `ord (Φ f) z = e * ord f w`, given a local-ring
  hom `ψ : stalk w →+* stalk z`, a function-field hom `Φ` with `Φ ∘ algebraMap = algebraMap ∘ ψ`,
  and `addVal (ψ π) = e`.  Reuses `addVal_map_eq_mul_ramification` from
  `LocalRamificationOrderLaw.lean`.

## Lean traps

- `Ring.ordFrac_eq_ord` and `Ring.ordMonoidWithZeroHom_eq_coe` take **`R` (and `K`) explicitly** —
  `rw [Ring.ordFrac_eq_ord hs]` fails with "expected Type"; pass `(R := …) (K := …)`.
- `U : X.affineOpens` → passing `U.2` leaves `[Nonempty ↥U]` unsynthesizable even after
  `haveI` on what looks like the same type.  Fix: give the lemma `{U : X.Opens} (hU : IsAffineOpen U)`
  and do the `Nonempty` case split **inside** it, so the binder and the `by_cases` share one `U`.
- `omit [inst] in` must precede the docstring.

## Repo hazard (ongoing)

`formal_tools.py lint --check-generated` reports `stale generated file` even when `index` is run
immediately before: another agent is adding Lean files concurrently (verified by diffing two
consecutive `index` runs — `RHTower/Sieve/DirichletSigmaTail.lean` appeared between them).  The
generator is deterministic; this is a race, not a defect.
