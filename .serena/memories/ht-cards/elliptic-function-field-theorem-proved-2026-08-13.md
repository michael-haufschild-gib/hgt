# Elliptic function field theorem: PROVED (mathlib gap closed)

`f` meromorphic on ℂ and Λ-periodic ⟹ `C(℘)·f = A(℘) + ℘'·B(℘)` with `C` monic
(`exists_rational_weierstrass_representation`, germ identity at every point,
`[propext, Classical.choice, Quot.sound]`).

## Modules (all wired into `GaloisForLFunctions.HTGeometry`)
1. `HTGeometry/EllipticMeromorphicOrderTools.lean`
   - `meromorphicOrderAt_lt_sub_of_trailingCoeff_eq` (equal order + equal trailing coeff ⟹ strictly
     bigger order of the difference)
   - `even_meromorphicOrderAt_of_neg_eq` (even function ⟹ even order at 0)
   - `exists_const_eventuallyEq_of_lattice_periodic` (elliptic Liouville, meromorphic form, via
     `toMeromorphicNFOn`; periodicity of the normal form via
     `MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds`)
2. `HTGeometry/EllipticEvenPolynomialWeierstrass.lean`
   - `meromorphicOrderAt_weierstrassP_pow_zero`, `exists_polynomial_eval_weierstrassP_of_even`
3. `HTGeometry/EllipticEvenRationalWeierstrass.lean`
   - `one_le_meromorphicOrderAt_of_analyticAt_eq_zero`,
     `le_meromorphicOrderAt_pow_of_analyticAt_eq_zero`,
     `exists_pole_representative_weierstrassP`, `poleOrder`,
     `exists_rational_eval_weierstrassP_of_even`
4. `HTGeometry/EllipticFunctionFieldWeierstrass.lean`
   - `meromorphicOrderAt_derivWeierstrassP_zero` (=-3), `eventually_derivWeierstrassP_ne_zero`,
     `exists_rational_weierstrass_representation`

## Proof route (NO Jensen, NO residue theorem, NO divisor balance)
even part + ℘'·(odd part/℘'); even elliptic ×∏(℘-℘(a))^{m_a} over parallelogram poles clears all
non-lattice poles; even + poles only on Λ ⟹ polynomial in ℘ by descending induction on the (even)
pole order at 0 with `℘^k` cancelling the leading Laurent term; base case elliptic Liouville.

## Reusable corpus pieces consumed
`const_of_lattice_periodic_differentiable` (EllipticLiouvilleFacetCodimension),
`meromorphicOrderAt_add_period` (PeriodRigidity), `meromorphicOrderAt_sub_latticeCombination` +
`finite_poles_fundamentalParallelogram` (EllipticLatticeOrder / EllipticFundamentalPoles),
`exists_bounded_intCombination` (FundamentalParallelogram).

## mathlib API notes
- `to_fun` attribute generates `fun_<name>` (e.g. `fun_meromorphicOrderAt_mul`,
  `fun_meromorphicOrderAt_zpow_id_sub_const`), NOT `<name>_fun`.
- `MeromorphicAt.const c x` takes the point explicitly.
- `meromorphicOrderAt_fun_neg : order f = order (fun z => -f z)` (reversed direction).
- WithTop ℤ has no `ring`; convert with `← WithTop.coe_add` + `congr 1` + `push_cast; ring`.
- `Order.one_le_iff_ne_zero`, `ENat.monotone_map_iff.mpr Nat.mono_cast` for ℕ∞ → WithTop ℤ.
- Trick for opaque local functions: `obtain ⟨fe, hfe⟩ : ∃ fe, ∀ w, fe w = … := ⟨_, fun _ => rfl⟩`.

## Still open for the ht cards (cards 4/5/6 elliptic column)
The deck ACTION on the phase field in the jet model needs `℘(u+c)` as a rational function of
`(℘ u, ℘' u)` — the ℘ addition theorem, which mathlib lacks. Alternatives considered:
generic-reparametrization differential field over a field of meromorphic functions (needs a Field
of meromorphic functions: `meroField univ` = fractions of ENTIRE germs does not obviously contain ℘
without a Weierstrass sigma / prescribed-divisor construction — corpus has
`weierstrassGenusProduct` in `PrescribedDivisorRealization.lean` which could supply it).
