# Card 4 (nonautonomous-rational-first-order-tail-orbifold-law): complete-tail identification plan

The remaining gate item "parabolic-orbifold uniformization and complete-tail identification"
reduces ENTIRELY to existing corpus machinery — no new analytic input needed:

## Key reduction (worked out 2026-08-13)
Model the universal cover as the free differential field C⟨u⟩ (u differentially independent).

1. **Translations layer (compact signatures)**: deck translations u ↦ u + c fix u′; the corpus's
   `ScalarAdditiveDifferentialTorsor.fixedField_zpowers_scalarDifferentialTranslation_one` gives
   fixed(one nonzero translation) = C⟨u′⟩, and since u′ is fixed by ALL translations, a lattice or
   dense torsion group of translations still gives exactly C⟨u′⟩. No rank-2 lattice theory needed.
2. **Rotation layer**: order-n rotation u ↦ ζu (n ∈ {2,3,4,6}) acts on v := u′ by scaling v ↦ ζv.
   Apply the RANK-1 instance of `TorusInvariantField`/`TorusInvariantMonomials`
   (`torusScale_invariant_iff_mem_torusInvariantMonomialField`) with acting set S = ⟨ζ⟩: invariant
   field = C⟨v′/v⟩ + monomials with exponent ≡ 0 mod n = C⟨vⁿ⟩, because
   v′/v = (vⁿ)′/(n·vⁿ) ∈ C⟨vⁿ⟩. So fixed field = **C⟨(u′)ⁿ⟩**, and u″/u′ ∈ C⟨(u′)ⁿ⟩ automatically.
3. **(2,2,∞) Chebyshev**: on E = C⟨w⟩, scalings (roots of unity, unbounded order) →
   fixed = C⟨ℓ⟩, ℓ = w′/w (existing `mem_logDerivField_of_scaling_invariant_family`); the inversion
   w ↦ w⁻¹ acts on ℓ by ℓ ↦ −ℓ = scaling by −1 on the free generator ℓ; rank-1 torus machinery with
   S = {−1} gives fixed = C⟨ℓ²⟩ (velocity ℓ′/ℓ = (ℓ²)′/(2ℓ²) is inside). Downstairs identity
   `logDeriv_sq_eq_chebyshev_current` identifies ℓ² with y′²/(y²−4).
4. **Transported currents**: `EuclideanOrbifoldCurrents.lean` already expresses (u′)ⁿ as the
   rational current in the orbifold coordinate for each compact signature; the inversion/involution
   automorphism of C⟨w⟩ can be built with `PaletteEndomorphism.paletteEndo` (w ↦ w⁻¹ palette; use
   `DifferentialIndependentTransfer.differentialIndependent_of_range_subset_closure` for
   independence of the inverse palette; involutivity via `paletteEndo_eq_of_apply`).
5. **Protocol assembly**: mirror `MultiplicativeProtocolLogCurrentTail` /
   `TorusProtocolMonomialTail` shape: define the deck groups per phase, tail = ⋂ prefix images,
   conclude tail = C⟨(u′)ⁿ⟩ resp. C⟨ℓ²⟩. The four compact signatures share ONE parametrized module
   (n ∈ {2,3,4,6} = rotation order; degree of invariant coordinate matches).
6. mathlib `Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass` (PeriodPair.weierstrassP, ODE)
   supplies analytic witnesses if non-vacuity instantiation is wanted.

Same reduction serves card 5's "global orbifold signature reduction" tail-side; card 5 additionally
needs the Lie–Cartan/Casale rank ≤ 3 classification (separate, much deeper).
