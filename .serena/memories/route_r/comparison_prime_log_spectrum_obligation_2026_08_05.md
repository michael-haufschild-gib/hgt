# Route R: any admissible comparison target must carry the prime-log spectrum

Formalized 2026-08-05, third result of the same session as
`route_r/cocycle_transport_non_erasure_2026_08_05` and
`route_r/phase_defect_character_blindness_no_go_2026_08_05`.

`GaloisForLFunctions/RHTower/RouteRComparisonPrimeSpectrumObligation.lean`.

## Statement

Let `f : CyclicSource →ₗ[ℂ] B` be multiplicative with `D_B ∘ f = f ∘ ∂_ℓ` and `τ_B ∘ f = ε₀`.
Then for every prime `p`:

- `D_B (f u_p) = (log p) • f u_p`, `f u_p ≠ 0`   (`hasEigenvector_primeAtomForward`)
- `D_B (f u_{p⁻¹}) = (−log p) • f u_{p⁻¹}`, `≠ 0` (`hasEigenvector_primeAtomBackward`)
- `± log p ∈ point spectrum D_B`                  (`hasEigenvalue_primeLog`)
- `{f u_p}_p` linearly independent                (`linearIndependent_primeAtomForward_image`)
- `¬ Module.Finite ℂ B`                            (`not_module_finite_of_comparison`)

Non-erasure is a *conclusion*, not a hypothesis — it comes from `primeAtom_not_erased`.

## Use

Cheap necessary test on any proposed Route R comparison target: **its derivation must already have
`{± log p}` in the point spectrum**. Finite-rank / finite-dimensional models are excluded outright.
This is the Hilbert–Pólya / Connes trace-formula signature, so the constraint discriminates rather
than prohibits.

Non-vacuity certified by the identity comparison `(S, ε₀, ∂_ℓ, id)` →
`cyclicSource_not_module_finite`.

Card: `docs/drafts/pipeline/3-formalized/route-r-comparison-prime-log-spectrum-obligation.md`.

## Lean notes

- `Module.End.eigenvectors_linearIndependent'` (indexed variant, injective eigenvalue map) is the
  right tool; the unprimed one wants a `Set` index.
- `Module.End.HasEigenvector` unfolds to an `And`, so dot-notation `.hasEigenvalue` fails; use
  `Module.End.hasEigenvalue_of_hasEigenvector`.
- `DB : B →ₗ[ℂ] B` is not syntactically `Module.End`, so dot notation on `Module.End` lemmas fails;
  call them with the explicit namespace.
- Infinite-dimensionality: `Module.Finite.not_linearIndependent_of_infinite`.
