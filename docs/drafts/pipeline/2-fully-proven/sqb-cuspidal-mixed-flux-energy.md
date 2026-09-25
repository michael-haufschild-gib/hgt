# SQB mixed cuspidal flux from form energy

- **ID:** SQB-CMF
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `MaassFiniteDeckCuspidalCrossFlux.lean`, `MaassFiniteDeckCuspidalTail.lean`, `MaassFiniteDeckCuspidalGreen.lean`
- **Statement:** The literal exceptional finite-deck source has zero mixed vertical boundary current at infinite height against every cusp-zero form pre-vector.

## Goal

Discharge the infinite-height boundary in the source-to-Friedrichs Green identity. This is a source-specific theorem about the existing finite-deck carrier. It does not establish the global form representation or normalized full-Xi occurrence.

## Gates

- [x] 0 → 1: literal source, test domain and current already defined in Lean.
- [x] 1 → 2: dependency-closed paper proof below. **[PROVED HERE]**
- [ ] 2 → 3: formalize the limit and infinite-strip identity in a new Lean leaf, wire the umbrella, and run only the leaf audit with Lake `--old`.
- [ ] 3 → 4: standalone paper and certificate.

## Exact theorem

Fix `N : ℕ`, an exceptional eigenvalue `lam`, its literal Maass cusp source `f`, and any `F : cuspidalFormPreDomain N`. Let `F₀` be its coercion to `formPreDomain N`, and let

`B(y) = sourceTestBoundaryCurrent N lam f F₀ y`.

Then `B(y) → 0` as `y → +∞`. More precisely, for every `c > 1`, the function `B` is integrable on `(c,∞)`, the existing `sourceTestGreenDensity N lam f F₀` is integrable there, and

`∫_{c}^{∞} sourceTestGreenDensity N lam f F₀ y dy = -B(c)`.

No extra source decay estimate, zero-location premise, or spectral assumption is used.

## Proof

Put `L=N+1` and write `U_q(x,y)` for the literal source deck coordinate and `F_q(x,y)` for the test coordinate. For `y>1`, retraction at height one is the identity. The boundary current is exactly

`B(y)=Σ_q ∫₀ᴸ (∂ᵧ U_q)(x,y) · conjugate(F_q(x,y)) dx`.

Define the nonnegative slice energies

`E_Y^U(y)=y⁻²∫₀ᴸ ‖hypGradY U(x+iy)‖² dx = ∫₀ᴸ ‖∂ᵧ U(x,y)‖² dx`, and

`E_X^F(y)=y⁻²∫₀ᴸ ‖hypGradX F(x+iy)‖² dx = ∫₀ᴸ ‖∂ₓ F(x,y)‖² dx`.

The source is a cusp-zero pre-vector by `sourceInCuspidalFormPreDomain`. Cauchy–Schwarz across the horizontal interval and finite deck, followed by `level_cusp_slice_poincare` for `F`, gives

`|B(y)| ≤ (L/(2π)) √(E_Y^U(y) E_X^F(y)) ≤ (L/(4π))(E_Y^U(y)+E_X^F(y))`.  (1)

Both energies are integrable on `(c,∞)` by the exact `level_hypGradY_slice_weighted_integrable` and `level_hypGradX_slice_weighted_integrable` theorems. Thus `B ∈ L¹(c,∞)`. Notice the cancellation of the two powers of `y`: the hyperbolic form energy controls the *unweighted* derivative needed by Green's boundary term. Cusp-zero Poincaré supplies the same unweighted control for the test value.

Let `D(y)=sourceTestGreenDensity N lam f F₀ y`. The already formalized `retractedSourceDeckComponent_laplacian` states `Uₓₓ+Uᵧᵧ=-lam·y⁻² U` above height one. Substitution into the literal Green density gives

`D(y)=Σ_q∫₀ᴸ [Uₓ·conjugate(Fₓ)+Uᵧ·conjugate(Fᵧ)-lam·y⁻² U·conjugate(F)] dx`.  (2)

Each gradient term is `L¹` in height by space-time Cauchy–Schwarz and the source/test form-energy `L²` admissions. The mass term is `L¹` by Cauchy–Schwarz in the hyperbolic measure and their `L²` value admissions. These are precisely the completed-form coordinates already present for the source and test. Hence `D ∈ L¹(c,∞)`.

For `c<d`, the formal theorem `sourceTestGreenDensity_increment` gives `B(d)-B(c)=∫_c^d D(y)dy`. Since `D ∈ L¹(c,∞)`, the right side converges as `d→∞`, so `B(d)` has a finite limit. Since also `B ∈ L¹(c,∞)`, this limit must be zero: a nonzero limit would bound `|B|` below by a positive constant on a tail of infinite measure. Taking the limit in the finite-strip identity proves both claims.

The proof uses the exact full deck sum and full periodic strip; no coordinate, primitive row, or source forcing is dropped.

## Consequence and remaining join

The top boundary of the mixed cusp Green identity is now zero **on paper** for every cusp-zero pre-vector. The lower boundary at finite height must still be joined to the compact-core Green formula, and the resulting form identity must be extended to the completed cuspidal form domain to place the source in the Friedrichs operator domain. SQB's independent normalized full-Xi occurrence and symmetric-power selection remain separate open obstacles. Do not treat this cusp theorem as RH or as a replacement for those joins.
