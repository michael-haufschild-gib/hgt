# Formalized: Burnol all-prime window Hilbert vector and reciprocal-Stokes Cartier jet wall

- **ID:** `burnol-all-prime-window-hilbert-cartier-jet-wall-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-all-prime-window-hilbert-cartier-jet-wall.md` (same directory)

## Lean modules

| Module | Role |
|---|---|
| `GaloisForLFunctions.RHTower.BurnolAllPrimeWindowEnergy` | window energies, Hilbert membership, the four-way jet equivalence |
| `GaloisForLFunctions.RHTower.BurnolReciprocalStokesSewing` | reciprocal endpoint multiplier, sewn factor, sewn conormal, unsewing wall, `Q ∉ ℓ²` |
| `GaloisForLFunctions.RHTower.BurnolAllPrimeCompletionWall` | the completion identity and the sharp `ℓ²` wall |
| `GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindowSource` | the honest co-Poisson sub-window vector (input) |
| `GaloisForLFunctions.RHTower.EvenL2LogUnitary` | the reflection identity for the even split (input) |

## Formal theorem chain

1. `burnolPrimeWindow` — `(HJ1)`, `(HJ10)`: the source is literally the co-Poisson value of
   `[p⁻¹,1]`, not a detached coefficient sequence.
2. `lintegral_even_eq_two_mul_Ioi` — the even split used throughout.
3. `burnolPrimeWindowEnergy_lower`, `burnolPrimeWindowEnergy_upper` — **`(HJ2)`**:
   `2(p-1)²/p ≤ ‖G_p‖₂² ≤ 8p`.  The lower bound is the constant `1-p` below the window end; the
   upper bound splits the positive ray at `(2p)⁻¹` between `|G_p| ≤ 2p` and `|G_p(t)| ≤ t⁻¹`.
4. `burnolSummable_primeWindowSourceEnergy` — **`(HJ3)`**, `(HJ14)`: the weighted family
   `(A_p G_p)_p` with `A_p = 1/(p log p)` lies in the Hilbert direct sum, because the upper bound
   turns its energy into `8 ∑ 1/(p (log p)²)`.
5. `burnolAllPrimeInverseCompletionCoefficient_eq` — `(HJ18)`.
6. `burnolAllPrimeCompletion_mul_inverseCoefficient` — `(HJ21)`: `C_ρ U_ρ = V_ρ`.
7. `burnolCompletedConormal_mem_range_iff` — `(HJ22)`: diagonal-range admission of the completed
   conormal is square summability of the jet.
8. `burnolBddAbove_finsetSums_iff_summable` — the finite-truncation reformulation.
9. `burnolAllPrimeCartierJet_tfae` — **`(HJ5)`**: uniform boundedness of the finite jet energies,
   `U_ρ ∈ ℓ²`, `V_ρ ∈ ran C_ρ`, and `Re ρ ≤ 1/2` are one condition.
10. `burnolReciprocalEndpointMultiplier`, `burnolSewnWindowFactor`,
    `burnolSewnWindowFactor_reflection`, `norm_burnolSewnWindowFactor_le` — `(HJ7)`, `(HJ25)`,
    `(HJ26)`, `(HJ27)`: the sewn factor is `w ↦ 1-w` invariant and bounded by `6` on the closed
    strip.  The bound uses `p^w p^{1-w} = p` and `(p^σ-1)(p^{1-σ}-1) ≥ 0`, not a crude triangle
    inequality.
11. `burnolSummable_sewnConormal_sq` — **`(HJ8)`**, `(HJ28)`: the sewn conormal is square summable
    at every point of the open strip, unconditionally.
12. `burnolSewnConormal_unsewing_wall` — **`(HJ9)`**, `(HJ29)`: unsewing has domain exactly
    `Re ρ ≤ 1/2`.
13. `burnolNotSummable_primeLogGreenPotential_sq` — `(HJ23)`: the unique prime-log Green potential
    is not square summable, so the false ordinary closed-range route is closed.

## Verification

- `lake env lean` clean, no warnings, on each module.
- `lake build GaloisForLFunctions.RHTower` compiles them inside the area umbrella.
- `#print axioms` on the numbered theorems: `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `GaloisForLFunctions.RHTower`.
