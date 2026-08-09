# Formalized: Burnol all-prime completion and singular-potential entrance wall

- **ID:** `burnol-all-prime-completion-singular-potential-entrance-wall-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-all-prime-completion-singular-potential-entrance-wall.md` (same directory)

## Lean modules

| Module | Role |
|---|---|
| `GaloisForLFunctions.RHTower.BurnolAllPrimeCompletionWall` | the whole card |
| `GaloisForLFunctions.RHTower.BurnolPrimeLogSummability` | the two prime series and the two growth comparisons |
| `GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindowSource` | the honest prime-window Sonine vector (input) |
| `GaloisForLFunctions.RHTower.ZetaCarrier` | `xi = archFactor · zeta` (input) |

## Formal theorem chain

1. `nat_cpow_sub_one_ne_zero`, `burnolAllPrimeCompletionMultiplier_ne_zero` — `(AW1)`: the prime
   dilation factor and the multiplier are nonzero in the open strip.
2. `soninMellinEvaluation_primeWindow_eq` — `(AW2)`: the completed Mellin source
   `Γ_ℝ(w)(p^w-1)ζ(w)/w` is the Mellin evaluation of the honest co-Poisson sub-window vector of
   `[p⁻¹,1]`, not a detached formula.
3. `burnolAllPrimeCompletionMultiplier_mul_completedMellin` — `(AW3)`: `C_p F_p = ξ`.
4. `burnolAllPrimeCompletedMellin_eq_zero_of_xi_eq_zero`,
   `burnolAllPrimeCompletionMultiplier_mul_dslope_completedMellin` — `(AW5)`: the completion is
   coefficient-faithful on first divided vectors, including the confluent value at `s = ρ`.
5. `tendsto_burnolAllPrimeMultiplicityJet` — `(AW4)`: for every multiplicity `m`, the divided
   leading coefficient of `F_p` is `c_ρ / C_p(ρ)`.
6. `burnolPhysicalEndpointWeight_add_valuationShuttle` — `(AW7)`.
7. `burnolPrimeLogGreenPotential_mul_valuationShuttle` — `(AW9)`: `Q_p R_p = 1/(p log p)`.
8. `burnolSummable_sourceBoundary_sq` — `(AW10)`.
9. `burnolPrimeLogGreenPotential_mul_endpointResponse`,
   `burnolPrimeLogGreenPotential_physical_presentation` — `(AW11)`.
10. `burnolAllPrimeInverseCompletionCoefficient_eq` — `(AW13)`.
11. `summable_burnolAllPrimeInverseCompletionCoefficient_sq_iff` — **Theorem 1 / `(AW0)`**: the sharp
    wall, proved in both directions
    (`summable_..._of_re_le_half`, `not_summable_..._of_half_lt_re`).
12. `burnolSummable_allPrimePhysicalCorrection_sq` — `(AW15)`.
13. `burnolAllPrimePhysical_inverse_completion` — `(AW16)`.
14. `summable_burnolAllPrimePhysicalPresentation_sq_iff` — `(AW17)`: both presentations share the
    entrance wall.

The convergent side of `(AW0)` is an integer comparison with `∑ 1/(n (log n)²)`
(`burnolSummable_one_div_mul_log_sq`, proved by a telescoping comparison with
`1/log n − 1/log (n+1)`); the divergent side uses only `log² p = o(p^{2δ})`
(`burnolEventually_log_pow_le_rpow`) and Euler's `∑ 1/p = ∞`
(`burnolNotSummable_prime_one_div`).  No prime number theorem and no zero-density input occurs.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/BurnolAllPrimeCompletionWall.lean` — clean, no warnings.
- `lake build GaloisForLFunctions.RHTower` compiles the module inside the area umbrella.
- `#print axioms` on the numbered theorems: `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `GaloisForLFunctions.RHTower`.
