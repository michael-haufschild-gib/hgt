# Formalization certificate — `ccm-growing-aperture-mellin-determinant-transfer`

- **Card:** `ccm-growing-aperture-mellin-determinant-transfer.md`
- **Stage:** 3-formalized
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMGrowingApertureMellin.lean`
- **Namespace:** `GaloisForLFunctions.RHTower`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on every declaration
- **Build:** `lake build GaloisForLFunctions.RHTower.CCMGrowingApertureMellin` — success

## Certified statements

New in `CCMGrowingApertureMellin` (15 theorems / 1 definition):

- `apertureEvalNormSq`, `integral_aperture_rpow` — equation `(3)` off the real axis: the squared
  operator norm of Mellin evaluation at `z = x + iy` on `I_λ = [λ⁻¹, λ]` with the multiplicative
  Haar measure is `∫_{λ⁻¹}^{λ} u^{2y-1} du = sinh(2y log λ)/y`.
- `integral_aperture_inv` — equation `(3)` on the real axis: the value is `2 log λ`.
- `sinh_div_self_strictMonoOn` — the missing quotient monotonicity: `u ↦ sinh u / u` is strictly
  increasing on `(0,∞)`.  Proved from `RHTower.sinh_lt_mul_cosh` via `strictMonoOn_of_deriv_pos`.
- `apertureEvalNormSq_eq`, `apertureEvalNormSq_mono`, `two_log_le_apertureEvalNormSq` — equation
  `(4)`: the squared evaluation norm is increasing in the substrip height, so the supremum over
  `|Im z| ≤ a` is attained at `|y| = a`, and it dominates the on-axis value `2 log λ`.
- `sq_modulus_cos`, `normSq_cos_mul` — the even representing function `cos(zt)` has squared
  modulus exactly `(cosh(2yt) + cos(2xt))/2`, both as a real identity and as the complex norm.
- `integral_cosh_symm`, `integral_cos_symm`, `evenAperture_normSq` — equation `(8a)`: the even
  squared norm on `[-L, L]` is `sinh(2yL)/(2y) + sin(2xL)/(2x)`.
- `evenAperture_growth` — the hyperbolic term of `(8a)` is at least `(λ^{2y} − 1)/(4y)`, so the
  exact CCM parity removes no power from `(5)`.
- `tendsto_evalTransfer` — equations `(5)`–`(8)`: a `λ^a`-bounded evaluation norm against a
  difference that is `o(λ^{-a})` gives a vanishing Mellin difference.
- `tendsto_rpow_mul_of_le` — `(7) ⇒ (5)` and `(12c) ⇒ (12b)`: an `O(λ^{-b})` quantity beats every
  power `λ^e` with `e < b`.
- `tendsto_rpow_mul_of_sq` — `(12b) ⇒ (5)`: a quadratic Rayleigh-excess bound `d² ≤ 2q` upgrades
  the form-level rate `λ^{2a} q → 0` to the projective vector rate `λ^a d → 0`.
- `ccmZeroFiber_energy_isLittleO` — equation `(14a)`: for a real-zero determinant family the
  horizontal defect energy is identically zero, hence `o((log N)²)`; the metric gate of
  `finite-prime-logarithmic-boundary-transfer` is discharged.

Reused from the existing tree, not rebuilt:

- `RHTower.self_lt_sinh` (`LegStripSteepness`).
- `RHTower.sinh_pos_of_pos`, `RHTower.sinh_lt_mul_cosh` (`CothInfra`).
- Mathlib's `Real.one_lt_cosh`, `integral_rpow`, `integral_inv_of_pos`.

## Deliberately outside the Lean statement

The CCM closed finite-Weil form and its self-adjointness; the regularized determinant identity
`(2)`; the Davis–Kahan residual bound `(10)`; the Rayleigh-excess inequality `(12a)`, which is the
subject of its own card `ccm-rayleigh-excess-determinant-transfer`; the prolate-seed Mellin
convergence of Connes–Consani–Moscovici; and Rouché/Hurwitz zero preservation.  These are cited
parents of the card.

The card's two declared open cores — large-aperture simple-evenness of the true finite-Weil ground
state, and the source-specific residual estimate `(11)` — are open research targets, not statements
the card proves; they are correspondingly absent from the Lean module.
