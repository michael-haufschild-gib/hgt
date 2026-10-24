# Transport in aperture as a renormalization flow: the shell-flux law of the ground energy

- **ID:** `aperture-rg-flow-shell-flux-2026-10-24`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2410/fable.md` §2.3 opening D (AOT, ACCE, ACT); ACT README open
  problem 7, ACCE README open problem 6, AOT README open problem 7.
- **Statement:** the restricted Weil ground energy `μ(A)` is an exact renormalization flow: each
  step is the shell flux of the smaller ground state read by the larger one, the flux never
  vanishes, the flow is strictly decreasing and crosses zero at most once (before the visibility
  aperture of any near-top zero), and its arithmetic part is the cross-collar correlation of the
  prime powers with `log n` in the shell `(2a, 2b]`; a relative flux law is RH and fails along
  every one-prime perturbation (Class III).

## Goal
Opening D asks for (i) the beta function of `A ↦ μ(A)` as a boundary-shell flux, (ii) a
sign-definite jump, (iii) the Class III nature of the beta function, (iv) the relative form of any
flux law compatible with the doubly exponential ceiling, (v) the first rung. The corpus had the
gauge-level identity for a fixed test and the telescoping of jumps, but no identity for `μ` itself.

## Results and Lean declarations
Module paths are under `formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/`.
`F` is any `CCMRemainderFamily` (literal ζ, prime-deleted, prime-inserted, countably perturbed,
prime-free), `u_a` its normalized ground state, `Φ_{a,b}(v) = form_b(ext u_a, v) − μ(a)⟨J ext u_a, Jv⟩`.

`TheApertureFlowIsAShellFlux` (every family):
1. Euler–Lagrange `form_a(u_a, w) = μ(a)⟨Ju_a, Jw⟩`: `shiftedForm_eq_zero_of_isGround`.
2. Polarized aperture compatibility: `apertureForm_ext`.
3. Shell support `Φ_{a,b}(ext w) = 0`: `shellFlux_ext_eq_zero`.
4. Flux law `Φ_{a,b}(u_b) = (μ(b) − μ(a))⟨J ext u_a, J u_b⟩`: `shellFlux_ground_eq`,
   `energy_sub_eq_shellFlux_div`.
5. Jump = relaxation `μ(a) − μ(b) = Re h_b(ext u_a − c u_b)`, flat step iff `ext u_a` is ground,
   then `Φ ≡ 0`: `energy_sub_energy_eq_shiftedForm`, `isGround_ext_iff_energy_eq`,
   `shellFlux_eq_zero_of_energy_eq`; bundle `apertureFlow_isShellFlux`.

`TheApertureFlowNeverStalls` (literal ζ):
6. Full translation invariance (polar characters `e^{∓h/2}` cancel):
   `ccmRestrictedWeilSourceQuadratic_translate_full`, `apertureForm_literal_translate`.
7. No non-radiating eigenvector for `a < b`, any eigenvalue: `not_isFormEigen_apertureExt`
   (translates + finite `ker(1 − K)` of the compact Birman–Schwinger pencil + `L²` translate
   independence).
8. `exists_shellFlux_ne_zero`, `strictAnti_ccmRestrictedWeilGroundEnergy`,
   `shiftedForm_ext_ground_pos`, `riemannHypothesis_iff_ccmRestrictedWeilGroundEnergy_pos`,
   `riemannHypothesis_or_unique_groundEnergyCrossing`; bundle `apertureFlow_neverStalls`.

`ThePrimeShellBetaFunction`:
9. Frozen-prime family (`frozenFamily N`, primes `n ≤ N`), equal to ζ below the cutoff:
   `frozenFamily_Q_eq`, `frozenFamily_energy_eq_of_floor_le`.
10. Two-step law with `N = ⌊e^{2a}⌋`: geometric relaxation of the frozen flow plus the arithmetic
    jump bracketed by shell correlations: `primeShell_sandwich`,
    `apertureFlow_step_eq_geometric_add_arithmetic`.
11. Shell correlation = von Mangoldt sum at shell lags, reading only the collars
    `[−c, c − 2a]`, `[2a − c, c]`: `primeShellCorrelation_eq_primeSum`,
    `inner_logTranslation_eq_collar`, `primeShellCorrelation_eq_collar`,
    `primeShellCorrelation_eq_of_collars_eq`.
12. Class III: relative law with nonnegative factors iff RH; fails for every insertion
    `x ≥ 2, w ≠ 0`: `relativeFluxLaw_isClassIII`.
13. Ceiling: no law `μ(b) ≥ e^{−C(b − a₀)} μ(a₀)` with `μ(a₀) > 0`: `not_exponential_relative_law`.
14. First rung: graded relaxation bound ⟹ `zetaZeroWidth ≤ σ`: `zetaZeroWidth_le_of_graded_relaxation`.
15. Off-line near-top zero ⟹ unique crossing `a* ≤ V/2 + w`: `groundEnergyCrossing_le_visibility`.
16. Synthesis: `apertureRenormalizationFlow`.

Axiom audit (`#print axioms`, all items above): `propext`, `Classical.choice`, `Quot.sound` only.

## Correction to the opening's heuristic
The beta function is not the flux of the primes with `log p ∈ (2A, 2A + dA)` alone. The exact step
is the residual of the smaller ground state on the shell (item 4); the primes newly entering the
shell contribute only through the arithmetic jump of item 10, and they read the ground state only
on the two collars (item 11). The geometric jump at frozen primes is a separate, nonnegative term.

## What remains open
The Class III estimate: a bound on the arithmetic jump (or the shell flux) of the actual ground
state relative to `μ`, from an input that does not presuppose the floor. By item 12 the relative
form is RH; by item 14 the graded form gives a zero-free strip. Neither is proved.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: three modules checked with `lake --old env lean`, axiom audit PASS
- [ ] 3 → 4  publication-ready

## Log
- 2026-10-24 — created; results proved on paper and formalized in the three modules above.
