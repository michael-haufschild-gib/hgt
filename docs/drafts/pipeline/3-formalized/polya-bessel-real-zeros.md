# Pólya's theorem: K_ν(a) vanishes only at purely imaginary orders

- **ID:** POLYA-BESSEL-REAL-ZEROS
- **Stage:** 3-formalized
- **Parent:** `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, cycle 88
- **STATUS:** MUST-610

## Theorems [L]

Module `formal/GaloisForLFunctions/HTGeometry/BesselOrderPolyaRealZeros.lean` (wired in `HTGeometry.lean`, standard axioms).

- `re_eq_zero_of_modifiedBesselKOrder_eq_zero`: for `a > 0`, `K_ν(a) = ∫₀^∞ e^{−a cosh t}cosh(νt)dt = 0` ⇒ `Re ν = 0`.
- `im_eq_zero_of_modifiedBesselKOrder_I_mul_eq_zero`: `z ↦ ∫₀^∞ e^{−a cosh t}cos(zt)dt` has only real zeros.
- Supporting lemmas:
  - `hasDerivAt_modifiedBesselKOrder_arg(_succ)` — the system `f' = (ν/x)f − g`, `g' = −f − ((ν+1)/x)g`;
  - `hasDerivAt_besselEnergyFlux` — `h' = ν²|f|²/x + x(|f|²+|f'|²)` for `h = x f' f̄`;
  - `norm_modifiedBesselKOrder_le_exp` — `‖K_ν(x)‖ ≤ e^{1−x}B(ν)`;
  - `eventually_re_modifiedBesselKOrder_pos` — `Re K_ν(x) > 0` for large `x`.

## Mechanism (Hilbert–Pólya in miniature)

Zeros of `K_{iz}(a)` are the eigenvalues `z²` of the positive operator `−x(x f')' + x² f` on `L²((a,∞), dx/x)` with a Dirichlet condition at `a`. The energy identity is the self-adjointness computation. Integrating it from `a` to `∞` (exponential decay, a nonvanishing point) forces `ν²` to be real and negative.

## Relation to RH

This is the real-zero mechanism behind Pólya's approximation of Riemann's `Φ`. The corpus reasons why the mechanism does not extend to `ξ`:
- `ξ`'s kernel is a sum over `n` of Bessel-type terms with different scales `πn²`.
- No single Sturm–Liouville problem in an auxiliary variable carries `ξ` as a boundary value. The Eisenstein/resonance version is the retired HB route.

## Addendum (cycle 90): the Pólya–Bessel kernel in the de Bruijn heat class [L]

Module `R:PolyaBesselHeatKernel`.

**Statements.**
- `superExpKernel_polyaKernel`: `e^{−a cosh x}` is a `SuperExpKernel`.
- `cosTransform_polyaKernel`: its transform is `2K_{iz}(a)`.
- `polyaKernel_mul_cosh_pow_zeros_real`: `e^{−a cosh x}cosh(λx)^j` has a real-rooted transform for all `λ > 0` and `j`.
- `polyaKernel_heat_zeros_real`: `e^{−a cosh x}e^{tx²}` has a real-rooted transform for every `t > 0`.

**Consequence.** The de Bruijn–Newman constant of the Pólya–Bessel kernel is `≤ 0`, while Riemann's kernel has `Λ ≥ 0` (corpus Newman theorem).

**Open question, recorded for the loop.** Is the Pólya–Bessel constant strictly negative? A paper heuristic says yes: the zeros form a single-sine picket fence, and small backward heat only shifts the phase. If so, Newman's `Λ ≥ 0` is an arithmetic phenomenon: the multi-term Riemann–Siegel structure decides it, not the leading theta term.
