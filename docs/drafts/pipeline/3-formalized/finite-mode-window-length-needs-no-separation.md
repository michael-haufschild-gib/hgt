# Finite-mode window length needs no separation

- **ID:** A95-finite-modes
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For distinct frequencies `γ_j≥Γ>0` and at least one nonzero coefficient, `Re Σ_{j<n}a_j exp(iγ_jt)` has a uniform negative excursion on every interval of length `L>nπ/Γ`. Adding a remainder tending to zero preserves these excursions on all late intervals of the same length.

## Proof

Twice the real trace has positive-frequency coefficients `a_j` and negative-frequency coefficients `conj(a_j)`. Bohr coefficient extraction prevents it from vanishing identically, including after any phase rotation. Half-period deletion prevents nonnegativity throughout `[0,L]` when `ΓL>nπ`.

On the compact phase torus, the open sets admitting a value below `−ε` form a directed cover as `ε` decreases to zero. A single positive `ε` works for every phase. Translation of the original trace is a phase rotation, proving the uniform interval claim. A remainder tending to zero costs at most half this margin eventually.

## Formalization

- Module: `SurfaceOfSpecZ/ScaleLocality/FiniteModeWindowLength.lean`.
- Theorems: `finite_spectrum_negative_in_every_window`, `finite_spectrum_negative_windows_of_remainder`.
- Direct `lake --old env lean` audit passed; transitive axioms are `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `SurfaceOfSpecZ.lean`.

## Finite top layers

`SurfaceOfSpecZ/ScaleLocality/FiniteTopLayersNeedNoSeparation.lean` pairs conjugate top exponents and applies the uniform finite-mode theorem. For zeta, every positive-depth active ordinate exceeds the verified height 67. At most `k` top quartets therefore give negative normalized excursions in every late interval of length `(k+1)π/67`, without a separation assumption. Exponential rescaling makes every fixed raw-trace floor fail on every sufficiently late interval of the same length.

- `topTrace_eq_positive_sum`, `finite_top_negative_in_every_window`.
- `zeta_finite_top_negative_windows`, `zeta_finite_top_breaks_every_floor`.
- Direct Lean check passed; axiom audit omitted as requested. Imported by `SurfaceOfSpecZ.lean`.
