# BHR — the parity of the Hecke modes: strong multiplicity one

- **ID:** bhr-hecke-parity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** "Not formalized" item of `bhr-the-multiplicity-of-the-hecke-modes.md`.
- **Statement:** Let `ι z = −z̄`.
  1. `f ↦ f ∘ ι` preserves `S(λ)`, commutes with every `T_p`, and `a_n(f ∘ ι) = a_{−n}(f)`.
  2. For every `λ`, `(c_p)` and `ε`, the space of `f ∈ S(λ)` with `T_p f = c_p f` for all `p` and `f ∘ ι = εf` has
     dimension at most one.
  3. For every eigenvalue `λ` of the cusp spectrum there are `(c_p)` and `ε = ±1` for which this space is a line.

## Paper proof
1. In the chart `ι` is the reflection `R ζ = −ζ̄`, real-linear with `R1 = −1`, `RI = I`; second directional
   derivatives transform as `D_v D_v(G∘R) = D_{Rv}D_{Rv}G ∘ R`, and `D_{−1}D_{−1} = D_1D_1`, so the Laplacian commutes
   with `ι`. Invariance: `ι(gz) = g'(ιz)` with `g'` the mirror conjugate. `ι(pz) = p ιz`, `ι((z+b)/p) = (ιz − b)/p`, and
   `(ιz − b)/p = (ιz + (−b mod p))/p − [b ≠ 0]`, so periodicity and `b ↦ −b` give `T_p(f∘ι) = (T_pf)∘ι`. For the modes,
   substitute `x ↦ −x` and use `1`-periodicity of `e(nx)f(x+iy)`.
2. `a_{−1} = a_1(f∘ι) = εa_1`, so `f ↦ a_1` is injective by Hecke rigidity, into a space of dimension at most one.
3. For a Hecke eigenform `h` (`exists_heckeEigenform`), `h ± h∘ι` are Hecke eigenforms with the same eigenvalues and
   parity `±1`, not both zero.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheParityOfTheHeckeModes.lean`, wired into `BlackHoleRingdown.lean`, checked
with `lake --old env lean`, no messages. Axioms of `finrank_paritySpace_le_one`, `exists_parity_heckeMaassForm`:
`propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.HeckeCusp`) |
|---|---|
| (1) | `reflL`, `dir_dir_refl`, `isMaassEigenfunction_comp_mirror`, `sum_neg_residues`, `heckeH_comp_mirror`, `fourierCoeff_comp_mirror`, `comp_mirror_mem_cuspSpace` |
| (2) | `paritySpace`, `finrank_paritySpace_le_one` |
| (3) | `exists_parity_heckeMaassForm` |

## Scope
On the graph black holes Hecke separates cusp forms of one eigenvalue (`heckeTwo_separates`). On the modular horizon,
after fixing the Hecke eigenvalues and the parity, there is nothing left to separate: a cusp mode is a line determined by
`(λ, (c_p), ε)`. Whether different `(c_p, ε)` occur at one `λ` (simplicity of the cusp spectrum) is open.

## Log
- 2026-11-08 — created and formalized.
