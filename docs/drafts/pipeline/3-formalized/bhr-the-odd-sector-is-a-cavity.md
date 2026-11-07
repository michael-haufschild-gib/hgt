# BHR — the mirror-odd sector of the horizon is a cavity

- **ID:** bhr-odd-sector-cavity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** continues `bhr-the-cusp-forms-of-the-modular-horizon-exist.md`.
- **Statement:** The mirror `z ↦ -z̄` acts on `L²` of the horizon as a unitary involution. Every mirror-odd
  datum is cuspidal, hence a superposition of cusp forms; for every datum `f`, `f - Mf` is cuspidal. The
  zeros of `ξ` couple only to the mirror-even half of the horizon.

## Paper proof
1. `ι = diag(-1,1) ∈ GL₂(ℝ)` acting on `ℍ`; the hyperbolic measure is `GL₂(ℝ)`-invariant; `ι` maps the
   cell to itself. So `Mf = f∘ι` is a unitary involution of `L²(cell)`.
2. `Im(M_{c,d} ιz) = Im(M_{-c,d} z)` (conjugation by `ι` maps the bottom row `(c,d)` to `(-c,d)`, and
   matrices with one bottom row differ by a translation). Reindexing the coprime rows, every incomplete
   Eisenstein series is `M`-even.
3. For odd `f` and an incomplete Eisenstein series `E`: `⟨E,f⟩ = ⟨ME,Mf⟩ = -⟨E,f⟩ = 0`; by continuity
   `f ⊥` the Eisenstein space, which is the cuspidal criterion of the corpus.

## Lean certificate
Module `formal/GaloisForLFunctions/BlackHoleRingdown/TheOddSectorIsACavity.lean`, wired into
`BlackHoleRingdown.lean`, `lake --old env lean` clean; axioms of `OddSector.hasSum_odd`,
`OddSector.sub_mirrorL2_mem_cuspidal`: `propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems |
|---|---|
| Mirror is `GL₂(ℝ)`, measure preserving | `OddSector.mirrorGL_smul`, `OddSector.measurePreserving_mirror_fd`, `OddSector.mirrorL2`, `OddSector.mirrorL2_mirrorL2` |
| Eisenstein series even | `OddSector.im_gammaSetMatrix_smul_mirror`, `OddSector.incEis_mirror`, `OddSector.mirrorL2_incEisL2` |
| Odd ⇒ cuspidal | `OddSector.inner_eisSpace_eq_zero_of_odd`, `OddSector.mem_cuspidalL2Closure_of_odd`, `OddSector.sub_mirrorL2_mem_cuspidal` |
| Cavity expansion | `OddSector.hasSum_odd` |

## Log
- 2026-11-07 — created and formalized.
