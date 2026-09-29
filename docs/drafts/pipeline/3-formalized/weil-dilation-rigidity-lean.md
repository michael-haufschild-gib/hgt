# Weil positivity forces the functional equation at the zeros (dilated von Mangoldt weights)

**Stage:** in progress (paper proof complete, loop L80; Lean in progress).
**Goal (Lean, unconditional):** if `Λ⋆(δ₁ + b)` is Weil-positive for a finitely supported real `b`, then `Im B(½+iγ) = 0` at every zero `½+iγ` of `ζ` on the critical line, where `B(s) = Σ b(m) m^{−s}`. After the density step: `b = 0`.

## Modules
- **A. `WeilDilationPrimeSumLine`**: `Σ_n (Λ⋆b)(n) n^{−½} k(log n) = (1/2π)∫ B(c+it) H_k(c+it) (−ζ'/ζ)(c+it) dt`, for `k ∈ C_c²` and `c ∈ (1, 3/2]`. Source: Zeta23 `prime_side_line` applied to the translates `k(· + log m)`, using `H_{k(·+log m)} = m^{½−s} H_k`.
- **B. `WeilDilationCriticalLineShift`**: for the twist tests `F = twistTest 0 τ₀ R S`, split `H = H_rad + H_err` with `H_rad` built from `radicalLimit`, which vanishes at every nontrivial zero (Riemann kernel, `riemannPhiTransform_eq_zero_of_nontrivial`).
  - `H_rad·B·ζ'/ζ` is analytic on `½ ≤ Re s ≤ c`: the pole at `s = 1` is killed by the polar-free bump.
  - Shift it to `Re s = ½` with Zeta23 `vertical_line_shift`.
  - `H_err` is super-exponentially small on `Re s = c`.
- **C. `WeilDilationTangentCriterion`**: spread-probe concentration plus the `ζ` zero-side bound `O(S^{10}e^{−S})` (`exists_norm_W_twistTest_log_le`) give `|ξ(½+iτ)|² Re(B(½+iτ)(−ζ'/ζ)(½+iτ)) ≤ 0` for every `τ`.
- **D. `WeilDilationResidueRealness`**: near a zero of Hardy's `Z` of order `m`, the continuous function in C is `−c·m·Im B·(τ−γ)^{2m−1} + O((τ−γ)^{2m})`, which changes sign unless `Im B(½+iγ) = 0`.
- **E (density, later).** Either the L51b division tests at off-line zeros (`1 + B(ρ) = 0`) plus Riemann–von Mangoldt (Zeta23 `RvM`) against Jensen for `B(s) − B(1−s)`, or Selberg's positive proportion.

## Status
- A–D: DONE (Lean, standard axioms), in `RHTower.WeilDilationCriticalLineShift` and `RHTower.WeilDilationResidueRealness`. Card: `3-formalized/weil-dilation-residue-realness.md`.
- E (density, giving `b = 0`): open in Lean. Options: Selberg's positive proportion, or the L51b division tests plus Zeta23 RvM plus Jensen for exponential sums.

## Final status (E closed)
- E (density): DONE in `RHTower.WeilDilationRigidity`. The Mellin test `Σ b(m)(h(mx) − h(x/m)/m)` has critical-line Mellin transform `2i·Im B·Mh`. It is fed to the corpus bounded-support uniqueness engine, which runs on the unconditional superlinear density of simple critical zeros (Alpöge–Furman via Zeta23).
- Headline: `dilatedVonMangoldt_eq_zero_of_weilPositive`, with standard axioms.
- **Stage:** formalized.
