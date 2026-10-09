# The Lee–Yang zero-gap law, and why integers cannot be Lee–Yang fields of Ξ

- **ID:** `lee-yang-zero-gap-law`
- **Stage:** 3-formalized material on a 1-in-progress card (MUST-824)
- **Type:** `[THEOREM + ROUTE KILL]`
- **Parents:** MUST-806 (prime-field stability no-go), MUST-819 (resolution law), MUST-820 (Γ-site chain), MUST-823 (quarter-turn count for chains).

## Statement
- **Abstract law.** Let `a, b` be entire, with `a ≠ 0` and `|b| ≤ |a|` on `Im z < 0`, and `|b| = |a|` on `ℝ`. Let `λ > 0`. Then `a + b e^{−iλt}` has a real zero in every interval `[t₀ − π/λ, t₀ + π/λ]`.
- **Lee–Yang data.** For a Lee–Yang datum (corpus `LeeYangDatum`) affine in the field `u_j`, the restriction `P(e^{−iλt})` has a real zero in every interval of radius `π/λ_j`. The real zero gaps are at most `2π/λ_j`.
- **Kill.** Lee–Yang restrictions affine in a field of frequency `≥ log 2` never converge to `E·Ξ` uniformly on `[−π/log 2, π/log 2]`. Ξ is zero-free for `|t| ≤ √32`.

## Proof
1. Suppose there is no zero in the window. Then `a ≠ 0` there, `w = b e^{−iλt}/a` has `|w| = 1` and `w ≠ −1`, so `ψ = arg w` is differentiable.
2. Below the axis, `|w(t − is)| ≤ e^{−λs}`. The slope of `s ↦ |w(t − is)|²` at `0⁺` equals `2 Im(conj(w) w') = 2 Im(w'/w)`, and it is `≤ −2λ`.
3. By the mean value theorem, `ψ(t₀ + π/λ) ≤ ψ(t₀) − π` and `ψ(t₀ − π/λ) ≥ ψ(t₀) + π`. Both cannot hold in `(−π, π]`.
4. **Datum instance.** Write `P = A + u_j B` (degree ≤ 1 in `u_j`).
   - Inside the polydisk, stability gives `A ≠ 0`, and a root `−A/B` inside the disk is impossible, so `|B| ≤ |A|`.
   - Outside, the reflection identity on the line through `u_j` gives `A + yB = yU conj Q₀ + U conj(Q₁ − Q₀)`. Hence `B = U conj Q₀ ≠ 0`, and a root `|y| > 1` is impossible, so `|A| ≤ |B|`.
   - On the torus, continuity gives `|A| = |B|`.
5. **Translation.** `a(· + t₀)` and `b(· + t₀)e^{−iλt₀}` satisfy the same hypotheses.

## Reading
- Lee–Yang fields that are integers (`n^{−it}`, `p^{−it}`) force a real zero every `2π/log n` or less. Ξ's opening gap `(−γ₁, γ₁)` therefore forbids any field with `|log q| ≥ π/γ₁ ≈ 0.2223`.
- So arithmetic cannot enter a stability producer of Ξ through its fields, on any graph. It can only enter through couplings among slow fields.
- This is the exact Lee–Yang form of "integrality enters only through the couplings" (compare the Weil-cone integrality hints, ZIPM).
- Novelty: the boundary-phase monotonicity of inner splittings is classical (Hermite–Biehler, Schur functions). The window form for Lee–Yang data and the kill of integer-anchored stability producers on every graph are corpus-new.

## Lean
- `RHTower/LeeYangFirstZeroLaw.lean`: `im_deriv_div_le`, `exists_zero_of_innerSplit`, `exists_zero_of_innerSplit_near`.
- `RHTower/LeeYangDatumFirstZero.lean`:
  - split: `eval_update_affine`, `degreeOf_dualPoly_le_one`, `restr_eq_split`, `splitA_ne_zero_and_norm_splitB_le`, `eval_update_reflect`, `norm_splitA_le_norm_splitB`, `norm_splitB_eq_norm_splitA`;
  - zeros: `exists_restr_eq_zero`, `exists_restr_eq_zero_near`;
  - kill: `not_tendstoUniformlyOn_leeYang_XiC`.
- All checks: direct `lake env lean` with zero messages, targeted `lake build --old`, standard axioms only. Wired after `GammaSiteLeeYangChainXiObstruction`.

## Log
- 2026-10-08: created and formalized (loop row 558).

## C559 — field-density budget (paper, 2026-10-08, loop row 559)
**Theorem [P].** Let `L` be a Lee–Yang datum, multiaffine in every field. For every `T > 0` and every `0 < ε`, the zeros of the restriction in `(0, T]`, counted with multiplicity, number at least `Σ_j ⌊(λ_j − ε)T/2π⌋`. In particular they number at least `Σ_j ⌊λ_jT/2π⌋` when no `λ_jT/2π` is an integer.

**Proof.** Induct over the fields, lowering `λ_n` to `ε` inside the same datum (frequencies stay positive, so no specialization or degeneration occurs).
- Split at `u_n`: `f_μ = a + b e^{−iμt}`, where `a` and `b` do not depend on `μ` and satisfy the inner-split hypotheses (`splitA_ne_zero_and_norm_splitB_le`, `norm_splitB_eq_norm_splitA`).
- On `ℝ`, `|a| = |b|` forces equal vanishing orders. So `g = b/a` extends analytically and unimodularly across the common zeros `C`, and its lift `φ_g` is non-increasing (boundary-slope lemma with `λ = 0`).
- With multiplicity, `N(f_μ) = m(C) + #{π + 2πℤ ∩ [φ_g(T) − μT, φ_g(0))}`, because the crossings of the strictly decreasing `φ_g − μt` are simple. Hence `N(f_λ) ≥ N(f_ε) + ⌊(λ − ε)T/2π⌋`.

**Corollary (Γ-criticality) [P].** Every Lee–Yang producer of `Ξ` that is uniformly close on `[0, T]` satisfies `Σ_j ⌊λ_jT/2π⌋ ≤ N_Ξ(T) = (T/2π)(log(T/2π) − 1) + O(log T)`.
- For the field measure `ν = Σ δ_{λ_j}` this reads `∫_{λ>2π/T} λ dν ≤ log(T/2π) + O(1)`.
- The Γ convergence factors `log(1+1/m)` saturate it: `Σ_{m≥M} ⌊Y log(1+1/m)⌋ = Y(log Y − 1 + γ − log M) + O(√Y)` with `Y = T/2π`. They pass exactly when `M ≥ 2`; `M = 1` fails by `γY`.
- Fields `c·log(1+1/m)` with `c > 1` fail at large `T`.
- Reading: the archimedean `Γ(s/2)` density is the maximal Lee–Yang field density compatible with `Ξ`. This is the Lee–Yang form of "no slack". MUST-819 gives the matching lower bound (many slow variables are needed). A Lee–Yang producer of Ξ must be Γ-critical, with the arithmetic entirely in the couplings.

**Lean status (2026-10-09, row 606).** Formalized, standard axioms: `RHTower/LeeYangSplitCountDifference` (`LeeYangSplitCount.zeroCount_sub_ge`: exact single-split count difference via the rectangle argument principle; no phase lift or common-zero factorization needed) and `RHTower/LeeYangFieldDensityBudget` (`LeeYangDatum.sum_floor_le_zeroCount`, `sum_ceil_sub_one_le_zeroCount`). The Γ-criticality corollary still needs Hurwitz on a complex neighbourhood (paper).
- 2026-10-09: C559 formalized (row 606); MUST-824 addendum.
