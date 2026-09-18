# Unconditional linear bound for the horizontal displacement of the zeta zeros

- **ID:** OFFLINE-MOMENT-002
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `3-formalized/zeta-off-line-first-moment-mollified-ceiling.md` (the `(L)` ceiling) ·
  `1-in-progress/levinson-critical-proportion-programme.md` Brick 5bz · weekly leads report
  (Najnudel–Nikeghbali `H(T)`, `docs/reports/This week produced one extraordinary but.md`)
- **Statement:** There is a real constant `C` such that for all large `V`
  `Σ_{ρ : ξ(ρ)=0, ½ < Re ρ < 1, 0 ≤ Im ρ ≤ V} m(ρ) (Re ρ − ½) ≤ C · V`.
  Lean: `RHTower.ZetaGateProductAFE.exists_eventually_offLineMoment_le_mul :
  ∃ C : ℝ, ∀ᶠ V in atTop, offLineMoment V ≤ C * V` (`ZetaGateProductAFEDyadicLaw.lean`), axioms
  `propext, Classical.choice, Quot.sound` only.

## Goal
This is Najnudel–Nikeghbali's `H(T) = O(T)` (their Lemma 8.4, classically Selberg 1946 / Littlewood)
and the corpus gate `(L)` of the phase-locking lane, now with **no hypothesis at all**: the whole
chain gate → two-thirds proportion → `(L)` ceiling of `OFFLINE-MOMENT-001` has been closed at the
bottom by an unconditional mollified mean square of `ζΨ` on the displaced line
`σ₀ = ½ − R/log U`. It is the first zero-density-type statement about `ζ` in the corpus (and, to
our knowledge, in any proof assistant): the multiplicity-weighted horizontal displacement of the
zeros grows at most linearly in the height.

The constant is crude (the assembly keeps every envelope constant symbolic), so the theorem does
not touch RH: `(L)` needs `o(V)`, and Brick 5bz's sharpening lane (`C ↓ (log c₁ − 5R/3)/4π`) is
where the constant lives. What is new relative to the corpus is that the mean-square gate
`ZetaMollifiedMeanSquareGate R c` is now a theorem for every `R > 0`
(`exists_zetaMollifiedMeanSquareGate_productAFE`), so all consumers of the gate are unconditional.

## Gates
- [x] 0 → 1  in-progress: Brick 5bz plan (product AFE, block windows, diagonal identification)
- [x] 1 → 2  fully-proven: the assembly plan on the Levinson card, corrected twice (free dual
  split `V`, constant of the carrier bound uniform in `d`)
- [x] 2 → 3  formalized: nine modules `ZetaGateProductAFE*` (wired in `RHTower.lean` after
  `ZetaGateFromDyadicMeanSquare`), `lake build` of the chain green, axioms clean
- [ ] 3 → 4  not pursued (user directive: no manuscripts)

## Approach (as formalized)
For a block `[a, v]`, `U^{1/8} ≤ a ≤ v ≤ 2a ≤ 2U`, with `u = a^{1/100}`, window
`w = blockWindow a v (u^95)`, product-AFE scale `x = a`, mollifier
`Ψ = Σ_{n ≤ N} (b_N(n)/log N) n^{-s}` (Barban–Vehov), `N = ⌊U^{1/100}⌋`:

1. **Block identity** (`ZetaGateProductAFEBlockExpansion.integral_window_normSq_eq`):
   `∫ w ‖ζΨ‖² = Σ_{h,k} b_h b_k (Σ'_P directTerm + Σ'_P dualTerm − residueTerm)` from
   `riemannZeta_mul_eq_productAFE` at `(s₁, s₂) = (σ₀+it, σ₀−it)`, `‖ζΨ‖² = ζΨ · conj(ζΨ)`, and
   the interchange `∫ Σ' = Σ' ∫` with the majorants of the cutoff and of the dual carrier weight.
2. **Diagonals** (`ZetaGateProductAFEDiagonalIndex`, `…BlockBound`): `h = g h'`, `k = g k'`;
   the direct diagonal `(m+1)h = (n+1)k` is `{((j+1)k'−1, (j+1)h'−1)}` and sums to
   `(hk)^{-σ₀}(h'k')^{-σ₀} smoothDiagonal σ₀ (h'k') x · ∫w`; the dual diagonal sums to
   `(hk)^{-σ₀}(h'k')^{-(½+d)} ∫ w · dualDiagonal`. Off the diagonals the term norms are exactly
   `directOffDiagTerm` / `dualOffDiagTerm` of the envelope modules.
3. **Main terms and cancellation** (`…BlockBound.blockPair_eq`, `…BlockInequality`):
   `smoothDiagonal = ζ(2σ₀) + res₁ + left₁`, `dualDiagonal = χχ ζ(1+2d) + res₂ + left₂`; the two
   residues cancel with the gcd coefficients (`smoothDiagonalShiftedResidue_add_dual_cancel`);
   `ζ(2σ₀) < 0` (`riemannZeta_real_strip_neg`), `∫w ≥ 0`, `S₁ = Σ a_h a_k gcd^{2σ₀}(hk)^{-2σ₀} ≥ 0`
   (`sum_gcd_rpow_div_nonneg`) drop the direct main term; the dual main term is
   `S₂ ‖ζ(1+2d)‖ ‖∫ w χχ‖` with `S₂ = Σ a_h a_k gcd^{1+2d}/(hk) ≤ C_L² N^{2d} 64(1+log N)/log²N`
   (`sum_barbanVehov_gcd_rpow_div_le`), `‖ζ(1+2d)‖ ≤ 3/2 + 1/(2d)`, `‖χχ‖ ≤ e (t/2π)^{2d}`.
   Result: `∫ w ‖ζΨ‖² ≤ S₂ ‖ζ(1+2d)‖ ‖∫wχχ‖ + Σ_{h,k} |b_h b_k| ‖pairError‖`.
4. **Envelopes with the block parameters** (`…HighBlockPieces`): direct `(A,K) = (20,38)`:
   `≤ W·const/u^{1306}`; dual split `K = 20, K'' = 40, V = u^5, Y₀ = u^{110}`:
   `≤ W·const/u^{190}`; left lines `≤ W·(K₁ + 2K₂(1+a−η)^{2d})/u^{21}`; residues
   `≤ W·576e/u^{300}`; `W = v − a + 2u^{95}`. Summed over `N² ≤ u^{16}` pairs: `≤ W·K/u^5`.
5. **High blocks** (`…HighBlock.exists_highBlock_bound_productAFE`): with `d log U ∈ [R, 2R]`,
   `N^{2d} ≤ e^{R/25}`, `(3U)^{2d} ≤ 2e^{4R}`, `(1+log N)/log²N ≤ 400/log U`, `1/(2d) ≤ log U/2R`:
   main `≤ W (200 M_R/R + 600 M_R/log U)`, `M_R = 128 e C_L² e^{R/25+4R}`; error
   `≤ W K U^{-1/160}`; `2u^{95}(c₀+ε) ≤ εa/2`. Hence `∫_a^v ‖ζΨ‖² ≤ (c₀+ε)(v−a) + εa`.
6. **Dyadic law, gate, ceiling** (`…DyadicLaw`): low blocks by
   `integral_normSq_zeta_mul_edPoly_crude` (`U^{129/200} ≤ εU/log U`); `d ≤ 1/8` from
   `log(U−1) ≥ 8R`; `zetaMollifiedMeanSquareGate_of_dyadicLaw`;
   `eventually_offLineMoment_le_of_zetaGate_twoThirds` at `R = 1`.

Corrections to the built bricks made on the way: `exists_norm_integral_blockWindow_dualCarrierWeight_le`
(split at `(p−η)/2`) replaced by a free split `V` (`ZetaGateProductAFEDualSplit`); its constant
was `d`-dependent (from `exists_norm_chiCarrier_le hd hdq`) and had to be made uniform in
`d ∈ (0, ¼]` (`exists_norm_zetaChi_le_negative_strip_uniform`, compactness on
`[−¾, −½] × [−2, 2]`) because `d = R/log U → 0` inside the dyadic law. Two duplicate theorem
names in `SmoothDiagonalContour.lean` (`norm_riemannZeta_le_of_two_le_re`,
`norm_smoothAFEGaussianKernel_eq`, colliding with `ZetaStripPolynomialBound` and
`HighBlockDualWeightVariation`) were renamed with suffixes; they made the consumer chain and the
block chain unimportable together.

## Novelty and significance
Classical (Selberg 1946; Najnudel–Nikeghbali 2026 Lemma 8.4 restates it); new in Lean, not new
mathematics. Its value for the programme is structural: every corpus theorem conditioned on
`ZetaMollifiedMeanSquareGate` is now unconditional, and the sharpening of the gate constant
(Brick 5bz's original target, Conrey's `θ = 4/7` values) is the only open item between the corpus
and the sharp `(L)` ceiling `0.0535 V`. `o(V)` — RH's `(L)` — is not reachable this way
(CANNOT-364, the cluster blindness of one-point laws; the mollified mean square has a positive
floor, `steinhaus-jensen-floor`).

## Log
- 2026-09-18 — Brick 5bz assembly: nine modules built, wired, axiom-clean; card created at stage 3.
