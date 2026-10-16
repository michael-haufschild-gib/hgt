# CHMD: no Weyl sequences above the threshold; Lévy-symbol log growth; window localization (2026-10-16)

RH goal ACTIVE. Contribution 4 of this lane (after MUST-1541–1546). STATUS rows MUST-1547/1548.
Card: docs/drafts/pipeline/3-formalized/chmd-no-weyl-above-threshold-2026-10-16.md.

## Result (unconditional, Lean, standard axioms; 70 declarations in 4 modules, namespace RHTower.CHMDPolar)
- `CHMDLevySymbolLowerBound`: `levySymbol r := γ(r) − γ(0) = 2∫ω(1−cos rx) ≥ 0`;
  `gammaBracket_ge_log : 4 ≤ |r| → log(|r|/2) − 3/2 − log π ≤ γ(r)` via `WeilHerglotz.gammaBracket_eq`
  (γ(r) = Re ψ(1/4 + ir/2) − log π) and `HTGeometry.norm_digamma_sub_log_le_of_re_pos`;
  `levySymbol_ge_log_of_le : 4 ≤ T → T ≤ |r| → log(T/2) − levyConst ≤ levySymbol r`.
- `CHMDWindowFourierTail`: `levyForm g = ∫_{Ioi 0} ω(x)∫(g u − g(u+x))²`; `fourierSq g r = ‖paperFT g r‖²`;
  `levyForm_eq_fourier` (needs only ContDiff 2 + compact support; hintR built from `exists_normSq_paperFT_le`
  + `EvenSector.abs_gammaBracket_le_log` + `integrable_one_add_norm`); Plancherel `integral_fourierSq_eq`
  (corpus `integral_norm_sq_paperFT_eq`); `fourier_tail_le : (log(T/2) − levyConst) ∫_{highFreq T} fourierSq ≤ 2π levyForm`.
- `CHMDWindowLocalization`: `windowBump R hR : ContDiffBump 0` (rIn R+1, rOut R+2), `windowTest R hR v = χ v`;
  `exists_window_levyForm_bound : ∃ C ≥ 0, ∀ v C²-compact, levyForm (χv) ≤ C (phiDoobArchJumpEnergy v + ‖v‖²_μ)`.
- `CHMDNoWeylAboveThreshold`: `WeaklyNull e := ∀ k, ⟪e n, k⟫ → 0`; `weaklyNull_of_orthonormal`;
  `tendsto_inner_source_zero` (sources of graph approximants of Riesz(e_n) are weakly null);
  `massVec φ` (= φ/massDensity in L²(μ)) with `inner_compactLift_massVec : ⟪(compactLift w).fst, massVec φ⟫ = ∫ w φ dx`;
  `paperFT_ofReal_re_im`; `tendsto_fourierSq_windowTest` (pointwise Fourier decay along weakly null families);
  **`no_weakly_null_weyl_above_half : 1/2 < μ → unit, WeaklyNull, ‖Re_n − μe_n‖ → 0 → False`**;
  `weyl_value_le_half`; `no_orthonormal_eigenfamily_above_half`.

## Why it moves the frontier
With MUST-1546 (cusp escape is a weakly null unit Weyl family at level 1/2): Weyl spectrum of R ⊆ [0,1/2], 1/2 attained.
Spectrum above 1/2 (= off-line zeros in the CHMD dictionary RH ⟺ R ≤ 1/2 on even primitives) is Weyl-discrete.
Obtained WITHOUT the archimedean operator core the other CHMD cards were pursuing: the Doob form on a window
dominates the flat Lévy form, whose symbol is ≥ log by digamma asymptotics (CCM/Suzuki log-Sobolev compactness
mechanism, but done via dominated convergence + Plancherel instead of total boundedness).

## Next
1. Finiteness of spectrum ∩ (1/2+ε, 1] (needs Weyl-sequence extraction from the real spectrum of a bounded
   selfadjoint operator in Lean — mathlib lacks it; corpus `WeylSpectrumCompactTransfer` is over ℂ).
2. Birman–Schwinger: eigenvalues of R above 1/2 ↔ nonreal Xi orbits.
3. Even-sector version.

## Lean traps met
- `∫ r in S, f r + g` parses `+ g` INSIDE the integrand (body precedence 60 > `+` 65 captured); parenthesize sums of integrals.
- `(n : ℝ)` with unbound n makes `∀ᶠ n in atTop` quantify over ℝ — write `∀ᶠ n : ℕ in atTop`.
- `hgc.comp_left (g := fun y => y^2)` can whnf-time-out; use `hvc.mul_left` + funext `pow_two` rewrite.
- Passing `Integrable (fun r => fourierSq g r * γ r)` where the corpus wants the unfolded `‖paperFT …‖^2 * γ r`
  times out in the unifier — `unfold fourierSq at h` first.
- `integrableOn_const.mpr` does not exist in this toolchain; use `continuous_const.integrableOn_Icc` + `mono_set`.
- `integral_re` is stated with `RCLike.re`; `simp only [RCLike.re_to_complex] at h` then `show (∫ …).re = _`.
- `le_or_lt` gone → `le_or_gt`; `pow_le_pow_left` → `pow_le_pow_left₀`; `add_le_add_left ?_ _` gets stuck → `add_le_add le_rfl ?_`.
