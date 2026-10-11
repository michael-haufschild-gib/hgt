# Anti-crystal law for zeta zeros and the gapless realization law for Ξ

- **ID:** ptr-anti-crystal
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** route PTR, docs/drafts/pipeline/1-in-progress/ptr-goal-loop-2026-10-09.md rows 60–62
- **Statement:** (A) No `h > 0`, `T₀` make all zeros above `T₀` on-line, simple and `h`-rigid
  (`g' ≤ g·e^{(g+g')/h}` for consecutive gaps). (B) For no `h > 0` is `Ξ(t) = Re G(t + ih)` with `G`
  in the Pólya class, i.e. a locally uniform limit of polynomials with all roots in `Im ≤ 0`.

## Goal
(B) says that every lossless (Hermite–Biehler) realization `E(z) = G(z + ih)` of `Ξ = Re E` has
resonances arbitrarily close to the real axis. This holds unconditionally: if RH fails no such `E`
exists, and if RH holds the zeros of Ξ are too irregular. It generalizes the cosine case of
CANNOT-497 (`G` real) to every complex `G`. For PTR, the port must be gapless (critical), so no
photonic or thin-slab realization can keep a resonance-free strip. (A) is the engine. It is a
statement about local zero statistics: ζ zeros are not locally a slowly modulated lattice at any
fixed scale.

## Gates
- [x] 0 → 1  in-progress: well-posed; inputs are all in the corpus (pair correlation, window counts, Lorentz mass, truncation)
- [x] 1 → 2  fully-proven (paper, below)
- [x] 2 → 3  formalized: `RHTower.not_rigidOrdinates`, `RHTower.not_exists_lowerPolyaClass_realization`; standard axioms
- [ ] 3 → 4  n/a (no stage 4 per user directive)

## Paper proof of (A)
Notation: `L = log T`, `x = T^α`, `S(x,t) = Σ_ρ x^{ρ−½}/(1 + (t + i(ρ−½))²)` (corpus
`lorentzZeroSumAll`). On the line the term is `x^{iγ}/(1 + (t−γ)²)`.

1. **Gap propagation.** By (R2), two gaps of one consecutive chain spanning length `D` differ by a
   factor of at most `e^{2D/h}`.
2. **Normalized gaps.**
   - Corpus window count `exists_xiZeroCount_window_ge_log`: every `(c − w, c + w]` holds at least
     `log c` zeros. Applied to `(γ_i, γ_i + 2w]`, this gives `g_i ≤ 2w e^{4w/h}/(log γ_i − 1)`.
   - Corpus Lorentz mass: the zeros in `[γ_i, γ_i + 1]` number at most `C_W log γ_i`. Hence
     `g_i ≥ 1/(C_W e^{2/h} log(γ_i + 1))`.
   - So `c₁ ≤ g_k log γ_k ≤ c₂` for large `γ_k`.
3. **Abel bound.** Take `t ∈ [T^{3/4}, T]` and the zeros in `J = [T^{1/2}, T²]`.
   - The increments are `θ_k = αL g_k ∈ [αc₁/2, 2αc₂]`. With `α = min(π/(4c₂), 1/8)`, every
     `θ_k ∈ [δ, π/2]`.
   - The increment variation is `|θ_{k+1} − θ_k| ≤ 16αc₂²/(hL)`.
   - Summation by parts with `c_k = w_k/(e^{iθ_k} − 1)` and `σ = 2 sin(δ/2)` gives
     `|Σ_J w_k x^{iγ_k}| ≤ (w_a + w_b + Σ|Δw|)/σ + Σ w_k|Δθ_k|/σ² ≤ 5/σ + 16K₁/σ²`. Here
     `Σ w_k ≤ 8 L_T` (corpus Lorentz mass) and the weights are unimodal.
   - Zeros outside `J` contribute `o(1)`, including the finitely many zeros below `T₀`, whose
     amplitude is at most `T^{α/2}`.
4. **Mean square.** `∫_0^T |S|² ≤ (C+1)² T + T^{3/4}(128 T^{α/2} L)² = O(T) + o(TL)`.
5. **Contradiction.** Corpus `integral_normSq_lorentzZeroSumAll_sub_montgomeryForm_le` and
   `tendsto_montgomeryForm_div_leadingOrder` give `∫_0^T |S|² ≥ (1 − ε)αTL/4` for large `T`.
   This contradicts step 4. ∎

## Paper proof of (B) from (A)
- `p_m → G` with the roots of `p_m` in `Im ≤ 0`. The polynomial `P_m(z) = (p_m(z+ih) + p_m^#(z−ih))/2`
  is real-rooted, because `|p_m(z+ih)| > |p_m^#(z−ih)|` for `Im z > 0` factor by factor. Also
  `P_m → Ξ`, so Ξ is LP and RH holds.
- `G(t+ih) ≠ 0` by Hurwitz. The phase speed `ω = −Im(G'/G)(t+ih) = Σ d_j/((t−x_j)²+d_j²)` has all
  depths `d_j ≥ h`, so `|ω'| ≤ ω/h`. Also `ω > 0`, otherwise `ω ≡ 0` and Ξ has no real zero.
- `Ξ = |G(t+ih)| cos φ` with `φ' = −ω`. So the zeros are simple and consecutive zeros enclose phase
  `π`. This gives `π ≤ g ω(γ₂) e^{g/h}` and `π ≥ g' ω(γ₂) e^{−g'/h}`, i.e. (R2). Then (A) applies.

## Lean plan
1. `ZetaZeroAntiCrystalAbel`: abstract summation-by-parts bound.
2. `ZetaZeroAntiCrystalGaps`: normalized gap bounds from (R1), (R2) and the corpus window counts.
3. `ZetaZeroAntiCrystalLaw`: the S-bound and the Montgomery contradiction, `not_exists_rigid_zero_crystal`.
4. `XiGaplessRealizationLaw`: Pólya class, RH, phase rigidity, `not_exists_polyaClass_realization`.

## Log
- 2026-10-11 — created (loop row 62); paper proofs of (A) and (B) written
- 2026-10-11 — (A) FORMALIZED: `RHTower.not_rigidOrdinates` (ZetaZeroAntiCrystalLaw), standard axioms. Modules:
  HTGeometry.WeightedPhaseSumSeparatedIncrements, RHTower.ZetaRigidOrdinateGaps, ZetaRigidOrdinateLocalRH,
  ZetaRigidOrdinateLorentzSum, ZetaZeroAntiCrystalLaw. All wired.
- Next: (B). Plan: (i) polynomial Hermite–Biehler comparison plus Rouché give RH and G(t+ih) ≠ 0;
  (ii) the phase speed ω = −Im(G'/G)(t+ih) satisfies |ω'| ≤ ω/h for polynomials and in the limit;
  (iii) a continuous phase gives consecutive zeros enclosing phase π, hence (R2);
  (iv) RigidOrdinates h 0 contradicts (A).
- 2026-10-11 — (B) FORMALIZED: `RHTower.not_exists_lowerPolyaClass_realization` (XiGaplessRealizationLaw), plus
  HTGeometry.PolyaClassPhaseRigidity. Standard axioms, wired. Moved to 3-formalized.
- Deviations from the paper proof: the log-Lipschitz constant is `2/h`, via the algebraic bound
  `u² + b² ≤ e^{2d/b}(v² + b²)`, so the contradiction uses `(h/2)`-rigidity. RH comes from the corpus
  Hurwitz transfer `riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants`. Normalized gap
  bounds use the corpus window count and Lorentz mass rather than a Riemann–von Mangoldt formula.
- 2026-10-11 — (C) accumulation: `RHTower.not_exists_shallow_lowerPolyaClass_realization` (XiGaplessRealizationAccumulation).
  Resonances of every realization `Q · G₀(· + ih)` accumulate at ℝ. Shared tail lemma
  `false_of_phase_rigid_realization`.
- 2026-10-11 (cycle 64): windowed versions formalized. `eventually_not_rigidWindow` (ZetaZeroAntiCrystalWindow, with the local chain/gap bounds in ZetaRigidOrdinateWindow) says that for every h > 0, eventually in T, the window [T^{1/2}, T³] of ordinates is not h-rigid. `eventually_exists_shallow_resonance` (XiCriticalityEveryScale) says a strict lower Pólya realization E of Ξ that is nonzero on ℝ has, for every h > 0 and all large T, a zero with Re z ∈ [T^{1/2} − 1, T³ + K] and Im z ≥ −h. Proof: a resonance-free box makes the approximants root-free there (Hurwitz via the minimum of |E| on the compact box). Every Poisson term is then log-Lipschitz on the window: deep roots, far-left roots and far-right roots each give this. Hence the zeros are simple and rigid in the window, contradicting (i). Standard axioms; wired.
- 2026-10-11 (cycle 66): log log depth. `exists_eventually_not_rigidWindow_loglog` (ZetaZeroAntiCrystalLogLog): ∃K, eventually [T^{1/2},T³] is not (K/log log T)-rigid. `exists_eventually_shallow_resonance_loglog` (XiCriticalityLogLogDepth): resonances within depth C/log log T at every scale. Input is the corpus Montgomery chain made uniform down to x = (log T)³ (`eventually_montgomeryForm_lower_uniform`, MontgomeryPairCorrelationShortLength). Method limit: the rigidity constants grow like e^{O(1/h)} and must stay ≪ log T. At the critical scale c/log T, pair correlation on (0,1) cannot decide rigidity, since heavy-tailed slowly varying lattices match F(α)=α there. Standard axioms; wired.
- 2026-10-11 (cycle 67): critical scale. `exists_eventually_not_rigidWindow_critical` (XiCriticalityCriticalDepth): ∃C, eventually [T^{1/2},T³] is not (C/log T)-rigid. `exists_eventually_shallow_resonance_critical`: every lossless realization has resonances within depth C/log T at every scale. Pair correlation is combined with explicit-formula count control on a grid, which kills the heavy-tailed countermodel of cycle 66. Card: 3-formalized/ptr-critical-scale-anti-crystal.md. Standard axioms; wired.
