# Typical JAS positivity below the zero-free abscissa fails (finite attained top)

- **ID:** jas-typical-cap-receiver
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** JAS ledger rows 181, 185, 186 (`1-in-progress/jas-goal-loop-2026-10-09.md`); STATUS MUST-1367
- **Statement:** Suppose `β₀ = max Re ρ` exists and is attained by finitely many zero copies. Then for every `σ ∈ (½, β₀)` there are `N ≥ 3` and `ε > 0` with the following property. For every `X` there is a finite set `P` of primes `p > X` such that more than `ε N^{|P|}` phase vectors `k : P → ℤ/N` give `Re jasPhaseAggregate σ 1 N P k < 0`.

## Goal
This is the receiver half of the typical-abscissa law. MUST-1354 gives typical positivity at `σ ≥ 1` unconditionally, and its half-plane form gives it at `σ > β₀`. The receiver makes the typical abscissa exactly `β₀` in finite-top worlds. As a no-go for producers: any proof of typical positivity below level `1` is a proof of a zero-free strip.

## Gates
- [x] 0 → 1  in-progress: well-posed; mechanism found (row 185)
- [x] 1 → 2  fully-proven: paper proof below
- [x] 2 → 3  formalized: `exists_card_jasPhaseAggregate_re_neg_gt_of_finite_top` in `RHTower/JointAncestryTypicalCapReceiver.lean`, over 12 modules (`JointAncestryPhaseOrbitMoments`, `JointAncestryRotationNegativity`, `CosineAvoidanceFiniteFrequencies`, `JointAncestryTypicalCap{Count,Window,Expansion,Local,Arith,Bad,Tail,Approx,Receiver}`). Built with `lake build --old`; `#print axioms` gives the standard three
- [ ] 3 → 4  publication-ready

## Notation
- Weights `w_q = 1/(ρ(1−ρ))`, `W = Σ|w_q|`, `Θ = β₀ − ½ > 0`.
- At `r = 1`, `jasPhaseAggregate σ 1 N P k = 2^{|P|} Σ_q w_q ∏_{p∈P} f_p(q, k_p)`, where `f_p(q, j) = 1 + d_p ω^j + c_p ω^{−j}`.
- Here `c_p(q) = ½p^{−σ}p^{ρ−½}` and `d_p(q) = ½p^{−σ}p^{½−ρ}`, so `c_p d_p = ¼p^{−2σ}`.
- Global shift `k ↦ k + j·1` with `j ∈ ℤ/N`. It is a bijection of `(ℤ/N)^P` and gives `f_p(q, k_p + j) = 1 + d_pω^{k_p}ω^{j} + c_pω^{−k_p}ω^{−j}`.

## Proof
1. **Counting by orbits.** `#bad = (1/N) Σ_k #{j : D(k + j1) < 0}`, where `D = Re jasPhaseAggregate`. So it suffices to show that for at least `N^{|P|}/16` vectors `k`, at least `cN` shifts `j` are bad.
2. **Window.** Take `η_X = 1/log X` and `W ⊂` primes in `(X, X(1+η_X)]`, an initial segment with `V := X^{2Θ}·¼Σ_{p∈W} p^{−2σ} ∈ [V*, V* + 1]`. This is possible because each term is `≤ ¼X^{2Θ−2σ} → 0` (as `σ > Θ`). The full window sum is `≍ η X^{1+2Θ−2σ}/log X → ∞`, since `σ < ½ + Θ`; this uses the VK prime number theorem in short intervals.
3. **Coherent variable.** Let `Z(k) = Σ_{p∈W} ½p^{−σ}ω^{−k_p}` and `ζ = X^Θ Z`. Then:
   - `E|ζ|² = V`.
   - `E|ζ|⁴ ≤ 2V²`, since for `N ≥ 3` only the pairings `{p,q} = {r,s}` survive.
   - Paley–Zygmund gives `#{|ζ|² ≥ V/2} ≥ N^{|P|}/8`.
   - Chebyshev gives `#{|ζ| > R₁} ≤ (V/R₁²)N^{|P|}`.
4. **Expansion.** For `|u| ≤ ½`, `log(1+u) = u − u²/2 + O(|u|³)`. With `u_p = c_pω^{−k_p−j} + d_pω^{k_p+j}`:
   - `log ∏ f_p = ω^{−j}S_q + ω^{j}T_q − ½ω^{−2j}Q_q − ½ω^{2j}Q'_q − Σc_pd_p + O(Σ|u_p|³)`.
   - Here `S_q = Σc_pω^{−k_p}`, `T_q = Σd_pω^{k_p}`, `Q_q = Σc_p²ω^{−2k_p}`, `Q'_q = Σd_p²ω^{2k_p}`.
   - Bounds: `E|T_q|² = Σ|d_p|² → 0` and `E|Q_q|² = Σ|c_p|⁴ → 0` (`N ≥ 3`). Also `Σc_pd_p = ¼Σp^{−2σ} → 0` and `Σ|u_p|³ ≤ (max|u_p|)·2V → 0`, all uniformly in `q`.
   - Zero copies with `Re ρ < ½` have the heavy coefficient in the `T` slot. Treat them symmetrically.
5. **High zeros** (`|γ| > H`):
   - The exponential moment is `E exp(λ Re(e^{iα}S_q)) ≤ exp(λ²Σ|c_p|²/2)` (Hoeffding's lemma, mean zero for `N ≥ 2`).
   - With `|Q_q| ≤ Σ|c_p|² ≤ V` and Cauchy–Schwarz, `E sup_j |∏f_p(q, k+j1)| ≤ C e^{4V}`, uniformly in `q`.
   - Markov then gives `Σ_{|γ|>H}|w_q| sup_j|∏f| ≤ ½` off a set of measure `≤ 2Ce^{4V}Σ_{|γ|>H}|w_q|`.
6. **Low zeros** (`|γ| ≤ H`, finitely many):
   - Coherence: `E|S_q − X^{ρ−½}Z|² ≤ 4V|ρ−½|²η_X² → 0`.
   - Top copies (`Re ρ = β₀`, `|γ| ≤ H`) give `X^{ρ−½}Z = e^{iγ log X}ζ`.
   - Non-top low copies have `|Re ρ − ½| ≤ Θ_H < Θ` (finite set), so `|X^{ρ−½}Z| ≤ X^{Θ_H−Θ}|ζ| → 0` on `{|ζ| ≤ R₁}`; they freeze to their weights.
   - Grouping each top copy with its partners `ρ̄`, `1−ρ`, `1−ρ̄`, off an exceptional set of measure `→ 0`, uniformly in `j`:
     `D(k + j1)·2^{−|P|} = L + 2Re E(ω^{−j}ζ(k)) + err`, with `|err| ≤ ½`.
   - Here `L = Σ_{|γ|≤H, non-top} w_q` (real, `|L| ≤ W`) and `E(ξ) = Σ_t (w_t e^{e^{iθ_t}ξ} + w̄_t e^{e^{−iθ_t}ξ})`.
   - The sum runs over top representatives, with `θ_t = γ_t log X` and multiplicities merged into `w_t`.
7. **Rotation lemma (deterministic).**
   - Let `g_1,…,g_m` be unit frequencies with `g_1` separated from the others: `Re(g_s/g_1) ≤ 1 − g₀`. Let `b_s ≠ 0` and `|L| ≤ W`.
   - On the arc `|ψ + arg g_1| ≤ α`, with `α` fixed by `g₀`, the term `b_1e^{g_1ξ}` dominates the rest by a factor `e^{−Rg₀/3}`.
   - Its phase `arg b_1 + R sin(ψ + arg g_1)` has derivative in `[R/2, R]`.
   - Hence the sample angles `arg ζ − 2πj/N` with `cos(phase) ≤ −½` number at least `(α/(12π))N` once `Rα ≥ 8π` and `N ≥ 6R₁`.
   - At those angles, `L + 2Re E ≤ W − |b_1|e^{R/2}/2 < −1` for `R ≥ R₀`.
8. **Separation.** The conditions `(γ_1 ∓ γ_t)u ∉ (−s₁, s₁) + 2πℤ` and `2γ_1u ∉ (−s₁, s₁) + 2πℤ` are finitely many, each with bad density `s₁/π`. So `u = log X` can be chosen arbitrarily large with all of them satisfied, which gives a uniform `g₀`.
9. **Assembly.** The top configuration is fixed once `H ≥ H₀` (finitely many top copies), so `R₀` and `α` are fixed. Choose, in order:
   - `V* = 2R₀² + 1`;
   - `R₁` with `V/R₁² ≤ 1/32`;
   - `H ≥ H₀` with `2Ce^{4V}Σ_{|γ|>H}|w| ≤ 1/64`;
   - `N ≥ max(3, 6R₁)`;
   - then `X` large along good `u`, so that the low-zero errors fail on at most `N^{|P|}/64` vectors.

   The good set has size `≥ (1/8 − 1/32 − 1/64 − 1/64)N^{|P|} = N^{|P|}/16`. Each good `k` has `≥ (α/(12π))N` bad shifts, so `#bad ≥ (α/(192π))N^{|P|}`. Take `ε = α/(400π)`.

## Approach / insight
- Short windows make every low zero's heavy sum a multiple of one random variable `ζ`. The global phase shift is an exact symmetry that rotates `ζ`. Negativity then reduces to a deterministic statement about one exponential sum on a circle.
- The side condition is needed. With infinitely many near-maximal zeros, incoherent high zeros dominate (`e^{V/8}` vs `e^{√V}`, random-energy-model regime). This is the corpus single-base non-attained core; see row 185 and `3-formalized/lag-progression-baire.md`.

## Log
- 2026-10-13 — paper proof complete (row 186); Lean formalization started.
- 2026-10-13 — Lean progress (each compiles with 0 messages; not yet wired):
  - `RHTower/JointAncestryPhaseOrbitMoments.lean`: orbit counting `card_filter_mul_eq_sum_card_shift`, moments of `linearPhaseSum`, Paley–Zygmund `card_half_le_normSq_linearPhaseSum`, Chebyshev, Markov.
  - `RHTower/JointAncestryRotationNegativity.lean`: `card_good_samples`, `neg_at_good_sample`, `exists_sample_angles`, `card_rotation_negative`.
  - `RHTower/CosineAvoidanceFiniteFrequencies.lean`: `exists_ge_forall_cos_le`.
  - Remaining: prime window via VK PNT, product/coherence expansion, assembly.
- 2026-10-13 — more Lean (0 messages each):
  - `JointAncestryTypicalCapCount` (`card_neg_ge_of_rotation_model`, the abstract assembly).
  - `JointAncestryTypicalCapWindow` (`eventually_exists_capWindow`).
  - `JointAncestryTypicalCapExpansion` (phase second moments, second-order product expansion, `norm_cexp_sub_cexp_le_two_mul`, product second moments).
  - `JointAncestryTypicalCapLocal` (`norm_prod_phaseFactor_shift_sub_exp_le`).
  - `JointAncestryTypicalCapArith` (`jasPhaseAggregate_one_eq`, `capA`/`capB` norms, coherence).
  - Remaining: `JointAncestryTypicalCapReceiver`, which covers top-set facts, bad-set counts, the approximation and the main theorem.
- 2026-10-13 — formalized and wired; STATUS MUST-1367. Moved to 3-formalized.
