# RH as Weil positivity on one exposing ray

- **ID:** MC-190
- **Stage:** 3-formalized (STATUS MUST-629)
- **Type:** THEOREM (Lean)
- **Source:** MC loop cycles 189–190. Combines:
  - the corpus' exposed-point theorem for the polar cone (`weilPolarCone_exposed_at_vonMangoldt`, `riemannHypothesis_iff_exists_weilPositive_polarExposing_nonneg`);
  - the all-level linear duality MUST-624/628.
- **Statement.**
  - Let `w(n) = Σ_k 2^{−k}(K_k(log n) + K_k(−log n))` with `K_k = P_cP_c(Φ⋆Φ̃)` at `c = 1/(k+1)`. This is the exposing weight.
  - Let `ℓ̄(lam) = Σ_{n≥2} lam(n)n^{−1/2}w(n)`.
  - Let `τ_N = Σ_{n>N}(log n + C₀)|w(n)|`, so that `τ_N → 0`.
  - Then RH ⟺ `∀N ∀A (N ≤ e^{2A})`: `WeilDualBound A (w·1_{≤N}) (ℓ̄(Λ) − τ_N)`.
  - In words: every finite family of polar tests at levels `≤ A`, with weights `α ≥ 0`, whose atom coefficients are `t·w(n)` on `n ≤ N` and `0` on `N < n ≤ e^{2A}`, has archimedean energy `≥ t(ℓ̄(Λ) − τ_N)`.

## Goal
Cycle 189 found that the "Ξ-annihilated cone" idea (tests whose transform vanishes at all zeros give one-sided constraints on Weil-positive weights) is the corpus' near-radical/exposed-point machinery. The exposing functional `ℓ̄` is already known to be maximized over the cone only at `Λ`, and RH ⟺ some Weil-positive `lam` has `ℓ̄(lam) ≥ ℓ̄(Λ)`. This theorem writes that primal statement in dual form. The prime-blind tests (`t = 0`) carry existence; one extra ray of prime traces, spanned by `w`, carries RH.

## Paper proof
- **⇒.** RH gives `Λ ∈ W` (polar). The box gives `|ℓ̄(Λ) − L_N(Λ)| ≤ τ_N`. Weak duality for `Λ` gives the bound at every level.
- **⇐.**
  1. For each `N`, all-level duality gives `lam_N ∈ W` with `L_N(lam_N) ≥ ℓ̄(Λ) − τ_N`, hence `ℓ̄(lam_N) ≥ ℓ̄(Λ) − 2τ_N`.
  2. The level-wise box `|lam(n)| ≤ √n(log n + C₀)` puts the `lam_N` in the compact product `∏[−box, box]`. A subsequence converges pointwise to some `lam`.
  3. The polar cone is closed under pointwise limits, since each energy involves finitely many atoms affinely. So `lam ∈ W`.
  4. Dominated convergence with majorant `(log n + C₀)|w(n)| = O(n^{−3/2})` gives `ℓ̄(lam) ≥ ℓ̄(Λ)`.
  5. Exposedness gives `lam = Λ`, hence RH.
- **Fubini.** `ℓ̄(v) = Σ_k 2^{−k}T_v(K_k) = Σ_n v(n)n^{−1/2}w(n)`. It holds because `|K_k(y)| ≤ De^{−2|y|}` uniformly in `k` and `Σ|v|/n² < ∞`.

## Lean
- Module `RHTower/WeilPolarConeExposedDuality.lean`, ~420 lines:
  - weight bounds: `exposingWeight`, `exists_abs_polarExposingKernel_le`, `exists_abs_exposingWeight_le`;
  - Fubini step: `polarExposingFunctional_eq_tsum`;
  - box and tail: `abs_le_boxWidth_of_weilPositive`, `vonMangoldt_le_boxWidth`, `summable_exposingMajorant`, `tendsto_exposingTail`, `abs_exposingValue_sub_linearWeightSum_le`;
  - closedness: `weilPositive_of_tendsto`;
  - main theorem: `riemannHypothesis_iff_forall_weilDualBound_exposing`.
- Audit:
  - `lake env lean` clean;
  - `#print axioms` standard (`propext`, `Classical.choice`, `Quot.sound`);
  - collision scan clean;
  - wired after `WeilPositivityLinearDuality` in `RHTower.lean`.

## Novelty / significance (honest)
- **What is new.** The equivalence is a duality reformulation; no new analytic input. What is new is the exact statement that Weil's criterion needs only prime-blind families plus one explicit ray of prime traces.
- **How it relates to Weil's criterion.** Weil's criterion uses all polar tests, i.e. all prime traces. Here the admissible prime traces form a half-line `ℝ₊·w` (truncated), and the threshold is the explicit constant `ℓ̄(Λ)`.
- **Significance.** Moderate. It makes ¬RH certifiable by a finite family of polar tests together with their values at `log n` and their archimedean energies. It locates RH's content in the energy minimum along one explicit direction.

## Open / next
- Express `ℓ̄(Λ)` archimedeanly (radicality of `K_k`: `ℓ̄(Λ) = Σ_k 2^{−k}(arch + pole)(K_k)` in the limit). That would make the criterion fully prime-free.
- Study the dual energy minimum along the ray: is `K` itself (the exposing kernel) the minimizer? That is the content of RH.

## Cycle 192: the threshold is archimedean (STATUS MUST-631)
- `archEnergy_polarRiemannDifference_eq`: on the polar Riemann difference `f_L = P_c(Φχ_L)`, `A(f_L) = 2π Re W(f_L,f_L) + 2π T_Λ(f_L)`. It combines three existing pieces:
  - the zero-side identity `zeta_W_eq_integral_weilAtomSymbol_vonMangoldt`;
  - the affine energy identity;
  - the atom-sum = atom-pairing identity.
- `tendsto_archEnergy_polarRiemannDifference`: `A(f_L)/(2π) → ℓ_c(Λ)`, because the zero side is at most `9·(5/4)S·E_L² → 0` and the atom pairing converges at rate `e^{−2L}`.
- `archimedeanExposingThreshold := Σ_k 2^{−k} limUnder_L A(f_{L,c_k})/(2π)` and `archimedeanExposingThreshold_eq : … = ℓ̄(Λ)`.
- `riemannHypothesis_iff_forall_weilDualBound_archimedean`: RH ⟺ `∀N A, WeilDualBound A (w·1_{≤N}) (E − τ_N)`. The statement contains no prime and no zero.
- **Reading.** HF's L166 calls the construction side "a statement about `A` and the set `log ℕ` only", equivalent to existence (PBAP). This theorem gives RH itself in that form, unconditionally. Existence is the prime-blind case `t = 0`; RH needs, in addition, one explicit ray of prime traces, with the threshold `E` computed from Riemann's kernel alone.

## Cycle 194: Weil's criterion restricted to the ray (STATUS MUST-633)
- `riemannHypothesis_of_forall_weilDualBound_exposing_mul`: the converse holds with any slack multiple `c·τ_N`, since the compactness argument needs only that the slack tends to `0`. The original iff is now the case `c = 1`.
- `archEnergy_eq_W_add_atoms`: for every polar test, `A(f) = 2π Re W(f,f) + 2π Σ_{n ≤ M} Λ(n)n^{−1/2}c_n(f)`.
- `sum_archEnergy_eq_of_matched`: on a family matched to `t·w_N`, `Σα A(f_i) = 2πΣα Re W(f_i) + t·L_N(Λ)`.
- `riemannHypothesis_iff_forall_restrictedWeilBound`: RH ⟺ `∀N A, RestrictedWeilBound A w_N (2τ_N)`.
  - `⇒`: from Weil positivity of `Λ` under RH.
  - `⇐`: via the `c = 3` converse, using `|ℓ̄(Λ) − L_N(Λ)| ≤ τ_N`.
- **Reading.** Weil's criterion (positivity on all polar tests) is equivalent to positivity, up to vanishing slack, on the subcone of families whose prime-trace vector lies on `ℝ₊·w_N`. The cone has codimension "all prime directions but one": the prime-blind tests plus one ray.
