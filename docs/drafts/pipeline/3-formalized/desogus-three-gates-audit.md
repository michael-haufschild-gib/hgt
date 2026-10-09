# Audit: Desogus, "The Three Gates" (arXiv 2609.20367v3, 6 Oct 2026)

- **Stage:** 3-formalized (external-claim audit; countermodel formalized, MUST-859)
- **Claim:** RH via odd-channel Weil positivity. A Schur induction over the endpoints `a_k = ½ log k` (k ≥ 7):
  - base `A_{7,−} ≻ 0` certified by interval arithmetic;
  - step `A_{k,−} ≻ 0 ⇒ A_{k+1,−} ≻ 0` from Theorem 8.6, `⟨H_k f, A_{k+1,−} H_k f⟩ ≥ g_k^{M+}|γ_k(f)|² + R_k^⊥[f]`;
  - closure through the restricted odd Weil criterion.
  The margin is `g_k^{M+} = ½ + log k − (439/250 log 2) Σ_m V_{k,m} − (5/2) W_k ≥ 1.878` (minimum at k = 33), growing like `0.476 log k`.

## Verdict: the proof is incomplete; the induction step proves too much

1. **The polar debit is not charged.**
   - The paper's own identities (121)–(122) give `H_k^* A_{k+1} H_k = T_k = S_k − 2δ_k |ζ_k⟩⟨ζ_k|`.
   - The term `−2δ_k|⟨ζ_k, f⟩|²` is the odd pole term `−2|s_{k+1}⟩⟨s_{k+1}|` on the harmonic graph. Equivalently it is the Green-root condition `RG*_k`.
   - The accounting in the proof of Theorem 8.6 (Section 8) has only:
     - the target diagonal `𝔅_k = ½ + log(1/w_k)`;
     - arithmetic losses (`χ_m ≤ V_{k,m}/log 2`, the mixed term, the aligned `W_k`);
     - the transverse reserve.
   - None of `δ_k`, `ζ_k`, `η_k`, `s_{k+1}` appears there. `RG*_k` is then "recovered a posteriori" from Theorem 8.6 (Corollary 8.7), which is circular if Theorem 8.6 never charged it. As written, Theorem 8.6 is at best a bound for the polar-free Schur block `S_k`, i.e. positivity of the polar-free core, and that is not RH.
2. **β-scaling countermodel (paper-level, rigorous modulo the paper's own estimates).**
   - Replace `Λ` by `βΛ` with `β ∈ (1 − ε₀, 1)`. Every arithmetic input of the induction is one-sided and only improves:
     - `V, W, σ` scale by `β²`, and `χ ≤ V/log 2`;
     - the Chebyshev capacity `ρ_aff` scales by `β`;
     - `βΛ(n) ≤ log n` still holds;
     - the divisor diagonal `Σ_{n∣q} βΛ(n) = β log q` is a smaller cost.
   - The base certificate at `Y = 7` has a strict interval margin, so it survives for `β` near 1.
   - Hence the argument, if valid, proves odd-channel Weil positivity for `βΛ`.
   - That is false for every `β < 1`. Take `f = φ(y − a′) − φ(−y − a′)` (an odd pair of bumps).
     - The pole gives `≈ −2c e^{a′}`.
     - The prime sum at `x ≈ 2a′` gives `+2βc e^{a′} +` the PNT fluctuation.
     - The PNT error term makes the fluctuation `o(e^{a′})` unconditionally.
     - So `W_{βΛ}(f) = −2(1 − β)c e^{a′}(1 + o(1)) < 0`.
   - This is the odd-channel analogue of the corpus pencil rigidity (MUST-816/821, full cone).
   - Reading: the odd pole carries the PNT main term. A correct odd-channel argument must cancel it with a two-sided (exact) PNT input. The paper's arithmetic enters only as small losses (`~0.147 log k`), never as the `e^{a}`-scale main term that cancels the pole.

## Useful to the corpus
- **Already owned:** the restricted odd criterion (paper Theorem 1.2) is `riemannHypothesis_iff_oddParityPole_nonneg` (CANNOT-485).
- **Possibly reusable lemmas (paper-level, not yet audited in full):**
  - Theorem 6.20, coherent multi-source capacity: `Short_S 𝔟 ⪰ (log(1/ε) + ½) ⊕ Q_{I_ν}` for the Cauchy/Legendre difference form on disjoint intervals of length `ε`;
  - Lemma 6.17, the two-source mean-zero bound `E_D ≥ log((D+1)/D)(‖f‖² + ‖g‖²)`;
  - the exact root recursion `δ_{k+1} = δ_k(1 − ℓ_k)` with the harmonic-graph identities (121)–(122);
  - the explicit Chebyshev capacity `sup_k (ψ(k) − log k)/k < 1.01824`.
- **Lean (done, MUST-859, `RHTower/WeilParityPoleDeletionAdditionLaws.lean`):**
  - The test vector is the paper's own polar vector `e^{x/2} − e^{−x/2} = 2s`. For `0 ≤ β < 1`, `Q_{βΛ}(odd pole) ≤ −(1−β)e^{2a} + O(a e^a)`, which is negative for all `a ≥ a₀(β)` (`eventually_oddParityPole_scaled_neg`). This is unconditional; it uses plain PNT through `tendsto_chebyshevPsiReal_div`.
  - This contradicts the paper's conclusion `A_{k,−}(βΛ) ≻ 0` at `a_k = ½ log k`, `k` large.
  - Positive survivor:
    - deletion law: odd-pole-positive subsystems `0 ≤ λ ≤ Λ` satisfy `Σ(Λ−λ)log(X/n) ≤ O(√X log X)`;
    - addition law: even-pole-positive supersystems satisfy `Σ(λ−Λ)log(X/n) ≤ 2U√X`.

## Log
- 2026-10-09: read the paper in full; located the uncharged polar debit in Theorem 8.6 and the β-scaling countermodel. No Lean yet.
- 2026-10-09: formalized the countermodel (MUST-859, loop row 613). All declarations use only the standard axioms. Wired into `RHTower.lean` after `WeilParityPoleOneSidedRH`.

## Second pass: audit and formalization of three reusable pieces (2026-10-09)

1. **Lemma 6.17 and Theorem 6.20 (Cauchy difference capacity): correct.** Both proofs were checked line by line.
   - Lean: `HTGeometry/CauchyDifferenceTwoIntervalBound.lean` and `HTGeometry/CauchyDifferenceMultiSourceCapacity.lean`.
   - The formal statements are real-valued, for measurable functions, with ENNReal energies, so `b[u] = ∞` is allowed.
   - **Two-interval form (stronger than Lemma 6.17, unequal lengths allowed).** `lintegral_twoInterval_ge`:
     `∫_I∫_J (f−g)²/(y−x) ≥ ‖f‖² ∫_J dy/(y−α) + ‖g‖² ∫_I dx/(β'−x)` for mean-zero `f ∈ L²(α,α')`, `g ∈ L²(β,β')`, `α' ≤ β`.
   - **Equal-length form (Lemma 6.17 in physical coordinates).** `lintegral_twoInterval_equalLength_ge`: the constant is `log((D+1)/D)`. Touching intervals (`D = 1`) are included.
   - **Theorem 6.20.** `capacity_multiSource`: `¼∫∫_{(0,1)²}(u(x)−u(y))²/|x−y| − ½∫log(x(1−x))u² ≥ (log(1/ε)+½) Σ_ν ‖u‖²_{L²(I_ν)}`. It holds for every measurable `u` that has mean zero and is L² on each `I_ν`, with nothing assumed on the free set.
   - The proof is the paper's region bookkeeping, recast as one-sided far-end charges `farCharge`: a pair pays exactly the two missing free charges.
2. **Root recursion (Lemmas 6.1–6.2): correct and classical** (the Schur-complement quotient formula).
   - The corpus already owned the core: `HTGeometry.complementarySchur_inverse_inner_split`.
   - New in `HTGeometry/RootedSchurLeverageRecursion.lean`:
     - `rootDefect_succ_eq` and `rootDefect_succ_eq_mul` give (72);
     - `normSq_inner_le_leverage_mul` and `normSq_inner_eq_leverage_mul` give (70) as an attained maximum (Cauchy–Schwarz for positive operators);
     - `rootedBlock_ge` gives (71).
   - Note: (72) is where the polar load lives, since `δ_{k+1} > 0 ⟺ ℓ_k < 1`. The step `ℓ_k < 1` for every `k` is exactly what MUST-859 shows cannot follow from inputs that are invariant under `Λ ↦ βΛ`.
3. **Chebyshev constant `C_tail = 1.018232801063381478` (Lemma 3.4): correct as a citation, not checkable here.**
   - The tail arithmetic is right: `1 + 0.2/15² + 1.00007/1800 + 1.78/150² = 1.001524`, since `log X₀ ≈ 15.10`, `√X₀ ≈ 1896` and `X₀^{1/3} ≈ 153`.
   - It rests on:
     - Dusart's bound `|θ(x)−x| < 0.2x/log²x` for `x ≥ 3 594 641`;
     - the bound `ψ−θ < 1.00007√x + 1.78x^{1/3}`;
     - a 3.6-million-point numerical sweep, with maximum `1.009309…` at `k = 199`. The sweep is not independently verified, because of the no-computation rule.
   - `C_tail` is not the supremum. It is `1.08·2√2/3` rounded down, i.e. reverse-engineered from the requirement `ρ_aff < 1.08`; the real slack is about `0.009`.
   - Lean (`RHTower/ChebyshevRatioPrimePowerJumps.lean`) covers the sweep's reduction step:
     - `exists_isPrimePow_psiLogRatio_ge`: for every `x ≥ 2` there is a prime power `m ≤ x` with `R(x) ≤ R(m)`, where `R(x) = (ψ(x) − log x)/x`;
     - the proof uses the `2^j` lower bound, concavity of `log` on `[1,2]`, and Bertrand's postulate;
     - `psiLogRatio_lt_of_isPrimePow_lt`: a bound at prime powers bounds all real `x ≥ 2`.
   - Not formalizable here: the sweep itself (certified numerics) and Dusart's bound (which rests on large-scale zero verification).
- All new declarations use only the standard axioms. The modules are wired into `HTGeometry.lean` (after `ComplementaryFeshbachImprovement`) and `RHTower.lean` (after `ChebyshevPsiScaling`).
