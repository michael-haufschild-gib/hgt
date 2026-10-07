# ζ-type poles never produce Weil positivity; large values of `Re ζ(½+it)` from a prime resonator

- **ID:** weil-cone-zeta-pole-producer-obstruction
- **Stage:** 3-formalized (MUST-815)
- **Type:** THEOREM (Lean, standard axioms)
- **Source:** Opus loop row 550; makes krein-producer-loops L88.2 unconditional and formal (L88.2 was paper, conditional on Bondarenko–Seip-type large values)
- **Statement.**
  1. *Large values* (`RHTower.ZetaResonator.exists_log_add_lt_re_zeta`). For every `K` and `T₀` there is `t ≥ T₀` with `Re ζ(½+it) > log t + K`.
  2. *Producer obstruction* (`RHTower.WeilZetaPole.not_weilPositiveFull_poleSystem`). Let `β ∈ ℝ`, and let `v` satisfy `v(0) = v(1) = 0` and `Σ|v(n)|n^{−½} < ∞`. Then `λ(n) = β·[n ≥ 2] + v(n)` is never full-cone Weil-positive.

## Why it matters (existence half, PBAP)
- After MUST-810, template (d) is U together with existence (PBAP), and every existence candidate needs a pole at `s = 1`.
- The simplest pole carrier is `ζ` itself: `D_λ = β(ζ − 1) + V`, i.e. `λ = 1 + ℓ¹(n^{−½})` up to scale.
- Weil positivity would pin `Re ζ(½+it) ≤ θ′(t) + O(1) ≈ ½ log t`. The resonance theorem shows `Re ζ` beats every `log t + K`, so the family is excluded.
- With L55 (`ℓ¹ ∪ (Λ + ℓ¹)`) this gives `W ∩ (ℓ¹ ∪ (Λ + ℓ¹) ∪ ℝ_{>0}·1 + ℓ¹) ⊆ {Λ}`. A producer has to carry its pole in a logarithmic derivative (FE-pinned), as L88 predicted.

## Paper proof (as formalized)
1. **Resonator.** Take `W_P(t) = ∏_{p∈P}(2 + 2cos(t log p)) ≥ 0` for a finite set `P` of primes.
2. **Recursion.** Since `W_{P∪{q}} = (2 + q^{it} + q^{−it})W_P`, the twisted integrals `∫_T^{2T} f W_P (m/d)^{it}` satisfy a three-term recursion with twists `m/d`, `mq/d`, `m/(dq)`. The main terms satisfy the same recursion whenever `q ∤ m, d`. Hence (`norm_sub_le_of_recursion`) the error grows by at most `4q^k` per prime.
3. **Base cases.** For `f = ζ(½+i·)` the base is the twisted first moment `[d∣m]√(d/m)T + O(√(dm)(√T m + m²))`. For `f = 1` it is `∫e^{iξt}` with `|ξ| ≥ 1/(md)`. Consequently:
   - `∫ζW_P = T ∏(2 + p^{−½}) + O(4^{|P|}Q³√T)`;
   - `∫W_P = 2^{|P|}T + O(4^{|P|}Q²)`, with `Q = ∏p`.
4. **Resonance.** If `Re ζ ≤ B` on `[T, 2T]`, then `T∏(2 + p^{−½}) − err ≤ B(2^{|P|}T + err′)`.
5. **Choice of parameters.** Take `P` = the primes `≤ y`, `y = N⁸`, `T = e^{20y}`. Then `Q ≤ 4^y` (`primorial_le_four_pow`) and `|P| ≤ y + 1`, so both errors are `≤ 35T`. This gives `∏_{p≤y}(1 + 1/(2√p)) ≤ 2B + 35`.
6. **Contradiction.** The gain satisfies `∏(1 + 1/(2√p)) ≥ exp(¼Σp^{−½}) ≥ exp(θ(y)/(4√y log y)) ≥ exp(N³/64)`, by mathlib's Chebyshev bound `θ(n) ≥ n log 2 − log(n+1) − 2√n log n`. Meanwhile `B = 20N⁸ + O(1)`, and `exp(N³/64) ≥ N^{12}/(64⁴·24)` eventually exceeds this.
7. **Weil application.** The identity theorem gives `(s−1)Φ = (s−1)(G + β − V) + 1 − β(s−1)ζ` on `Re s > ½`.
   - At `s = 1` this forces `β = 1`.
   - Then `Φ = G + 1/(s−1) + 1 − ζ − V`, which is continuous up to the line.
   - Hence `Re ζ(½+it) ≤ θ′(t) + 1 + Σ|v|n^{−½} ≤ log t + 5 + Σ|v|n^{−½}` for `t ≥ 1`, contradicting step 1.

## Lean
- `RHTower/ZetaLineResonatorLargeValues.lean` (namespace `RHTower.ZetaResonator`):
  - definitions: `resW`, `resGain`, `primeProd`, `twistInt`;
  - recursion: `twistInt_insert`, `norm_sub_le_of_recursion`;
  - moments: `norm_twistInt_zeta_sub_le`, `norm_twistInt_one_sub_le`;
  - resonance: `resGain_le_of_re_le`;
  - prime bounds: `theta_div_le_sum`, `half_le_theta`, `errors_le`;
  - gain: `prod_gain_le`, `exp_le_prod_gain`;
  - main: `exists_log_add_lt_re_zeta`.
- `RHTower/WeilConeZetaPoleProducerObstruction.lean` (namespace `RHTower.WeilZetaPole`):
  - setup: `poleSystem`, `LSeries_poleSystem`;
  - identity: `mul_weilContinuation_eq`, `beta_eq_one`, `weilContinuation_eq_poleBoundary`;
  - boundary: `re_poleBoundary_line_nonneg`, `re_zeta_line_le`;
  - main: `not_weilPositiveFull_poleSystem`.
- Both modules are wired after `WeilConeBoundaryMobiusRigidity`.

## Scope
- This is an existence-side kill of one producer family, not RH.
- The large-values theorem is classical in strength. Montgomery and Balasubramanian–Ramachandra give `exp(c√(log t/log log t))`; here an elementary product resonator gives growth faster than every `log t + K`, which is all the application needs.
- Not covered: `ζ·M` with `M ∈ ℓ¹(n^{−½})` non-constant, i.e. multiplicative pole carriers. The resonance functional then evaluates `M` at points of the Bohr torus, and a rotation argument (as in C539 Step 5) would be needed.

## Log
- 2026-10-07: created and formalized in one cycle (loop row 550).
- 2026-10-07: `{Λ, 1}` pencil extension (loop row 551, MUST-816).

## Extension: the `{Λ, 1}` pencil (MUST-816, loop row 551)
- **Statement** (`RHTower.WeilPencil.eq_vonMangoldt_of_weilPositiveFull_pencil`). Let `β, γ ∈ ℝ`, and let `v` satisfy `v(0) = v(1) = 0` and `Σ|v(n)|n^{−½} < ∞`. If `βΛ + γ·[n ≥ 2] + v` is full-cone Weil-positive, then `β = 1`, `γ = 0` and `v = 0`.
- **Proof.**
  - The master identity `Z₁((s−1)(Φ − G + V) − 1) = β((s−1)Z₁′ − Z₁) − γZ₁(Z₁ − (s−1))` gives `β + γ = 1` and `Φζ = H := (G + 1/(s−1) − γ(ζ − 1) − V)ζ + βζ′`.
  - Continuity up to the line, together with the line FE, gives `|ζ|²(γ(θ′ − Re ζ + 1) − Re V) ≥ 0`.
  - `γ > 0`: the resonance theorem (MUST-815).
  - `γ < 0`: Hardy's zeros (`exists_Xi_zero_gt`, `Xi_eq_zero_iff_hardyZ`) are isolated, while `Re ζ ≥ θ′ − O(1) ≥ 1` on a punctured neighbourhood of a high zero and `Re ζ → 0` there.
  - `γ = 0`: MUST-804.
- **Lean.** `RHTower/WeilConeVonMangoldtZetaPencil.lean`:
  - setup: `pencil`, `LSeries_pencil`, `masterLeft_pencil`, `beta_add_gamma`;
  - numerator: `weilContinuation_mul_zeta_pencil`, `line_ineq`;
  - cases: `gamma_nonpos`, `gamma_nonneg`, `eventually_zeta_linePt_ne_zero` (zeros of ζ on the line are isolated);
  - main: `eq_vonMangoldt_of_weilPositiveFull_pencil`.
  - Standard axioms, wired.
- **Reading.** Along the line from `Λ` to the ζ-pole carrier `1`, and past `Λ` toward `2Λ − 1`, nothing besides `Λ` is Weil-positive, even with a regular part. `γ > 0` fails by large values of `Re ζ`; `γ < 0` fails by zeros of `ζ` on the line.
- 2026-10-07: novelty audit. Part (ii) of MUST-815, and the `γ > 0` half of MUST-816, follow in a few lines from the corpus `weil_multiplicativeToeplitz_bound` with the divisor resonator `1_{m ∣ y#}`. The new parts are the formal unconditional Ω₊ for `Re ζ(½+it)` (classical in substance) and the `γ < 0` half (Hardy zeros).
