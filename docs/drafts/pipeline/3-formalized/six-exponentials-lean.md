# Six exponentials theorem in Lean (target of `ULF-F1-002` Theorem B)

- **ID:** TRANS-LEAN-SIX
- **Stage:** 3-formalized (Lean complete 2026-09-02)
- **Type:** THEOREM (classical; Lang–Ramachandra 1966) — Lean formalization, missing in mathlib
- **Source:** `5-failed/f1-frobenius-integrality-torsion-law.md` Theorem B (at most two primes
  `p` have `p^ρ` algebraic for a nonreal `ρ`); reuse map from `GelfondSchneiderProof`,
  `GelfondSchneiderSiegel`, `BakerProof`.
- **Statement:** for `x₁, x₂ ∈ ℂ` ℚ-linearly independent and `y₁, y₂, y₃ ∈ ℂ` ℚ-linearly
  independent, at least one of `exp(x_i y_j)` is transcendental over ℚ.
- **Corollary to formalize:** for nonreal `ρ` and distinct primes `p₁, p₂, p₃`, not all of
  `p_j^ρ` are algebraic (`x = (1, ρ)`, `y = (log p_j)`; `p_j^ρ = exp(ρ log p_j)` with the
  principal `Complex.cpow` for a positive real base).

## Paper proof (fixed quantifiers, no zero-counting theorem needed)

Assume all `α_{ij} = exp(x_i y_j)` algebraic. Let `K = ℚ(α_{ij})`, `d = [K:ℚ]`, `D ∈ ℕ⁺` a common
denominator (`D α_{ij}` algebraic integers), `H = max house(D α_{ij})`, `X = |x₁| + |x₂|`,
`Y = |y₁| + |y₂| + |y₃|`.

1. **Points and frequencies.** `S_M = {m₁y₁ + m₂y₂ + m₃y₃ : 1 ≤ m_j ≤ M}` has exactly `M³`
   points (ℚ-independence of the `y_j` makes `m ↦ m·y` injective), all of modulus `≤ MY`.
   The frequencies `λ_{ab} = a x₁ + b x₂`, `1 ≤ a, b ≤ L`, are pairwise distinct (ℚ-independence
   of the `x_i`) with `|λ_{ab}| ≤ LX`.
2. **Siegel.** For `L² > d M₀³` there is `c ∈ ℤ^{L²} ∖ 0` with `F(z) = Σ c_{ab} e^{λ_{ab} z}`
   vanishing on `S_{M₀}`: the value `F(m·y) = Σ c_{ab} ∏_j α_{1j}^{a m_j} α_{2j}^{b m_j}`, and after
   multiplying by `D^{6 L M₀}` the coefficients are algebraic integers of house `≤ (DH)^{6LM₀}`;
   the corpus's `GelfondSchneiderSiegel.exists_ne_zero_int_vec_house_le` gives `|c| ≤ B` with
   `log B ≤ c₀ L M₀` (constants from `K`). Take `L² = 2dM₀³` (so `L ≤ 2√d M₀^{3/2}`).
3. **Nonvanishing.** `F ≢ 0`: if `F ≡ 0` then `F^{(k)}(0) = Σ c_{ab} λ_{ab}^k = 0` for
   `k < L²`, a Vandermonde system in the distinct `λ_{ab}`, so `c = 0`.
4. **Step `M → M+1`** (for every `M ≥ M₀`). Suppose `F` vanishes on `S_M`; let `s ∈ S_{M+1}`.
   `multipoint_schwarz_bound` with points `S_M`, order `1`, radius `R = 4(M+1)Y`: on `|w| = R`,
   `|F(w)| ≤ L² B e^{LXR}` and `∏_{c∈S_M}|w − c| ≥ (R − MY)^{M³} ≥ (3(M+1)Y)^{M³}`; at `s`,
   `∏|s − c| ≤ (2(M+1)Y)^{M³}`. Hence `|F(s)| ≤ L² B e^{4LXY(M+1)} (2/3)^{M³}`. If `F(s) ≠ 0`,
   `D^{6L(M+1)} F(s)` is a nonzero algebraic integer of house `≤ L² B (DH)^{6L(M+1)}`, and
   `algebraicInteger_eq_zero_of_distinguished_mul_house_pow_lt_one` (Liouville) gives
   `|F(s)| ≥ D^{-6L(M+1)} (L² B (DH)^{6L(M+1)})^{-(d-1)}`. The two bounds contradict as soon as
   `M³ log(3/2) > c₁ L (M+1) + c₂ log(L² B)` with `c₁, c₂` depending only on `d, D, H, X, Y`;
   since `L ≤ 2√d M₀^{3/2} ≤ 2√d M^{3/2}` and `log B ≤ c₀ L M₀ ≤ c₀' M^{5/2}`, this holds for all
   `M ≥ M₀` once `M₀` exceeds an explicit constant. So `F(s) = 0`: `F` vanishes on `S_{M+1}`.
5. **`F ≡ 0`.** By induction `F` vanishes on every `S_M`, `M ≥ M₀`. For fixed `z`, apply the
   Schwarz bound with points `S_M` and `R = 4MY` (for `M ≥ |z|/Y`): `|F(z)| ≤ L² B e^{4LXYM}
   (2/3)^{M³} → 0`, so `F(z) = 0`. This contradicts 3.

No Jensen formula, zero-density estimate, or Tijdeman bound is used; the only analytic input
is the corpus's multipoint Schwarz lemma and the growth of an exponential polynomial.

## Lean plan (modules under `RHTower/SixExponentials/`)

| module | content | reuse |
|---|---|---|
| `Points.lean` | `S_M` as `Finset ℂ`, injectivity from ℚ-independence, `card = M³`, modulus bound | — |
| `Frequencies.lean` | `λ_{ab}`, distinctness from ℚ-independence, bound `LX` | `BakerProof.AuxiliaryFunction` frequency lemmas as pattern |
| `Vandermonde.lean` | `Σ c_λ e^{λ z} ≡ 0 ⇒ c = 0` via iterated derivatives at `0` and `Matrix.det_vandermonde` | mathlib |
| `Values.lean` | `F(m·y)` as an element of `K`, denominator `D^{6LM}`, house bound `L² B (DH)^{6LM}` | `GelfondSchneiderProof.MainAlgSetup` house lemmas |
| `Siegel.lean` | apply `exists_ne_zero_int_vec_house_le` to the `M₀³ × L²` matrix | `GelfondSchneiderSiegel` |
| `Schwarz.lean` | the bound of step 4 from `multipoint_schwarz_bound` | `BakerProof.MultipointSchwarz` |
| `Induction.lean` | step 4 with Liouville; step 5 | `BakerProof.AuxiliaryArithmetic` |
| `Main.lean` | `six_exponentials`, `not_all_prime_cpow_isAlgebraic` | `exists_common_field_of_isAlgebraic` generalised to six numbers (`IntermediateField.finiteDimensional_adjoin`) |

## Lean (built, wired into `GaloisForLFunctions.RHTower`, axioms `propext, Classical.choice, Quot.sound`)

| module | declarations |
|---|---|
| `SixExponentials.Setup` | `Data`, `E`, `expo`, `freq`, `npt`, `pt`, `freq_injective`, `pt_injective`, `X`, `Y`, `Y_pos`, `norm_freq_le`, `norm_pt_le`, `ex`, `sum_ex_le`, `exp_freq_mul_pt` |
| `SixExponentials.Field` | `AlgData`, `K`, `σ`, `lift`, `scale`, `β`, `cz`, `entry`, `entry_ne_zero`, `σ_entry`, `house_prod_le_of_le`, `Hb`, `one_le_Hb`, `house_entry_le` |
| `SixExponentials.Auxiliary` | `one_le_siegel_c₁`, `siegel_bound_le`, `mat`, `exists_coefficients`, `F`, `differentiable_F`, `sval`, `σ_sval`, `F_pt_eq_zero_of_ker`, `house_sval_le`, `norm_F_le`, `exists_F_ne_zero` |
| `SixExponentials.Extrapolation` | `samples`, `card_samples`, `norm_F_le_of_vanishing` (Schwarz step), `one_le_of_F_ne_zero` (Liouville step) |
| `SixExponentials.Main` | `two_thirds_pow_mul_lt`, `exists_parameter`, `exists_M_large`, `final_lt_one`, `combine_step`, `AlgData.false`, **`six_exponentials`** |
| `SixExponentials.PrimePowers` | `exp_mul_log_eq_cpow`, `exp_log_nat`, `prime_logs_independent` (via the corpus's Baker theorem), **`not_all_three_prime_cpow_isAlgebraic`** |

Reused corpus assets: `BakerGeneralProof.AlgebraicFamilyField` (number field of a finite algebraic
family, common integer denominator), `GelfondSchneiderSiegel.exists_ne_zero_int_vec_house_le`
(Siegel over number fields with explicit constant), `CExpPoly.eq_zero_of_cexpFn_eq_zero`
(exponential polynomials with distinct frequencies), `BakerProof.multipoint_schwarz_bound`,
`BakerProof.algebraicInteger_eq_zero_of_distinguished_mul_house_pow_lt_one` (Liouville),
`baker_prime_mult_indep`. Parameters: `d = [K:ℚ]`, `N` from `exists_parameter`, `M₀ = N²`,
`L = 2 d N³`.

## Gates
- [x] Lean modules built and wired (2026-09-02).

## Log
- 2026-09-02 — created; paper proof fixed in the Schwarz-only form; reuse map recorded.
- 2026-09-02 — six modules built (~1000 lines), wired, axioms clean; moved to 3-formalized.
