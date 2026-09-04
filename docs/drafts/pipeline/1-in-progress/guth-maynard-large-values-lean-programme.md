# Guth–Maynard large values estimate — Lean programme

**Stage:** 1 (in progress), opened 2026-09-04.  Target theorem (Guth–Maynard, *New large value estimates
for Dirichlet polynomials*, Annals 203 (2026), arXiv:2405.20552v2, Theorem 1.1):

> `(b_n)` complex with `|b_n| ≤ 1`, `(t_r)_{r ≤ R}` 1-separated in `[0, T]`, `|Σ_{N ≤ n ≤ 2N} b_n n^{it_r}| ≥ V`
> for all `r ≤ R`.  Then `R ≤ T^{o(1)} (N² V⁻² + N^{18/5} V⁻⁴ + T N^{12/5} V⁻⁴)`.

Classical comparison (their (1.1)): `R ≤ T^{o(1)}(N²V⁻² + T·min(NV⁻², N⁴V⁻⁶))` from the mean value
theorem plus Montgomery–Halász–Huxley.  Consequences: `N(σ,T) ≤ T^{15(1−σ)/(3+5σ)+o(1)}` (Thm 1.2),
`N(σ,T) ≤ T^{30(1−σ)/13+o(1)}` (1.4), primes in intervals of length `x^{17/30+ε}` (Cor 1.3).

## Corpus inventory (search tool, 2026-09-04)

Already in Lean under `RHTower/Sieve/` and `RHTower/`: discrete/dyadic mean value theorems
(`dirichlet_meanValue_theorem`, `dirichlet_meanValue`, `dirichlet_meanValue_dyadic`), the integral
Halász–Montgomery bound with explicit constants (`setIntegral_normSq_dirPoly_le_explicit`,
memory `halasz-montgomery-integral-lean`), large-values counts from second moments (`large_values_count`,
`large_values_dpoly`, `large_values_separated`, `card_largeValues_div_le`), Huxley's large-values theorem in
closed and local forms (`huxley_large_values_closed`, `huxley_local_large_values`,
`huxley_multiblock_large_values_finset`), Montgomery/Heath-Brown grouped counts
(`montgomery_heathBrown_grouped_large_values_finset`), Halász large-value windows.  So the classical
right-hand side of (1.1) is corpus-owned; the programme is the new term `N^{18/5}V⁻⁴ + TN^{12/5}V⁻⁴`.

## Proof structure to formalize (from the paper)

1. Reduction to the matrix form: `R V² ≤ Σ_{r,r'} |Σ_n b_n b̄_n n^{i(t_r − t_{r'})}|`-type duality.
2. The new ingredient: an energy/large-sieve estimate on the matrix `(n^{i(t_r − t_{r'})})` controlled through
   the additive structure of the set of differences `t_r − t_{r'}` at scale `N^{o(1)}`, avoiding the sixth-power
   moment.  (Sections 2–6 of the paper; to be extracted statement by statement.)
3. Assembly with the dyadic decomposition and the `T^{o(1)}` bookkeeping.

## Plan

* Extract the exact intermediate propositions from the paper (pages 4–12) into this card with numbering.
* Formalize the reduction (1) on top of the corpus's duality module `HalaszMontgomeryDual`.
* Formalize the core estimate (2) as a standalone module family `GuthMaynard*`.
* Assemble (3) and derive Theorem 1.2/(1.4) using the corpus's zero-density machinery
  (`ChenGuptaLiZeroDensityExponents`, `DensityEnvelopeNoGo`).

Status: card only; first Lean module to follow after the constrained-Weil tasks.

## Proposition chain of Guth–Maynard (arXiv 2405.20552), extracted 2026-09-04 (pp. 4–24)

Notation: `D_N(t) = Σ_n w(n/N) b_n n^{it}` with `w` a fixed smooth bump on `[1,2]`, `w = 1` on
`[6/5, 9/5]`; `W ⊂ [0,T]` a `T^ε`-separated set; `M_W` the `|W| × N` matrix `(M_W)_{t,n} = w(n/N) n^{it}`;
`h_t(u) = w(u)² u^{it}`; `R(v) = Σ_{t∈W} |v|^{it}`; `E(W)` the additive energy (1.7).

* **Reduction (Prop 3.1 ⇒ Thm 1.1).** Enough: `σ ∈ [7/10, 8/10]`, `T = N^{6/5}`, then
  `|W| ≤ T N^{(12−20σ)/5 + o(1)}`.  Elementary: subdivision, `T^η`-separated thinning, and the trivial
  bound (1.6) `|W| = O(T N^{1−2σ})` in the other ranges.
* **Lemma 4.1 (singular value).** `|W| N^{2σ} ≤ Σ_t |D_N(t)|² = ‖M_W b‖² ≤ s₁(M_W)² ‖b‖²`, and
  `‖b‖² ≪ N`.  Pure linear algebra.
* **Lemma 4.2 (trace inequality).** For an `m × n` complex matrix `A`,
  `s₁(A) ≤ 2 (tr((AA*)³) − tr(AA*)³/m²)^{1/6} + 2 (tr(AA*)/m)^{1/2}`.  Reduces to the scalar
  inequality (4.3) for nonnegative reals `x₁ ≥ … ≥ x_k`:
  `x₁ ≤ 2 (Σ x_i⁶ − (Σ x_i²)³/k²)^{1/6} + 2 (Σ x_i²/k)^{1/2}`, proved by Hölder on `i ≥ 2` and the
  case split `x₁⁶ ≤ max(4(Σx⁶ − (Σx²)³/k²), 8(Σx²)³/k³)`.  **Lean-ready, self-contained.**
* **Lemma 4.3 (non-stationary phase).** `ĥ_t(ξ) ≪_j (1+|t|)^j/|ξ|^j` and `≪_j (1+|ξ|)^j/|t|^j`.
  Integration by parts, `j` times.
* **Lemma 4.4 (Hilbert–Schmidt).** `tr(M_W M_W*) = N|W|‖w‖²_{L²} + O(N^{−100})` by Poisson summation.
* **Lemma 4.5 (cubic trace).** `tr((M_W M_W*)³) = N³|W|‖w‖⁶ + Σ_{m ∈ ℤ³∖0} I_m + O(T^{−100})`,
  `I_m = N³ Σ_{t₁,t₂,t₃∈W} ĥ_{t₁−t₂}(m₁N) ĥ_{t₂−t₃}(m₂N) ĥ_{t₃−t₁}(m₃N)`.
* **Prop 4.6.** `|W| ≪_ε N^{2−2σ} + N^{1−2σ} (Σ_{m≠0} I_m)^{1/3}` — the `N³|W|‖w‖⁶` term cancels
  against `tr(M M*)³/|W|²` in Lemma 4.2.  So the whole theorem is a bound on `Σ_{m≠0} I_m = S₁+S₂+S₃`
  (5.5), split by the number of nonzero `m_i`.
* **Prop 5.1.** `S₁ = O(T^{−10})` (Lemma 4.3 + separation).
* **Lemma 6.2 (approximate functional equation).** For `|t| ~ T₀ ≥ T^ε`:
  `|Σ_{m≠0} ĥ_t(mN)| ≪ T₀^{−1/2} ∫_{|u|≲1} |Σ_{m ≲ T₀/N} m^{−i(t+u)}| du + O(T^{−100})`; proved by Mellin
  inversion and the van der Corput first/second derivative bounds (Montgomery, Ch. 3, Lemmas 1–2).
* **Prop 6.1 (S₂).** For every `k ∈ ℕ`:
  `S₂ ≲ N²|W|² + T N |W|^{2−1/k} + N²|W|² (T^{1/2}/|W|^{3/4})^{1/k}`, via (6.1)–(6.4): Lemma 6.2, Hölder
  with exponent `k`, and Heath-Brown's Theorem 1.6 (`Σ_{t₁,t₂∈𝒯}|Σ a_n n^{i(t₁−t₂)}|² ≲ |𝒯|²N + |𝒯|N² +
  |𝒯|^{5/4}T^{1/2}N`).
* **Prop 7.1 (cancellation inside `I_m`).** `|I_m| ≪ N³ ∫_{|m₁v₁+m₂v₂+m₃| ≲ 1/N, v₁≍v₂≍1}
  |R(v₁)R(v₂/v₁)R(v₂)| dv₁dv₂ + O(T^{−200})`; and `I_m = O(T^{−200})` unless `|m₂| ≍ |m₃|` when
  `|m₁| ≤ |m₂| ≤ |m₃|`.  Change of variables `v₁ = u₁/u₃, v₂ = u₂/u₃` (Jacobian `u₃²`) followed by
  non-stationary phase in `u₃`: this is the key step that is *specific to Dirichlet polynomials*
  (the multiplicative structure `n^{it}` makes the `u₃`-integral either oscillatory or stationary,
  never in between; the paper's Remark p. 22).
* **Prop 7.2 (expansion of `S₃`).** With the smoothed `R̃ = R̃_{ψ̃₁,ψ̃₂,M}` (7.5):
  `S₃ ≲ (N²/M) Σ_{|m₁|~M₁, |m₂|,|m₃|≍M} Ĩ_m + O(T^{−100})`,
  `Ĩ_m = ∫_{v₁≍1} |R(v₁) R̃((m₁v₁+m₃)/(m₂v₁)) R̃((m₁v₁+m₃)/m₂)| dv₁`.
* Pages 25 ff (not yet read): the `L²`/`L⁴` bounds on `R̃` in terms of `|W|` and `E(W)`, the
  "small closed set `U`" argument (approximate closure under `u ↦ (m₁u+m₂)/m₃`), the refined energy
  bound `E(W) ≲ |W|³N²/T²`, and the assembly of Prop 3.1.

### Formalization order (revised)
1. Lemma 4.2 (scalar (4.3) + matrix form via `Matrix.IsHermitian.eigenvalues`; the corpus already has
   `trace_pow_eq_sum_eigenvalues_pow` and `trace_re_eq_sum_eigenvalues`).
2. Lemma 4.1 (Rayleigh bound `‖Ab‖² ≤ λ_max(A*A)‖b‖²`), then Prop 4.6 as a conditional theorem in
   terms of an abstract `Σ I_m` bound (`|W| ≤ C(ε)(N^{2−2σ} + N^{1−2σ} S^{1/3})`).
3. Lemma 4.3 (integration by parts; the corpus has iterated-derivative Fourier decay tools in the
   Schwartz files), Lemma 4.4 (Poisson summation; corpus: `HermiteCompleteness`/Jacobi theta tools).
4. Prop 5.1, Lemma 6.2 (van der Corput first/second derivative tests — check `RHTower/Sieve/` and
   the exponential-sum modules), Prop 6.1 on top of the corpus Heath-Brown/Huxley large values file.
5. Section 7–10: the `S₃` analysis (the genuinely new content).

### Lean (2026-09-04)
* `RHTower/Sieve/GuthMaynardTraceSingularValue.lean` (wired after `Sieve.HalaszMontgomeryDyadic`, axioms
  `[propext, Classical.choice, Quot.sound]`): `cube_sum_le_card_sq_mul_sum_cube` (power mean),
  `cube_le_max_trace_defect` — Guth–Maynard (4.3) in the eigenvalue variables:
  `y_{i₀}³ ≤ max(4(Σy³ − (Σy)³/k²), 8(Σy)³/k³)` for nonnegative `y`; and
  `eigenvalue_cube_le_max_trace_defect` for a Hermitian matrix with nonnegative eigenvalues, read off
  `tr H³` and `tr H` through the corpus's `trace_pow_eq_sum_eigenvalues_pow`.  This is Lemma 4.2 in
  the form actually used in Prop. 4.6 (`s₁(M)⁶ = λ_max(MM*)³`).
* Next: Lemma 4.1 (`‖Mb‖² ≤ λ_max(M*M)‖b‖²`, Rayleigh), then Prop. 4.6 conditional on an abstract
  bound for `Σ_{m≠0} I_m`; Lemmas 4.3–4.5 (non-stationary phase, Poisson summation).
