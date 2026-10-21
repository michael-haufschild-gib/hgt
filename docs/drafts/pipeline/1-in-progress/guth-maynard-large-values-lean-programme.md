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

### Lean (2026-09-08): Lemma 4.1 and Proposition 4.6 (conditional on the trace asymptotics)

* `RHTower/Sieve/GuthMaynardRayleigh.lean` (wired after `GuthMaynardTraceSingularValue`, axioms clean):
  `re_star_dotProduct_mulVec_le` (Rayleigh bound `Re ⟨v, A v⟩ ≤ μ Σ‖v‖²` for Hermitian `A` with eigenvalues
  `≤ μ`, via the corpus spectral factorisation `hermitian_eq_conj_diagonal`), `re_star_dotProduct_le_sqrt_mul_sqrt`
  (Cauchy–Schwarz for `⬝ᵥ` through `EuclideanSpace`), and **Lemma 4.1** `sum_normSq_mulVec_le`:
  `Σ_t ‖(M b)_t‖² ≤ λ_max(M Mᴴ) Σ‖b‖²` for rectangular `M`, proved without comparing the spectra of `Mᴴ M` and
  `M Mᴴ` (`‖u‖² = Re⟨Mᴴ u, b⟩ ≤ ‖Mᴴ u‖‖b‖`, `‖Mᴴ u‖² ≤ λ_max ‖u‖²`).
* `RHTower/Sieve/GuthMaynardPropFourSix.lean` (wired, axioms clean): `le_rpow_third_add_rpow_third`
  (`y³ ≤ a + b ⇒ y ≤ a^{1/3} + b^{1/3}`), `prop46_abstract` (real-number assembly: the flat baseline
  `(tr H)³/|W|²` cancels the main term of `tr H³` exactly; error terms `|E₁| ≤ 1/N²`, `|E₃| ≤ 1` cost only
  `K = 3c² + 3c + 2`), and **Prop. 4.6** `card_le_of_trace_bounds`: for `M : Matrix W N ℂ`, `H = M Mᴴ`, if
  `|W| n^{2σ} ≤ Σ_t ‖(M b)_t‖²`, `Σ‖b‖² ≤ C n`, `Re tr H = n|W|c + E₁`, `Re tr H³ = n³|W|c³ + S + E₃` with
  `S ≥ 0`, `|E₁| ≤ 1/n²`, `|E₃| ≤ 1`, then `|W| ≤ C n^{1−2σ} ((4(S + K))^{1/3} + 2nc + 2)`.
* Remaining inputs, in the order of the paper: Lemma 4.3 (non-stationary phase), Lemma 4.4 (Poisson summation
  for `tr H`), Lemma 4.5 (the cubic trace as `N³|W|‖w‖⁶ + Σ_{m≠0} I_m`), then Sections 5–10 for `S`.
* Traps: `posSemidef_self_mul_conjTranspose` over `ℂ` needs `open scoped ComplexOrder`; `set u := M *ᵥ b` lets
  `rw [Matrix.star_mulVec]` rewrite through the abbreviation — use `obtain ⟨u, hu⟩ : ∃ u, u = …` and rewrite
  standalone equations; `Finite.exists_max` for the top eigenvalue.

### Cross-reference (2026-09-08): the Chen–Gupta–Li tower already carries this chain for character packets

The corpus has ~250 modules `RHTower/ChenGuptaLi*.lean` (last commit 2026-08-22, no pipeline card) formalizing the
Guth–Maynard method for Dirichlet-character packets: `cglLemma41_source_bound` (Lemma 4.1 with constant 36),
`cglLemma42_source_bound` (Lemma 4.2), `cglLemma45_cubicTrace_eq_threeFrequencySums` and the `ChenGuptaLiLemma45*`
family (the cubic trace by Poisson summation, zero mode and nonzero frequencies split), `cglProposition46_realAsymptotic_bound`
(Prop. 4.6: `R+1 ≤ 288 (K^{1/3}+1) N^{2−2σ} + 288 N^{1−2σ} (max 0 Re S)^{1/3}`), `ChenGuptaLiProposition51*` (the axial
residue, S₁), and the `ChenGuptaLiLemma62*` family (approximate functional equation for `L(s,χ)`). Smooth bumps:
`CGLSmoothBump` (support `[1,2]`, plateau `[6/5,9/5]`), `cglSmoothBumpHt` (`h_t = w(u)² u^{it}` as a Schwartz map),
`cglSmoothBumpHt_tsum_eq_tsum_fourier` (Poisson), `cglSmoothBumpHt_abs_pow_mul_norm_fourier_le` (Lemma 4.3 decay).
`ChenGuptaLiHorizontalCollisionNoGo` records why that tower was built (the HC route's reflected-pair count) and why it
cannot close that endpoint (`cglProposition46_rhs_ge_288`, reflection partners collapse to one row).

Consequences for this programme:
* `GuthMaynardRayleigh` / `GuthMaynardPropFourSix` (this date) are the *abstract, constant-free, index-type-generic*
  forms of CGL's Lemma 4.1 and Prop. 4.6; they add nothing beyond generality. Do not build Lemmas 4.3–4.5 again:
  instantiate the CGL bump and `cglSmoothBumpHt` Poisson/decay lemmas.
* What neither tower has: Prop. 6.1 (the `S₂` bound through Heath-Brown's Theorem 1.6, whose Lean form is in the
  corpus's `huxley_*`/`montgomery_heathBrown_*` large-values files), and Sections 7–10 (the `S₃` analysis, the genuinely
  new Guth–Maynard content: Prop. 7.1 cancellation in `I_m`, the `R̃` moments, the small-closed-set argument, the energy
  bound `E(W) ≲ |W|³N²/T²`). The `ζ` case is the principal character `q = 1` of the CGL packets, to be checked when the
  chain is assembled.
* The zero-density corollary (Thm 1.2, `N(σ,T) ≪ T^{15(1−σ)/(3+5σ)+o(1)}`) also needs the zero-detecting-polynomial
  reduction, of which `ChenGuptaLiFiniteZeroDetector` and the corpus's `InghamDetector*` tower are the pieces.

### Lean (2026-09-08, later): Proposition 6.1 assembly, from the paper's §6 read directly (pp. 16–20)

* `RHTower/Sieve/GuthMaynardPropSixOne.lean` (wired after `GuthMaynardPropFourSix`, axioms clean):
  `sum_pow_le_card_pow_mul_sum_pow` (power mean `(Σx)^k ≤ |s|^{k−1} Σ x^k`), `sum_le_card_rpow_mul_sum_pow_rpow`
  (the scalar Hölder step (6.2): `Σ x ≤ |s|^{1−1/k} (Σ x^k)^{1/k}`), `rpow_inv_add_three_le`, and
  **`prop61_abstract`**: from (6.1) `S₂ ≤ C (N²/M) X`, (6.2) `X ≤ (W²)^{1−1/k} Y^{1/k}`, (6.3)
  `Y ≤ C' (W² M^k + W M^{2k} + W^{5/4} T^{1/2} M^k)` and `M ≤ T/N`:
  `S₂ ≤ C C'^{1/k} (N² W² + T N W^{2−1/k} + N² W^{2−3/(4k)} T^{1/(2k)})`, with `third_term_eq` giving the paper's
  form `N² W² (T^{1/2}/W^{3/4})^{1/k}` for the last term. This is (6.4) with explicit constants.
* Exact statements now on file (paper pp. 4, 15–20): **Theorem 1.6 (Heath-Brown)**: `𝒯` 1-separated in an interval of
  length `T`, `|a_n| ≤ T^{o(1)}`: `Σ_{t₁,t₂∈𝒯} |Σ_{n=N}^{2N} a_n n^{i(t₁−t₂)}|² ≤ T^{o(1)}(|𝒯|²N + |𝒯|N² + |𝒯|^{5/4}T^{1/2}N)`.
  **Lemma 6.2 (AFE)**: for `|t| ∼ T₀ ≥ T^ε`, `|Σ_{m≠0} ĥ_t(mN)| ≪ T₀^{−1/2} ∫_{|u|≲1} |Σ_{m≲T₀/N} m^{−i(t+u)}| du + O(T^{−100})`,
  proved by Mellin inversion of `w²` (`H(s) = ∫ w(u)² u^{s−1} du`, entire, `≪_j |s|^{−j}` for `|Re s| ≤ 10`), truncation
  `|s| ≲ 1`, the substitution `v = Nmu`, and the van der Corput first/second derivative bounds
  `∫_V^{2V} v^{−1+ir} e(−v) dv ≪ 1/|r|` (`V ≤ |r|/20` or `V ≥ 20|r|`) and `≪ |r|^{−1/2}` (`|r|/20 ≤ V ≤ 20|r|`).
  **Reduction to (6.1)**: `S₂ = 3N³ ĥ₀(0) Σ_{t₁,t₂∈W} |Σ_{m≠0} ĥ_{t₁−t₂}(mN)|² + O(T^{−10})` using (5.1) for `t₁ ≠ t₃`,
  the conjugation symmetry `ĥ_{−t}(ξ) = conj ĥ_t(−ξ)`, then a dyadic split in `|t₁−t₂| ∼ MN` and Lemma 6.2 with
  Cauchy–Schwarz in `u`; the polynomial of (6.1) has length `M ≲ T/N` and `|a_m| ≤ 1`; the `k`-th power in (6.2) has
  coefficients `b_m ≤ M^{o(1)}` by the divisor bound (corpus: `Sieve.DivisorBound.card_divisors_le_rpow`).
* Remaining for Prop. 6.1: (i) Heath-Brown's Theorem 1.6 — **absent from the corpus** (the `huxley_*`,
  `montgomery_heathBrown_*`, Bourgain double-large-sieve modules are the Montgomery–Huxley pointwise-count form, not
  the pair-sum form); it is a sub-programme of its own. (ii) Lemma 6.2 for `ζ` (the CGL `ChenGuptaLiLemma62*`
  family is the character version with conductor; specialise or port). (iii) The reduction to (6.1) on top of
  `cglSmoothBumpHt` and (5.1)–(5.4). (iv) The `k`-fold Dirichlet convolution identity for finite polynomials with the
  divisor-bound coefficient control.

### Source audit for Heath-Brown's Theorem 1.6 (2026-09-08)

* Guth–Maynard cite [HB] = D. R. Heath-Brown, *A large values estimate for Dirichlet polynomials*, J. London Math.
  Soc. (2) 20 (1979), 8–18, Theorem 1 (paywalled: doi:10.1112/jlms/s2-20.1.8). Chen–Gupta–Li (arXiv:2507.08296, §2)
  use the same estimate for characters, `Σ_{(t₁,χ₁),(t₂,χ₂)∈W} |Σ_{n∼N} b_n n^{i(t₁−t₂)} χ₁χ̄₂(n)|² ≲ |W|²N + |W|N² + (qT)^{1/2}|W|^{5/4}N`,
  by citation only. The ANTEDB blueprint (Tao–Trudgian–Yang, `teorth.github.io/expdb`) records it as Lemma 10.18
  ("if `(σ,τ,ρ,ρ*,s) ∈ 𝓔` then `s ≤ max(ρ+1, 2ρ, 5ρ/4 + τ/2) + 1`") with citation only: [HB 1979, Theorem 1] or
  [Ivić, *The Riemann Zeta-Function*, Lemma 11.5]. No open-access proof was found (arXiv 1909.12075 Kerr, 2501.16779
  Tao–Trudgian–Yang, 2403.13157 all cite it).
* Consequence: this brick is **blocked on source access, not on mathematics**. It must not be reconstructed from memory.
  Obtain HB 1979 or Ivić Ch. 11 (Lemma 11.5 and its proof) before any Lean on Theorem 1.6.
* Bricks that are fully sourced from the Guth–Maynard text now on file and can proceed without Theorem 1.6:
  Lemma 6.2 for `ζ` (pp. 19–20: Mellin inversion of `w²`, truncation `|s| ≲ 1`, substitution `v = Nmu`, and the van der
  Corput first/second derivative bounds for `∫_V^{2V} v^{−1+ir} e(−v) dv`; the corpus has `norm_integral_oscillatory_le`
  in `HTGeometry/OscillatoryIntegrationByParts` for the first-derivative case and no second-derivative test yet), and the
  reduction of `S₂` to (6.1) (p. 17–18: (5.1) kills `t₁ ≠ t₃`, `ĥ_{−t}(ξ) = conj ĥ_t(−ξ)`, dyadic split in `|t₁−t₂| ∼ MN`,
  Cauchy–Schwarz in `u`).

### Corpus inventory for Lemma 6.2 (2026-09-08, later)

* Van der Corput derivative tests are corpus-owned: `RHTower.firstDerivTest` (`ContDiff ℝ 2 φ`, `deriv (deriv φ) ≥ 0`,
  `|deriv φ| ≥ λ` on `[a,b]`, `C¹` amplitude `A`: `‖∫ A e^{iφ}‖ ≤ 4(‖A b‖ + ‖A a‖ + ∫‖A'‖)/λ`) and
  `RHTower.secondDerivTest` (`deriv (deriv φ) ≥ μ`: `≤ 32(…)/√μ`), in `RHTower/VanDerCorput.lean`; also
  `VanDerCorputIBP` (frequency lower bound without monotonicity), `VanDerCorputSecond`, `VanDerCorputWeighted*`,
  `DiscreteVanDerCorput`. Do not rebuild them.
* The Chen–Gupta–Li Lemma 6.2 chain (`ChenGuptaLiLemma62*`, ~65 modules, last commit 2026-08-22) already carries the
  Mellin inversion of the bump (`…InitialMellin`, `…MellinKernel`), the contour and horizontal-edge bounds, the
  small-time and large-time source regimes with `X^{−200}` truncation errors (`cglLemma62_smallTime_finiteCritical_window_bound`,
  `cglLemma62_largeTime_finiteCritical_window_bound`: `‖∫ contour integrand‖ ≤ C N^{1/2} ∫ ‖Dirichlet head‖`), the
  principal-character residue and regularized contour (`…Principal*`), and the nonprincipal reassembly
  (`cglLemma62_nonprincipal_smallTime_window_error_X200_bound`, `…largeTime…`). Moduli are `CGLPositiveModulus`
  (`0 < q`), so `q = 1` is admissible. **A single assembled statement of the form `|Σ_{m≠0} ĥ_t(mN)| ≤ …` was not
  found**; before writing Lemma 6.2 for `ζ`, trace this chain to its terminus (start from the two window bounds
  and the `Principal*` modules) and record what is missing. Only then specialise to `q = 1`.

### Terminus of the CGL Lemma 6.2 chain (2026-09-08, later)

Reference count over all `ChenGuptaLi*` modules: 206 theorems in `ChenGuptaLiLemma62*`, of which 24 are referenced
nowhere else. The unreferenced ones are the regime endpoints — `cglLemma62_nonprincipal_smallTime_window_error_X200_bound`,
`cglLemma62_nonprincipal_largeTime_source_bound`, `cglLemma62_smallTime_finiteCritical_window_bound`,
`cglLemma62_largeTime_truncated_conductor_tail_bound`, the `Principal*` residue/reflection/regularized-contour
pieces, and `cglLemma62_smoothedCharacterSum_eq_scale_mul_raw` — so **the chain is unassembled**: no statement of the
form `|Σ_{m≠0} ĥ_t(mN)| ≤ T₀^{−1/2} ∫ |Σ_{m ≲ T₀/N} m^{−i(t+u)}| du + O(T^{−100})` exists. Assembling it (even for `q = 1`)
requires reading the definitions of the regimes (`CGLLemma62SmallTimeSourceRegime`, `…LargeTime…`,
`CGLLemma62InducedCharacter`, the truncation radii and cutoffs) across ~60 modules; it is a multi-day task with
the paper's pp. 19–20 as the only external input. Not started.

### Lemma 6.2 for `ζ`: exact remaining list (2026-09-08, later)

The reassembled nonprincipal branch is closed to `ζ`: `CGLLemma62InducedCharacter` carries `nonprincipal : character ≠ 1`.
The principal branch (`Q : CGLPositiveModulus`, principal character; `q = 1` is `ζ`) has: the contour shift with the
residue at the pole `1 + it` (`cglLemma62_principal_initialVerticalIntegral'_eq_residue_add_reflected`,
`rectIntegral_cglLemma62PrincipalContourIntegrand`), the reflected split into finite head and tail
(`cglLemma62_principal_reflected_eq_finite_add_tail`), the residue bound in the high-time regime
(`cglLemma62_principal_highTime_residue_bound`: `‖residue‖ ≤ C X^{−100}` for `CGLLemma62PrincipalHighTimeSourceRegime`),
the `L`-strip bounds and horizontal edges (`ChenGuptaLiLemma62PrincipalBounds`, `…PrincipalHorizontalEdges`), the
regularized contour integrands and the Euler correction. Missing, in the order of the nonprincipal chain they mirror:
1. `cglLemma62_principal_smallTime/largeTime_finiteCritical_window_bound` — `‖∫_{window} PrincipalFiniteContourIntegrand‖ ≤ C N^{1/2} ∫_{window} ‖Dirichlet head‖` (mirror of `ChenGuptaLiLemma62FiniteWindowBound`, `…LargeTimeFiniteWindowBound`);
2. `cglLemma62_principal_smallTime/largeTime_farTail_truncation_error_X200_bound` (mirror of `…SmallTimeTailTruncation`, `…LargeTimeTailTruncation`);
3. `cglLemma62_principal_reflected_truncation_error_X200_bound` and the reassembly
   `2π·phase·SmoothedSum = residue + finite window + far-tail window + O(X^{−200})` (mirror of `…ReflectedReassembly`, `…NonprincipalReassembly`);
4. the final inequality in Guth–Maynard's form: subtract the `m = 0` Poisson mode (`N ĥ_t(0)`, small for `|t| ≥ X^ε` by the
   `ChenGuptaLiHtReciprocal*` decay) and divide by `N`, giving `|Σ_{m≠0} ĥ_t(mN)| ≤ C T₀^{−1/2} ∫ |Σ_{m ≲ T₀/N} m^{−i(t+u)}| du + O(T^{−100})`
   (the normalizations `N^{1/2}` versus `T₀^{−1/2}` and the window widths must be reconciled against pp. 19–20 of the paper).
Estimated size: four to six modules mirroring the nonprincipal ones (each 100–300 lines). Even when done, Proposition 6.1
for `ζ` stays blocked on Heath-Brown's Theorem 1.6 (source access). Not started.

### Lean (2026-09-08, later): the two modulus facts for the principal window bound

* `HTGeometry/GammaCosineCriticalModulus.lean` (wired, axioms clean, mathlib-only imports):
  `normSq_Gamma_half_sub_mul_I : |Γ(1/2 − iy)|² = π / cosh(πy)` (reflection formula + `Γ(conj z) = conj Γ(z)`),
  `normSq_cos_pi_mul_half_sub_mul_I_div_two : |cos(π(1/2 − iy)/2)|² = cosh(πy)/2` (product-to-sum), and
  **`norm_zetaFunctionalFactor_critical : ‖2 (2π)^{−(1/2−iy)} Γ(1/2−iy) cos(π(1/2−iy)/2)‖ = 1`** — the modulus of
  `cglLemma62PrincipalRegularizedFunctionalFactor (1/2 + iy)` (same expression with `z = 1/2 + iy`, `1 − z = 1/2 − iy`).
* `RHTower/ZetaChiCriticalModulus.lean` (wired after `ZetaCarrier`, axioms clean): `norm_zetaChi_critical :
  ‖zetaChi (1/2 + iy)‖ = 1` from `zetaChi_conj` and the strip identity `χ(s)χ(1−s) = 1`.
* These give the pointwise norm identity for the principal finite integrand on the critical line (mirror of
  `cglLemma62_finiteCritical_norm_eq`): `‖PrincipalRegularizedFiniteContourIntegrand w N Q t M (1/2+iu)‖ =
  ‖Mellin‖ · N^{1/2} · ‖EulerCorrectionAt Q (1/2 + i(u−t))‖ · ‖DirichletHead 1 M (1/2 − i(u−t))‖`, with
  `‖EulerCorrectionAt Q‖ ≤ cglLemma62PrincipalEulerBudget Q` (`= 1` for `q = 1`). Still missing for the window bound:
  the integrability of the principal finite integrand on the critical line (mirror of
  `cglLemma62_finiteContourIntegrand_right_integrable`) and the assembly itself.

### Lean (2026-09-08, later): principal branch on the critical line

`RHTower/ChenGuptaLiLemma62PrincipalCriticalIntegrability.lean` (wired after `…PrincipalRegularizedContour`, axioms clean):
`norm_cglLemma62PrincipalRegularizedFunctionalFactor_critical` (`= 1` on `Re z = 1/2`, via `norm_zetaFunctionalFactor_critical`),
`cglLemma62_principalEulerRightFactorAt_critical_conj`, `cglLemma62_principalEulerLeftFactorAt_critical_ne_zero`,
`norm_cglLemma62PrincipalEulerCorrectionAt_critical` (`= 1`), `norm_cglLemma62DirichletHead_le` (`≤ M + 1` on `Re s ≥ 0`, any
character), the pointwise bound `‖PrincipalRegularizedFiniteContourIntegrand w N Q t M (1/2 + iv)‖ ≤ ‖H(1/2+iv)‖ · N^{1/2} · (M+1)`,
continuity along the line, and **`cglLemma62PrincipalRegularizedFinite_critical_integrable`** (absolute integrability along
`Re s = 1/2`, Mellin decay of order two against the bounded factors). This is the integrability input of the principal
finite-window bound; the window bound itself (mirror of `cglLemma62_smallTime_finiteCritical_window_bound`, now a
`norm_integral_le_integral_norm` + `integral_mono_on` assembly with the pointwise bound) and the truncation/reassembly
mirrors remain.

### Lean (2026-09-08, later): principal finite-window bound

`RHTower/ChenGuptaLiLemma62PrincipalFiniteWindowBound.lean` (wired, axioms clean): the exact critical-line norm
`‖F(1/2+iu)‖ = ‖H(1/2+iu)‖ · N^{1/2} · ‖D_M(1/2 − i(u−t))‖` and
**`cglLemma62_principal_finiteCritical_window_bound (hR : 0 ≤ R) : ‖∫_{−R}^{R} F(1/2+iu) du‖ ≤ C · N^{1/2} · ∫_{−R}^{R} ‖D_M(…)‖ du`**,
`C = cglLemma62MellinLineDecayBudget w (1/2) 0`, for every radius and cutoff (mirror 1 of the missing list, regime-free).
Remaining mirrors: the contour shift of the principal finite integrand from `Re s = −1` to `Re s = 1/2` with its
horizontal edges, the far-tail truncation, and the reassembly with the residue.

### Lean (2026-09-08, later): principal reflected line reassembled (finite → critical line, tail → deep line)

Seven wired modules (axioms `[propext, Classical.choice, Quot.sound]`), all `RHTower/ChenGuptaLiLemma62Principal*`:
- `FiniteStripBounds`: `cglLemma62_exists_bound_principalRegularizedFactor_strip` (Gamma–cosine multiplier
  `≤ C|Im z|^n` on `-1 ≤ Re z ≤ 1/2`, `|Im z| ≥ 1`: Stirling decay of `Γ(1−z)` against `‖cos‖ ≤ e^{π|Im|/2}`),
  `norm_cglLemma62PrincipalEulerCorrectionAt_le_strip` (budget `∏_{p|q} 4(1+p)`; right factor `≥ (1/4)^{ω(q)}`
  since `|p^{-(1-z)}| ≤ 2^{-1/2}`), `cglLemma62_exists_principalRegularizedFinite_strip_bound` (`‖F(x+iy)‖ ≤ C/y²`).
- `FiniteShift`: horizontal edges vanish, vertical integrability on every line of the strip, and
  **`cglLemma62_principalReflectedFinite_integral_eq_critical`**:
  `∫ ReflectedFinite(−1 line) = ∫ F(1/2+iv) dv` (Cauchy on tall rectangles, no residue).
- `TailContour`: `cglLemma62PrincipalTailContourIntegrand` (= `H·N^s·χ_reg·E·(L(1−s+it,χ₀) − D_M)`), its
  identifications on `Re s = −1` (reflected tail) and `Re s = −2k` (`cglLemma62PrincipalFarTailIntegrand`,
  literal complementary series), holomorphy on `−2k ≤ Re s ≤ −1`; `cglLemma62PrincipalEulerCorrectionAt_differentiableAt`
  for every `Re z ≤ 1/2`.
- `TailStripBounds`: `exists_bound_norm_Gamma_low_box` (compactness below unit height),
  `cglLemma62_exists_bound_principalRegularizedFactor_all_heights` (`≤ C(1+|Im z|)^n` on any strip `Re ≤ b < 1`),
  deep Euler budget `∏ 4(1+p^{2k})`, `norm_cglLemma62DirichletTail_one_le` (`≤ M^{-1}` for `Re s ≥ 2`),
  `cglLemma62_exists_principalTail_strip_bound` (arbitrary polynomial decay on the deep strip).
- `TailShift`: **`cglLemma62_principalReflectedTail_integral_eq_farTail`** (`∫ ReflectedTail = ∫ FarTail_k`),
  `cglLemma62_principalFarTail_rapid_point_bound`, `cglLemma62_principalFarTail_integral_sub_truncation_le_power`.
- `ReflectedReassembly`: **`cglLemma62_principal_reflected_integral_eq_finiteCritical_add_farTail`**
  (`∫ ReflectedLine = ∫ F(1/2+iv) + ∫ FarTail_k`, every cutoff `M ≥ 1`, every depth `k ≥ 1`), and
  `cglLemma62_principal_finiteCritical_integral_sub_truncation_le_power`.
- `SmallTimeRegime`: `CGLLemma62PrincipalSmallTimeSourceRegime N Q t` (`X ≥ max(1,q)`, `|t| ≤ X^ε`,
  `M = ⌊X^{2ε}q/N⌋`, depth `⌈(202+ε)/(2ε)⌉`, radius `X^{ε/2}`, rate `⌈2+400/ε⌉`) and
  **`cglLemma62_principal_smallTime_reflected_truncation_error_X200_bound`**: reflected line = critical finite window
  + deep tail window + `O(X^{-200})`.

Tree repair on the way: commit `9b32e9bd1` (2026-09-07) rewrote `HTGeometry/PolygammaVerticalDecay.lean` and deleted
`tendsto_iteratedDeriv_succ_digamma_vertical`, breaking `DigammaFieldValuation`, `LinePolyGrowth` and every
`ChenGuptaLiLemma62Tail*` build. Restored (appended, namespace `GaloisForLFunctions`) from the new
`norm_iteratedDeriv_digamma_le_of_re_pos`; closure rebuilt (11407 jobs).

Remaining for the ζ (principal) Lemma 6.2: (i) the deep-window bound `‖∫_{|v|≤X^{ε/2}} FarTail_k‖ ≪ X^{-200}` — needs the
**sharp** Stirling exponent `‖χ_reg(z)‖ ≤ C(1+|Im z|)^{2k+1/2}` on `Re z ∈ [−2k, −1]` (my strip bound has an
existential exponent, which cannot be traded against `M^{-2k}N^{-2k}`); the nonprincipal chain owns this as
`cglLemma62_primitiveFunctionalFactor_tail_all_factorized_bound` (`TailFunctionalCompact`) — mirror its Gamma input;
(ii) assembly with `cglLemma62_principal_initialVerticalIntegral'_eq_residue_add_reflected`
(`VerticalIntegral' … 2 = residue + (1/2πi)·i·∫ReflectedLine`) into
`SmoothedSum = residue + (1/2π)·window + O(X^{-200})`; (iii) the GM-form inequality (subtract the Poisson `m=0` mode).

### Heath-Brown Theorem 1.6, open-source audit (2026-09-08, later)

Tao's 254A Notes 6 (2015, open) prove the mean-value large-values theorem (`Σ_j |D(σ_j+it_j)|² ≪ (T+N)Σ|a_n|²`, 1-separated
points) and **Montgomery's** large-values bound (Proposition 9: after deleting `O(T^β)` unit intervals,
`|D| ≪ N^{1−σ}(T^{−β/2} + T^{1/4}N^{−1/2}) log^{O(1)}`; ingredients: generalized Bessel inequality, Poisson summation,
oscillatory integrals). They contain **no** Heath-Brown estimate (no `T^{1/2}` or `|𝒯|^{5/4}` term) and refer to
Iwaniec–Kowalski Ch. 9–10 for the refinements. The block stands: HB 1979 JLMS Thm 1 / Ivić / Iwaniec–Kowalski are the
only proofs on record and none is open-access. Montgomery's Proposition 9 is a possible weaker substitute for the `S₂`
bound; whether GM's Theorem 1.1 survives with it is not examined.

### Heath-Brown Theorem 1.6, source audit continued (2026-10-03)
* Checked: Kerr arXiv:1909.12075 (Theorem 1), Tao–Trudgian–Yang arXiv:2501.16779 (and the ANTEDB blueprint,
  Lemma 10.18 `add_lver_heath_brown_1979`), Chen–Gupta–Li arXiv:2507.08296 (Theorem 10.1, character form). All
  cite [HB79b, Theorem 1] or Ivić Lemma 11.5; none prove it. The PSU study-group notes (`Heath-Brown.pdf`) are
  offline (404); the Wiley PDF is behind a bot wall.
* Paper attempts at a proof from corpus tools (positivity reduction to `a_n ≡ 1`; Kusmin–Landau for `N ≥ T`;
  reflection `N ↦ T/N`; Hölder lengthening; dual large sieve with ratio multiplicities; Halász with the
  `|ζ|` kernel; pointwise twelfth moment) all stop at `|𝒯|^{3/2}T^{1/2}` or `|𝒯|^{11/6}T^{1/3}`; the `5/4`
  needs an input beyond these. Still blocked on the source.

### Programme resumed (2026-10-21): sources and work split

* Sources. Guth–Maynard is open (arXiv 2405.20552v2; Oxford ORA copy
  `https://ora.ox.ac.uk/objects/uuid:ad11b8bf-ad2b-4ebf-a627-647f023c378f/files/s73666708v`). Heath-Brown 1979
  (JLMS 20, DOI 10.1112/jlms/s2-20.1.8) and Jutila 1977 (Acta Arith. 32, `matwbn.icm.edu.pl/ksiazki/aa/aa32/aa3216.pdf`)
  are behind bot walls for automated fetches (Wiley 403, Anubis challenge on matwbn); a browser download would
  unblock them. The Warwick notes (Seth Hardy, Feb 2025, "Large values of Dirichlet polynomials: difference sets and
  additive energy", `warwick.ac.uk/fac/sci/maths/people/staff/hardy/large_values_of_dirichlet_polynomials.pdf`) state
  Heath-Brown's theorem verbatim — `Σ_{r,s≤R}|Σ_{n∼N} a_n n^{−i(t_r−t_s)}|² ≤ T^{o(1)}(R²N + RN² + R^{5/4}T^{1/2}N)`,
  last term droppable for `N ∈ [T^{2/3}, T]` — and sketch its proof: majorant principle through
  `Σ_{r,s}|Σ_n a_n n^{−i(t_r−t_s)}|² = Σ_{n,m} a_n ā_m |Σ_r (n/m)^{−it_r}|²`; Jutila's smoothed approximate functional
  equation (`|Σ_n b_n n^{−it}| ≪ N^{1/2}∫_{−h²}^{h²}|Σ_{n≤T/πN} n^{−1/2+i(t+τ)}|dτ`, `b_n = e^{−(n/2N)^h} − e^{−(n/N)^h}`,
  `h = log T`, `T^ε < |t| ≤ T`); Heath-Brown's Lemma 2 (monotonicity of `𝒜(N) = Σ_{r,s}|Σ_{n∼N} n^{−1/2−i(t_r−t_s)}|²`
  in `N`, "white lie" form) with the corollary `𝒜(T/πN) ≤ T^{o(1)} R 𝒜(N)^{1/2}` (Cauchy–Schwarz, fourth moment,
  divisor bound); and the bootstrap `𝒜(N) ≪ RN + T^{o(1)}R𝒜(N)^{1/2} ⇒ 𝒜(N) ≪ T^{o(1)}(RN + R²)`. The same notes
  (§3) sketch the high-energy application: `E(S_V) ≤ V^{−2}|S_V| Σ_{t₁,t₂∈S_V}|Σ_{n∼N} n^{−i(t₁−t₂)}|²`, hence
  `E(S_V) ≤ T^{o(1)}(|S_V|³NV^{−2} + |S_V|²N²V^{−2})` for `N ∈ (T^{2/3}, T]`.
* Work split (five Lean agents, user-authorised): (1) Heath-Brown pair-sum theorem,
  `RHTower/Sieve/HeathBrownPairSum*`; (2) Lemma 6.2 for `ζ` in Guth–Maynard form and the `S₂` reduction to (6.1),
  `RHTower/ChenGuptaLiLemma62Principal*`, `RHTower/Sieve/GuthMaynardSTwoReduction*`; (3)–(5) Sections 7–11 of the
  paper (Prop. 7.1–7.2, the `R̃` moments, the small-closed-set argument, the energy bound, Prop. 3.1 and the
  reduction to Theorem 1.1), split after the statement extraction of pp. 20–45.
* Consumers waiting on Theorem 1.1: `N(σ,T) ≪ T^{(30/13)(1−σ)+o(1)}` through the corpus's class-count machinery
  (`ZetaZeroDensityEdgeRanges`, `class_count_*_of_exponent`, `ZetaZeroDensityTwelveFifths` as the template), then
  primes in `(x, x + x^{17/30+ε}]` through `tendsto_tsum_zeroShortWeight_of_density` (any exponent `A < 4`), and the
  prime-row dispersion regime of `BezoutValuationIncidence/CentredPrimeRowPassesTheCoherentBlockObstruction`
  extends from `Q ≤ P^{12/7}` to `Q ≤ P^{30/17}`.

### 2026-10-21 (later) — second wave and fixed interfaces

Running bricks (each in its own `RHTower/Sieve/GuthMaynard<Section>*.lean` modules, new files only):
Heath-Brown pair sum (`HeathBrownPairSum*`), Lemma 6.2 for ζ + S₂ reduction (`ChenGuptaLiLemma62Principal*`,
`GuthMaynardSTwoReduction*`), §7 (`GuthMaynardSmoothedLagSum`, `GuthMaynardCubicTermIntegral`,
`GuthMaynardPropSevenOne*`, `GuthMaynardPropSevenTwo*`), §8 (`GuthMaynardLagSumL2`, `…L4`,
`GuthMaynardSmoothedLagSumFourierDecay`, `GuthMaynardPropEightOne`), §9–10 (`GuthMaynardAffineSum`,
`…AffineIteration`, `…AffineEquidistribution`, `GuthMaynardPropTenOne`).

Briefs written for the next wave (scratchpad `gm-brief-s11-energy.md`, `gm-brief-s12-assembly.md`,
`gm-brief-s13-zero-density.md`): §11 energy bound (Lemmas 11.3–11.9, 1.5, Props 11.1, 11.2), §3+§12 assembly
(Prop 3.1 from the S-bounds, Theorem 1.1 from Prop 3.1, Prop 12.1), §13.1 zero density through the corpus
detector (`exists_window_class_card_le` template, `exists_zeroHeightBox_ncard_le_window`,
`tendsto_tsum_zeroShortWeight_of_density` for the 17/30 transfer).

Fixed Lean shape of Theorem 1.1 (interface between the §12 and §13 bricks):
`theorem guthMaynard_largeValues {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (T T₀ V : ℝ) (b : ℕ → ℂ)
(W : Finset ℝ), 1 ≤ N → 2 ≤ T → 0 < V → (∀ n, ‖b n‖ ≤ 1) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
(∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t − t'|) →
(∀ t ∈ W, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
(W.card : ℝ) ≤ C * T ^ ε * (N² / V² + N^{18/5} / V⁴ + T N^{12/5} / V⁴)`, plus the scaled form for `‖b n‖ ≤ B`.
Zero-density target: `ncard (zeroHeightBox σ T) ≤ D (1 + log T)^B T^{(30/13 + ε)(1−σ)}` uniformly in
`σ ∈ [1/2, 1]` for `T ≥ T₀`; window `a = 10/(6 + 10σ)` (ratio 3/2, equal to (13.1)) on `[7/10, 8/10]`,
mean-value window `a = 10/13` below, Huxley window `a = 35/52` above; then `u < 13/30` in
`tendsto_tsum_zeroShortWeight_of_density` gives `ψ(x + x^α) − ψ(x) ∼ x^α` for `α > 17/30`.
