# Fable 3010, §6: the three questions (Q-A receiver rate, Q-B same-point, Q-C coalescent surplus)

- **ID:** fable-3010-q5
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop)
- **Source:** ../../../reports/review-3010/fable.md §6
- **Statement:** Full answers, formalized unconditionally, to Q-A (rate `r(N)` with
  `c_N = c*_N r(N)` an RH receiver; can `r` be bounded), Q-B (prime-side bound for the Hecke
  defect at `L ≍ log T`, or `O(T) ≤ cN(T)`, `c < 1/4`), Q-C (`CoalescentSurplusAtMost β`, `β ≤ 2`).

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2
- [ ] 2 → 3

## Facts fixed by reading the corpus

- Receiver synthesis (`SuperGevreyCriticalGrowth`): RH ⇔ eventual atomic positivity of a
  logarithmic-DC profile for **every** dilation `κ_N` with `(N/κ_N)/(L (log L)²) → ∞`,
  `L = log log κ_N` (`riemannHypothesis_iff_atomicFamilies_nonneg_of_superGevrey`). The
  "endpoint" `L(log L)² log log L` is one instance; the condition is `r → ∞` relative to
  `L (log L)²`, at any speed.
- Synthesis places a test of log-width `2R` at the top block `[N/B, N]`, `B = blockSize R ≍ e^{2R}`;
  the overlap at the bottom of the block is `c/B`. Synthesis error ≈ derivative majorant of
  the Fourier tail at `c/B`, Weil weight `log N` (`synthLevy`: `log κ · err² → 0`).
- Q-C as stated is a zero-free-strip statement: the Zeta23 Gram matrix at `λ = 4/3`
  (`X = T^{4/3}`) has zero side `Σ_ρ φ̂(γ_ρ−τ_k)φ̂(γ_ρ−τ_l)`, off-line terms of size `X^{δ}`,
  Frobenius contribution `X^{2δ} = T^{(8/3)δ}` against normalization `≍ T log³ T`; a bound on
  the prime surplus at budget `O(1)` forces `δ ≤ 3/8`, i.e. no zeros with `Re ρ > 7/8 + ε` at
  large height. (paper argument; not yet formalized)
- Q-B in the `N`-normalized form is the `75 %` problem (`N − N₀ ≤ O`).

## Q-A — answered and formalized

Units: `μ_B(c) = inf_q B^q q! (log(q+3))^{2q}/c^q` is the derivative majorant of the Fourier
tail (`|φ̂(ξ)| ≤ A μ_B(2π|ξ|)`); `c*_N` = least `c ≥ 1` with `μ_B(c)² log N ≤ 1`. Since
`μ_B ≥ |φ̂|/A`, this `c*` is the critical overlap of the majorant, not of the exact transform.

Answer.
1. `c*_N ≍ L (log L)²`: `L(log L)²/(32e) ≤ c*_N ≤ 4eB L(log L)²` eventually.
2. Every unbounded rate is a receiver: `r_N → ∞`, `N/(r_N c*_N) → ∞` ⇒ RH ⇔ eventual
   nonnegativity at overlap `r_N c*_N`, for every profile of the class (Steklov: `B = 12`).
3. RH ⇔ for every `K ≥ 1`, eventual nonnegativity at overlap `K c*_N`.
4. One bounded rate `K` sees a window: eventual nonnegativity at `K c*_N` ⇒ `W(g) ≥ 0` for every
   `C²` test supported in `[−R, R]` with `24 e B ⌈1 + e^{2(R+1)}⌉ < K/(32e)`; radius
   `½ log K + O(1)`. Mechanism: a radius-`R` test is synthesized on the block `[N/B, N]`,
   `B ≍ e^{2R}`, where the quadrature ratio is `≤ 24 B_φ B/K < e^{−1}`.
So `r` can be bounded only jointly (all `K`); a single bounded `r` reads Weil positivity on a
window of radius `½ log r + O(1)`, and RH-completeness requires every window.

Lean (`TransMetzlerWeilPositivity/`, umbrella wired; `lake --old env lean` clean; axioms
`propext`, `Classical.choice`, `Quot.sound`):
- `ABoundedOverlapRateSeesASemilocalWindow`: `dcRate`, `dcScale`,
  `nonneg_of_atomicFamilies_nonneg_of_rate`, `riemannHypothesis_iff_forall_bounded_rate`,
  `riemannHypothesis_iff_nonneg_of_divergent_rate`, `steklovDCProfile_window`.
- `TheCriticalOverlapIsLogLogTimesLogSquared`: `dcMajorant`, `dcCriticalOverlap`,
  `norm_fourier_le_dcMajorant`, `dcMajorant_le_exp`, `exp_le_dcMajorant`,
  `eventually_dcCriticalOverlap_le`, `eventually_le_dcCriticalOverlap`,
  `riemannHypothesis_iff_nonneg_of_critical_rate`, `nonneg_of_critical_multiple`,
  `riemannHypothesis_iff_forall_critical_multiple`,
  `riemannHypothesis_iff_steklovDCProfile_critical_multiples`.

## Q-B, Q-C — what the statements contain

- Q-C (`coalescentSurplus u η T ≤ (1/18 + ε) N(T,2T)`, the `75 %` budget; the review's
  "`β ≤ 2`" is the form-factor loss factor, not the Lean budget `β`): prime side of the
  bandwidth-`4/3` Frobenius norm = diagonal `43/36` + coalescent band + `o(N)`. The zero side
  contains `Σ_{off-line} X^{2δ_ρ}`-size terms, `X = T^{4/3}`. A budget `O(N)` forces
  `Σ_{ρ off-line, T<γ≤2T} T^{(8/3)δ_ρ} ≪ T polylog T`: no zeros with `Re ρ > 7/8 + o(1)`, and a
  density bound stronger than the density hypothesis near `σ = 3/4`.
- Q-B: `N − N₀ ≤ O`; `O(T) ≤ cN(T)`, `c < 1/4`, is the `75 %` theorem. A depth-weighted Hecke
  defect at `L = κ log T` does not see zeros with `δ ≪ 1/log T`, so it cannot by itself bound `O`.


## Loop record (Q-B, Q-C)

- C1 (paper, open caveat). At `λ = 4/3` the zero-side Gram matrix is `Σ_ρ m_ρ a_ρ a_ρᵀ` with
  `a_ρ = φ̂(γ_ρ − τ_k)` (bilinear). For an off-line pair the cross term `(a_ρ·ā_ρ)² = ‖a_ρ‖⁴`
  enters `‖G‖_F²`, and `‖a_ρ‖² ≍ L·X^{δ}` (sesquilinear norm sees depth; bilinear trace is blind).
  Hence a Frobenius budget `O(L²N)` forces `X^{δ} ≲ √N` for an isolated off-line pair:
  `Re ρ ≤ 7/8 + o(1)`. Not closed: cross terms `(a_ρ·a_ρ′)²` between distinct off-line zeros are
  complex squares and may cancel; no rigorous non-cancellation argument yet.
- B1 (corpus fact). `RHTower.exists_eventually_offLineBlock_le`:
  `Σ_{β>1/2, S≤γ≤2S} (2S)^{β−1/2} ≤ C S (log 2S)^{19/10}`, and `depthKernel(½ log 2S, δ) ≤ (2S)^δ`:
  the Hecke-defect depth trace at `L = ½ log T` over a height block is `O(N (log N)^{9/10})`.
  Layer rates (`22/25` near the line, `6/5` Ingham–Gabriel) give `O(N)` for `L = κ log T`,
  `2κ < 0.84`. This answers the literal first form of Q-B; it cannot reach the `c < 1/4` form,
  since the kernel vanishes to second order at depth `0`.
- Barrier map. Simple-critical proportion in the rank–trace method is `2 − κ(λ)`,
  `κ(λ) = 1/λ + λ/3 ≥ 4/3` for `λ ≤ 1`; `75 %` needs `κ ≤ 5/4`, hence `λ > 1`, hence
  trans-threshold prime pairs; at `λ > 1` the off-line zeros enter with weight `X^{2δ}`.
  `O/N` is the `α → ∞` limit of the multiplicity-weighted pair correlation minus one.

## Log
- 2026-10-30 — card created; corpus read for all three questions.
- 2026-10-30 — Q-A formalized (two modules). Q-B/Q-C content analysed; loop continues on Q-B/Q-C.
