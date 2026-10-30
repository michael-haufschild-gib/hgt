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

## Q-A — working answer

1. Every unbounded rate is a receiver (corpus theorem, once `c*_N ≍ L (log L)²` is fixed).
2. RH ⇔ for every `K`, eventual positivity at `K c*_N` (diagonal argument from 1).
3. One bounded rate `K` synthesizes exactly the tests of log-width `≲ log K` at the top block:
   positivity at `K c*_N` ⇒ Weil positivity on tests supported in a window growing with `K`.
To formalize: 2 and 3 with the DC majorant; the Fourier-tail lower bound that identifies
`c*_N` for a box-convolution profile.

## Log
- 2026-10-30 — card created; corpus read for all three questions.
