# Vinogradov–Korobov cancellation in the undamped Möbius Hilbert form

- **Stage:** 3-formalized
- **Wall:** Π50
- **Theorem:** For some C>0 and all large T, uniformly for every N≤T,
  `0≤H(N)=Σ_{m,n≤N} μ(m)μ(n)/(m+n) ≤ C T exp(−κ vkScale(T)/27)`.
- **Scope:** Actual undamped Hilbert form; subpower growth remains open.

Here `vkScale(x)=(log x)^(3/5)(log log x)^(-5/3)` and
`κ=1/(12·10^8)`, matching the corpus's unconditional Mertens bound.

## Paper proof

Put `Q=vkScale` and `s=κQ(T)/27`. The existing Abel–Cauchy estimate gives
`H(N) ≤ M(N)²/N + 2Σ_{1≤n≤N} M(n)²/n²`.
Vinogradov–Korobov gives `|M(n)|≤B n exp(−κQ(n)/24)` for n≥n₀.
Take T≥n₀² and log T≥3. For uniformity in N≤T, extend the nonnegative
sum through T and split at √T. Its lower part costs at most √T because
`|M(n)|≤n`. On the upper part, n≥n₀ and `Q(n)≥(4/9)Q(T)`, so each squared
normalized summand costs at most `B² exp(−s)`. Thus the sum costs at most
`√T+B²T exp(−s)`.

Split the endpoint at the same cutoff: its small case costs √T, and its
large case costs `B²T exp(−s)`. Consequently
`H(N)≤3√T+3B²T exp(−s)` for every 1≤N≤T; H(0)=0.
Since Q(T)/log T→0, eventually s≤log(T)/2, so
`√T≤T exp(−s)`. Choose C=3+3B². This proves uniform control
without assuming monotonicity of H, whose signed finite sections need not
be monotone.

## Corpus boundary

`MobiusMertensMeanSquareExponentLaw.finiteMobiusGammaHankelEnergy_le_mertens`
supplies the energy comparison. Existing BVI Vinogradov–Korobov estimates
control damped divisor-incidence energies, not this undamped Hilbert form.
No new zero-free region or Mertens estimate is claimed.

## Verification

Module: `ArithmeticContinuationAndCriticalEnergy/MobiusHilbertVinogradovKorobov.lean`.
Theorem: `exists_uniform_mobiusHilbert_le_vinogradovKorobov`.

Direct `lake --old env lean` audit passed without warnings.
Transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.
Umbrella and README wired; no olean or umbrella build.

Π50: Sharpened → Partially solved. The undamped Hilbert form now has this
unconditional upper bound; its RH-equivalent subpower estimate and the
small-damping horizon-uniform incidence estimate remain open.
