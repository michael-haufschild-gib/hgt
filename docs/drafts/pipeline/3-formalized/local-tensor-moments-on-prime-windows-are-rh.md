# Local tensor moments on prime windows are RH

- **ID:** A71
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** RH is equivalent to `∃ A, ∀ k≥1, ∃ C_k, ∀ U, ∃ T≥U, Σ_{p in window(T)} log p · (2c_B(log p))^(2k) ≤ C_k exp(A T)`.

## Proof

Under RH the prime trace is bounded on arbitrarily late logarithmic windows. Each window has at most `2 exp(2T)` primes, each with `log p≤exp(2T)`, giving exponent `A=4` for every order.

Conversely, on a sufficiently late window each nonnegative summand is bounded by its moment, `log p≥1`, and `T≤2 log p`. Taking the `2k`-th root bounds the prime trace by `|C_k|^(1/(2k)) p^(|A|/k)`. The absolute logarithmic-window criterion puts every zero in `Re ρ≤1/2+|A|/k`. Since the exponent `A` is independent of `k`, every zero lies on the critical line.

Constants and observation windows may depend on the tensor order; no compatibility is required.

## Formalization

- Module: `SurfaceOfSpecZ/ScaleLocality/LocalTensorMoments.lean`.
- Theorems: `zeta_re_le_of_localPrimeTraceMoment_bound`, `riemannHypothesis_iff_localPrimeTraceMoments`.
- Direct `lake --old env lean` audit passed. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `SurfaceOfSpecZ.lean`.
