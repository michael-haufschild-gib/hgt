# Finite core projections retain every direction

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `MayerScattering/WindowCoreProjectionAndTailCompensation.lean`.
- **Statement:** Every positive-length real window surjects onto every finite PM core span. Finite projection positivity is exactly critical-line confinement of its resonances; short-window coercivity includes essential omitted-tail compensation.

## Exact statements

Write `s♯=1/2−conjugate(s)` and `P(S)=S∪S♯`. For every `A>0`, finite upper-resonance set `S`, and prescribed complex coefficients `c_s`, a real `C²` test supported in `[−A,0]` satisfies

`windowZeroMap(H)(2s)=c_s`, `s∈S`.

Consequently every actual PM core vector supported in `P(S)` equals the finite packet `v_S(H)` of such a test. In particular,

`∀H∈windowTests(A), Re[v_S(H),v_S(H)]≥0`

iff every `s∈S` has `Re s=1/4`.

If an included resonance lies off that line, a test realizes `b_s−b_(s♯)` and has finite Krein square `−2`. For `0<A≤1/1000`, its omitted complete-Weil tail obeys

`Q(H)−2 Re[v_S(H),v_S(H)] ≥ 4+∫H²/4`.

This does not assert that off-line resonances exist. It distinguishes full short-window positivity from positivity of each finite spectral projection.

## Proof

For upper resonances, the Fourier nodes `γ_(2s)` have positive real part. They and their reflections `−conjugate(γ_(2s))` are distinct. Existing interpolation on any interval `[-A/2,A/2]`, with conjugate data at reflected nodes, followed by taking the real part, preserves the prescribed values because

`FT(Re f)(z)=(FT(f)(z)+conjugate(FT(f)(−conjugate(z))))/2`.

Translate to `[−A,0]`; compensate its nonzero exponential factor and the positive square-root multiplicities. This gives arbitrary finite coordinates. Applying the existing PM basis representation yields surjectivity onto its finite span.

An off-line reflection pair has the existing core vector `b_s−b_(s♯)` of square `−2`, so surjectivity rules out positivity on that projection. Conversely, on-line reflection fixes the selected span and the Krein form equals its positive coefficient inner product. Existing CWS short-window coercivity gives the tail inequality.

## Lean audit

- `exists_windowZeroMap_prescribed`
- `exists_windowWeilCorePacket_eq`
- `exists_windowWeilCorePacket_neg_two`
- `windowWeilCorePacket_nonneg_iff`
- `exists_short_window_core_tail_compensation`

Final individual `lake --old env lean` check passed without warnings. All four printed endpoint audits use only `propext`, `Classical.choice`, `Quot.sound`. Imported by `RenormalizedIntersectionTheory.lean`.
