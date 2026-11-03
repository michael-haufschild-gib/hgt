# Bulk entries at overlap c and character packets

- **ID:** BEOC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** AHD README §9 item 2 (after BSOS: the prime part of the bulk entries)
- **Statement:** (i) character packets `X_χ(n) = χ(n)/√n`, `χ, ψ ≠ 1` mod `q`: `⟨P X_χ, X_ψ⟩ − (S_ψ + S̄_χ)⟨X_χ, X_ψ⟩ →
  [χ = ψ] (φ(q)/q)(I_χ + Ī_χ)`, `S_χ = −L'/L(1, χ)`, `I_χ = −(L'/L)'(1, χ)`; (ii) at overlap `0 < c < 1` the complete Weil
  entry `⟨W R_e, R_{e'}⟩ − E_e(c)⟨R_e, R_{e'}⟩ → −D(e, e') + Cen_α(e, e') − Cr_{φ,c}(e, e')`.

## Goal
The second order of every bulk entry of the complete Weil matrix at fixed overlap, and of the prime matrix on
character packets (where `L'(1, χ)/L(1, χ)` enters: it is the first-order energy, and `(L'/L)'(1, χ)` the second order).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proof (below), numerically confirmed
- [x] 2 → 3  formalized: `tendsto_charPacketPairing_sub` (TheCharacterPacketsReadTheLogarithmicDerivative),
  `tendsto_completeWeilBulkEntry` (TheBulkEntriesAtEveryOverlap), with `tendsto_centerPairing_sub`
  (TheCenterPartOfTheBulkEntries), `tendsto_crossPairing` (TheCrossErrorOfTheBulkEntries) and the hyperbola
  lemmas `tendsto_sum_periodic_mul_hyperbola`, `tendsto_sum_hyperbola_sub_integral`
  (HyperbolaSumsOfAVonMangoldtTail), all in `ArithmeticHodgeTheoryOfDegenerations/`

## Statements and proofs
**Characters.** `B(χ,ψ) = Σ_{nm ≤ N} η(n)/n (ψ(m) + χ̄(m))Λ(m)/m`, `η = ψχ̄`, `⟨X_χ, X_ψ⟩ = Σ_{n≤N} η(n)/n`. With
`S(x) = Σ_{m ≤ x} χ(m)Λ(m)/m → S_χ` (MCAP) and `δ = S − S_χ`: `B − (S_ψ + S̄_χ)⟨X_χ,X_ψ⟩ = Σ_{n≤N} η(n)/n (δ_ψ + δ̄_χ)(⌊N/n⌋)`.
(a) mean-zero periodic `v`: `Σ_{n ≤ N} v(n)δ(⌊N/n⌋)/n → 0` (Abel in `n`; `Σ |δ(⌊N/n⌋)|/n² → 0`; block variation
`Σ_n (1/n)|δ(⌊N/n⌋) − δ(⌊N/(n+1)⌋)| → 0`: `n ≤ K` by `δ → 0`, `n > K` by `1/n < 2m/N` on the block and Chebyshev).
(b) `Σ_{n≤N} δ(⌊N/n⌋)/n − ∫_0^{log N} δ(⌊e^u⌋) du → 0` (same two estimates).
(c) Newman: `f(u) = δ(⌊e^u⌋)` bounded, `∫_0^∞ f e^{−zu} = (G(z) − G(0))/z`, `G(z) = −L'/L(1+z, χ)`; `dslope G 0` analytic on
`Re z ≥ 0`; so `∫_0^T f → G'(0) = I_χ`. Mean of `‖χ‖²` is `φ(q)/q`. Numerics (N = 4·10⁶, q = 3,4,5,7): 3 digits.

**Overlap.** `W = (log N + F(c) − γ + s_N)I − P + Cen − Cr + Pe` (RAPT, `c/N < atomSpacing N`), `E_e(c) = F − γ + ρ_e + [e=1]α`.
`s_N ⟨R_e,R_{e'}⟩ → 0`, `⟨Pe R_e, R_{e'}⟩ → 0` (coefficient `O(N^{-3})`).
Center, pole gauge: `Cen/(√n√j) = (α/N)(1/n + 1/j − [n≠j]½(1/|n−j| + 1/(n+j)))`; limits (minus `[e=1]α⟨R_e,R_{e'}⟩`):
`(1,1): α(1 − log 2)`; `(e,e), e>1: αΛ(e)/φ(e)`; `(e,1), e>1: −αΛ(e)/√φ(e)`; otherwise `0` (numerics N = 8000).
Cross error: `Cr(n,j) = (w/∫φ²)∫A_φ(τ)(ω(s + wτ) − ω(s))dτ`, `w = c/N`, `s = |log(j/n)|`, `ω(y) = 1/(2y) + O(1)`;
limit `[e=e'](c/(φ(e)∫φ²)) Σ_{d≥1} c_e(d) ∫ A_φ(τ)(log(1 + cτ/d)/(cτ) − 1/d) dτ` (numerics: 6 digits, c = 0.5, 0.9).

## Log
- 2026-11-03 — proved and formalized.
