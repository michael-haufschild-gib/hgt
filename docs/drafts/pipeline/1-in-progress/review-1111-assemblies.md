# Review-1111 assemblies of proved pieces

- **ID:** review-1111-assemblies
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1111/obstacles-summary.md`, §2.1, "Assemblies of proved pieces".
- **Goal:** a complete, unconditional Lean solution for each task, easiest first.

## Status

| Task | Status |
|---|---|
| A78 | Already a theorem: `SurfaceOfSpecZ.ScaleLocality.finite_top_negative_in_every_window` (any finite top layer, no separation, windows longer than `card(S)π/Γ`). |
| A47 | Already formalized: `3-formalized/one-quartet-current-constant.md`. |
| A136 | Frontier map now grades the comb index, trace classification, Laguerre tails, horocycle and detector moment modules [L]. `ReflectedHalvesAreNotDirichletSeries` compiles cleanly. `TheShiftedSelbergFormIsAHarmonicModel`, `TheMobiusKernelConvergesInMean` are under active peer edits (MZF/Levinson card A111): not touched. |
| A134 | Owned by the peer Levinson card `levinson-gate-from-below-square-root-twists.md` (A111): not duplicated. |
| A133 | In progress (below). |
| A137, A135, A89, A132 | Queued. |

## A133: the degree-two Artin character of `ℚ(∛2, ω)`

**Target.** For the two-dimensional character `ρ` of `Gal(ℚ(∛2,ω)/ℚ) ≅ S₃`, with contacts
`Λ_ρ(p^k) = (#{x ∈ 𝔽_{p^k} : x³ = 2} − 1) log p` for `p ∤ 6` and `0` for `p | 6`
(trace of Frobenius on the permutation representation minus the trivial one): Weil's form of `ρ`
has `n` negative squares on some family of `n` tests iff `L(s,ρ)` has at least `n` distinct right
zeros.

**Proof.**
1. `K = ℚ(ω)`, `𝔪 = (6)`. Every ideal prime to `3` has a unique generator `α ≡ ±1 (mod 3)`
   (the six units map bijectively onto `(ℤ[ω]/3)ˣ`). `χ(𝔞) = α mod 2 ∈ 𝔽₄ˣ ≅ μ₃` is a ray
   class character mod `(6)`; the ray class group mod `(6)` has order `18/6 = 3` and the
   ray class groups mod `2`, `3`, `2λ` are trivial, so `χ` is primitive of conductor `(6)`.
2. Cubic character of 2. For `p ≡ 1 (3)`, `p = ππ̄`, `χ_π(a) ≡ a^{(p−1)/3} (mod π)`:
   `J = Σ_a χ_π(a)χ_π(1−a)`. The group `⟨a↦1−a, a↦1/a⟩ ≅ S₃` preserves `χ_π(a(1−a))` on
   `𝔽_p∖{0,1}`; orbits have size 6 except `{2, −1, 1/2}` (value `χ_π(2)`) and the two primitive
   sixth roots (value `1`). So `J = 2 + 3χ_π(2) + 6S`, hence `J ≡ −1 (3)` and `J ≡ χ_π(2) (2)`.
   `J ≡ 0 (π)` (degree `2(p−1)/3 < p−1` power sum) and `N(J) = p`, so `J` is the associate of `π`
   that is `≡ −1 (3)`. Therefore `χ(𝔭) = (2/π)₃`: 2 is a cube mod `p` iff `χ(𝔭) = 1`.
3. Contacts. Inert `p ≡ 2 (3)`, `p ≠ 2`: `χ((p)) = 1`, `x³ = 2` has one root in `𝔽_{p^k}` for
   odd `k` and three for even `k`. Split `p`: `#{x³=2 in 𝔽_{p^k}} − 1 = χ(𝔭)^k + χ(𝔭̄)^k`.
   `p = 2, 3`: both sides vanish. So `heckeMangoldt χ = Λ_ρ`.
4. Apply `exists_le_negIndex_heckeGram_iff` and `W_heckeZeros_eq` to `χ`.

## Queued notes

- A137: an asymptotic of `x^{−Θ}M_φ(x)` needs control of `Σ 1/ζ′(ρ)` near the top line; the
  explicit formula for `Λ` uses integral multiplicities and has no such input. Decide the
  strongest unconditional statement before formalizing.
