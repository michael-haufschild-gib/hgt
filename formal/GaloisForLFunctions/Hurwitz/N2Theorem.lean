/-
# Hurwitz N=2 — the final theorem (conditional on the Laurent-coefficient extractions)

Ties the whole assembly. The relation is taken in the genuine **factored** form, `F_k = E_k + R_k` with
`E_k = e^{−(s+k)z}` and `R_k = tailFactored s k n (e^z)` (the cut-free analytic tail = the genuine
analytic Hurwitz local expansion; the principal `cpow` series is non-analytic near `a=−n` and is *not*
used). From it:

* `relation_collect` + `PhiB_eq_products` give `Φb + Ψb + Θb = relation = 0` on the strip;
* `n2_blocks_vanish` (analyticity from `blockSum_analytic`, periodicity from `tailFactored_periodic`)
  ⟹ each block vanishes on the deep half-plane;
* `n2_quad_coeffs` ⟹ `q₀₀ = q₂₂ = 0` and the survivor identity `q₀₂ + q₁₁ + q₂₀ = 0`;
* `n2_survivor_and_linear` (the density-shadow / non-rationality core) ⟹ the survivor `q₀₂+q₂₀ = 0`
  (hence `q₁₁ = 0`) and `l₂ = l₀ = l₁ = c = 0`.

The only inputs taken as named hypotheses are the **Laurent-coefficient extractions** `hrow, h0, h1, hc`
— the `x^{−s−k}`-coefficient relations `lim_{x→0} x^{s+k}·(block) = 0`. Everything else is discharged.
-/
import GaloisForLFunctions.Hurwitz.N2BlockAnalytic
import GaloisForLFunctions.Hurwitz.N2DensityShadow
import Mathlib.Analysis.Complex.ExponentialBounds

open Complex HurwitzN2Main HurwitzN2Tail HurwitzN2BlockAnalytic HurwitzN2DensityShadow
open HurwitzZetaShift HurwitzEncoding

namespace HurwitzN2Theorem

/-- **Hurwitz N=2 — no quadratic relation among `ζ(s,a), ζ(s+1,a), ζ(s+2,a)`** (conditional on the
Laurent extractions). With `1 < s.re`, `s ∉ ℤ`, `2s ∉ ℤ`, if the genuine relation
`∑_{i,j} q_{ij}(a)F_iF_j + ∑_k l_k(a)F_k + c(a) = 0` holds near every large `a = −n` (`F_k` the analytic
local expansion `E_k + R_k`), and the Laurent-coefficient extractions `hrow, h0, h1, hc` hold, then the
symmetric quadratic form, the linear coefficients, and the constant all vanish:
`q₀₀ = q₂₂ = q₁₁ = 0`, `q₀₂ + q₂₀ = 0`, `l₂ = l₀ = l₁ = 0`, `c = 0`. -/
theorem hurwitz_n2 {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s) (h2sZ : ∀ k : ℤ, (k : ℂ) ≠ 2 * s)
    (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ) {N : ℕ}
    (hrel : ∀ n, N ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + Complex.exp z) *
          ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin 3, (l k).eval (-(n : ℂ) + Complex.exp z) *
            (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0)
    (hrow : ∀ᶠ n : ℕ in Filter.atTop,
      (q 0 2 + q 2 0).eval (-(n : ℂ)) * hzeta s (-(n : ℂ)) + (l 2).eval (-(n : ℂ)) = 0)
    (h0 : ∀ᶠ n : ℕ in Filter.atTop, (l 0).eval (-(n : ℂ)) = 0)
    (h1 : ∀ᶠ n : ℕ in Filter.atTop, (l 1).eval (-(n : ℂ)) = 0)
    (hc : ∀ᶠ n : ℕ in Filter.atTop, cc.eval (-(n : ℂ)) = 0) :
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 1 1 = 0 ∧ q 0 2 + q 2 0 = 0
      ∧ l 2 = 0 ∧ l 0 = 0 ∧ l 1 = 0 ∧ cc = 0 := by
  have hlog : -1 < -Real.log 2 := by
    have := Real.log_two_lt_d9; linarith
  -- Step 1: the quadratic block vanishes for every large n.
  have hPhi0 : ∀ n, N ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → PhiB s n q z = 0 := by
    intro n hn
    set R : Fin 3 → ℂ → ℂ := fun k z => tailFactored s (k : ℕ) n (Complex.exp z) with hRdef
    have hRper : ∀ k z, R k (z + 2 * (Real.pi : ℂ) * Complex.I) = R k z := fun k z =>
      tailFactored_periodic s (k : ℕ) n z
    have hsplit : ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
        PhiB s n q z + PsiB s n q l R z + ThetaB s n q l cc R z = 0 := by
      intro z hz hz1 hz2
      rw [PhiB_eq_products, PsiB, ThetaB]
      have hcoll := relation_collect (s := s)
        (fun i j => (q i j).eval (-(n : ℂ) + Complex.exp z))
        (fun k => (l k).eval (-(n : ℂ) + Complex.exp z))
        (cc.eval (-(n : ℂ) + Complex.exp z)) z (fun k => R k z)
      have hr := hrel n hn z hz hz1 hz2
      linear_combination hr - hcoll
    exact fun z hz => (n2_blocks_vanish s n hsZ h2sZ q l cc R hRper
      (z0 := -1) (B := -Real.log 2) (by simpa using hlog) (by simpa using Real.pi_pos)
      (by simpa using Real.pi_pos) (blockSum_analytic hs1 n q l cc) hsplit).1 z hz
  -- Step 2: the triangular system.
  obtain ⟨hq00, hq22, hsurv⟩ := n2_quad_coeffs s q hPhi0
  -- Step 3: the density-shadow + linear close.
  obtain ⟨hQ, hl2, hl0, hl1, hcc⟩ :=
    n2_survivor_and_linear hs1 (fun k => (hsZ k).symm) hrow h0 h1 hc
  refine ⟨hq00, hq22, ?_, hQ, hl2, hl0, hl1, hcc⟩
  linear_combination hsurv - hQ

end HurwitzN2Theorem
