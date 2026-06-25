/-
# Hurwitz N=2 — the density-shadow crux + linear close

After the quadratic filtration, the survivor relation near `a=−n` is
`q(a)(F_0F_2−F_1²)+l_0F_0+l_1F_1+l_2F_2+c=0`. The leading doubly-singular term cancels
(`x^{-s}x^{-s-2}−x^{-s-1}x^{-s-1}=0`), and the next term is `F_0F_2−F_1² = x^{-s-2}·R_{n,0}(0)+O(x^{-s-1})`,
so the `x^{-s-2}` Laurent coefficient gives the **row relation** `q(−n)·R_{n,0}(0)+l_2(−n)=0` (∀ large `n`),
with `R_{n,0}(0) = ζ(s,−n) = hzeta s (−n)`. Since `R_{n,0}(0)−R_{n−1,0}(0) = η·n^{−s}`
(`hzeta_neg_nat_diff`, `η=e^{−πis}≠0`), `survivor_q_eq_zero`'s finite-difference non-rationality forces
`q=0`, then `l_2=0`. The remaining `l_0F_0+l_1F_1+c=0` is killed by the distinct-exponent extraction
(`−s,−s−1,0` distinct), each coefficient vanishing at infinitely many `−n`.

The `x^{-s-2}`-coefficient Laurent extraction (the `lim x^{s+2}·relation`) and the distinct-exponent
extraction are taken here as the named hypotheses `hrow`/`h0`/`h1`/`hc` — the row/coefficient relations
they produce — exactly the inputs the committed non-rationality core and root-counting consume.
-/
import GaloisForLFunctions.Hurwitz.N2Survivor
import GaloisForLFunctions.Hurwitz.HurwitzZeta
import GaloisForLFunctions.Hurwitz.DescentAlgebra

open Complex Filter HurwitzZetaShift HurwitzN2Survivor HurwitzDescent

namespace HurwitzN2DensityShadow

/-- A polynomial vanishing at `−n` for all large `n` is zero. -/
theorem eventually_root_zero {p : Polynomial ℂ}
    (h : ∀ᶠ n : ℕ in atTop, p.eval (-(n : ℂ)) = 0) : p = 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  exact eq_zero_of_eventually_neg_nat_roots (N := N) (fun n hn => hN n hn)

/-- **Density-shadow crux.** The row relation `q(−n)·ζ(s,−n)+l_2(−n)=0` (the `x^{-s-2}` Laurent
coefficient of the survivor relation) plus the committed finite-difference `ζ(s,−n)−ζ(s,−(n−1))=η·n^{−s}`
forces the survivor coefficient `q=0` (via `survivor_q_eq_zero`'s non-rationality), and then `l_2=0`. -/
theorem survivor_killed {s : ℂ} (hs1 : 1 < s.re) (hs : ∀ k : ℤ, s ≠ (k : ℂ))
    {q l₂ : Polynomial ℂ}
    (hrow : ∀ᶠ n : ℕ in atTop,
      q.eval (-(n : ℂ)) * hzeta s (-(n : ℂ)) + l₂.eval (-(n : ℂ)) = 0) :
    q = 0 ∧ l₂ = 0 := by
  have hη : Complex.exp (-((Real.pi : ℂ) * Complex.I * s)) ≠ 0 := Complex.exp_ne_zero _
  have hq : q = 0 :=
    survivor_q_eq_zero (V := fun n => hzeta s (-(n : ℂ))) hs hη
      (fun n hn => hzeta_neg_nat_diff hs1 hn) hrow
  refine ⟨hq, eventually_root_zero ?_⟩
  filter_upwards [hrow] with n hn
  rw [hq] at hn
  simpa using hn

/-- **Linear close.** With the quadratic part gone, the residual `l_0F_0+l_1F_1+c=0` has the distinct
exponents `−s,−s−1,0`; the distinct-exponent extraction yields `l_0(−n)=l_1(−n)=c(−n)=0` for all large
`n` (the hypotheses), so each rational coefficient vanishes. -/
theorem linear_killed {l₀ l₁ c : Polynomial ℂ}
    (h0 : ∀ᶠ n : ℕ in atTop, l₀.eval (-(n : ℂ)) = 0)
    (h1 : ∀ᶠ n : ℕ in atTop, l₁.eval (-(n : ℂ)) = 0)
    (hc : ∀ᶠ n : ℕ in atTop, c.eval (-(n : ℂ)) = 0) :
    l₀ = 0 ∧ l₁ = 0 ∧ c = 0 :=
  ⟨eventually_root_zero h0, eventually_root_zero h1, eventually_root_zero hc⟩

/-- **N=2 survivor + linear close (combined).** All residual coefficients vanish: the survivor `q` and
`l_2` by the density-shadow non-rationality, and `l_0,l_1,c` by the distinct-exponent extraction. -/
theorem n2_survivor_and_linear {s : ℂ} (hs1 : 1 < s.re) (hs : ∀ k : ℤ, s ≠ (k : ℂ))
    {q l₂ l₀ l₁ c : Polynomial ℂ}
    (hrow : ∀ᶠ n : ℕ in atTop,
      q.eval (-(n : ℂ)) * hzeta s (-(n : ℂ)) + l₂.eval (-(n : ℂ)) = 0)
    (h0 : ∀ᶠ n : ℕ in atTop, l₀.eval (-(n : ℂ)) = 0)
    (h1 : ∀ᶠ n : ℕ in atTop, l₁.eval (-(n : ℂ)) = 0)
    (hc : ∀ᶠ n : ℕ in atTop, c.eval (-(n : ℂ)) = 0) :
    q = 0 ∧ l₂ = 0 ∧ l₀ = 0 ∧ l₁ = 0 ∧ c = 0 := by
  obtain ⟨hq, hl2⟩ := survivor_killed hs1 hs hrow
  obtain ⟨hl0, hl1, hcc⟩ := linear_killed h0 h1 hc
  exact ⟨hq, hl2, hl0, hl1, hcc⟩

end HurwitzN2DensityShadow
