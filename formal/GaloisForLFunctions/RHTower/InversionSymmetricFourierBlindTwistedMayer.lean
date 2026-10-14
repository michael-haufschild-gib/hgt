import GaloisForLFunctions.RHTower.InversionSymmetricFourierBlindGaussTransfer

/-!
# Fourier-blind cores as a twisted Mayer equation at `s = ½`

Let `G : ℝ → ℝ` be continuous and even, with `G(1/x) = x G(x)` for `x > 0`, vanishing on `[0, c)`
for some `c > ½`, and with Fourier transform vanishing at every integer `|n| ≥ 2`.  Put
`H(v) = G(1 − 1/v)/v`, `τ(v) = 2 + 1/(v − 1)`, and let `F = fareySeriesR (a₀ + 2a₁) (2a₁)` with
`a₀ = Re Ĝ(0)`, `a₁ = Re Ĝ(1)`.

**Alternating parabolic sum** (`eq_sub_sum_of_gauss_farey_steps`,
`inversionSymmetric_alternating_parabolic_sum`).  The Gauss–Farey equation
`H(v) + H(v + 1) + H(τv)/(v − 1) = F(v) + F(v + 1)` (`v ≥ 2`) can be summed with alternating signs
along the parabolic orbit `v, v + 1, …, v + N`.  Once `v + N ≥ c/(2c − 1)`, where `H = F`, this
gives

`H(v) = F(v) − Σ_{n<N} (−1)^n H(τ(v + n))/(v + n − 1)`.

The parabolic branch `v ↦ v + 1` (the cusp) has been eliminated, and only the Gauss branch remains.

**Twisted Mayer form** (`inversionSymmetric_twistedMayerHalf`).  With `ϑ(r) = H(2 + r)`, for
`0 ≤ r` and `c/(2c − 1) ≤ 2 + N`,

`ϑ(r) + M_N ϑ(r) = F(2 + r)`,   `M_N ϑ(r) = Σ_{m=1}^{N} (−1)^{m−1} ϑ(1/(r + m))/(r + m)`
(`twistedMayerHalf`).

`M_N` is the Mayer transfer operator of the Gauss map at `s = ½`, with branches `r ↦ 1/(r + m)`
and weights `(r + m)^{−1}`, twisted by the signs `(−1)^{m−1}`.  These signs are the values of a
character of `PGL(2, ℤ)` that is `−1` on the translation `T`, so the cusp is closed.  The terms with
`2 + 1/(r + m) ≤ 1/(1 − c)` vanish, because `H = 0` on `[2, 1/(1 − c)]`.  Hence the operator does
not depend on `c`, and `c` enters only through the support condition `ϑ = 0` on
`[0, 1/(1 − c) − 2]`.
-/

open MeasureTheory Set Real Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

/-- **Alternating summation of the Gauss–Farey steps.**  If
`H(v + n) + H(v + n + 1) + H(τ(v + n))/(v + n − 1) = F(v + n) + F(v + n + 1)` for `n < N` and
`H(v + N) = F(v + N)`, then `H(v) = F(v) − Σ_{n<N} (−1)^n H(τ(v + n))/(v + n − 1)`. -/
theorem eq_sub_sum_of_gauss_farey_steps {H F : ℝ → ℝ} {v : ℝ} {N : ℕ}
    (hE : ∀ n < N, H (v + n) + H (v + n + 1) + H (gaussBranch (v + n)) / (v + n - 1) =
      F (v + n) + F (v + n + 1))
    (hEnd : H (v + N) = F (v + N)) :
    H v = F v - ∑ n ∈ Finset.range N,
      (-1) ^ n * (H (gaussBranch (v + n)) / (v + n - 1)) := by
  have key : ∀ M ≤ N, H v + (∑ n ∈ Finset.range M,
      (-1) ^ n * (H (gaussBranch (v + n)) / (v + n - 1))) - F v =
      (-1) ^ M * (H (v + M) - F (v + M)) := by
    intro M hM
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ]
      have e := hE M (by omega)
      have ih' := ih (by omega)
      push_cast
      rw [pow_succ]
      have e2 : v + ((M : ℝ) + 1) = v + M + 1 := by ring
      rw [e2]
      linear_combination ih' + (-1 : ℝ) ^ M * e
  have h := key N le_rfl
  rw [hEnd, sub_self, mul_zero] at h
  linarith

/-- **The alternating parabolic sum** for an inversion-symmetric Fourier-blind `G` with `c > ½`. -/
theorem inversionSymmetric_alternating_parabolic_sum {G : ℝ → ℝ} (hG : Continuous G)
    (heven : ∀ x, G (-x) = G x) (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x) {c : ℝ}
    (hc : 1 / 2 < c) (hsupp : ∀ x, 0 ≤ x → x < c → G x = 0)
    (hblind : ∀ n : ℤ, 2 ≤ |n| → 𝓕 (fun x => (G x : ℂ)) n = 0) {v : ℝ} (hv : 2 ≤ v) {N : ℕ}
    (hN : c / (2 * c - 1) ≤ v + N) :
    G (1 - 1 / v) / v =
      fareySeriesR ((𝓕 (fun x => (G x : ℂ)) 0).re + 2 * (𝓕 (fun x => (G x : ℂ)) 1).re)
        (2 * (𝓕 (fun x => (G x : ℂ)) 1).re) v -
      ∑ n ∈ Finset.range N, (-1) ^ n *
        (G (1 - 1 / gaussBranch (v + n)) / gaussBranch (v + n) / (v + n - 1)) := by
  set a₀ := (𝓕 (fun x => (G x : ℂ)) 0).re with ha₀
  set a₁ := (𝓕 (fun x => (G x : ℂ)) 1).re with ha₁
  set F := fareySeriesR (a₀ + 2 * a₁) (2 * a₁) with hF
  set H : ℝ → ℝ := fun w => G (1 - 1 / w) / w with hH
  have hgf : ∀ w, 2 ≤ w → H w + H (w + 1) + H (gaussBranch w) / (w - 1) = F w + F (w + 1) := by
    intro w hw
    have e : H w + H (w + 1) + H (gaussBranch w) / (w - 1) =
        (a₀ + 2 * a₁ * Real.cos (2 * π / w)) / w :=
      inversionSymmetric_gauss_farey_equation hG heven hinv hc hsupp hblind hw
    rw [e, hF, fareySeriesR_add_one _ _ (by linarith)]
    ring
  have h := eq_sub_sum_of_gauss_farey_steps (H := H) (F := F) (v := v) (N := N)
    (fun n _ => by
      have hn : (0 : ℝ) ≤ n := n.cast_nonneg
      exact hgf (v + n) (by linarith))
    (inversionSymmetric_profile_eq_fareySeriesR hG heven hinv hc hsupp hblind
      (max_le (by have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith) hN))
  exact h

/-- The Mayer transfer operator of the Gauss map at `s = ½`, twisted by the signs `(−1)^{m−1}` and
truncated at `m ≤ N`: `M_N ϑ(r) = Σ_{m=1}^{N} (−1)^{m−1} ϑ(1/(r + m))/(r + m)`. -/
def twistedMayerHalf (N : ℕ) (ϑ : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (-1) ^ n * (ϑ (1 / (r + (n + 1))) / (r + (n + 1)))

/-- **Fourier-blind cores solve a twisted Mayer equation.**  With `ϑ(r) = H(2 + r)`,
`ϑ(r) + M_N ϑ(r) = F(2 + r)` for `r ≥ 0` and `c/(2c − 1) ≤ 2 + N`. -/
theorem inversionSymmetric_twistedMayerHalf {G : ℝ → ℝ} (hG : Continuous G)
    (heven : ∀ x, G (-x) = G x) (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x) {c : ℝ}
    (hc : 1 / 2 < c) (hsupp : ∀ x, 0 ≤ x → x < c → G x = 0)
    (hblind : ∀ n : ℤ, 2 ≤ |n| → 𝓕 (fun x => (G x : ℂ)) n = 0) {r : ℝ} (hr : 0 ≤ r) {N : ℕ}
    (hN : c / (2 * c - 1) ≤ 2 + N) :
    G (1 - 1 / (2 + r)) / (2 + r) +
      twistedMayerHalf N (fun ρ => G (1 - 1 / (2 + ρ)) / (2 + ρ)) r =
      fareySeriesR ((𝓕 (fun x => (G x : ℂ)) 0).re + 2 * (𝓕 (fun x => (G x : ℂ)) 1).re)
        (2 * (𝓕 (fun x => (G x : ℂ)) 1).re) (2 + r) := by
  have h := inversionSymmetric_alternating_parabolic_sum hG heven hinv hc hsupp hblind
    (v := 2 + r) (by linarith) (N := N) (by linarith)
  rw [h, twistedMayerHalf]
  have e : ∀ n ∈ Finset.range N, (-1 : ℝ) ^ n *
      (G (1 - 1 / gaussBranch (2 + r + n)) / gaussBranch (2 + r + n) / (2 + r + n - 1)) =
      (-1) ^ n * (G (1 - 1 / (2 + 1 / (r + (n + 1)))) / (2 + 1 / (r + (n + 1))) /
        (r + (n + 1))) := by
    intro n _
    have e1 : gaussBranch (2 + r + n) = 2 + 1 / (r + (n + 1)) := by
      unfold gaussBranch; congr 2; ring
    have e2 : (2 + r + n - 1 : ℝ) = r + (n + 1) := by ring
    rw [e1, e2]
  rw [Finset.sum_congr rfl e]
  ring

end

end RHTower
