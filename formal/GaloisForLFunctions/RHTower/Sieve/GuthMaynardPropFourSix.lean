import GaloisForLFunctions.RHTower.Sieve.GuthMaynardTraceSingularValue
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardRayleigh

/-!
# Guth–Maynard, Proposition 4.6: the large-value count from the cubic trace

Let `M : Matrix W N ℂ` be the Dirichlet-polynomial matrix `(w(n/N) n^{it})_{t ∈ W, n}` and `b` the
coefficient vector.  Guth–Maynard (arXiv 2405.20552, Prop. 4.6) bound the number of large values
`|W|` through the traces of `H = M Mᴴ`:

* Lemma 4.1: `|W| N^{2σ} ≤ Σ_t |D_N(t)|² = ‖M b‖² ≤ λ_max(H) ‖b‖²`, `‖b‖² ≤ C N`;
* Lemma 4.2: `λ_max(H)³ ≤ max (4 (tr H³ − (tr H)³/|W|²)) (8 (tr H)³/|W|³)`;
* Lemmas 4.4–4.5: `tr H = N|W|c + E₁`, `tr H³ = N³|W|c³ + S + E₃` with `c = ‖w‖²_{L²}`, `S` the
  off-diagonal sum `Σ_{m ≠ 0} I_m`, and negligible `E₁, E₃`.

The flat-spectrum baseline `(tr H)³/|W|²` cancels the main term of `tr H³` exactly, so

`|W| ≤ C N^{1−2σ} ((4(S + K))^{1/3} + 2 N c + 2)`, `K = 3c² + 3c + 2`,

i.e. `|W| ≪ N^{2−2σ} + N^{1−2σ} S^{1/3}`.  This module proves the assembly: first as a statement
about real numbers (`prop46_abstract`), then for an actual matrix with the trace hypotheses
(`card_le_of_trace_bounds`).  The trace asymptotics (Poisson summation, Lemmas 4.4–4.5) and the
bound on `S` (Sections 5–10 of the paper) are the remaining inputs of the programme.
-/

open Matrix Finset
open scoped ComplexOrder

namespace RHTower.GuthMaynard

/-- Cube roots: if `y ≥ 0` and `y³ ≤ a + b` with `a, b ≥ 0`, then `y ≤ a^{1/3} + b^{1/3}`. -/
theorem le_rpow_third_add_rpow_third {y a b : ℝ} (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : y ^ 3 ≤ a + b) : y ≤ a ^ ((1 : ℝ) / 3) + b ^ ((1 : ℝ) / 3) := by
  set A := a ^ ((1 : ℝ) / 3) with hA
  set B := b ^ ((1 : ℝ) / 3) with hB
  have hA0 : 0 ≤ A := Real.rpow_nonneg ha _
  have hB0 : 0 ≤ B := Real.rpow_nonneg hb _
  have hA3 : A ^ 3 = a := by
    rw [hA, ← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
  have hB3 : B ^ 3 = b := by
    rw [hB, ← Real.rpow_natCast, ← Real.rpow_mul hb]; norm_num
  have hcube : y ^ 3 ≤ (A + B) ^ 3 := by
    have : (A + B) ^ 3 = A ^ 3 + B ^ 3 + 3 * A * B * (A + B) := by ring
    rw [this, hA3, hB3]
    nlinarith [mul_nonneg (mul_nonneg hA0 hB0) (add_nonneg hA0 hB0)]
  exact (pow_le_pow_iff_left₀ hy (add_nonneg hA0 hB0) (by norm_num)).1 hcube

/-- The cube of `8 (Nc + 1)³` has cube root `2 (Nc + 1)`. -/
theorem rpow_third_eight_mul_cube {x : ℝ} (hx : 0 ≤ x) :
    (8 * x ^ 3) ^ ((1 : ℝ) / 3) = 2 * x := by
  rw [show (8 : ℝ) * x ^ 3 = (2 * x) ^ 3 by ring, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num

/-- **Prop. 4.6, abstract form.** With `T₁ = tr H`, `T₃ = tr H³`, `y = λ_max(H)`, and
`W ≥ 1`, `N ≥ 1`, `c > 0`:
from `W N^{2σ} ≤ y C N`, the cubic-trace bound for `y`, and the trace asymptotics with errors
`|E₁| ≤ 1/N²`, `|E₃| ≤ 1`, one gets `W ≤ C N^{1−2σ} ((4(S + K))^{1/3} + 2Nc + 2)`. -/
theorem prop46_abstract {W N σ y T₁ T₃ S E₁ E₃ c C : ℝ} (hW : 1 ≤ W) (hN : 1 ≤ N) (hc : 0 < c)
    (hC : 0 ≤ C) (hy0 : 0 ≤ y)
    (hR : W * N ^ (2 * σ) ≤ y * (C * N))
    (hcube : y ^ 3 ≤ max (4 * (T₃ - T₁ ^ 3 / W ^ 2)) (8 * T₁ ^ 3 / W ^ 3))
    (h1 : T₁ = N * W * c + E₁) (h3 : T₃ = N ^ 3 * W * c ^ 3 + S + E₃)
    (hS : 0 ≤ S) (hE1 : |E₁| ≤ 1 / N ^ 2) (hE3 : |E₃| ≤ 1) :
    W ≤ C * N ^ (1 - 2 * σ) *
      ((4 * (S + (3 * c ^ 2 + 3 * c + 2))) ^ ((1 : ℝ) / 3) + 2 * N * c + 2) := by
  have hW0 : 0 < W := by linarith
  have hN0 : 0 < N := by linarith
  have hE1' : |E₁| ≤ 1 := by
    refine hE1.trans ?_
    rw [div_le_one (by positivity)]; nlinarith
  -- the defect: `T₃ − T₁³/W² = S + E₃ − 3N²c²E₁ − 3NcE₁²/W − E₁³/W²`
  have hdefect : T₃ - T₁ ^ 3 / W ^ 2
      = S + E₃ - 3 * N ^ 2 * c ^ 2 * E₁ - 3 * N * c * E₁ ^ 2 / W - E₁ ^ 3 / W ^ 2 := by
    rw [h1, h3]; field_simp; ring
  -- bound the three error terms
  have hb1 : |3 * N ^ 2 * c ^ 2 * E₁| ≤ 3 * c ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 3 * N ^ 2 * c ^ 2)]
    calc 3 * N ^ 2 * c ^ 2 * |E₁| ≤ 3 * N ^ 2 * c ^ 2 * (1 / N ^ 2) := by gcongr
      _ = 3 * c ^ 2 := by field_simp
  have hb2 : |3 * N * c * E₁ ^ 2 / W| ≤ 3 * c := by
    rw [abs_div, abs_of_pos hW0, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 3 * N * c),
      abs_pow]
    have hE1sq : |E₁| ^ 2 ≤ 1 / N ^ 2 := by
      calc |E₁| ^ 2 ≤ |E₁| * 1 := by nlinarith [abs_nonneg E₁]
        _ ≤ 1 / N ^ 2 := by simpa using hE1
    calc 3 * N * c * |E₁| ^ 2 / W ≤ 3 * N * c * (1 / N ^ 2) / 1 := by gcongr
      _ = 3 * c / N := by field_simp
      _ ≤ 3 * c := by rw [div_le_iff₀ hN0]; nlinarith
  have hb3 : |E₁ ^ 3 / W ^ 2| ≤ 1 := by
    rw [abs_div, abs_pow, abs_pow, abs_of_pos hW0]
    have : |E₁| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hE1'
    calc |E₁| ^ 3 / W ^ 2 ≤ 1 / 1 := by gcongr; nlinarith
      _ = 1 := by norm_num
  have hdef_le : T₃ - T₁ ^ 3 / W ^ 2 ≤ S + (3 * c ^ 2 + 3 * c + 2) := by
    rw [hdefect]
    linarith [(abs_le.mp hb1).1, (abs_le.mp hb2).1, (abs_le.mp hb3).1, (abs_le.mp hE3).2]
  -- the flat term: `8 T₁³/W³ ≤ 8 (Nc + 1)³`
  have hflat : 8 * T₁ ^ 3 / W ^ 3 ≤ 8 * (N * c + 1) ^ 3 := by
    have hq : T₁ / W = N * c + E₁ / W := by rw [h1]; field_simp
    have habs : |T₁ / W| ≤ N * c + 1 := by
      rw [hq]
      calc |N * c + E₁ / W| ≤ |N * c| + |E₁ / W| := abs_add_le _ _
        _ = N * c + |E₁| / W := by rw [abs_of_pos (by positivity), abs_div, abs_of_pos hW0]
        _ ≤ N * c + 1 := by
            have : |E₁| / W ≤ 1 := by
              rw [div_le_one hW0]; linarith
            linarith
    have hcube' : (T₁ / W) ^ 3 ≤ (N * c + 1) ^ 3 := by
      have hx : (T₁ / W) ^ 3 ≤ |T₁ / W| ^ 3 := by
        rcases le_or_gt 0 (T₁ / W) with h | h
        · rw [abs_of_nonneg h]
        · have h1 : (T₁ / W) ^ 3 < 0 := Odd.pow_neg ⟨1, by norm_num⟩ h
          have h2 : 0 ≤ |T₁ / W| ^ 3 := by positivity
          linarith
      exact hx.trans (pow_le_pow_left₀ (abs_nonneg _) habs 3)
    calc 8 * T₁ ^ 3 / W ^ 3 = 8 * (T₁ / W) ^ 3 := by field_simp
      _ ≤ 8 * (N * c + 1) ^ 3 := by gcongr
  -- `y³ ≤ 4(S+K) + 8(Nc+1)³`
  have hy3 : y ^ 3 ≤ 4 * (S + (3 * c ^ 2 + 3 * c + 2)) + 8 * (N * c + 1) ^ 3 := by
    refine hcube.trans ?_
    have h4 : 4 * (T₃ - T₁ ^ 3 / W ^ 2) ≤ 4 * (S + (3 * c ^ 2 + 3 * c + 2)) := by linarith
    have hpos1 : 0 ≤ 4 * (S + (3 * c ^ 2 + 3 * c + 2)) := by positivity
    have hpos2 : 0 ≤ 8 * (N * c + 1) ^ 3 := by positivity
    exact max_le (by linarith) (by linarith)
  have hy : y ≤ (4 * (S + (3 * c ^ 2 + 3 * c + 2))) ^ ((1 : ℝ) / 3) + 2 * N * c + 2 := by
    have := le_rpow_third_add_rpow_third hy0 (by positivity) (by positivity) hy3
    rw [rpow_third_eight_mul_cube (by positivity)] at this
    linarith
  -- assemble with `hR`: `W ≤ y C N^{1−2σ}`
  have hpow : N ^ (2 * σ) * N ^ (1 - 2 * σ) = N := by
    rw [← Real.rpow_add hN0]; norm_num
  have hpow0 : 0 < N ^ (2 * σ) := Real.rpow_pos_of_pos hN0 _
  have hW' : W ≤ y * (C * N ^ (1 - 2 * σ)) := by
    have hprod : (y * (C * N ^ (1 - 2 * σ))) * N ^ (2 * σ) = y * (C * N) := by
      calc (y * (C * N ^ (1 - 2 * σ))) * N ^ (2 * σ)
          = y * C * (N ^ (2 * σ) * N ^ (1 - 2 * σ)) := by ring
        _ = y * (C * N) := by rw [hpow]; ring
    have : W * N ^ (2 * σ) ≤ (y * (C * N ^ (1 - 2 * σ))) * N ^ (2 * σ) := by
      rw [hprod]; exact hR
    exact le_of_mul_le_mul_right this hpow0
  calc W ≤ y * (C * N ^ (1 - 2 * σ)) := hW'
    _ ≤ ((4 * (S + (3 * c ^ 2 + 3 * c + 2))) ^ ((1 : ℝ) / 3) + 2 * N * c + 2)
          * (C * N ^ (1 - 2 * σ)) := by
        exact mul_le_mul_of_nonneg_right hy (by positivity)
    _ = _ := by ring

/-- **Prop. 4.6 for a matrix.** `M : Matrix W N ℂ`, `H = M Mᴴ`.  If every row value satisfies the
large-value hypothesis in the aggregate form `|W| n^{2σ} ≤ Σ_t ‖(M b)_t‖²`, the coefficients have
`Σ ‖b‖² ≤ C n`, and the traces satisfy `Re tr H = n |W| c + E₁`, `Re tr H³ = n³ |W| c³ + S + E₃`
with `|E₁| ≤ 1/n²`, `|E₃| ≤ 1`, `S ≥ 0`, then
`|W| ≤ C n^{1−2σ} ((4(S + 3c² + 3c + 2))^{1/3} + 2nc + 2)`. -/
theorem card_le_of_trace_bounds {W N : Type*} [Fintype W] [Fintype N] [DecidableEq W]
    [Nonempty W] (M : Matrix W N ℂ) (b : N → ℂ) {n σ c C S E₁ E₃ : ℝ}
    (hn : 1 ≤ n) (hc : 0 < c) (hC : 0 ≤ C)
    (hlarge : (Fintype.card W : ℝ) * n ^ (2 * σ) ≤ ∑ t, ‖(M *ᵥ b) t‖ ^ 2)
    (hb : ∑ j, ‖b j‖ ^ 2 ≤ C * n)
    (htr1 : (M * Mᴴ).trace.re = n * (Fintype.card W : ℝ) * c + E₁)
    (htr3 : ((M * Mᴴ) ^ 3).trace.re = n ^ 3 * (Fintype.card W : ℝ) * c ^ 3 + S + E₃)
    (hS : 0 ≤ S) (hE1 : |E₁| ≤ 1 / n ^ 2) (hE3 : |E₃| ≤ 1) :
    (Fintype.card W : ℝ) ≤ C * n ^ (1 - 2 * σ) *
      ((4 * (S + (3 * c ^ 2 + 3 * c + 2))) ^ ((1 : ℝ) / 3) + 2 * n * c + 2) := by
  classical
  have hH := Matrix.isHermitian_mul_conjTranspose_self M
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i =>
    (Matrix.posSemidef_self_mul_conjTranspose M).eigenvalues_nonneg i
  -- the top eigenvalue
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max hH.eigenvalues
  set y := hH.eigenvalues i₀ with hy
  have hy0 : 0 ≤ y := hnn i₀
  have hμ : ∀ i, hH.eigenvalues i ≤ y := hi₀
  have hW1 : (1 : ℝ) ≤ Fintype.card W := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  -- Lemma 4.1 with the hypotheses
  have hR : (Fintype.card W : ℝ) * n ^ (2 * σ) ≤ y * (C * n) := by
    calc (Fintype.card W : ℝ) * n ^ (2 * σ) ≤ ∑ t, ‖(M *ᵥ b) t‖ ^ 2 := hlarge
      _ ≤ y * ∑ j, ‖b j‖ ^ 2 := sum_normSq_mulVec_le M hy0 hμ b
      _ ≤ y * (C * n) := mul_le_mul_of_nonneg_left hb hy0
  -- Lemma 4.2
  have hcube := eigenvalue_cube_le_max_trace_defect hH hnn i₀
  rw [← hy] at hcube
  exact prop46_abstract hW1 hn hc hC hy0 hR hcube htr1 htr3 hS hE1 hE3

end RHTower.GuthMaynard
