import GaloisForLFunctions.RHTower.Sieve.InvZetaSegmentBound
import GaloisForLFunctions.RHTower.Sieve.HalfComparison

/-!
# The left edge bound, fully explicit

Assembling the segment estimate with the discharged comparison gives an unconditional bound for
`‖invZeta‖` on a vertical line strictly left of the abscissa, at every height `|γ| ≥ 1`.

The abscissa of the line is `1 - c/(16 log⁹N)` with `c = zeroFreeConst`, the same constant and the
same exponent as the zero-free region.  The choice is forced by the comparison: with
`σ = 1 + δ` and `δ = c/(2 log⁹N)` the distance moved left must satisfy `D⁴ log⁹N < c·δ³`, and
`D = (9/8)δ` does so with room, since `(9/8)⁴ < 2`.  The resulting `β = σ - D = 1 - δ/8` is the
line below.
-/

namespace RHTower.Sieve

open Complex

/-- **The left edge bound.**  At every height `|γ| ≥ 1`, with `N` at least `3 + 2|γ|`, the regular
reciprocal of zeta is bounded on the line `re s = 1 - c/(16 log⁹N)` by an explicit quantity of size
`log^{1/4}N · log^{27/4}N` — polynomial in `log N`, and in particular independent of any hypothesis
on the zeros. -/
theorem norm_invZeta_left_le_range {β γ : ℝ} {N : ℕ}
    (hlogN : 3 ≤ Real.log N) (hN : 2 ≤ N) (hγ : 1 ≤ |γ|)
    (hNbig : 3 + 2 * |γ| ≤ (N : ℝ))
    (hβlo : 1 - zeroFreeConst / (16 * (Real.log N) ^ 9) ≤ β)
    (hβhi : β ≤ 1 + zeroFreeConst / (2 * (Real.log N) ^ 9)) :
    ‖invZeta ((β : ℂ) + (γ : ℂ) * Complex.I)‖
      ≤ 2 / Real.exp ((-22
          - 3 * Real.log (1 + 1 / (zeroFreeConst / (2 * (Real.log N) ^ 9)))
          - Real.log (5 / 2 + Real.log N)) / 4) := by
  set L : ℝ := Real.log N with hLdef
  have hL0 : (0 : ℝ) < L := by linarith
  have hL9 : (27 : ℝ) ≤ L ^ 9 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ L ^ 3 := by gcongr
      _ ≤ L ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hL9pos : (0 : ℝ) < L ^ 9 := by linarith
  have hA0 := zeroFreeConst_pos
  have hA1 := zeroFreeConst_le_one
  set δ : ℝ := zeroFreeConst / (2 * L ^ 9) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδsmall : δ ≤ 1 / 54 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA1, hA0]
  set D : ℝ := 9 / 8 * δ with hDdef
  have hD0 : 0 < D := by rw [hDdef]; linarith
  have hDsmall : D ≤ 9 / (8 * 54) := by rw [hDdef]; linarith
  set σ : ℝ := 1 + δ with hσdef
  have hβval : 1 - δ / 8 = 1 - zeroFreeConst / (16 * L ^ 9) := by
    rw [hδdef]
    field_simp
    ring
  have hβlo' : 1 - δ / 8 ≤ β := by rw [hβval]; exact hβlo
  have hβhi' : β ≤ σ := by rw [hσdef, hδdef]; exact hβhi
  set R : ℝ := 1 / (4 * L) with hRdef
  have hR0 : (0 : ℝ) < R := by rw [hRdef]; positivity
  have hRsmall : R ≤ 1 / 12 := by
    rw [hRdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- the arithmetic hypotheses
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hβσ : β ≤ σ := hβhi'
  have hβhalf : 1 / 2 + R ≤ β := by linarith
  have hL8 : (6561 : ℝ) ≤ L ^ 8 := by
    calc (6561 : ℝ) = 3 ^ 8 := by norm_num
      _ ≤ L ^ 8 := by gcongr
  have hδ8 : δ / 8 ≤ 1 / (4 * L) := by
    rw [hδdef, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hL9eq : L ^ 9 = L * L ^ 8 := by ring
    nlinarith [hA1, hA0, hL8, hL0, hL9eq]
  have hhalfL : 1 / (4 * L) + 1 / (4 * L) ≤ 1 / L := by
    have hsum : 1 / (4 * L) + 1 / (4 * L) = 1 / (2 * L) := by
      field_simp
      ring
    rw [hsum, div_le_div_iff₀ (by positivity) hL0]
    linarith
  have hlow : 1 - 1 / L ≤ β - R := by
    rw [hRdef]
    linarith
  have hRγ : R < |γ| := by linarith
  have hNbig' : σ + |γ| + R ≤ (N : ℝ) := by
    rw [hσdef]
    linarith
  -- the bound at the doubled frequency
  have hne1 : (σ : ℂ) + (2 * γ : ℂ) * Complex.I ≠ 1 := by
    intro hcon
    have him : ((σ : ℂ) + (2 * γ : ℂ) * Complex.I).im = 2 * γ := by simp
    rw [hcon] at him
    simp only [Complex.one_im] at him
    rcases abs_cases γ with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have hNw : ‖(σ : ℂ) + (2 * γ : ℂ) * Complex.I‖ ≤ (N : ℝ) := by
    have hb := Complex.norm_le_abs_re_add_abs_im ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)
    have hre : ((σ : ℂ) + (2 * γ : ℂ) * Complex.I).re = σ := by simp
    have him : ((σ : ℂ) + (2 * γ : ℂ) * Complex.I).im = 2 * γ := by simp
    rw [hre, him] at hb
    have h1 : |σ| = σ := abs_of_nonneg (by rw [hσdef]; linarith)
    have h2 : |2 * γ| = 2 * |γ| := by rw [abs_mul]; norm_num
    rw [h1, h2] at hb
    rw [hσdef] at hb ⊢
    linarith
  have hB := norm_riemannZeta_double_le (σ := σ) (γ := γ) (N := N)
    (by rw [hσdef]; linarith) hγ (by omega) hNw hne1
  -- the comparison
  have hscale : D ^ 4 * L ^ 9 < zeroFreeConst * δ ^ 3 := by
    have hδL9 : δ * L ^ 9 = zeroFreeConst / 2 := by
      rw [hδdef]
      field_simp
    have hexp : D ^ 4 * L ^ 9 = (9 / 8 : ℝ) ^ 4 * δ ^ 3 * (δ * L ^ 9) := by
      rw [hDdef]; ring
    rw [hexp, hδL9]
    have hδ3 : (0 : ℝ) < δ ^ 3 := by positivity
    nlinarith [mul_pos hA0 hδ3]
  have hhalfbase := half_comparison (L := L) (δ := δ) (D := D) hlogN hδ0
    (by linarith) hD0 hscale
  have hderiv := deriv_const_le (γ := γ) (N := N) hlogN hγ
  have hhalf : (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R
      * (σ - β)
      ≤ Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log (5 / 2 + L)) / 4) / 2 := by
    have hgap : σ - β ≤ D := by rw [hσdef, hDdef]; linarith
    have hgap0 : (0 : ℝ) ≤ σ - β := by linarith
    have hδ1 : σ - 1 = δ := by rw [hσdef]; ring
    rw [hδ1]
    have hMnn : (0 : ℝ) ≤ (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R)
        + 2 * Real.exp 1) / R := by
      have hRγ' : (0 : ℝ) < |γ| - R := by linarith
      have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      positivity
    have hderiv' : (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R
        ≤ 4 * 8 * L ^ 2 := by
      rw [hRdef, hLdef]
      exact hderiv
    calc (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R * (σ - β)
        ≤ 4 * 8 * L ^ 2 * (σ - β) := mul_le_mul_of_nonneg_right hderiv' hgap0
      _ ≤ 4 * 8 * L ^ 2 * D := by
          refine mul_le_mul_of_nonneg_left hgap ?_
          positivity
      _ ≤ _ := hhalfbase
  -- assemble
  have hmain := norm_invZeta_left_le_segment (β := β) (σ := σ) (γ := γ) (R := R) (N := N)
    hR0 hσ1 hβσ hβhalf (by rw [← hLdef]; exact hlow) hRγ hN hNbig' hB hhalf
  have hσval : σ - 1 = zeroFreeConst / (2 * L ^ 9) := by rw [hσdef, hδdef]; ring
  rw [hσval] at hmain
  exact hmain

/-- **The left edge bound.**  The instance of `norm_invZeta_left_le_range` on the line
`re s = 1 - c/(16 log⁹N)`. -/
theorem norm_invZeta_left_le_explicit {γ : ℝ} {N : ℕ}
    (hlogN : 3 ≤ Real.log N) (hN : 2 ≤ N) (hγ : 1 ≤ |γ|)
    (hNbig : 3 + 2 * |γ| ≤ (N : ℝ)) :
    ‖invZeta (((1 - zeroFreeConst / (16 * (Real.log N) ^ 9) : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖
      ≤ 2 / Real.exp ((-22
          - 3 * Real.log (1 + 1 / (zeroFreeConst / (2 * (Real.log N) ^ 9)))
          - Real.log (5 / 2 + Real.log N)) / 4) := by
  have hA0 := zeroFreeConst_pos
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  refine norm_invZeta_left_le_range hlogN hN hγ hNbig le_rfl ?_
  have h1 : (0 : ℝ) < zeroFreeConst / (16 * (Real.log N) ^ 9) := by positivity
  have h2 : (0 : ℝ) < zeroFreeConst / (2 * (Real.log N) ^ 9) := by positivity
  linarith

end RHTower.Sieve
