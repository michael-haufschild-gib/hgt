import GaloisForLFunctions.RHTower.Sieve.MellinDecayUniform

/-!
# Absolute constants at proportional smoothing

Taking the smoothing width equal to the cutoff, `H = N`, turns the explicit factor
`H^{-(j+1)}(N+H+1)^{j+1}` of the uniform decay bound into `((2N+1)/N)^{j+1} ≤ 3^{j+1}`, a number.
So at proportional smoothing the decay constant is absolute — it depends on the order alone — and
the only cutoff dependence left anywhere in the contour bound is the honest factor `(2N+1)^{Re s}`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- **The decay constant at proportional smoothing is absolute.** -/
theorem exists_bound_mellin_smoothWeight_diag (j : ℕ) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ N : ℝ, 1 ≤ N → ∀ s : ℂ, 0 < s.re →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N N x : ℝ) : ℂ)) s‖
        ≤ Cj * (N + N + 1) ^ s.re := by
  obtain ⟨Cj, hCj, hbd⟩ := exists_bound_mellin_smoothWeight_uniform_all j
  refine ⟨Cj * 3 ^ (j + 1), by positivity, fun N hN s hs => ?_⟩
  have hN0 : (0 : ℝ) < N := by linarith
  have hb0 : (0 : ℝ) < N + N + 1 := by linarith
  have hbase := hbd N N hN0 hN0 s hs
  refine le_trans hbase ?_
  have hratio : (N + N + 1) / N ≤ 3 := by
    rw [div_le_iff₀ hN0]
    linarith
  have hratio0 : (0 : ℝ) ≤ (N + N + 1) / N := by positivity
  have hpow : ((N + N + 1) / N) ^ (j + 1) ≤ 3 ^ (j + 1) :=
    pow_le_pow_left₀ hratio0 hratio (j + 1)
  have hrew : Cj / N ^ (j + 1) * (N + N + 1) ^ (j + 1 : ℕ)
      = Cj * ((N + N + 1) / N) ^ (j + 1) := by
    rw [div_pow]
    field_simp
  rw [hrew]
  have hre0 : (0 : ℝ) < (N + N + 1) ^ s.re := Real.rpow_pos_of_pos hb0 _
  have hstep : Cj * ((N + N + 1) / N) ^ (j + 1) ≤ Cj * 3 ^ (j + 1) :=
    mul_le_mul_of_nonneg_left hpow hCj
  exact mul_le_mul_of_nonneg_right hstep hre0.le

/-- The form the contour argument consumes: valid up to a given abscissa, with the abscissa
dependence a single power of `2N+1`. -/
theorem exists_bound_mellin_smoothWeight_diag_upto (j : ℕ) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ N : ℝ, 1 ≤ N → ∀ σ : ℝ, ∀ s : ℂ, 0 < s.re → s.re ≤ σ →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N N x : ℝ) : ℂ)) s‖
        ≤ Cj * (N + N + 1) ^ σ := by
  obtain ⟨Cj, hCj, hbd⟩ := exists_bound_mellin_smoothWeight_diag j
  refine ⟨Cj, hCj, fun N hN σ s hs hsσ => ?_⟩
  have hb1 : (1 : ℝ) ≤ N + N + 1 := by linarith
  refine le_trans (hbd N hN s hs) ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb1 hsσ) hCj

end RHTower.Sieve
