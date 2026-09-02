import GaloisForLFunctions.HTGeometry.PoincareSeriesPeterssonUnfolding
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The Petersson product of a cusp form against a Poincaré series

For a level-one cusp form `f = Σ a_f(n) q^n` of weight `k ≥ 3` and `m ≥ 1`,

  `⟨f, P_m⟩ = 2 · (4πm)^{1-k} Γ(k-1) · conj(a_f(m))`.

After unfolding to the strip, Fubini gives `∫_0^∞ y^{-2} (∫_0^1 conj(f(x+iy)) e(m(x+iy)) y^k dx) dy`;
the inner integral is `e^{-4π m y} y^k conj(a_f(m))` by the integral formula for the `q`-expansion
coefficients, and the outer integral is a Gamma integral.
-/

open UpperHalfPlane hiding I
open MeasureTheory Set ModularForm Complex
open scoped MatrixGroups ModularForm ComplexConjugate Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem one_mem_strictPeriods_SL2Z :
    (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_SL2Z]
  exact AddSubgroup.mem_zmultiples 1

theorem ofComplex_mk_eq {x y : ℝ} (hy : 0 < y) :
    ((ofComplex (⟨x, y⟩ : ℂ) : ℍ) : ℂ) = (x : ℂ) + y * I := by
  rw [ofComplex_apply_of_im_pos (by simpa using hy)]
  exact Complex.mk_eq_add_mul_I x y

theorem im_ofComplex_mk {x y : ℝ} (hy : 0 < y) : (ofComplex (⟨x, y⟩ : ℂ)).im = y := by
  rw [ofComplex_apply_of_im_pos (by simpa using hy)]
  rfl

/-! ## The coefficient integral at height `y` -/

/-- **The coefficient integral**: `a_f(m) = ∫_0^1 e^{-2πi m (x+iy)} f(x+iy) dx` for every `y > 0`. -/
theorem coeff_qExpansion_eq_setIntegral_Ico {k : ℤ} (f : CuspForm 𝒮ℒ k) (m : ℕ) {y : ℝ}
    (hy : 0 < y) :
    (PowerSeries.coeff m) (qExpansion 1 ⇑f)
      = ∫ x in Ico (0 : ℝ) 1,
          Complex.exp (-(2 * π * I * m * ((x : ℂ) + y * I))) * f (ofComplex ⟨x, y⟩) := by
  rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral f one_pos one_mem_strictPeriods_SL2Z m
    hy, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    integral_Ico_eq_integral_Ioo]
  simp only [Complex.ofReal_one, div_one, one_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
  have hpt : (ofComplex (⟨x, y⟩ : ℂ) : ℍ) = ⟨(x : ℂ) + y * I, by simpa using hy⟩ :=
    UpperHalfPlane.ext (ofComplex_mk_eq hy)
  rw [hpt]
  congr 1
  rw [Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul, one_div,
    ← Complex.exp_neg]
  congr 1
  ring

/-- The Petersson integrand at `x + iy` in terms of the coefficient integrand. -/
theorem petersson_expSeed_ofComplex_mk {k : ℤ} (m : ℕ) (f : CuspForm 𝒮ℒ k) {y : ℝ} (hy : 0 < y)
    (x : ℝ) :
    petersson k f (expSeed m) (ofComplex ⟨x, y⟩)
      = ((y : ℂ) ^ k * Real.exp (-(4 * π * m * y))) *
          conj (Complex.exp (-(2 * π * I * m * ((x : ℂ) + y * I))) * f (ofComplex ⟨x, y⟩)) := by
  rw [petersson, expSeed, im_ofComplex_mk hy, ofComplex_mk_eq hy, map_mul, ← Complex.exp_conj]
  have hconj : conj (-(2 * π * I * m * ((x : ℂ) + y * I)))
      = 2 * π * I * m * x + 2 * π * m * y := by
    simp only [map_neg, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
      Complex.conj_natCast]
    linear_combination (-(2 * π * m * y)) * Complex.I_sq
  rw [hconj, Complex.ofReal_exp]
  have hexp : Complex.exp (2 * π * I * m * ((x : ℂ) + y * I))
      = Complex.exp ((-(4 * π * m * y) : ℝ)) * Complex.exp (2 * π * I * m * x + 2 * π * m * y) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (2 * π * m * y) * Complex.I_sq
  rw [hexp]
  ring

/-- The inner integral: `∫_0^1 ψ(x + iy) dx = y^k e^{-4π m y} conj(a_f(m))`. -/
theorem setIntegral_Ico_petersson_expSeed {k : ℤ} (m : ℕ) (f : CuspForm 𝒮ℒ k) {y : ℝ}
    (hy : 0 < y) :
    ∫ x in Ico (0 : ℝ) 1, petersson k f (expSeed m) (ofComplex ⟨x, y⟩)
      = ((y : ℂ) ^ k * Real.exp (-(4 * π * m * y))) *
          conj ((PowerSeries.coeff m) (qExpansion 1 ⇑f)) := by
  simp_rw [petersson_expSeed_ofComplex_mk m f hy]
  rw [integral_const_mul, integral_conj, ← coeff_qExpansion_eq_setIntegral_Ico f m hy]

/-! ## The strip integral -/

/-- **The strip integral of the Petersson integrand**:
`∫_{strip} conj(f) e_m y^k dμ = (4πm)^{1-k} Γ(k-1) conj(a_f(m))`. -/
theorem setIntegral_modularStrip_petersson_expSeed {k : ℤ} (hk : 3 ≤ k) {m : ℕ} (hm : 1 ≤ m)
    (f : CuspForm 𝒮ℒ k) :
    ∫ z in modularStrip, petersson k f (expSeed m) z
      = (((1 / (4 * π * m)) ^ ((k : ℝ) - 1) * Real.Gamma ((k : ℝ) - 1) : ℝ) : ℂ) *
          conj ((PowerSeries.coeff m) (qExpansion 1 ⇑f)) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  set A := (PowerSeries.coeff m) (qExpansion 1 ⇑f) with hA
  have hpt : ∀ y ∈ Ioi (0 : ℝ),
      (y ^ 2)⁻¹ • ∫ x in Ico (0 : ℝ) 1, petersson k f (expSeed m) (ofComplex ⟨x, y⟩)
        = ((y ^ ((k : ℝ) - 1 - 1) * Real.exp (-(4 * π * m * y)) : ℝ) : ℂ) * conj A := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    rw [setIntegral_Ico_petersson_expSeed m f hy', Complex.real_smul, ← mul_assoc]
    congr 1
    have hexp : ((k : ℝ) - 1 - 1) = ((k - 2 : ℤ) : ℝ) := by push_cast; ring
    rw [hexp, Real.rpow_intCast, zpow_sub₀ hy'.ne', zpow_ofNat]
    push_cast
    ring
  calc ∫ z in modularStrip, petersson k f (expSeed m) z
      = ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ •
          ∫ x in Ico (0 : ℝ) 1, petersson k f (expSeed m) (ofComplex ⟨x, y⟩) :=
        setIntegral_modularStrip_eq_iterated _ (integrableOn_modularStrip_petersson_expSeed hk hm f)
    _ = ∫ y in Ioi (0 : ℝ),
          ((y ^ ((k : ℝ) - 1 - 1) * Real.exp (-(4 * π * m * y)) : ℝ) : ℂ) * conj A :=
        setIntegral_congr_fun measurableSet_Ioi hpt
    _ = (∫ y in Ioi (0 : ℝ), ((y ^ ((k : ℝ) - 1 - 1) * Real.exp (-(4 * π * m * y)) : ℝ) : ℂ))
          * conj A := integral_mul_const _ _
    _ = ((∫ y in Ioi (0 : ℝ), y ^ ((k : ℝ) - 1 - 1) * Real.exp (-(4 * π * m * y)) : ℝ) : ℂ)
          * conj A := by
        congr 1
        exact integral_ofReal
    _ = (((1 / (4 * π * m)) ^ ((k : ℝ) - 1) * Real.Gamma ((k : ℝ) - 1) : ℝ) : ℂ) * conj A := by
        rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity)]

/-- **The Petersson product of a cusp form against the Poincaré series `P_m`**, level one,
weight `k ≥ 3`, `m ≥ 1`: `⟨f, P_m⟩ = 2 (4πm)^{1-k} Γ(k-1) conj(a_f(m))`. -/
theorem peterssonInner_poincareSeries {k : ℤ} (hk : 3 ≤ k) {m : ℕ} (hm : 1 ≤ m)
    (f : CuspForm 𝒮ℒ k) :
    peterssonInner k f (poincareSeries k m)
      = 2 * ((((1 / (4 * π * m)) ^ ((k : ℝ) - 1) * Real.Gamma ((k : ℝ) - 1) : ℝ) : ℂ) *
          conj ((PowerSeries.coeff m) (qExpansion 1 ⇑f))) := by
  rw [peterssonInner_poincareSeries_eq_two_mul_setIntegral_modularStrip hk hm f,
    setIntegral_modularStrip_petersson_expSeed hk hm f]

end

end GaloisForLFunctions.HTGeometry
