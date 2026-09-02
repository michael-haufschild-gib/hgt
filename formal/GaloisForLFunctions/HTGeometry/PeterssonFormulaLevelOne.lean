import GaloisForLFunctions.HTGeometry.PeterssonInnerProductLevelOne

/-!
# The Petersson formula for level one, abstract form

Expanding the Poincaré series `P_m` in an orthonormal basis `(b_i)` of the level-one cusp forms
of weight `k ≥ 3` for the Petersson product, `P_m = Σ_i ⟨b_i, P_m⟩ b_i`, and taking the `n`-th
Fourier coefficient gives

  `a_{P_m}(n) = 2 (4πm)^{1-k} Γ(k-1) · Σ_i conj(a_{b_i}(m)) a_{b_i}(n)`,

since `⟨b_i, P_m⟩ = 2 (4πm)^{1-k} Γ(k-1) conj(a_{b_i}(m))` and the coefficient map is linear.
-/

open UpperHalfPlane hiding I
open MeasureTheory Set ModularForm Complex
open scoped MatrixGroups ModularForm ComplexConjugate Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k : ℤ}

/-! ## The coefficient functional -/

/-- The `n`-th Fourier coefficient of a level-one cusp form. -/
def cuspCoeff (n : ℕ) (f : CuspForm 𝒮ℒ k) : ℂ := (PowerSeries.coeff n) (qExpansion 1 ⇑f)

theorem cuspCoeff_add (n : ℕ) (f g : CuspForm 𝒮ℒ k) :
    cuspCoeff n (f + g) = cuspCoeff n f + cuspCoeff n g := by
  unfold cuspCoeff
  rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL2Z f g, map_add]

theorem cuspCoeff_smul (n : ℕ) (c : ℂ) (f : CuspForm 𝒮ℒ k) :
    cuspCoeff n (c • f) = c * cuspCoeff n f := by
  unfold cuspCoeff
  rw [show ⇑(c • f) = c • ⇑f from rfl,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL2Z c f, map_smul, smul_eq_mul]

/-- The coefficient functional on the Petersson space. -/
def cuspCoeffLinear (n : ℕ) : PeterssonSpace k →ₗ[ℂ] ℂ where
  toFun f := cuspCoeff n f.toCuspForm
  map_add' f g := cuspCoeff_add n f.toCuspForm g.toCuspForm
  map_smul' c f := cuspCoeff_smul n c f.toCuspForm

theorem cuspCoeffLinear_apply (n : ℕ) (f : PeterssonSpace k) :
    cuspCoeffLinear n f = cuspCoeff n f.toCuspForm := rfl

/-! ## The Poincaré series in the Petersson space -/

/-- `P_m` as an element of the Petersson space. -/
def poincarePS (hk : 3 ≤ k) {m : ℕ} (hm : 1 ≤ m) : PeterssonSpace k := poincareSeriesCF hk hm

/-- The Petersson constant `2 (4πm)^{1-k} Γ(k-1)`. -/
def peterssonConstant (k : ℤ) (m : ℕ) : ℂ :=
  2 * (((1 / (4 * π * m)) ^ ((k : ℝ) - 1) * Real.Gamma ((k : ℝ) - 1) : ℝ) : ℂ)

/-- `⟨f, P_m⟩ = 2 (4πm)^{1-k} Γ(k-1) conj(a_f(m))` in the Petersson space. -/
theorem inner_poincarePS (hk : 3 ≤ k) {m : ℕ} (hm : 1 ≤ m) (f : PeterssonSpace k) :
    inner ℂ f (poincarePS hk hm) = peterssonConstant k m * conj (cuspCoeff m f.toCuspForm) := by
  rw [inner_peterssonSpace]
  show peterssonInner k f.toCuspForm (poincareSeries k m) = _
  rw [peterssonInner_poincareSeries hk hm f.toCuspForm, peterssonConstant, cuspCoeff]
  ring

/-! ## The Petersson formula -/

/-- **The Petersson formula (abstract form).** For an orthonormal basis `b` of the level-one
cusp forms of weight `k ≥ 3` and `m ≥ 1`,
`a_{P_m}(n) = 2 (4πm)^{1-k} Γ(k-1) Σ_i conj(a_{b_i}(m)) a_{b_i}(n)`. -/
theorem cuspCoeff_poincareSeriesCF_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (PeterssonSpace k)) (hk : 3 ≤ k) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    cuspCoeff n (poincareSeriesCF hk hm)
      = peterssonConstant k m *
          ∑ i, conj (cuspCoeff m (b i).toCuspForm) * cuspCoeff n (b i).toCuspForm := by
  have hexp := b.sum_repr (poincarePS hk hm)
  have this : cuspCoeffLinear n (poincarePS hk hm)
      = cuspCoeffLinear n (∑ i, (b.repr (poincarePS hk hm)).ofLp i • b i) := by rw [hexp]
  rw [map_sum] at this
  simp_rw [map_smul, smul_eq_mul, OrthonormalBasis.repr_apply_apply, inner_poincarePS hk hm] at this
  rw [Finset.mul_sum]
  refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [cuspCoeffLinear_apply]
  ring

/-- The Petersson formula with the standard orthonormal basis of the Petersson space. -/
theorem cuspCoeff_poincareSeriesCF_eq_sum_std (hk : 3 ≤ k) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    cuspCoeff n (poincareSeriesCF hk hm)
      = peterssonConstant k m *
          ∑ i, conj (cuspCoeff m ((stdOrthonormalBasis ℂ (PeterssonSpace k)) i).toCuspForm) *
            cuspCoeff n ((stdOrthonormalBasis ℂ (PeterssonSpace k)) i).toCuspForm :=
  cuspCoeff_poincareSeriesCF_eq_sum _ hk hm n

end

end GaloisForLFunctions.HTGeometry
