import GaloisForLFunctions.RHTower.GL3FundamentalDomain
import GaloisForLFunctions.HTGeometry.ModularStripUnfolding


/-!
# Unfolding along the integral Heisenberg group

`U(ℤ) = {n(a₁,a₂,a₃)}` acts on `h³` by Heisenberg translations
`(x₁,x₂,x₃) ↦ (x₁+a₁, x₂+a₂, x₃+a₃+a₂x₁)` (`unipZ_smul`). Choosing `a₁ = −⌊x₁⌋`, `a₂ = −⌊x₂⌋` and then
`a₃` shows that the unit cell `0 ≤ x₁, x₂, x₃ < 1` meets each orbit exactly once, so it is a
fundamental domain for `U(ℤ)` (`isFundamentalDomain_heisCell`).

With representatives of `U(ℤ)\SL₃(ℤ)`, the translates of the `SL₃(ℤ)` fundamental domain form a
second fundamental domain for `U(ℤ)`. Comparing the two gives the unfolding identity
(`lintegral_poincare_unfold`):
`∫_{SL₃(ℤ)\h³} (Σ_{γ ∈ U(ℤ)\SL₃(ℤ)} φ(γz)) F(z) dz = ∫_{U(ℤ)\h³} φ(z) F(z) dz`
for nonnegative measurable `φ` invariant under `U(ℤ)` and `F` invariant under `SL₃(ℤ)`.
-/

open Matrix MeasureTheory
open scoped Pointwise ENNReal

namespace GaloisForLFunctions.RHTower.GL3
namespace H3

/-- `SL₃(ℤ)`. -/
abbrev SL3Z := Matrix.SpecialLinearGroup (Fin 3) ℤ

instance : MeasurableConstSMul SL3Z H3 :=
  ⟨fun γ => (continuous_const_smul (slToGL γ)).measurable⟩

/-! ### The integral Heisenberg group -/

/-- The upper unipotent integral matrix `n(a₁, a₂, a₃)`. -/
def unipMat (a1 a2 a3 : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![1, a2, a3; 0, 1, a1; 0, 0, 1]

theorem det_unipMat (a1 a2 a3 : ℤ) : (unipMat a1 a2 a3).det = 1 := by
  simp [unipMat, Matrix.det_fin_three]

/-- `n(a₁, a₂, a₃) ∈ SL₃(ℤ)`. -/
def unipZ (a1 a2 a3 : ℤ) : SL3Z := ⟨unipMat a1 a2 a3, det_unipMat a1 a2 a3⟩

/-- The integral Heisenberg group `U(ℤ)`. -/
def heisZ : Subgroup SL3Z where
  carrier := {γ | ∃ a1 a2 a3 : ℤ, γ = unipZ a1 a2 a3}
  mul_mem' := by
    rintro _ _ ⟨a1, a2, a3, rfl⟩ ⟨b1, b2, b3, rfl⟩
    refine ⟨a1 + b1, a2 + b2, a3 + b3 + a2 * b1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipZ, unipMat, Matrix.mul_apply, Fin.sum_univ_three]
    all_goals ring
  one_mem' := ⟨0, 0, 0, by ext i j; fin_cases i <;> fin_cases j <;> simp [unipZ, unipMat]⟩
  inv_mem' := by
    rintro _ ⟨a1, a2, a3, rfl⟩
    refine ⟨-a1, -a2, a2 * a1 - a3, ?_⟩
    rw [inv_eq_iff_mul_eq_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipZ, unipMat, Matrix.mul_apply, Fin.sum_univ_three]
    ring

theorem unipZ_smul (a1 a2 a3 : ℤ) (z : H3) :
    unipZ a1 a2 a3 • z = z.translate a1 a2 a3 := by
  rw [sl_smul_def, ← nGL_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slToGL, unipZ, unipMat, nGL, nmat]

instance : MeasurableConstSMul heisZ H3 := ⟨fun h => measurable_const_smul (h : SL3Z)⟩

instance : SMulInvariantMeasure heisZ H3 volume :=
  ⟨fun h _ hs => SMulInvariantMeasure.measure_preimage_smul (h : SL3Z) hs⟩

/-- The unit cell `0 ≤ x₁, x₂, x₃ < 1`. -/
def heisCell : Set H3 :=
  {z | z.x1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.x2 ∈ Set.Ico (0 : ℝ) 1 ∧ z.x3 ∈ Set.Ico (0 : ℝ) 1}

theorem measurableSet_heisCell : MeasurableSet heisCell :=
  (measurableSet_Ico.preimage continuous_x1.measurable).inter
    ((measurableSet_Ico.preimage continuous_x2.measurable).inter
      (measurableSet_Ico.preimage continuous_x3.measurable))

theorem int_eq_zero_of_Ico {a : ℤ} {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (hax : x + a ∈ Set.Ico (0 : ℝ) 1) : a = 0 := by
  have h1 : (-1 : ℝ) < a := by linarith [hx.2, hax.1]
  have h2 : (a : ℝ) < 1 := by linarith [hx.1, hax.2]
  have h1' : -1 < a := by exact_mod_cast h1
  have h2' : a < 1 := by exact_mod_cast h2
  omega

/-- The unit cell meets each `U(ℤ)`-orbit at most once. -/
theorem eq_one_of_mem_heisCell {h : heisZ} {z : H3} (hz : z ∈ heisCell) (hhz : h • z ∈ heisCell) :
    h = 1 := by
  obtain ⟨a1, a2, a3, ha⟩ := h.2
  rw [Subgroup.smul_def, ha, unipZ_smul] at hhz
  obtain ⟨hx1, hx2, hx3⟩ := hz
  obtain ⟨k1, k2, k3⟩ := hhz
  simp only [translate] at k1 k2 k3
  have e1 := int_eq_zero_of_Ico hx1 k1
  have e2 := int_eq_zero_of_Ico hx2 k2
  subst e1 e2
  simp only [Int.cast_zero, zero_mul, add_zero] at k3
  have e3 := int_eq_zero_of_Ico hx3 k3
  subst e3
  apply Subtype.ext
  rw [ha]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipZ, unipMat]

/-- Every `U(ℤ)`-orbit meets the unit cell. -/
theorem exists_smul_mem_heisCell (z : H3) : ∃ h : heisZ, h • z ∈ heisCell := by
  set a1 := -⌊z.x1⌋
  set a2 := -⌊z.x2⌋
  set a3 := -⌊z.x3 + a2 * z.x1⌋
  refine ⟨⟨unipZ a1 a2 a3, a1, a2, a3, rfl⟩, ?_⟩
  rw [Subgroup.smul_def]
  show unipZ a1 a2 a3 • z ∈ heisCell
  rw [unipZ_smul]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [translate, a1, a2, a3, Int.cast_neg] <;> constructor
  · linarith [Int.floor_le z.x1]
  · linarith [Int.lt_floor_add_one z.x1]
  · linarith [Int.floor_le z.x2]
  · linarith [Int.lt_floor_add_one z.x2]
  · have := Int.floor_le (z.x3 + -(⌊z.x2⌋ : ℝ) * z.x1)
    linarith
  · have := Int.lt_floor_add_one (z.x3 + -(⌊z.x2⌋ : ℝ) * z.x1)
    linarith

/-- **The unit cell is a fundamental domain for `U(ℤ)`.** -/
theorem isFundamentalDomain_heisCell : IsFundamentalDomain heisZ heisCell volume where
  nullMeasurableSet := measurableSet_heisCell.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall exists_smul_mem_heisCell
  aedisjoint := by
    intro h₁ h₂ hne
    refine (Set.disjoint_left.2 ?_).aedisjoint
    rintro z ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, hw⟩
    apply hne
    have h12 : (h₂⁻¹ * h₁) • w₁ = w₂ := by
      simp only at hw
      rw [mul_smul, ← hw, inv_smul_smul]
    have := eq_one_of_mem_heisCell hw₁ (h12 ▸ hw₂)
    rw [inv_mul_eq_one] at this
    exact this.symm

/-! ### Unfolding -/

/-- The cosets `U(ℤ)\SL₃(ℤ)`. -/
abbrev HeisCoset := Quotient (QuotientGroup.rightRel heisZ)

/-- A representative of each coset `U(ℤ)γ`. -/
noncomputable def cosetRep (i : HeisCoset) : SL3Z := Quotient.out i

theorem cosetRep_surj (g : SL3Z) : ∃ (h : heisZ) (i : HeisCoset), (h : SL3Z) * cosetRep i = g := by
  have hg : QuotientGroup.rightRel heisZ (cosetRep ⟦g⟧) g := Quotient.mk_out g
  rw [QuotientGroup.rightRel_apply] at hg
  exact ⟨⟨_, hg⟩, ⟦g⟧, by simp⟩

theorem cosetRep_uniq (h h' : heisZ) (i i' : HeisCoset)
    (heq : (h : SL3Z) * cosetRep i = (h' : SL3Z) * cosetRep i') : h = h' ∧ i = i' := by
  have hii : i = i' := by
    rw [← Quotient.out_eq i, ← Quotient.out_eq i']
    apply Quotient.sound
    show QuotientGroup.rightRel heisZ (cosetRep i) (cosetRep i')
    rw [QuotientGroup.rightRel_apply]
    have e : cosetRep i' = (h' : SL3Z)⁻¹ * h * cosetRep i := by
      rw [mul_assoc, heq, inv_mul_cancel_left]
    have : cosetRep i' * (cosetRep i)⁻¹ = (h' : SL3Z)⁻¹ * h := by
      rw [e, mul_inv_cancel_right]
    rw [this]
    exact heisZ.mul_mem (heisZ.inv_mem h'.2) h.2
  subst hii
  exact ⟨Subtype.ext (mul_right_cancel heq), rfl⟩

theorem isFundamentalDomain_iUnion_cosetRep :
    IsFundamentalDomain heisZ (⋃ i, cosetRep i • fundDomain) volume :=
  GaloisForLFunctions.HTGeometry.isFundamentalDomain_iUnion_smul_of_cosetReps
    isFundamentalDomain_fundDomain heisZ cosetRep cosetRep_surj cosetRep_uniq

/-- **Unfolding.** For `φ ≥ 0` invariant under `U(ℤ)` and `F ≥ 0` invariant under `SL₃(ℤ)`,
`∫_{SL₃(ℤ)\h³} (Σ_{γ ∈ U(ℤ)\SL₃(ℤ)} φ(γz)) F(z) dz = ∫_{U(ℤ)\h³} φ(z) F(z) dz`. -/
theorem lintegral_poincare_unfold {φ F : H3 → ℝ≥0∞} (hφ : Measurable φ) (hF : Measurable F)
    (hφU : ∀ (h : heisZ) (z : H3), φ (h • z) = φ z)
    (hFΓ : ∀ (γ : SL3Z) (z : H3), F (γ • z) = F z) :
    ∫⁻ z in fundDomain, (∑' i, φ (cosetRep i • z)) * F z = ∫⁻ z in heisCell, φ z * F z := by
  have hinv : ∀ (h : heisZ) (z : H3), φ (h • z) * F (h • z) = φ z * F z := fun h z => by
    rw [hφU, Subgroup.smul_def, hFΓ]
  rw [isFundamentalDomain_heisCell.setLIntegral_eq isFundamentalDomain_iUnion_cosetRep _ hinv]
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => cosetRep i • fundDomain) :=
    fun i i' hii => isFundamentalDomain_fundDomain.aedisjoint fun heq =>
      hii (cosetRep_uniq 1 1 i i' (by simpa using heq)).2
  rw [lintegral_iUnion₀ (fun i => isFundamentalDomain_fundDomain.nullMeasurableSet_smul _) hdisj]
  have hterm : ∀ i, ∫⁻ z in cosetRep i • fundDomain, φ z * F z =
      ∫⁻ z in fundDomain, φ (cosetRep i • z) * F z := by
    intro i
    rw [← Set.image_smul, ← (measurePreserving_smul (cosetRep i) volume).setLIntegral_comp_emb
      (measurableEmbedding_const_smul _)]
    simp only [hFΓ]
  simp_rw [hterm]
  calc ∫⁻ z in fundDomain, (∑' i, φ (cosetRep i • z)) * F z
      = ∫⁻ z in fundDomain, ∑' i, φ (cosetRep i • z) * F z := by
        simp_rw [ENNReal.tsum_mul_right]
    _ = ∑' i, ∫⁻ z in fundDomain, φ (cosetRep i • z) * F z :=
        lintegral_tsum fun i => ((hφ.comp (measurable_const_smul (cosetRep i))).mul hF).aemeasurable

end H3
end GaloisForLFunctions.RHTower.GL3
