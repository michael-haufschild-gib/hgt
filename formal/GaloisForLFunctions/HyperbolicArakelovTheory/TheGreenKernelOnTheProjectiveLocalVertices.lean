import GaloisForLFunctions.HyperbolicArakelovTheory.TheFullAdelicDegreeConfiguration
import GaloisForLFunctions.HyperbolicArakelovTheory.TheFinitePlacesAreTrees

/-!
# The projective local Green ratio

The ratio of determinant norm to squared maximal entry norm is unchanged
by integral basis changes. It is the radial coordinate of the Green kernel
on local lattice-homothety classes.
-/

set_option autoImplicit false
noncomputable section
open Matrix

namespace GaloisForLFunctions.HyperbolicArakelovTheory.AdelicGreen
open FullAdelic
local instance (p : {p : ℕ // p.Prime}) : Fact p.1.Prime := ⟨p.2⟩

variable (p : {p : ℕ // p.Prime})

/-- Maximal entry norm, before passing to homothety classes. -/
def entrySize (g : LocalGL p) : ℝ :=
  max (max ‖g 0 0‖ ‖g 0 1‖) (max ‖g 1 0‖ ‖g 1 1‖)

theorem entry_norm_le (g : LocalGL p) (i j : Fin 2) : ‖g i j‖ ≤ entrySize p g := by
  fin_cases i <;> fin_cases j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem entrySize_nonneg (g : LocalGL p) : 0 ≤ entrySize p g :=
  (norm_nonneg (g 0 0)).trans (entry_norm_le p g 0 0)

theorem entrySize_le (g : LocalGL p) {c : ℝ} (h : ∀ i j, ‖g i j‖ ≤ c) :
    entrySize p g ≤ c :=
  max_le (max_le (h 0 0) (h 0 1)) (max_le (h 1 0) (h 1 1))

theorem entrySize_pos (g : LocalGL p) : 0 < entrySize p g := by
  by_contra hn
  have hz (i j : Fin 2) : g i j = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm ((entry_norm_le p g i j).trans (le_of_not_gt hn)) (norm_nonneg _)
  apply g.det_ne_zero
  rw [Matrix.det_fin_two, hz 0 0, hz 0 1, hz 1 0, hz 1 1]
  ring

/-- Integral right multiplication contracts the maximal entry norm. -/
theorem entrySize_mul_le (g h : LocalGL p) (hh : ∀ i j, ‖h i j‖ ≤ 1) :
    entrySize p (g * h) ≤ entrySize p g := by
  apply entrySize_le
  intro i j
  change ‖(g.val * h.val) i j‖ ≤ _
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  apply (Padic.nonarchimedean _ _).trans
  apply max_le
  · rw [norm_mul]
    simpa only [mul_one] using mul_le_mul (entry_norm_le p g i 0) (hh 0 j)
      (norm_nonneg _) (entrySize_nonneg p g)
  · rw [norm_mul]
    simpa only [mul_one] using mul_le_mul (entry_norm_le p g i 1) (hh 1 j)
      (norm_nonneg _) (entrySize_nonneg p g)

/-- Integral left multiplication contracts the maximal entry norm. -/
theorem entrySize_mul_le_left (g h : LocalGL p) (hg : ∀ i j, ‖g i j‖ ≤ 1) :
    entrySize p (g * h) ≤ entrySize p h := by
  apply entrySize_le
  intro i j
  change ‖(g.val * h.val) i j‖ ≤ _
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  apply (Padic.nonarchimedean _ _).trans
  apply max_le
  · rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hg i 0) (entry_norm_le p h 0 j)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hg i 1) (entry_norm_le p h 1 j)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem entrySize_mul_integral (g : LocalGL p) (h : GL (Fin 2) ℤ_[p.1]) :
    entrySize p (g * integralMap p h) = entrySize p g := by
  apply le_antisymm (entrySize_mul_le p g _ (fun i j => (h i j).2))
  have he := entrySize_mul_le p (g * integralMap p h) (integralMap p h⁻¹)
    (fun i j => (h⁻¹ i j).2)
  simpa only [map_inv, mul_inv_cancel_right] using he

theorem entrySize_integral_mul (g : LocalGL p) (h : GL (Fin 2) ℤ_[p.1]) :
    entrySize p (integralMap p h * g) = entrySize p g := by
  apply le_antisymm (entrySize_mul_le_left p _ g (fun i j => (h i j).2))
  have he := entrySize_mul_le_left p (integralMap p h⁻¹) (integralMap p h * g)
    (fun i j => (h⁻¹ i j).2)
  simpa only [map_inv, inv_mul_cancel_left] using he

/-- The determinant ratio giving the projective radial Green coordinate. -/
def greenRatio (g : LocalGL p) : ℝ := ‖g.val.det‖ / entrySize p g ^ 2

theorem greenRatio_pos (g : LocalGL p) : 0 < greenRatio p g :=
  div_pos (norm_pos_iff.mpr g.det_ne_zero) (sq_pos_of_pos (entrySize_pos p g))

theorem greenRatio_le_one (g : LocalGL p) : greenRatio p g ≤ 1 := by
  apply (div_le_one (sq_pos_of_pos (entrySize_pos p g))).mpr
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  apply (Padic.nonarchimedean _ _).trans
  rw [norm_neg, norm_mul, norm_mul]
  apply max_le
  · simpa only [pow_two] using mul_le_mul (entry_norm_le p g 0 0)
      (entry_norm_le p g 1 1) (norm_nonneg _) (entrySize_nonneg p g)
  · simpa only [pow_two] using mul_le_mul (entry_norm_le p g 0 1)
      (entry_norm_le p g 1 0) (norm_nonneg _) (entrySize_nonneg p g)

theorem greenRatio_mul_integral (g : LocalGL p) (h : GL (Fin 2) ℤ_[p.1]) :
    greenRatio p (g * integralMap p h) = greenRatio p g := by
  rw [greenRatio, GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul,
    integralMap_det_norm, mul_one, entrySize_mul_integral]
  rfl

theorem greenRatio_integral_mul (g : LocalGL p) (h : GL (Fin 2) ℤ_[p.1]) :
    greenRatio p (integralMap p h * g) = greenRatio p g := by
  rw [greenRatio, GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul,
    integralMap_det_norm, one_mul, entrySize_integral_mul]
  rfl

private theorem max_mul_nonnegative (a b c : ℝ) (hc : 0 ≤ c) :
    max (a * c) (b * c) = max a b * c := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, max_eq_right (mul_le_mul_of_nonneg_right hab hc)]
  · rw [max_eq_left hba, max_eq_left (mul_le_mul_of_nonneg_right hba hc)]

theorem entrySize_mul_scalar (g : LocalGL p) (u : ℚ_[p.1]ˣ) :
    entrySize p (g * GeneralLinearGroup.scalar (Fin 2) u) = entrySize p g * ‖u.val‖ := by
  have he (i j : Fin 2) :
      (g * GeneralLinearGroup.scalar (Fin 2) u) i j = g i j * u.val := by
    change (g.val * Matrix.scalar (Fin 2) u.val) i j = _
    simp only [Matrix.scalar_apply, Matrix.mul_diagonal]
  simp only [entrySize, he, norm_mul,
    max_mul_nonnegative _ _ _ (norm_nonneg u.val)]

/-- The ratio is unchanged by scalar homothety. -/
theorem greenRatio_mul_scalar (g : LocalGL p) (u : ℚ_[p.1]ˣ) :
    greenRatio p (g * GeneralLinearGroup.scalar (Fin 2) u) = greenRatio p g := by
  have hd : ‖(GeneralLinearGroup.scalar (Fin 2) u).val.det‖ = ‖u.val‖ ^ 2 := by
    simp [GeneralLinearGroup.coe_scalar, norm_pow]
  have hu : ‖u.val‖ ≠ 0 := norm_ne_zero_iff.mpr u.ne_zero
  have hg : entrySize p g ≠ 0 := (entrySize_pos p g).ne'
  rw [greenRatio, GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul, hd,
    entrySize_mul_scalar, greenRatio]
  field_simp

theorem greenRatio_eq_of_projective_eq {g h : LocalGL p}
    (he : ProjGenLinGroup.mk g = ProjGenLinGroup.mk h) :
    greenRatio p g = greenRatio p h := by
  obtain ⟨u, rfl⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
  exact (greenRatio_mul_scalar p g u).symm

/-- The radial coordinate descends through scalar homothety. -/
def projectiveRatio : LocalPGL p → ℝ :=
  Quotient.lift (greenRatio p) fun _ _ h =>
    greenRatio_eq_of_projective_eq p (Quotient.sound h)

@[simp] theorem projectiveRatio_mk (g : LocalGL p) :
    projectiveRatio p (ProjGenLinGroup.mk g) = greenRatio p g := rfl

theorem projectiveRatio_mul_mem (g k : LocalPGL p) (hk : k ∈ integralPGL p) :
    projectiveRatio p (g * k) = projectiveRatio p g := by
  obtain ⟨h, rfl⟩ := hk
  obtain ⟨a, rfl⟩ := ProjGenLinGroup.mk_surjective g
  rw [← map_mul, projectiveRatio_mk, projectiveRatio_mk, greenRatio_mul_integral]

theorem projectiveRatio_mem_mul (k g : LocalPGL p) (hk : k ∈ integralPGL p) :
    projectiveRatio p (k * g) = projectiveRatio p g := by
  obtain ⟨h, rfl⟩ := hk
  obtain ⟨a, rfl⟩ := ProjGenLinGroup.mk_surjective g
  rw [← map_mul, projectiveRatio_mk, projectiveRatio_mk, greenRatio_integral_mul]

/-- The invariant relative coordinate on actual local lattice classes. -/
def vertexRatio : LocalVertex p → LocalVertex p → ℝ :=
  Quotient.lift
    (fun g => Quotient.lift (fun h => projectiveRatio p (g⁻¹ * h))
      (fun h₁ h₂ he => by
        have hk : h₁⁻¹ * h₂ ∈ integralPGL p := QuotientGroup.eq.mp
          (Quotient.sound he : (QuotientGroup.mk h₁ : LocalVertex p) = QuotientGroup.mk h₂)
        have hr := projectiveRatio_mul_mem p (g⁻¹ * h₁) (h₁⁻¹ * h₂) hk
        simpa only [mul_assoc, mul_inv_cancel_left] using hr.symm))
    (fun g₁ g₂ he => by
      funext h
      refine Quotient.inductionOn h fun h => ?_
      have hk : g₁⁻¹ * g₂ ∈ integralPGL p := QuotientGroup.eq.mp
        (Quotient.sound he : (QuotientGroup.mk g₁ : LocalVertex p) = QuotientGroup.mk g₂)
      have hki : g₂⁻¹ * g₁ ∈ integralPGL p := by
        simpa only [mul_inv_rev, inv_inv] using (integralPGL p).inv_mem hk
      have hr := projectiveRatio_mem_mul p (g₂⁻¹ * g₁) (g₁⁻¹ * h) hki
      simpa only [mul_assoc, mul_inv_cancel_left] using hr.symm)

@[simp] theorem vertexRatio_mk (g h : LocalPGL p) :
    vertexRatio p (QuotientGroup.mk g) (QuotientGroup.mk h) =
      projectiveRatio p (g⁻¹ * h) := rfl

theorem vertexRatio_smul (g : LocalPGL p) (x y : LocalVertex p) :
    vertexRatio p (g • x) (g • y) = vertexRatio p x y := by
  refine Quotient.inductionOn₂ x y fun a b => ?_
  change projectiveRatio p ((g * a)⁻¹ * (g * b)) = projectiveRatio p (a⁻¹ * b)
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/-- Upper integral shear for reducing a maximal pivot. -/
def upperShear (t : ℤ_[p.1]) : GL (Fin 2) ℤ_[p.1] :=
  ⟨!![1, t; 0, 1], !![1, -t; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- Lower integral shear for reducing a maximal pivot. -/
def lowerShear (t : ℤ_[p.1]) : GL (Fin 2) ℤ_[p.1] :=
  ⟨!![1, 0; t, 1], !![1, 0; -t, 1],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def swapBasis : GL (Fin 2) ℤ_[p.1] :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def pivotBasis (i : Fin 2) : GL (Fin 2) ℤ_[p.1] := if i = 0 then 1 else swapBasis p

theorem exists_maximal_entry (g : LocalGL p) : ∃ i j, ‖g i j‖ = entrySize p g := by
  rcases le_total (max ‖g 0 0‖ ‖g 0 1‖) (max ‖g 1 0‖ ‖g 1 1‖) with h | h
  · rcases le_total ‖g 1 0‖ ‖g 1 1‖ with h' | h'
    · exact ⟨1, 1, by rw [entrySize, max_eq_right h, max_eq_right h']⟩
    · exact ⟨1, 0, by rw [entrySize, max_eq_right h, max_eq_left h']⟩
  · rcases le_total ‖g 0 0‖ ‖g 0 1‖ with h' | h'
    · exact ⟨0, 1, by rw [entrySize, max_eq_left h, max_eq_right h']⟩
    · exact ⟨0, 0, by rw [entrySize, max_eq_left h, max_eq_left h']⟩

theorem pivotBasis_entry (g : LocalGL p) (i j : Fin 2) :
    (integralMap p (pivotBasis p i) * g * integralMap p (pivotBasis p j)) 0 0 = g i j := by
  fin_cases i <;> fin_cases j <;>
    simp [pivotBasis, swapBasis, integralMap, GeneralLinearGroup.map,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The diagonal representative of a local lattice class. -/
def diagonal (d : ℚ_[p.1]ˣ) : LocalGL p :=
  ⟨!![1, 0; 0, d.val], !![1, 0; 0, (d⁻¹).val],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private theorem integral_upperShear_val (t : ℤ_[p.1]) :
    (integralMap p (upperShear p t)).val = !![1, (t : ℚ_[p.1]); 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem integral_lowerShear_val (t : ℤ_[p.1]) :
    (integralMap p (lowerShear p t)).val = !![1, 0; (t : ℚ_[p.1]), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem diagonal_reduction_of_maximal_pivot (g : LocalGL p)
    (hpivot : ‖g 0 0‖ = entrySize p g) :
    ∃ l r : GL (Fin 2) ℤ_[p.1], ∃ u d : ℚ_[p.1]ˣ,
      ‖d.val‖ ≤ 1 ∧
      integralMap p l * g * integralMap p r =
        diagonal p d * GeneralLinearGroup.scalar (Fin 2) u := by
  have ha : g 0 0 ≠ 0 := norm_ne_zero_iff.mp (by rw [hpivot]; exact (entrySize_pos p g).ne')
  have hquot (i j : Fin 2) : ‖-(g i j / g 0 0)‖ ≤ 1 := by
    rw [norm_neg, norm_div]
    apply (div_le_one (norm_pos_iff.mpr ha)).mpr
    rw [hpivot]
    exact entry_norm_le p g i j
  let t : ℤ_[p.1] := ⟨-(g 0 1 / g 0 0), hquot 0 1⟩
  let v : ℤ_[p.1] := ⟨-(g 1 0 / g 0 0), hquot 1 0⟩
  let d : ℚ_[p.1]ˣ := Units.mk0 (g.val.det / g 0 0 ^ 2)
    (div_ne_zero g.det_ne_zero (pow_ne_zero 2 ha))
  refine ⟨lowerShear p v, upperShear p t, Units.mk0 (g 0 0) ha, d, ?_, ?_⟩
  · change ‖g.val.det / g 0 0 ^ 2‖ ≤ 1
    rw [norm_div, norm_pow, hpivot]
    exact greenRatio_le_one p g
  · apply Units.ext
    rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul,
      integral_lowerShear_val, integral_upperShear_val,
      GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonal, t, v, d, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    all_goals field_simp [ha]
    all_goals ring

/-- Every local lattice class has an integral diagonal reduction, with ratio at most one. -/
theorem exists_diagonal_reduction (g : LocalGL p) :
    ∃ l r : GL (Fin 2) ℤ_[p.1], ∃ u d : ℚ_[p.1]ˣ,
      ‖d.val‖ ≤ 1 ∧
      integralMap p l * g * integralMap p r =
        diagonal p d * GeneralLinearGroup.scalar (Fin 2) u := by
  obtain ⟨i, j, hij⟩ := exists_maximal_entry p g
  have hpivot : ‖(integralMap p (pivotBasis p i) * g * integralMap p (pivotBasis p j)) 0 0‖ =
      entrySize p (integralMap p (pivotBasis p i) * g * integralMap p (pivotBasis p j)) := by
    rw [pivotBasis_entry, entrySize_mul_integral, entrySize_integral_mul]
    exact hij
  obtain ⟨l, r, u, d, hd, he⟩ := diagonal_reduction_of_maximal_pivot p _ hpivot
  refine ⟨l * pivotBasis p i, pivotBasis p j * r, u, d, hd, ?_⟩
  simpa only [map_mul, mul_assoc] using he

#print axioms greenRatio_mul_scalar
#print axioms vertexRatio_smul
#print axioms exists_diagonal_reduction

end GaloisForLFunctions.HyperbolicArakelovTheory.AdelicGreen
