import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicNorm

/-!
# Norm laws and attainment for cubic observations

The curved factor and five-coordinate pairing capacity are absolutely
homogeneous and satisfy the triangle inequality. Together with their audited
kernels these are norms. The scalar maximum and the actual physical capacity
are attained; the five pairing observations are independent on the section.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set


theorem cubicArcCapacity_add_le (A E A' E' : ℝ) :
    cubicArcCapacity (A+A') (E+E') ≤ cubicArcCapacity A E+cubicArcCapacity A' E' := by
  apply csSup_le (cubicArcValues_nonempty (A+A') (E+E'))
  rintro y ⟨t,ht,rfl⟩
  have hv : cubicArcReadout (A+A') (E+E') t=
      cubicArcReadout A E t+cubicArcReadout A' E' t := by
    unfold cubicArcReadout
    ring
  dsimp only
  rw [hv]
  exact (abs_add_le _ _).trans (add_le_add
    (cubicArcCapacity_bounds A E ht) (cubicArcCapacity_bounds A' E' ht))

theorem cubicArcCapacity_smul_le (k A E : ℝ) :
    cubicArcCapacity (k*A) (k*E) ≤ |k| * cubicArcCapacity A E := by
  apply csSup_le (cubicArcValues_nonempty (k*A) (k*E))
  rintro y ⟨t,ht,rfl⟩
  have hv : cubicArcReadout (k*A) (k*E) t=k*cubicArcReadout A E t := by
    unfold cubicArcReadout
    ring
  dsimp only
  rw [hv,abs_mul]
  exact mul_le_mul_of_nonneg_left (cubicArcCapacity_bounds A E ht) (abs_nonneg k)

theorem cubicArcCapacity_smul (k A E : ℝ) :
    cubicArcCapacity (k*A) (k*E)=|k| * cubicArcCapacity A E := by
  apply le_antisymm (cubicArcCapacity_smul_le k A E)
  by_cases hk : k=0
  · simp [hk,cubicArcCapacity_zero]
  have hA : (1/k)*(k*A)=A := by field_simp
  have hE : (1/k)*(k*E)=E := by field_simp
  have h := cubicArcCapacity_smul_le (1/k) (k*A) (k*E)
  rw [hA,hE,abs_div,abs_one] at h
  have hkn : |k| ≠ 0 := abs_ne_zero.mpr hk
  calc
    |k| * cubicArcCapacity A E ≤ |k| * ((1/|k|)*cubicArcCapacity (k*A) (k*E)) :=
      mul_le_mul_of_nonneg_left h (abs_nonneg k)
    _ = cubicArcCapacity (k*A) (k*E) := by field_simp

theorem cubicMonotoneCapacity_nonneg (A B C D E : ℝ) :
    0 ≤ cubicMonotoneCapacity A B C D E := by
  rw [cubicMonotoneCapacity_decomposition,cubicMonotoneCapacity_lost]
  exact (cubicArcCapacity_nonneg A E).trans (le_max_left _ _)

theorem cubicMonotoneCapacity_add_le (A B C D E A' B' C' D' E' : ℝ) :
    cubicMonotoneCapacity (A+A') (B+B') (C+C') (D+D') (E+E') ≤
      cubicMonotoneCapacity A B C D E+cubicMonotoneCapacity A' B' C' D' E' := by
  rw [cubicMonotoneCapacity_physical]
  apply csSup_le (cubicReadoutValues_nonempty (A+A') (B+B') (C+C') (D+D') (E+E'))
  rintro y ⟨g,hg,rfl⟩
  have hv : cubicReadout (A+A') (B+B') (C+C') (D+D') (E+E') g=
      cubicReadout A B C D E g+cubicReadout A' B' C' D' E' g := by
    unfold cubicReadout
    ring
  dsimp only
  rw [hv]
  exact (abs_add_le _ _).trans (add_le_add
    (cubicMonotoneCapacity_bounds A B C D E hg)
    (cubicMonotoneCapacity_bounds A' B' C' D' E' hg))

theorem cubicMonotoneCapacity_smul (k A B C D E : ℝ) :
    cubicMonotoneCapacity (k*A) (k*B) (k*C) (k*D) (k*E)=
      |k| * cubicMonotoneCapacity A B C D E := by
  rw [cubicMonotoneCapacity_formula,cubicMonotoneCapacity_formula]
  unfold cubicNormFormula
  rw [cubicArcCapacity_smul]
  simp only [abs_mul,mul_max_of_nonneg _ _ (abs_nonneg k)]
  congr 2 <;> ring

theorem cubicReadout_section_kernel (A B C D E : ℝ) :
    EqOn (cubicReadout A B C D E) (fun _ => 0) cubicProbeSection ↔
      A=0 ∧ B=0 ∧ C=0 ∧ D=0 ∧ E=0 := by
  constructor
  · intro h
    apply (cubicMonotoneCapacity_zero_iff A B C D E).mp
    apply le_antisymm
    · rw [cubicMonotoneCapacity_physical]
      apply csSup_le (cubicReadoutValues_nonempty A B C D E)
      rintro y ⟨g,hg,rfl⟩
      change |cubicReadout A B C D E g| ≤ 0
      rw [h hg,abs_zero]
    · exact cubicMonotoneCapacity_nonneg A B C D E
  · rintro ⟨rfl,rfl,rfl,rfl,rfl⟩
    intro g _
    simp [cubicReadout]


theorem cubicArcCapacity_attained (A E : ℝ) :
    ∃ t ∈ Icc (0:ℝ) 1, |cubicArcReadout A E t|=cubicArcCapacity A E := by
  have hc : Continuous (fun t => |cubicArcReadout A E t|) := by
    unfold cubicArcReadout
    fun_prop
  obtain ⟨t,ht,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) 1).Nonempty from ⟨0,le_rfl,zero_le_one⟩) hc.continuousOn
  refine ⟨t,ht,le_antisymm (cubicArcCapacity_bounds A E ht) ?_⟩
  apply csSup_le (cubicArcValues_nonempty A E)
  rintro y ⟨u,hu,rfl⟩
  exact hmax hu

theorem cubicMonotoneCapacity_attained (A B C D E : ℝ) :
    ∃ g ∈ cubicProbeSection, |cubicReadout A B C D E g|=cubicMonotoneCapacity A B C D E := by
  let V := (fun g => |cubicReadout A B C D E g|) '' cubicProbeSection
  have hmax : ∀ x y : ℝ, x ∈ V → y ∈ V → max x y ∈ V := by
    intro x y hx hy
    rcases le_total x y with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  have hJ : cubicArcCapacity A E ∈ V := by
    obtain ⟨t,ht,he⟩ := cubicArcCapacity_attained A E
    refine ⟨cubicArcProbe t,cubicArcProbe_section ht,?_⟩
    change |cubicReadout A B C D E (cubicArcProbe t)|=cubicArcCapacity A E
    rwa [cubicArcReadout_probe]
  have hedges : ∀ j : Fin 3, |![4*B/27,4*C/27,D/4] j| ∈ V := by
    intro j
    refine ⟨cubicEdgeWitness j,cubicEdgeWitness_mem j,?_⟩
    exact congrArg abs (congrFun (cubicEdgeWitness_readout A B C D E) j)
  have hB : 4*|B|/27 ∈ V := by simpa [abs_mul,abs_div] using hedges 0
  have hC : 4*|C|/27 ∈ V := by simpa [abs_mul,abs_div] using hedges 1
  have hD : |D|/4 ∈ V := by simpa [abs_div] using hedges 2
  have hcap : cubicMonotoneCapacity A B C D E ∈ V := by
    rw [cubicMonotoneCapacity_formula]
    exact hmax _ _ (hmax _ _ hJ hB) (hmax _ _ hC hD)
  exact hcap

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
