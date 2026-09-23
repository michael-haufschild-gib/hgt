import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicArcNorm

/-!
# Exact five-generator cubic monotone norm

The actual pairing capacity is the maximum of the curved A,E norm and three
sharp one-dimensional factors. Explicit physical probes attain all three edge
constants. The resulting unit-ball factorization and contractive projection
identify exactly which metric information is erased by the ring retraction.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set


def cubicNormFormula (A B C D E : ℝ) : ℝ :=
  max (max (cubicArcCapacity A E) (4*|B|/27)) (max (4*|C|/27) (|D|/4))

theorem cubicEdge_sharp_bound (B x y : ℝ) :
    |B*x*y^(2 : ℕ)| ≤ (4*|B|/27)*(|x|+|y|)^(3 : ℕ) := by
  have h := mul_nonneg (sq_nonneg (|x|-|y|/2))
    (show 0 ≤ |x|+4*|y| by positivity)
  rw [← separated_cubic_gap] at h
  have hh := mul_nonneg (abs_nonneg B) h
  simp only [abs_mul,abs_pow]
  nlinarith only [hh]

theorem cubicEdge_quadratic_bound (D x y : ℝ) :
    |D*x*y| ≤ (|D|/4)*(|x|+|y|)^(2 : ℕ) := by
  have h := mul_nonneg (abs_nonneg D) (sq_nonneg (|x|-|y|))
  simp only [abs_mul]
  nlinarith only [h]

def cubicEdgeWitness : Fin 3 → Fin 5 → ℝ :=
  ![![1/3,0,0,2/3,0],![0,2/3,0,0,1/3],![0,1/2,0,1/2,0]]

theorem cubicEdgeWitness_mem (j : Fin 3) : cubicEdgeWitness j ∈ cubicProbeSection := by
  fin_cases j
  all_goals refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | (intro q; fin_cases q <;> simp [cubicEdgeWitness] <;> positivity)
    | (simp [cubicEdgeWitness] <;> ring)

theorem cubicEdgeWitness_readout (A B C D E : ℝ) :
    (fun j => cubicReadout A B C D E (cubicEdgeWitness j))=![4*B/27,4*C/27,D/4] := by
  funext j
  fin_cases j <;> simp [cubicReadout,cubicEdgeWitness] <;> ring

theorem cubicNormFormula_bounds (A B C D E : ℝ) :
    MapsTo (fun g => |cubicReadout A B C D E g|) cubicProbeSection
      (Iic (cubicNormFormula A B C D E)) := by
  intro g hg
  have hlost := cubicArcCapacity_lost_bound A E hg
  rcases hg with ⟨hnn,hsum,h01,h12,h23,h34⟩
  change |cubicReadout A B C D E g| ≤ cubicNormFormula A B C D E
  have hJ : cubicArcCapacity A E ≤ cubicNormFormula A B C D E :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hB : 4*|B|/27 ≤ cubicNormFormula A B C D E :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hC : 4*|C|/27 ≤ cubicNormFormula A B C D E :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hD : |D|/4 ≤ cubicNormFormula A B C D E :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hfaces : (g 1=0 ∧ g 3=0) ∨ (g 1=0 ∧ g 2=0 ∧ g 4=0) ∨
      (g 0=0 ∧ g 2=0 ∧ g 4=0) ∨ (g 0=0 ∧ g 2=0 ∧ g 3=0) := by
    have h01' := mul_eq_zero.mp h01
    have h12' := mul_eq_zero.mp h12
    have h23' := mul_eq_zero.mp h23
    have h34' := mul_eq_zero.mp h34
    tauto
  rcases hfaces with ⟨hb,hd⟩ | ⟨hb,hc,he⟩ | ⟨ha,hc,he⟩ | ⟨ha,hc,hd⟩
  · have hv : cubicReadout A B C D E g=cubicReadout A 0 0 0 E g := by
      simp [cubicReadout,hb,hd]
    rw [hv]
    exact hlost.trans hJ
  · have hs : g 0+g 3=1 := by simpa [hb,hc,he] using hsum
    have hh := cubicEdge_sharp_bound B (g 0) (g 3)
    rw [abs_of_nonneg (hnn 0),abs_of_nonneg (hnn 3),hs,one_pow,mul_one] at hh
    have hv : cubicReadout A B C D E g=B*g 0*(g 3)^(2 : ℕ) := by
      simp [cubicReadout,hb,hc,he]
      ring
    rw [hv]
    exact hh.trans hB
  · have hs : g 1+g 3=1 := by simpa [ha,hc,he] using hsum
    have hh := cubicEdge_quadratic_bound D (g 1) (g 3)
    rw [abs_of_nonneg (hnn 1),abs_of_nonneg (hnn 3),hs,one_pow,mul_one] at hh
    have hv : cubicReadout A B C D E g=D*g 1*g 3 := by
      unfold cubicReadout
      rw [hsum]
      simp [ha,hc,he]
    rw [hv]
    exact hh.trans hD
  · have hs : g 4+g 1=1 := by
      have hs' : g 1+g 4=1 := by simpa [ha,hc,hd] using hsum
      linarith
    have hh := cubicEdge_sharp_bound C (g 4) (g 1)
    rw [abs_of_nonneg (hnn 4),abs_of_nonneg (hnn 1),hs,one_pow,mul_one] at hh
    have hv : cubicReadout A B C D E g=C*g 4*(g 1)^(2 : ℕ) := by
      simp [cubicReadout,ha,hc,hd]
      ring
    rw [hv]
    exact hh.trans hC

theorem cubicMonotoneCapacity_formula (A B C D E : ℝ) :
    cubicMonotoneCapacity A B C D E=cubicNormFormula A B C D E := by
  apply le_antisymm
  · rw [cubicMonotoneCapacity_physical]
    apply csSup_le (cubicReadoutValues_nonempty A B C D E)
    rintro y ⟨g,hg,rfl⟩
    exact cubicNormFormula_bounds A B C D E hg
  · have hJ : cubicArcCapacity A E ≤ cubicMonotoneCapacity A B C D E := by
      apply csSup_le (cubicArcValues_nonempty A E)
      rintro y ⟨t,ht,rfl⟩
      have h := cubicMonotoneCapacity_bounds A B C D E (cubicArcProbe_section ht)
      change |cubicReadout A B C D E (cubicArcProbe t)| ≤ _ at h
      rwa [cubicArcReadout_probe] at h
    have hedges : ∀ j : Fin 3, |![4*B/27,4*C/27,D/4] j| ≤
        cubicMonotoneCapacity A B C D E := by
      intro j
      have h := cubicMonotoneCapacity_bounds A B C D E (cubicEdgeWitness_mem j)
      change |cubicReadout A B C D E (cubicEdgeWitness j)| ≤ _ at h
      rw [congrFun (cubicEdgeWitness_readout A B C D E) j] at h
      exact h
    unfold cubicNormFormula
    apply max_le
    · apply max_le hJ
      simpa [abs_mul,abs_div] using hedges 0
    · apply max_le
      · simpa [abs_mul,abs_div] using hedges 1
      · simpa [abs_div] using hedges 2


theorem cubicMonotoneCapacity_lost (A E : ℝ) :
    cubicMonotoneCapacity A 0 0 0 E=cubicArcCapacity A E := by
  rw [cubicMonotoneCapacity_formula]
  simp [cubicNormFormula,max_eq_left (cubicArcCapacity_nonneg A E)]

theorem cubicMonotoneCapacity_retained (B C D : ℝ) :
    cubicMonotoneCapacity 0 B C D 0=max (4*|B|/27) (max (4*|C|/27) (|D|/4)) := by
  rw [cubicMonotoneCapacity_formula]
  simp [cubicNormFormula,cubicArcCapacity_zero,
    max_eq_right (show (0:ℝ) ≤ 4*|B|/27 by positivity)]

theorem cubicMonotoneCapacity_decomposition (A B C D E : ℝ) :
    cubicMonotoneCapacity A B C D E=
      max (cubicMonotoneCapacity A 0 0 0 E) (cubicMonotoneCapacity 0 B C D 0) := by
  rw [cubicMonotoneCapacity_formula,cubicMonotoneCapacity_lost,cubicMonotoneCapacity_retained]
  exact max_assoc _ _ _

theorem cubicMonotoneCapacity_projection (A B C D E : ℝ) :
    cubicMonotoneCapacity 0 B C D 0 ≤ cubicMonotoneCapacity A B C D E := by
  rw [cubicMonotoneCapacity_decomposition A B C D E]
  exact le_max_right _ _

theorem cubicMonotoneCapacity_zero_iff (A B C D E : ℝ) :
    cubicMonotoneCapacity A B C D E=0 ↔ A=0 ∧ B=0 ∧ C=0 ∧ D=0 ∧ E=0 := by
  constructor
  · intro h
    rw [cubicMonotoneCapacity_formula] at h
    have hh : max (max (cubicArcCapacity A E) (4*|B|/27))
        (max (4*|C|/27) (|D|/4)) ≤ 0 := h.le
    rcases max_le_iff.mp hh with ⟨hjB,hCD⟩
    rcases max_le_iff.mp hjB with ⟨hj,hB⟩
    rcases max_le_iff.mp hCD with ⟨hC,hD⟩
    rcases (cubicArcCapacity_zero_iff A E).mp
      (le_antisymm hj (cubicArcCapacity_nonneg A E)) with ⟨hA,hE⟩
    exact ⟨hA,abs_eq_zero.mp (by linarith [abs_nonneg B]),
      abs_eq_zero.mp (by linarith [abs_nonneg C]),
      abs_eq_zero.mp (by linarith [abs_nonneg D]),hE⟩
  · rintro ⟨rfl,rfl,rfl,rfl,rfl⟩
    rw [cubicMonotoneCapacity_lost,cubicArcCapacity_zero]

theorem cubicMonotoneCapacity_unitBall :
    {c : Fin 5 → ℝ | cubicMonotoneCapacity (c 0) (c 1) (c 2) (c 3) (c 4) ≤ 1}=
    {c | cubicArcCapacity (c 0) (c 4) ≤ 1 ∧ |c 1| ≤ 27/4 ∧
      |c 2| ≤ 27/4 ∧ |c 3| ≤ 4} := by
  ext c
  change cubicMonotoneCapacity (c 0) (c 1) (c 2) (c 3) (c 4) ≤ 1 ↔ _
  rw [cubicMonotoneCapacity_formula]
  simp only [cubicNormFormula,max_le_iff,Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hJ,hB⟩,hC,hD⟩
    exact ⟨hJ,by linarith,by linarith,by linarith⟩
  · rintro ⟨hJ,hB,hC,hD⟩
    exact ⟨⟨hJ,by linarith⟩,by linarith,by linarith⟩

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
