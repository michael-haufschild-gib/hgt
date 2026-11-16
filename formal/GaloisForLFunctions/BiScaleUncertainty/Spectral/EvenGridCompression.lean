import GaloisForLFunctions.BiScaleUncertainty.CoprimeProjectionNeighbors

/-!
# The complete even-grid compression of every arithmetic tent space

Each tent either lies on the even grid or has two even neighbors. Compression
back to its own grid therefore has eigenvalue `1` or `1/2`. Continuity extends
this local calculation to the entire Hilbert space, giving explicit spectral
projections and exact overlap energies.
-/

open scoped RealInnerProductSpace
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
noncomputable section

/-- Compression of the even-grid projection to the grid of spacing `n+3`. -/
def evenGridCompression (n : ℕ) : Velocity →L[ℝ] Velocity :=
  (coprimeProjector (n+1)).comp ((coprimeProjector 0).comp (coprimeProjector (n+1)))

private lemma projector_idem (d : ℕ) (v : Velocity) :
    coprimeProjector d (coprimeProjector d v) = coprimeProjector d v :=
  coprimeProjection_idempotent d v

@[simp] lemma evenGridCompression_project (n : ℕ) (v : Velocity) :
    evenGridCompression n (coprimeProjector (n+1) v) = evenGridCompression n v := by
  simp only [evenGridCompression, ContinuousLinearMap.comp_apply, projector_idem]

@[simp] lemma project_evenGridCompression (n : ℕ) (v : Velocity) :
    coprimeProjector (n+1) (evenGridCompression n v) = evenGridCompression n v := by
  simp only [evenGridCompression, ContinuousLinearMap.comp_apply, projector_idem]

/-- The local cross-Gram calculation has only two possible eigenvalues. -/
theorem evenGridCompression_tent (n j : ℕ) :
    evenGridCompression n (tentVelocity (n+1) j) =
      (if 2 ∣ coprimeCenter (n+1) j then (1:ℝ) else 1/2) • tentVelocity (n+1) j := by
  unfold evenGridCompression
  simp only [ContinuousLinearMap.comp_apply, coprimeProjector_apply, coprimeProjection_tent_self]
  by_cases hd : 2 ∣ coprimeCenter (n+1) j
  · rw [if_pos hd, coprimeProjection_tent_of_dvd 0 (n+1) j hd,
      coprimeProjection_tent_self, one_smul]
  · rw [if_neg hd]
    obtain ⟨i,k,hi,hk⟩ := exists_two_even_neighbors (e := n+1) (by omega) hd
    rw [coprimeProjection_tent_two_neighbors hi hk]
    change coprimeProjector (n+1) ((-1/2:ℝ) • (tentVelocity 0 i + tentVelocity 0 k)) = _
    rw [map_smul, map_add]
    have hli : TentAdjacent (n+1) j 0 i := (TentAdjacent.symm (Or.inl hi))
    have hri : TentAdjacent (n+1) j 0 k := (TentAdjacent.symm (Or.inr hk))
    simp only [coprimeProjector_apply,
      coprimeProjection_tent_one_neighbor (by omega : 1 ≤ n+1) hli,
      coprimeProjection_tent_one_neighbor (by omega : 1 ≤ n+1) hri]
    module

/-- The two-point compression polynomial holds on the full infinite-dimensional space. -/
theorem evenGridCompression_quadratic (n : ℕ) (v : Velocity) :
    evenGridCompression n (evenGridCompression n v) =
      (3/2:ℝ) • evenGridCompression n v - (1/2:ℝ) • coprimeProjector (n+1) v := by
  have h := comp_coprimeProjector_eq (n+1)
    ((evenGridCompression n).comp (evenGridCompression n))
    ((3/2:ℝ) • evenGridCompression n - (1/2:ℝ) • coprimeProjector (n+1)) (by
      intro j
      simp only [ContinuousLinearMap.comp_apply, sub_apply,
        smul_apply, evenGridCompression_tent, map_smul,
        coprimeProjector_apply, coprimeProjection_tent_self]
      split_ifs <;> module)
  have hv := congrArg (fun A : Velocity →L[ℝ] Velocity => A v) h
  simpa only [ContinuousLinearMap.comp_apply, sub_apply,
    smul_apply, evenGridCompression_project, projector_idem] using hv

/-- Projection onto tents whose centers also belong to the even grid. -/
def evenGridCommonPart (n : ℕ) : Velocity →L[ℝ] Velocity :=
  (2:ℝ) • evenGridCompression n - coprimeProjector (n+1)

/-- Projection onto the complementary two-neighbor modes. -/
def evenGridHalfPart (n : ℕ) : Velocity →L[ℝ] Velocity :=
  (2:ℝ) • (coprimeProjector (n+1) - evenGridCompression n)

/-- Every projected velocity splits into common and half-overlap components. -/
theorem evenGrid_parts_sum (n : ℕ) (v : Velocity) :
    evenGridCommonPart n v + evenGridHalfPart n v = coprimeProjector (n+1) v := by
  simp only [evenGridCommonPart, evenGridHalfPart, sub_apply,
    smul_apply]
  module

/-- The common component has unit compression eigenvalue. -/
theorem evenGridCommonPart_eigen (n : ℕ) (v : Velocity) :
    evenGridCompression n (evenGridCommonPart n v) = evenGridCommonPart n v := by
  simp only [evenGridCommonPart, sub_apply, smul_apply,
    map_sub, map_smul, evenGridCompression_project, evenGridCompression_quadratic]
  module

/-- The remaining component has compression eigenvalue exactly one half. -/
theorem evenGridHalfPart_eigen (n : ℕ) (v : Velocity) :
    evenGridCompression n (evenGridHalfPart n v) = (1/2:ℝ) • evenGridHalfPart n v := by
  simp only [evenGridHalfPart, sub_apply, smul_apply,
    map_sub, map_smul, evenGridCompression_project, evenGridCompression_quadratic]
  module

/-- Both spectral components are fixed by their original grid projection. -/
lemma evenGrid_parts_project (n : ℕ) (v : Velocity) :
    coprimeProjector (n+1) (evenGridCommonPart n v) = evenGridCommonPart n v ∧
    coprimeProjector (n+1) (evenGridHalfPart n v) = evenGridHalfPart n v := by
  simp only [evenGridCommonPart, evenGridHalfPart, sub_apply,
    smul_apply, map_sub, map_smul, project_evenGridCompression,
    projector_idem, and_self]

/-- The two explicit spectral maps are idempotent and annihilate one another. -/
theorem evenGrid_parts_projections (n : ℕ) (v : Velocity) :
    evenGridCommonPart n (evenGridCommonPart n v) = evenGridCommonPart n v ∧
    evenGridHalfPart n (evenGridHalfPart n v) = evenGridHalfPart n v ∧
    evenGridCommonPart n (evenGridHalfPart n v) = 0 ∧
    evenGridHalfPart n (evenGridCommonPart n v) = 0 := by
  have hE := (evenGrid_parts_project n v).1
  have hF := (evenGrid_parts_project n v).2
  constructor
  · change (2:ℝ) • evenGridCompression n (evenGridCommonPart n v) -
      coprimeProjector (n+1) (evenGridCommonPart n v) = _
    rw [evenGridCommonPart_eigen, hE]
    module
  constructor
  · change (2:ℝ) • (coprimeProjector (n+1) (evenGridHalfPart n v) -
      evenGridCompression n (evenGridHalfPart n v)) = _
    rw [evenGridHalfPart_eigen, hF]
    module
  constructor
  · change (2:ℝ) • evenGridCompression n (evenGridHalfPart n v) -
      coprimeProjector (n+1) (evenGridHalfPart n v) = _
    rw [evenGridHalfPart_eigen, hF]
    module
  · change (2:ℝ) • (coprimeProjector (n+1) (evenGridCommonPart n v) -
      evenGridCompression n (evenGridCommonPart n v)) = _
    rw [evenGridCommonPart_eigen, hE]
    module

private lemma projector_inner (d : ℕ) (u v : Velocity) :
    ⟪coprimeProjector d u, v⟫ = ⟪u, coprimeProjector d v⟫ := by
  simpa only [coprimeProjector_adjoint] using
    (ContinuousLinearMap.adjoint_inner_left (coprimeProjector d) v u)

/-- The compression is self-adjoint in the actual velocity inner product. -/
lemma evenGridCompression_inner (n : ℕ) (u v : Velocity) :
    ⟪evenGridCompression n u, v⟫ = ⟪u, evenGridCompression n v⟫ := by
  simp only [evenGridCompression, ContinuousLinearMap.comp_apply]
  rw [projector_inner, projector_inner, projector_inner]

/-- The two spectral components are mutually orthogonal, even for distinct inputs. -/
theorem evenGrid_parts_orthogonal (n : ℕ) (u v : Velocity) :
    ⟪evenGridCommonPart n u, evenGridHalfPart n v⟫ = 0 := by
  have h := evenGridCompression_inner n (evenGridCommonPart n u) (evenGridHalfPart n v)
  rw [evenGridCommonPart_eigen, evenGridHalfPart_eigen, real_inner_smul_right] at h
  linarith only [h]

/-- The original projected energy splits without cross terms. -/
theorem evenGrid_parts_energy (n : ℕ) (v : Velocity) :
    ‖coprimeProjector (n+1) v‖^2 =
      ‖evenGridCommonPart n v‖^2 + ‖evenGridHalfPart n v‖^2 := by
  have ho : ⟪evenGridHalfPart n v, evenGridCommonPart n v⟫ = 0 := by
    rw [real_inner_comm]
    exact evenGrid_parts_orthogonal n v v
  rw [← evenGrid_parts_sum n v, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, evenGrid_parts_orthogonal,
    ho,
    real_inner_self_eq_norm_sq, add_zero, zero_add]

/-- Exact overlap energy: common modes transmit fully and the other modes transmit one half. -/
theorem evenGrid_overlap_energy (n : ℕ) (v : Velocity) :
    ‖coprimeProjector 0 (coprimeProjector (n+1) v)‖^2 =
      ‖evenGridCommonPart n v‖^2 + (1/2:ℝ)*‖evenGridHalfPart n v‖^2 := by
  have hp := projector_inner 0 (coprimeProjector (n+1) v)
    (coprimeProjector 0 (coprimeProjector (n+1) v))
  rw [projector_idem, real_inner_self_eq_norm_sq] at hp
  have hq := projector_inner (n+1) (coprimeProjector (n+1) v)
    (coprimeProjector 0 (coprimeProjector (n+1) v))
  rw [projector_idem] at hq
  have hc : evenGridCompression n v =
      evenGridCommonPart n v + (1/2:ℝ) • evenGridHalfPart n v := by
    simp only [evenGridCommonPart, evenGridHalfPart, sub_apply,
      smul_apply]
    module
  have ho : ⟪evenGridHalfPart n v, evenGridCommonPart n v⟫ = 0 := by
    rw [real_inner_comm]
    exact evenGrid_parts_orthogonal n v v
  rw [hp, hq]
  change ⟪coprimeProjector (n+1) v, evenGridCompression n v⟫ = _
  rw [hc, ← evenGrid_parts_sum n v]
  simp only [inner_add_left, inner_add_right, real_inner_smul_right,
    evenGrid_parts_orthogonal,
    ho,
    real_inner_self_eq_norm_sq, mul_zero, add_zero, zero_add]

/-- Uniform overlap bounds on the full projected space, rather than a finite tent block. -/
theorem evenGrid_overlap_bounds (n : ℕ) (v : Velocity) :
    (1/2:ℝ)*‖coprimeProjector (n+1) v‖^2 ≤
        ‖coprimeProjector 0 (coprimeProjector (n+1) v)‖^2 ∧
    ‖coprimeProjector 0 (coprimeProjector (n+1) v)‖^2 ≤
        ‖coprimeProjector (n+1) v‖^2 := by
  rw [evenGrid_overlap_energy, evenGrid_parts_energy]
  constructor <;> nlinarith only [sq_nonneg ‖evenGridCommonPart n v‖,
    sq_nonneg ‖evenGridHalfPart n v‖]

/-- For every odd spacing, the first two tents realize the two distinct spectral components. -/
theorem evenGrid_odd_tent_parts (n : ℕ) :
    evenGridCommonPart (2*n) (tentVelocity (2*n+1) 0) = 0 ∧
    evenGridHalfPart (2*n) (tentVelocity (2*n+1) 0) = tentVelocity (2*n+1) 0 ∧
    evenGridCommonPart (2*n) (tentVelocity (2*n+1) 1) = tentVelocity (2*n+1) 1 ∧
    evenGridHalfPart (2*n) (tentVelocity (2*n+1) 1) = 0 := by
  have h0 : ¬2 ∣ coprimeCenter (2*n+1) 0 := by
    simp only [coprimeCenter]
    omega
  have h1 : 2 ∣ coprimeCenter (2*n+1) 1 := by
    simp only [coprimeCenter]
    omega
  simp only [evenGridCommonPart, evenGridHalfPart, sub_apply, smul_apply,
    evenGridCompression_tent, if_neg h0, if_pos h1, coprimeProjector_apply,
    coprimeProjection_tent_self]
  constructor
  · module
  constructor
  · module
  constructor <;> module

private lemma tent_norm_sq (d j : ℕ) : ‖tentVelocity d j‖^2 = 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_tentVelocity, if_pos rfl]

/-- Both overlap bounds are attained by nonzero tents at every odd spacing. -/
theorem evenGrid_overlap_sharp (n : ℕ) :
    ‖tentVelocity (2*n+1) 0‖^2 = 2 ∧
    ‖coprimeProjector 0 (tentVelocity (2*n+1) 0)‖^2 = 1 ∧
    ‖tentVelocity (2*n+1) 1‖^2 = 2 ∧
    ‖coprimeProjector 0 (tentVelocity (2*n+1) 1)‖^2 = 2 := by
  obtain ⟨hE0,hF0,hE1,hF1⟩ := evenGrid_odd_tent_parts n
  have h0 := evenGrid_overlap_energy (2*n) (tentVelocity (2*n+1) 0)
  have h1 := evenGrid_overlap_energy (2*n) (tentVelocity (2*n+1) 1)
  simp only [coprimeProjector_apply, coprimeProjection_tent_self, hE0, hF0, hE1, hF1,
    tent_norm_sq, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, add_zero] at h0 h1
  exact ⟨tent_norm_sq _ _, by simpa [coprimeProjector_apply] using h0, tent_norm_sq _ _, h1⟩

#print axioms evenGridCompression_quadratic
#print axioms evenGrid_parts_projections
#print axioms evenGrid_parts_orthogonal
#print axioms evenGrid_overlap_energy
#print axioms evenGrid_overlap_bounds
#print axioms evenGrid_overlap_sharp
end
end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
