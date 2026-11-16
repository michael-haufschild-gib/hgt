import GaloisForLFunctions.BiScaleUncertainty.Spectral.EvenGridCompression
import GaloisForLFunctions.BiScaleUncertainty.Spectral.TwoArmTentUncertainty
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# The full uncertainty spectra against the even arithmetic grid

The two-point compression law forces a degree-five polynomial identity for
`2-P-Q`. Self-adjointness removes the repeated factors in the algebraic
annihilator. Explicit tent modes and the unused first cell realize its roots.
Odd spacings have five levels, proper even subgrids have three, and the
identical grid has only the two endpoint levels.
-/

open scoped RealInnerProductSpace Polynomial
open Polynomial
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
noncomputable section

private lemma first_cell_ne_zero : unitCell 0 ≠ 0 := by
  intro hz
  have h := inner_unitCell 0 0
  rw [hz,inner_zero_left] at h
  norm_num at h

local instance : Nontrivial (Velocity →L[ℝ] Velocity) :=
  ⟨⟨1,0,fun h => first_cell_ne_zero (congrArg (fun T : Velocity →L[ℝ] Velocity => T (unitCell 0)) h)⟩⟩

/-- The centered sum of the two interpolation projections. -/
def centeredEvenGridSum (n : ℕ) : Velocity →L[ℝ] Velocity :=
  coprimeProjector 0 + coprimeProjector (n+1) - 1

/-- The complete compression polynomial forces a square-free degree-five operator identity. -/
theorem centeredEvenGridSum_annihilator (n : ℕ) :
    centeredEvenGridSum n * (centeredEvenGridSum n ^ 2 - 1) *
      (centeredEvenGridSum n ^ 2 + centeredEvenGridSum n ^ 2 - 1) = 0 := by
  let P := coprimeProjector 0
  let Q := coprimeProjector (n+1)
  let A := P+Q-1
  let C := A*A
  let S := Q*P*Q
  let Y := (C-1)*(C+C-1)
  have hP : P*P=P := by
    apply ContinuousLinearMap.ext
    intro v
    exact coprimeProjection_idempotent 0 v
  have hQ : Q*Q=Q := by
    apply ContinuousLinearMap.ext
    intro v
    exact coprimeProjection_idempotent (n+1) v
  have hPP (T : Velocity →L[ℝ] Velocity) : P*(P*T)=P*T := by rw [← mul_assoc, hP]
  have hQQ (T : Velocity →L[ℝ] Velocity) : Q*(Q*T)=Q*T := by rw [← mul_assoc, hQ]
  have hS : S*S+S*S-S-S-S+Q=0 := by
    apply ContinuousLinearMap.ext
    intro v
    change evenGridCompression n (evenGridCompression n v) +
      evenGridCompression n (evenGridCompression n v) - evenGridCompression n v -
      evenGridCompression n v - evenGridCompression n v + coprimeProjector (n+1) v = 0
    rw [evenGridCompression_quadratic]
    module
  have hC : C = 1-P-Q+P*Q+Q*P := by
    calc
      C = P*P+Q*Q+1+P*Q+Q*P-P-P-Q-Q := by dsimp [C,A]; noncomm_ring
      _ = _ := by rw [hP,hQ]; abel
  have hCP : C*P=P*C := by
    rw [hC]
    simp only [add_mul, sub_mul, mul_add, mul_sub, one_mul, mul_one, mul_assoc, hP, hPP]
    abel
  have hQC : Q*C=S := by
    rw [hC]
    simp only [mul_add, mul_sub, mul_one, mul_assoc, hQ, hQQ, S]
    abel
  have hSQ : S*Q=S := by simp only [S,mul_assoc,hQ]
  have hQC2 : Q*(C*C)=S*S := by
    calc
      Q*(C*C) = (Q*C)*C := (mul_assoc _ _ _).symm
      _ = S*C := by rw [hQC]
      _ = (S*Q)*C := by rw [hSQ]
      _ = S*(Q*C) := mul_assoc _ _ _
      _ = S*S := by rw [hQC]
  have hQY : Q*Y=0 := by
    have he : Q*Y = Q*(C*C)+Q*(C*C)-Q*C-Q*C-Q*C+Q := by
      dsimp [Y]
      noncomm_ring
    rw [he,hQC2,hQC]
    exact hS
  have hPY : P*Y=Y*P := by
    have hc : Commute P C := hCP.symm
    exact (hc.sub_right (Commute.one_right P)).mul_right
      ((hc.add_right hc).sub_right (Commute.one_right P))
  have hCY : C*Y=Y-P*Y := by
    rw [hC]
    simp only [add_mul, sub_mul, one_mul, mul_assoc, hQY, mul_zero, sub_zero, add_zero]
    rw [hPY, ← mul_assoc, hQY, zero_mul, add_zero]
  have hCPY : C*(P*Y)=0 := by
    rw [← mul_assoc, hCP, mul_assoc, hCY, mul_sub, hPP, sub_self]
  have hCYann : C*(C-1)*Y=0 := by
    calc
      C*(C-1)*Y = C*(C*Y-Y) := by noncomm_ring
      _ = - (C*(P*Y)) := by rw [hCY]; noncomm_ring
      _ = 0 := by rw [hCPY, neg_zero]
  have hg2 : (A*Y)*(A*Y)=0 := by
    calc
      (A*Y)*(A*Y) = C*(C-1)*Y*(C+C-1) := by dsimp [Y,C]; noncomm_ring
      _ = 0 := by rw [hCYann,zero_mul]
  have hPA : star P=P := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact coprimeProjector_adjoint 0
  have hQA : star Q=Q := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact coprimeProjector_adjoint (n+1)
  have hAA : star A=A := by simp only [A, star_sub, star_add, star_one, hPA,hQA]
  have hgstar : star (A*Y)=A*Y := by
    simp only [Y,C,star_mul,star_sub,star_add,star_one,hAA]
    noncomm_ring
  have hg : A*Y=0 := by
    have hn : ‖A*Y‖*‖A*Y‖=0 := by
      rw [← CStarRing.norm_star_mul_self, hgstar, hg2, norm_zero]
    simpa using hn
  change A*(A^2-1)*(A^2+A^2-1)=0
  simpa only [Y,C,pow_two,mul_assoc] using hg

/-- An explicit scalar polynomial annihilating the uncertainty operator. -/
def evenGridUncertaintyPolynomial : ℝ[X] :=
  X*(X-1)*(X-2)*((X-1)^2+(X-1)^2-1)

/-- The full operator, without a restriction to finitely many tents, satisfies the polynomial. -/
theorem coprimeUncertainty_evenGrid_annihilator (n : ℕ) :
    aeval (coprimeUncertainty 0 (n+1)) evenGridUncertaintyPolynomial = 0 := by
  let A := centeredEvenGridSum n
  have hu : coprimeUncertainty 0 (n+1) = 1-A := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [coprimeUncertainty, centeredEvenGridSum, A, sub_apply, add_apply,
      smul_apply, ContinuousLinearMap.id_apply, one_apply_eq_self]
    module
  have h := centeredEvenGridSum_annihilator n
  change A*(A^2-1)*(A^2+A^2-1)=0 at h
  simp only [evenGridUncertaintyPolynomial, map_mul, map_sub, map_add, map_pow,
    map_one, map_ofNat, aeval_X]
  rw [hu]
  calc
    _ = -(A*(A^2-1)*(A^2+A^2-1)) := by noncomm_ring
    _ = 0 := by rw [h,neg_zero]

/-- There are no spectral values beyond the five roots forced by the overlap geometry. -/
theorem coprimeUncertainty_evenGrid_spectrum_subset (n : ℕ) :
    spectrum ℝ (coprimeUncertainty 0 (n+1)) ⊆
      {0,1,2,1-Real.sqrt 2/2,1+Real.sqrt 2/2} := by
  intro r hr
  have h := spectrum.subset_polynomial_aeval (coprimeUncertainty 0 (n+1))
    evenGridUncertaintyPolynomial ⟨r,hr,rfl⟩
  rw [coprimeUncertainty_evenGrid_annihilator, spectrum.zero_eq, Set.mem_singleton_iff] at h
  have hz : r*(r-1)*(r-2)*((r-1)^2+(r-1)^2-1)=0 := by
    simpa [evenGridUncertaintyPolynomial] using h
  simp only [mul_eq_zero, sub_eq_zero] at hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hz with ((h|h)|h)|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have he : (r-1)^2 = (Real.sqrt 2/2)^2 := by nlinarith only [h,hs]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with he|he
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by linarith only [he]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith only [he]))))

private lemma eigen_mem_spectrum (T : Velocity →L[ℝ] Velocity) (r : ℝ) (v : Velocity)
    (hv : v ≠ 0) (he : T v=r • v) : r ∈ spectrum ℝ T := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact (Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr he,hv⟩)).mem_spectrum

private lemma tent_ne_zero (d j : ℕ) : tentVelocity d j ≠ 0 := by
  intro hz
  have h := inner_tentVelocity d j j
  rw [hz,inner_zero_left] at h
  norm_num at h

/-- The first unit cell is invisible to every arithmetic interpolation grid. -/
theorem coprimeProjector_first_cell_zero (d : ℕ) : coprimeProjector d (unitCell 0)=0 := by
  have ht : tentAnalysis d (unitCell 0)=0 := by
    apply lp.ext
    funext j
    change tentAnalysis d (unitCell 0) j=0
    have hc := coprimeCenter_ge_two d j
    simp only [tentAnalysis_apply, ← inner_tentVelocity_velocity, tentVelocity,
      inner_sub_left, inner_unitCell,
      if_neg (show coprimeCenter d j-1 ≠ 0 by omega),
      if_neg (show coprimeCenter d j ≠ 0 by omega),sub_self,mul_zero]
  change tentSynthesis d (tentAnalysis d (unitCell 0))=0
  rw [ht,map_zero]

/-- The full uncertainty spectrum at every odd spacing consists of exactly five values. -/
theorem coprimeUncertainty_even_odd_spectrum (n : ℕ) :
    spectrum ℝ (coprimeUncertainty 0 (2*n+1)) =
      {0,1,2,1-Real.sqrt 2/2,1+Real.sqrt 2/2} := by
  apply Set.Subset.antisymm (coprimeUncertainty_evenGrid_spectrum_subset (2*n))
  intro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl
  · apply eigen_mem_spectrum _ _ (tentVelocity (2*n+1) 1) (tent_ne_zero _ _)
    have hd : 2 ∣ coprimeCenter (2*n+1) 1 := by
      simp only [coprimeCenter]
      omega
    simp only [coprimeUncertainty, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      coprimeProjector_apply, coprimeProjection_tent_self,
      coprimeProjection_tent_of_dvd 0 (2*n+1) 1 hd]
    module
  · apply eigen_mem_spectrum _ _ (twoArmTent n 1 (-1) 0) (twoArmTent_modes_nonzero n).1
    simpa only [one_smul] using twoArmTent_middle_eigen n
  · apply eigen_mem_spectrum _ _ (unitCell 0)
    · intro hz
      have h := inner_unitCell 0 0
      rw [hz,inner_zero_left] at h
      norm_num at h
    · simp only [coprimeUncertainty, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
        coprimeProjector_first_cell_zero, sub_zero]
  · exact eigen_mem_spectrum _ _ _ (twoArmTent_modes_nonzero n).2.1 (twoArmTent_lower_eigen n)
  · exact eigen_mem_spectrum _ _ _ (twoArmTent_modes_nonzero n).2.2 (twoArmTent_upper_eigen n)

private lemma even_grid_nested (n : ℕ) :
    coprimeProjector 0 * coprimeProjector (2*n+2) = coprimeProjector (2*n+2) ∧
    coprimeProjector (2*n+2) * coprimeProjector 0 = coprimeProjector (2*n+2) := by
  have h := comp_coprimeProjector_eq (2*n+2) (coprimeProjector 0) 1 (by
    intro j
    change coprimeProjection 0 (tentVelocity (2*n+2) j)=tentVelocity (2*n+2) j
    apply coprimeProjection_tent_of_dvd
    refine ⟨(n+2)*(j+1),?_⟩
    simp only [coprimeCenter]
    ring)
  have hpq : coprimeProjector 0 * coprimeProjector (2*n+2) = coprimeProjector (2*n+2) := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun T : Velocity →L[ℝ] Velocity => T v) h
  refine ⟨hpq,?_⟩
  have hs := congrArg star hpq
  simpa only [star_mul, ContinuousLinearMap.star_eq_adjoint, coprimeProjector_adjoint] using hs

/-- Nested even grids reduce the full uncertainty polynomial to degree three. -/
theorem coprimeUncertainty_even_even_annihilator (n : ℕ) :
    aeval (coprimeUncertainty 0 (2*n+2)) (X*(X-1)*(X-2) : ℝ[X]) = 0 := by
  let P := coprimeProjector 0
  let Q := coprimeProjector (2*n+2)
  let A := P+Q-1
  have hP : P*P=P := by
    apply ContinuousLinearMap.ext
    intro v
    exact coprimeProjection_idempotent 0 v
  have hQ : Q*Q=Q := by
    apply ContinuousLinearMap.ext
    intro v
    exact coprimeProjection_idempotent (2*n+2) v
  obtain ⟨hPQ,hQP⟩ := even_grid_nested n
  change P*Q=Q at hPQ
  change Q*P=Q at hQP
  have hA2 : A*A-1 = -P+Q := by
    calc
      _ = P*P+Q*Q+P*Q+Q*P-P-P-Q-Q := by dsimp [A]; noncomm_ring
      _ = _ := by rw [hP,hQ,hPQ,hQP]; abel
  have ha : A*(A*A-1)=0 := by
    rw [hA2]
    simp only [A, add_mul, sub_mul, mul_add, mul_neg, one_mul, hP,hQ,hPQ,hQP]
    abel
  have hu : coprimeUncertainty 0 (2*n+2)=1-A := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [coprimeUncertainty,A,P,Q,sub_apply,add_apply,smul_apply,
      ContinuousLinearMap.id_apply,one_apply_eq_self]
    module
  simp only [map_mul,map_sub,map_one,map_ofNat,aeval_X]
  rw [hu]
  calc
    _ = -(A*(A*A-1)) := by noncomm_ring
    _ = 0 := by rw [ha,neg_zero]

/-- Every proper even subgrid has exactly the three integer uncertainty levels. -/
theorem coprimeUncertainty_even_even_spectrum (n : ℕ) :
    spectrum ℝ (coprimeUncertainty 0 (2*n+2)) = {0,1,2} := by
  apply Set.Subset.antisymm
  · intro r hr
    have h := spectrum.subset_polynomial_aeval (coprimeUncertainty 0 (2*n+2))
      (X*(X-1)*(X-2) : ℝ[X]) ⟨r,hr,rfl⟩
    rw [coprimeUncertainty_even_even_annihilator,spectrum.zero_eq,Set.mem_singleton_iff] at h
    have hz : r*(r-1)*(r-2)=0 := by simpa using h
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,mul_eq_zero,sub_eq_zero,or_assoc] using hz
  · intro r hr
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hr
    rcases hr with rfl|rfl|rfl
    · apply eigen_mem_spectrum _ _ (tentVelocity (2*n+2) 0) (tent_ne_zero _ _)
      have hd : 2 ∣ coprimeCenter (2*n+2) 0 := by
        refine ⟨n+2,?_⟩
        simp only [coprimeCenter]
        ring
      simp only [coprimeUncertainty,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
        coprimeProjector_apply,coprimeProjection_tent_self,
        coprimeProjection_tent_of_dvd 0 (2*n+2) 0 hd]
      module
    · apply eigen_mem_spectrum _ _ (tentVelocity 0 0) (tent_ne_zero _ _)
      have hd : 2 ∣ (2*n+2)+2 := by omega
      have he : 2 ∣ 0+2 := by decide
      have hz := coprimeProjection_tent_of_common_divisor (2*n+2) 0 0 2 (by omega) hd he
      have hnd : ¬(2*n+2)+2 ∣ coprimeCenter 0 0 := by
        intro hh
        have hl := Nat.le_of_dvd (by norm_num [coprimeCenter] : 0 < coprimeCenter 0 0) hh
        simp only [coprimeCenter] at hl
        omega
      rw [if_neg hnd] at hz
      simp only [coprimeUncertainty,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
        coprimeProjector_apply,coprimeProjection_tent_self,hz]
      module
    · apply eigen_mem_spectrum _ _ (unitCell 0)
      · intro hz
        have h := inner_unitCell 0 0
        rw [hz,inner_zero_left] at h
        norm_num at h
      · simp only [coprimeUncertainty,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
          coprimeProjector_first_cell_zero,sub_zero]

/-- Identical even grids retain only the common and invisible uncertainty levels. -/
theorem coprimeUncertainty_same_grid_spectrum :
    spectrum ℝ (coprimeUncertainty 0 0) = {0,2} := by
  have ha : aeval (coprimeUncertainty 0 0) (X*(X-2) : ℝ[X])=0 := by
    have hP : coprimeProjector 0 * coprimeProjector 0 = coprimeProjector 0 := by
      apply ContinuousLinearMap.ext
      intro v
      exact coprimeProjection_idempotent 0 v
    have hu : coprimeUncertainty 0 0 = 1+1-coprimeProjector 0-coprimeProjector 0 := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [coprimeUncertainty,sub_apply,add_apply,smul_apply,
        ContinuousLinearMap.id_apply,one_apply_eq_self]
      module
    simp only [map_mul,map_sub,map_ofNat,aeval_X]
    rw [hu]
    calc
      _ = (coprimeProjector 0*coprimeProjector 0-coprimeProjector 0) +
          (coprimeProjector 0*coprimeProjector 0-coprimeProjector 0) +
          (coprimeProjector 0*coprimeProjector 0-coprimeProjector 0) +
          (coprimeProjector 0*coprimeProjector 0-coprimeProjector 0) := by noncomm_ring
      _ = 0 := by rw [hP]; simp only [sub_self,add_zero]
  apply Set.Subset.antisymm
  · intro r hr
    have h := spectrum.subset_polynomial_aeval (coprimeUncertainty 0 0)
      (X*(X-2) : ℝ[X]) ⟨r,hr,rfl⟩
    rw [ha,spectrum.zero_eq,Set.mem_singleton_iff] at h
    have hz : r*(r-2)=0 := by simpa using h
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,mul_eq_zero,sub_eq_zero] using hz
  · intro r hr
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hr
    rcases hr with rfl|rfl
    · apply eigen_mem_spectrum _ _ (tentVelocity 0 0) (tent_ne_zero _ _)
      simp only [coprimeUncertainty,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
        coprimeProjector_apply,coprimeProjection_tent_self]
      module
    · apply eigen_mem_spectrum _ _ (unitCell 0)
      · intro hz
        have h := inner_unitCell 0 0
        rw [hz,inner_zero_left] at h
        norm_num at h
      · simp only [coprimeUncertainty,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
          coprimeProjector_first_cell_zero,sub_zero]

#print axioms centeredEvenGridSum_annihilator
#print axioms coprimeUncertainty_evenGrid_annihilator
#print axioms coprimeUncertainty_evenGrid_spectrum_subset
#print axioms coprimeUncertainty_even_odd_spectrum
#print axioms coprimeUncertainty_even_even_spectrum
#print axioms coprimeUncertainty_same_grid_spectrum
end
end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
