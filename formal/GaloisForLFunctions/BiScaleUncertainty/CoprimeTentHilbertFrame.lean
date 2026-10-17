import GaloisForLFunctions.BiScaleUncertainty.SobolevTraceEnergy
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The Hilbert frame of coprime tent velocities

Disjoint unit cells give normalized tent derivatives at positive multiples of
an integer at least two. Their synthesis is an actual isometry from ℓ² into L².
The adjoint reads centered second differences of the Sobolev primitive.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

abbrev TraceData := lp (fun _ : ℕ => ℝ) 2

def unitCell (k : ℕ) : Velocity :=
  indicatorConstLp 2 (measurableSet_Ioc (a := (k : ℝ)) (b := k+1))
    measure_Ioc_lt_top.ne 1

def prefixCell (n : ℕ) : Velocity :=
  indicatorConstLp 2 (measurableSet_Ioc (a := (0 : ℝ)) (b := n))
    measure_Ioc_lt_top.ne 1

theorem inner_unitCell (i j : ℕ) :
    ⟪unitCell i, unitCell j⟫ = if i = j then 1 else 0 := by
  rw [unitCell, unitCell, L2.real_inner_indicatorConstLp_one_indicatorConstLp_one _ _
    measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne]
  split_ifs with hij
  · subst j
    simp [Measure.real, Real.volume_Ioc]
  · have hd : Ioc (i : ℝ) (i+1) ∩ Ioc (j : ℝ) (j+1) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro t ⟨hi, hj⟩
      rcases lt_or_gt_of_ne hij with h | h
      · have : (i : ℝ)+1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
        linarith [hi.2, hj.1]
      · have : (j : ℝ)+1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
        linarith [hj.2, hi.1]
    simp [hd]

theorem inner_prefixCell (n : ℕ) (q : Velocity) :
    ⟪prefixCell n, q⟫ = primitive q n := by
  rw [prefixCell, L2.inner_indicatorConstLp_one, primitive,
    intervalIntegral.integral_of_le (Nat.cast_nonneg n)]

theorem inner_unitCell_velocity (k : ℕ) (q : Velocity) :
    ⟪unitCell k, q⟫ = primitive q (k+1) - primitive q k := by
  rw [unitCell, L2.inner_indicatorConstLp_one, primitive_sub,
    intervalIntegral.integral_of_le (by linarith : (k : ℝ) ≤ k+1)]

theorem inner_prefixCell_unitCell (n k : ℕ) :
    ⟪prefixCell n, unitCell k⟫ = if k < n then 1 else 0 := by
  rw [prefixCell, unitCell, L2.real_inner_indicatorConstLp_one_indicatorConstLp_one _ _
    measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne]
  split_ifs with h
  · have hkn : (k : ℝ)+1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt h
    have he : Ioc (0 : ℝ) n ∩ Ioc (k : ℝ) (k+1) = Ioc (k : ℝ) (k+1) := by
      apply Set.inter_eq_right.mpr
      intro t ht
      exact ⟨lt_of_le_of_lt (Nat.cast_nonneg k) ht.1, ht.2.trans hkn⟩
    simp [he, Measure.real, Real.volume_Ioc]
  · have hnk : (n : ℝ) ≤ k := by exact_mod_cast Nat.le_of_not_gt h
    have he : Ioc (0 : ℝ) n ∩ Ioc (k : ℝ) (k+1) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro t ⟨hn, hk⟩
      linarith [hn.2, hk.1]
    simp [he]

def coprimeCenter (d j : ℕ) : ℕ := (d+2)*(j+1)

theorem coprimeCenter_ge_two (d j : ℕ) : 2 ≤ coprimeCenter d j := by
  unfold coprimeCenter
  nlinarith

private theorem center_separation (d : ℕ) {i j : ℕ} (h : i < j) :
    coprimeCenter d i + 2 ≤ coprimeCenter d j := by
  unfold coprimeCenter
  nlinarith

theorem coprimeCenter_injective (d : ℕ) : Function.Injective (coprimeCenter d) := by
  intro i j h
  rcases lt_trichotomy i j with hl | he | hg
  · have := center_separation d hl
    omega
  · exact he
  · have := center_separation d hg
    omega

def tentVelocity (d j : ℕ) : Velocity :=
  unitCell (coprimeCenter d j - 1) - unitCell (coprimeCenter d j)

theorem inner_tentVelocity (d i j : ℕ) :
    ⟪tentVelocity d i, tentVelocity d j⟫ = if i = j then 2 else 0 := by
  have hi := coprimeCenter_ge_two d i
  have hj := coprimeCenter_ge_two d j
  simp only [tentVelocity, inner_sub_left, inner_sub_right, inner_unitCell]
  by_cases hij : i = j
  · subst j
    simp [show coprimeCenter d i - 1 ≠ coprimeCenter d i by omega,
      show coprimeCenter d i ≠ coprimeCenter d i - 1 by omega]
    norm_num
  · have hsep : coprimeCenter d i + 2 ≤ coprimeCenter d j ∨
        coprimeCenter d j + 2 ≤ coprimeCenter d i := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact Or.inl (center_separation d h)
      · exact Or.inr (center_separation d h)
    simp [hij, show coprimeCenter d i - 1 ≠ coprimeCenter d j - 1 by omega,
      show coprimeCenter d i - 1 ≠ coprimeCenter d j by omega,
      show coprimeCenter d i ≠ coprimeCenter d j - 1 by omega,
      show coprimeCenter d i ≠ coprimeCenter d j by omega]

theorem inner_prefixCell_tentVelocity (d n j : ℕ) :
    ⟪prefixCell n, tentVelocity d j⟫ = if n = coprimeCenter d j then 1 else 0 := by
  have := coprimeCenter_ge_two d j
  simp only [tentVelocity, inner_sub_right, inner_prefixCell_unitCell]
  split_ifs <;> first | omega | norm_num

def traceCurvature (q : Velocity) (d j : ℕ) : ℝ :=
  2 * primitive q (coprimeCenter d j) - primitive q ((coprimeCenter d j : ℝ)-1) -
    primitive q ((coprimeCenter d j : ℝ)+1)

theorem inner_tentVelocity_velocity (d j : ℕ) (q : Velocity) :
    ⟪tentVelocity d j, q⟫ = traceCurvature q d j := by
  have hn := coprimeCenter_ge_two d j
  have hc : ((coprimeCenter d j - 1 : ℕ) : ℝ) = (coprimeCenter d j : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ coprimeCenter d j)]
    simp
  simp only [tentVelocity, inner_sub_left, inner_unitCell_velocity, hc,
    sub_add_cancel, traceCurvature]
  ring

def normalizedTent (d j : ℕ) : Velocity := (Real.sqrt 2)⁻¹ • tentVelocity d j

theorem orthonormal_normalizedTent (d : ℕ) : Orthonormal ℝ (normalizedTent d) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [normalizedTent, real_inner_smul_left, real_inner_smul_right, inner_tentVelocity]
  split_ifs
  · have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have hp : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    field_simp
    nlinarith
  · simp

/-- Synthesis of the normalized disjoint tent derivatives. -/
def tentSynthesis (d : ℕ) : TraceData →ₗᵢ[ℝ] Velocity :=
  (orthonormal_normalizedTent d).orthogonalFamily.linearIsometry

theorem tentSynthesis_single (d j : ℕ) (a : ℝ) :
    tentSynthesis d (lp.single 2 j a) = a • normalizedTent d j := by
  exact (orthonormal_normalizedTent d).orthogonalFamily.linearIsometry_apply_single a

theorem hasSum_tentSynthesis (d : ℕ) (v : TraceData) :
    HasSum (fun j => v j • normalizedTent d j) (tentSynthesis d v) :=
  (orthonormal_normalizedTent d).orthogonalFamily.hasSum_linearIsometry v

theorem isClosed_range_tentSynthesis (d : ℕ) : IsClosed (Set.range (tentSynthesis d)) :=
  (tentSynthesis d).isometry.isUniformInducing.isComplete_range.isClosed

/-- The adjoint produces actual square-summable coefficient data. -/
def tentAnalysis (d : ℕ) : Velocity →L[ℝ] TraceData :=
  (tentSynthesis d).toContinuousLinearMap.adjoint

theorem tentAnalysis_apply (d j : ℕ) (q : Velocity) :
    tentAnalysis d q j = (Real.sqrt 2)⁻¹ * traceCurvature q d j := by
  have h := (tentSynthesis d).toContinuousLinearMap.adjoint_inner_right
    (lp.single 2 j (1 : ℝ)) q
  change ⟪lp.single 2 j (1 : ℝ), tentAnalysis d q⟫ =
    ⟪tentSynthesis d (lp.single 2 j 1), q⟫ at h
  rw [lp.inner_single_left, tentSynthesis_single, one_smul, normalizedTent,
    real_inner_smul_left, inner_tentVelocity_velocity] at h
  simpa using h

theorem tentAnalysis_tentSynthesis (d : ℕ) (v : TraceData) :
    tentAnalysis d (tentSynthesis d v) = v := by
  exact congrArg (fun A : TraceData →L[ℝ] TraceData => A v)
    (tentSynthesis d).adjoint_comp_self

theorem norm_sq_traceData (v : TraceData) : ‖v‖^2 = ∑' j, (v j)^2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  congr 1
  funext j
  simp [Real.norm_eq_abs, sq_abs]

theorem norm_sq_velocity (q : Velocity) : ‖q‖^2 = ∫ t, (q t)^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext t
  simp [Real.norm_eq_abs, sq_abs]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
