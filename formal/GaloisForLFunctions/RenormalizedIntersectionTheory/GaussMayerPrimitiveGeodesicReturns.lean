import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerRealEigenbasis
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerGeodesicFlow
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerHyperbolicLength

/-! Actual primitive Gauss matrices produce periodic modular geodesics whose
least positive return is their displacement-defined translation length. -/

open Matrix
open scoped MatrixGroups UpperHalfPlane
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerGeodesicFlow MayerRealEigenbasis
open MayerHyperbolic MayerGaussCoding MayerPairMultiplier MayerCycleIndex MayerPrimitiveCycles
open MayerHyperbolicLength MayerOrbitWords
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPrimitiveGeodesicReturns

/-- The actual pair-word matrix as an integral determinant-one frame. -/
def pairReturn (ps : List (ℕ × ℕ)) : IntegralFrame :=
  ⟨actualPairedMatrix ps,actualPairedMatrix_det ps⟩

/-- The integral return matrix of the chosen primitive-cycle representative. -/
def cycleReturn (c : Orbit) : IntegralFrame := pairReturn (representative c).val

theorem integralMap_pairReturn (ps : List (ℕ × ℕ)) : integralMap (pairReturn ps)=pairElement ps := rfl

private theorem diagonalElement_eq_flow {l : ℝ} (hl : 0 < l) :
    diagonalElement l l⁻¹ (mul_inv_cancel₀ hl.ne')=diagonalFlow (2*Real.log l) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · change l=Real.exp ((2*Real.log l)/2)
    rw [show (2*Real.log l)/2=Real.log l by ring,Real.exp_log hl]
  · rfl
  · rfl
  · change l⁻¹=Real.exp (-(2*Real.log l)/2)
    rw [show -(2*Real.log l)/2= -Real.log l by ring,Real.exp_neg,Real.exp_log hl]

/-- Every actual nonempty pair word has a real frame with its prescribed geometric return. -/
theorem exists_pair_return_frame (ps : List (ℕ × ℕ)) (hps : ps ≠ []) :
    ∃ C : Frame, integralMap (pairReturn ps)*C=C*diagonalFlow (2*Real.log (pairMultiplier ps)) := by
  have hl := pairMultiplier_gt_one ps hps
  have hc : pairElement ps 1 0 ≠ 0 := by
    have h := lowerLeft_ne_zero (actualPairedMatrix ps)
      (by simpa only [Matrix.det_fin_two] using actualPairedMatrix_det ps)
      (actualPairedMatrix_trace_gt_two ps hps)
    change (actualPairedMatrix ps 1 0 : ℝ) ≠ 0
    exact_mod_cast h
  have hr : (pairMultiplier ps)^2-(pairElement ps 0 0+pairElement ps 1 1)*pairMultiplier ps+1=0 := by
    have h := (expandingMultiplier_spec (actualPairedMatrix_trace_gt_two ps hps)).2
    simpa only [pairElement,pairMultiplier,Int.cast_add] using h
  obtain ⟨C,hC⟩ := exists_expanding_eigenbasis (pairElement ps) (pairMultiplier ps) hl hc hr
  refine ⟨C,?_⟩
  rw [integralMap_pairReturn]
  rw [diagonalElement_eq_flow (zero_lt_one.trans hl)] at hC
  exact hC

/-- Symbolic pair primitivity excludes every proper integral matrix root. -/
theorem cycleReturn_primitive (c : Orbit) (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∃ B : IntegralFrame, B^n=cycleReturn c := by
  rintro ⟨B,hB⟩
  have hb := congrArg (fun A : IntegralFrame => (A : Matrix (Fin 2) (Fin 2) ℤ)) hB
  change (B : Matrix (Fin 2) (Fin 2) ℤ)^n=actualPairedMatrix (representative c).val at hb
  obtain ⟨qs,hqs⟩ := (actualPairedMatrix_root_iff (representative c).val
    (representative c).property.1 n).mp ⟨B,B.property,hb⟩
  exact (representative c).property.2 qs n (by omega) hqs

private theorem return_nat_pow (C : Frame) (γ : IntegralFrame) (T : ℝ)
    (hγ : integralMap γ*C=C*diagonalFlow T) (n : ℕ) :
    integralMap (γ^n)*C=C*diagonalFlow ((n : ℝ)*T) := by
  induction n with
  | zero => simp only [pow_zero,map_one,one_mul,Nat.cast_zero,zero_mul,diagonalFlow_zero,mul_one]
  | succ n ih =>
    rw [Nat.cast_succ,add_mul,one_mul,diagonalFlow_add,pow_succ,map_mul]
    calc
      (integralMap (γ^n)*integralMap γ)*C=integralMap (γ^n)*(integralMap γ*C) := mul_assoc _ _ _
      _ = integralMap (γ^n)*(C*diagonalFlow T) := by rw [hγ]
      _ = (integralMap (γ^n)*C)*diagonalFlow T := (mul_assoc _ _ _).symm
      _ = (C*diagonalFlow ((n : ℝ)*T))*diagonalFlow T := by rw [ih]
      _ = C*(diagonalFlow ((n : ℝ)*T)*diagonalFlow T) := mul_assoc _ _ _

/-- A shorter fundamental period would give a proper integral root of the return matrix. -/
private theorem periods_of_primitive_return (C : Frame) (γ : IntegralFrame) (L : ℝ)
    (hL : 0 < L) (hγ : integralMap γ*C=C*diagonalFlow L)
    (hprimitive : ∀ n : ℕ, 2 ≤ n → ¬ ∃ B : IntegralFrame, B^n=γ) :
    periods (frame C)=AddSubgroup.zmultiples L := by
  have hLp : L ∈ periods (frame C) := (mem_periods_frame C L).mpr ⟨γ,hγ⟩
  rcases periods_eq_bot_or_positive_lattice (frame C) with hbot | ⟨T,hT,hP⟩
  · rw [hbot,AddSubgroup.mem_bot] at hLp
    exact (hL.ne' hLp).elim
  · have hmem : L ∈ AddSubgroup.zmultiples T := by rwa [← hP]
    obtain ⟨k,hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    rw [zsmul_eq_mul] at hk
    have hkpos : (0 : ℝ) < k := by
      by_contra hn
      have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hT.le
      rw [hk] at hp
      exact (not_le_of_gt hL) hp
    have hkI : (0 : ℤ) < k := by exact_mod_cast hkpos
    lift k to ℕ using hkI.le with n hn
    simp only [Int.cast_natCast] at hk
    have hnpos : 0 < n := by omega
    by_cases hn1 : n=1
    · subst n
      simp only [Nat.cast_one,one_mul] at hk
      rwa [hk] at hP
    · have hTp : T ∈ periods (frame C) := by
        rw [hP,AddSubgroup.mem_zmultiples_iff]
        exact ⟨1,by simp⟩
      obtain ⟨B,hB⟩ := (mem_periods_frame C T).mp hTp
      have he : integralMap (B^n)*C=integralMap γ*C := by
        calc
          _ = C*diagonalFlow ((n : ℝ)*T) := return_nat_pow C B T hB n
          _ = C*diagonalFlow L := by rw [hk]
          _ = _ := hγ.symm
      have hroot : B^n=γ := SpecialLinearGroup.map_intCast_injective (mul_right_cancel he)
      exact (hprimitive n (by omega) ⟨B,hroot⟩).elim

/-- Every primitive pair cycle has a genuine modular frame with exactly its geometric period lattice. -/
theorem exists_cycle_frame_periods (c : Orbit) :
    ∃ C : Frame,
      integralMap (cycleReturn c)*C=C*diagonalFlow (orbitTranslationLength c) ∧
      periods (frame C)=AddSubgroup.zmultiples (orbitTranslationLength c) := by
  obtain ⟨C,hC⟩ := exists_pair_return_frame (representative c).val (representative c).property.1
  have hc : integralMap (cycleReturn c)*C=C*diagonalFlow (orbitTranslationLength c) := by
    simpa only [cycleReturn,orbitTranslationLength_eq,multiplier] using hC
  exact ⟨C,hc,periods_of_primitive_return C (cycleReturn c) (orbitTranslationLength c)
    (orbitTranslationLength_pos c) hc (cycleReturn_primitive c)⟩

/-- A real eigenframe chosen from the proved actual return construction. -/
def cycleFrame (c : Orbit) : Frame := (exists_cycle_frame_periods c).choose

theorem cycleFrame_return (c : Orbit) :
    integralMap (cycleReturn c)*cycleFrame c=cycleFrame c*diagonalFlow (orbitTranslationLength c) :=
  (exists_cycle_frame_periods c).choose_spec.1

theorem cycleFrame_periods (c : Orbit) :
    periods (frame (cycleFrame c))=AddSubgroup.zmultiples (orbitTranslationLength c) :=
  (exists_cycle_frame_periods c).choose_spec.2

/-- The displacement-defined length is the least positive return of the constructed modular geodesic. -/
theorem cycleFrame_least_period (c : Orbit) :
    IsLeast {T : ℝ | T ∈ periods (frame (cycleFrame c)) ∧ 0 < T}
      (orbitTranslationLength c) := by
  have hL := orbitTranslationLength_pos c
  refine ⟨⟨?_,hL⟩,?_⟩
  · rw [cycleFrame_periods,AddSubgroup.mem_zmultiples_iff]
    exact ⟨1,by simp⟩
  · rintro T ⟨hTp,hT⟩
    rw [cycleFrame_periods,AddSubgroup.mem_zmultiples_iff] at hTp
    obtain ⟨k,hk⟩ := hTp
    rw [zsmul_eq_mul] at hk
    have hkpos : (0 : ℝ) < k := by
      by_contra hn
      have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hL.le
      rw [hk] at hp
      exact (not_le_of_gt hT) hp
    have hkI : (0 : ℤ) < k := by exact_mod_cast hkpos
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    have he := mul_le_mul_of_nonneg_right hk1 hL.le
    simpa only [one_mul,hk] using he

#print axioms integralMap_pairReturn
#print axioms exists_pair_return_frame
#print axioms cycleReturn_primitive
#print axioms exists_cycle_frame_periods
#print axioms cycleFrame_return
#print axioms cycleFrame_periods
#print axioms cycleFrame_least_period

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPrimitiveGeodesicReturns
