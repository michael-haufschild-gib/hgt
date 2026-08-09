import GaloisForLFunctions.HTGeometry.FreeFockMatrixSemicircle
import GaloisForLFunctions.HTGeometry.CarriedConclusion

open scoped BigOperators Matrix
open Matrix
open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

def finsuppL1 {α : Type*} (x : α →₀ ℂ) : ℝ :=
  x.sum fun _ c => ‖c‖

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem finsuppL1_nonneg {α : Type*} (x : α →₀ ℂ) : 0 ≤ finsuppL1 x := by
  exact Finsupp.sum_nonneg fun _ _ => norm_nonneg _

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
@[simp] theorem finsuppL1_zero {α : Type*} : finsuppL1 (0 : α →₀ ℂ) = 0 := by
  simp [finsuppL1]

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
@[simp] theorem finsuppL1_single {α : Type*} (a : α) (c : ℂ) :
    finsuppL1 (Finsupp.single a c) = ‖c‖ := by
  classical
  simp [finsuppL1]

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem finsuppL1_add_le {α : Type*} (x y : α →₀ ℂ) :
    finsuppL1 (x + y) ≤ finsuppL1 x + finsuppL1 y := by
  classical
  let s := x.support ∪ y.support
  rw [finsuppL1, Finsupp.sum_of_support_subset (s := s) _ (by
    exact Finsupp.support_add) _ (by simp)]
  rw [finsuppL1, Finsupp.sum_of_support_subset (s := s) _
    (Finset.subset_union_left) _ (by simp)]
  rw [finsuppL1, Finsupp.sum_of_support_subset (s := s) _
    (Finset.subset_union_right) _ (by simp)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  exact norm_add_le _ _

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
@[simp] theorem finsuppL1_smul {α : Type*} (c : ℂ) (x : α →₀ ℂ) :
    finsuppL1 (c • x) = ‖c‖ * finsuppL1 x := by
  classical
  rw [finsuppL1, Finsupp.sum_smul_index]
  · rw [finsuppL1, Finsupp.mul_sum]
    apply Finsupp.sum_congr
    intro a ha
    exact norm_mul _ _
  · intro a
    simp

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem finsuppL1_finsetSum_le {α L : Type*} (s : Finset L) (f : L → α →₀ ℂ) :
    finsuppL1 (∑ a ∈ s, f a) ≤ ∑ a ∈ s, finsuppL1 (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      calc
        finsuppL1 (f a + ∑ b ∈ s, f b) ≤
            finsuppL1 (f a) + finsuppL1 (∑ b ∈ s, f b) := finsuppL1_add_le _ _
        _ ≤ finsuppL1 (f a) + ∑ b ∈ s, finsuppL1 (f b) := by gcongr

def matrixFamilyEntryL1 (A : K → Matrix I I ℂ) : ℝ :=
  ∑ k : K, ∑ i : I, ∑ j : I, ‖A k i j‖

omit [DecidableEq I] [DecidableEq K] in
theorem norm_matrixEntry_le_matrixFamilyEntryL1
    (A : K → Matrix I I ℂ) (k : K) (i j : I) :
    ‖A k i j‖ ≤ matrixFamilyEntryL1 A := by
  rw [matrixFamilyEntryL1]
  calc
    ‖A k i j‖ ≤ ∑ j' : I, ‖A k i j'‖ :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i' : I, ∑ j' : I, ‖A k i' j'‖ :=
      Finset.single_le_sum
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ k' : K, ∑ i' : I, ∑ j' : I, ‖A k' i' j'‖ :=
      Finset.single_le_sum
        (fun _ _ => Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)

omit [DecidableEq I] [DecidableEq K] in
theorem finsuppL1_freeFockCreationBasisAction_le
    (A : K → Matrix I I ℂ) (jw : I × List K) :
    finsuppL1 (freeFockCreationBasisAction A jw) ≤ matrixFamilyEntryL1 A := by
  rw [freeFockCreationBasisAction]
  refine (finsuppL1_finsetSum_le Finset.univ
    (fun k => ∑ i : I, Finsupp.single (i, k :: jw.2) (A k i jw.1))).trans ?_
  apply le_trans (Finset.sum_le_sum fun k _ =>
    finsuppL1_finsetSum_le Finset.univ
      (fun i => Finsupp.single (i, k :: jw.2) (A k i jw.1)))
  simp only [finsuppL1_single]
  rw [matrixFamilyEntryL1]
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.single_le_sum (fun _ _ => norm_nonneg _)
  simp

omit [DecidableEq I] [DecidableEq K] in
theorem finsuppL1_freeFockAnnihilationBasisAction_le
    (A : K → Matrix I I ℂ) (jw : I × List K) :
    finsuppL1 (freeFockAnnihilationBasisAction A jw) ≤ matrixFamilyEntryL1 A := by
  rcases jw with ⟨j, w⟩
  cases w with
  | nil =>
      simp only [freeFockAnnihilationBasisAction, finsuppL1_zero]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _
  | cons k w =>
      rw [freeFockAnnihilationBasisAction]
      refine (finsuppL1_finsetSum_le Finset.univ
        (fun i => Finsupp.single (i, w) (A k i j))).trans ?_
      simp only [finsuppL1_single]
      rw [matrixFamilyEntryL1]
      apply le_trans (show (∑ i : I, ‖A k i j‖) ≤
        ∑ i : I, ∑ j' : I, ‖A k i j'‖ by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.single_le_sum (fun _ _ => norm_nonneg _)
          simp)
      exact Finset.single_le_sum
        (fun _ _ => Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)

omit [DecidableEq I] [DecidableEq K] in
theorem finsuppL1_freeFockBasisAction_le
    (A : K → Matrix I I ℂ) (jw : I × List K) :
    finsuppL1 (freeFockBasisAction A jw) ≤ 2 * matrixFamilyEntryL1 A := by
  rw [freeFockBasisAction]
  calc
    finsuppL1 (freeFockCreationBasisAction A jw + freeFockAnnihilationBasisAction A jw) ≤
        finsuppL1 (freeFockCreationBasisAction A jw) +
          finsuppL1 (freeFockAnnihilationBasisAction A jw) := finsuppL1_add_le _ _
    _ ≤ matrixFamilyEntryL1 A + matrixFamilyEntryL1 A := add_le_add
      (finsuppL1_freeFockCreationBasisAction_le A jw)
      (finsuppL1_freeFockAnnihilationBasisAction_le A jw)
    _ = 2 * matrixFamilyEntryL1 A := by ring

omit [DecidableEq I] [DecidableEq K] in
theorem finsuppL1_freeFockAction_le
    (A : K → Matrix I I ℂ) (x : FreeFockVector I K) :
    finsuppL1 (freeFockAction A x) ≤ 2 * matrixFamilyEntryL1 A * finsuppL1 x := by
  rw [freeFockAction, Finsupp.linearCombination_apply]
  refine (finsuppL1_finsetSum_le x.support
    (fun a => x a • freeFockBasisAction A a)).trans ?_
  simp only [finsuppL1_smul]
  rw [finsuppL1, Finsupp.sum]
  calc
    (∑ a ∈ x.support, ‖x a‖ * finsuppL1 (freeFockBasisAction A a)) ≤
        ∑ a ∈ x.support, ‖x a‖ * (2 * matrixFamilyEntryL1 A) := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left
        (finsuppL1_freeFockBasisAction_le A a) (norm_nonneg _)
    _ = 2 * matrixFamilyEntryL1 A * ∑ a ∈ x.support, ‖x a‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

omit [DecidableEq I] [DecidableEq K] in
theorem matrixFamilyEntryL1_nonneg (A : K → Matrix I I ℂ) :
    0 ≤ matrixFamilyEntryL1 A := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => norm_nonneg _

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem norm_finsupp_apply_le_finsuppL1 {α : Type*} (x : α →₀ ℂ) (a : α) :
    ‖x a‖ ≤ finsuppL1 x := by
  classical
  by_cases ha : a ∈ x.support
  · rw [finsuppL1, Finsupp.sum]
    exact Finset.single_le_sum (fun _ _ => norm_nonneg _) ha
  · have hzero : x a = 0 := by simpa [Finsupp.mem_support_iff] using ha
    rw [hzero, norm_zero]
    exact finsuppL1_nonneg x

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in
theorem finsuppL1_freeFockVacuum (j : I) :
    finsuppL1 (freeFockVacuum (K := K) j) = 1 := by
  simp [freeFockVacuum]

omit [DecidableEq I] [DecidableEq K] in
theorem finsuppL1_freeFockPower_le
    (A : K → Matrix I I ℂ) (j : I) (n : ℕ) :
    finsuppL1 (freeFockPower A j n) ≤ (2 * matrixFamilyEntryL1 A) ^ n := by
  induction n with
  | zero => simp [freeFockPower, finsuppL1_freeFockVacuum]
  | succ n ih =>
      rw [freeFockPower_succ, pow_succ]
      have hC : 0 ≤ (2 : ℝ) * matrixFamilyEntryL1 A :=
        mul_nonneg (by norm_num) (matrixFamilyEntryL1_nonneg A)
      exact (finsuppL1_freeFockAction_le A _).trans (by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left ih hC)

omit [DecidableEq I] [DecidableEq K] in
theorem norm_freeFockPower_apply_le
    (A : K → Matrix I I ℂ) (j i : I) (w : List K) (n : ℕ) :
    ‖freeFockPower A j n (i, w)‖ ≤ (2 * matrixFamilyEntryL1 A) ^ n :=
  (norm_finsupp_apply_le_finsuppL1 (freeFockPower A j n) (i, w)).trans
    (finsuppL1_freeFockPower_le A j n)

omit [DecidableEq I] [DecidableEq K] in
theorem freeFockTraceMoment_le_power [Nonempty I]
    (A : K → Matrix I I ℂ) (n : ℕ) :
    freeFockTraceMoment A n ≤ (2 * matrixFamilyEntryL1 A) ^ n := by
  rw [freeFockTraceMoment]
  have hcard : 0 < (Fintype.card I : ℝ) := by
    exact_mod_cast Fintype.card_pos
  calc
    (Fintype.card I : ℝ)⁻¹ * ∑ i : I, (freeFockPower A i n (i, [])).re ≤
        (Fintype.card I : ℝ)⁻¹ *
          ∑ _i : I, (2 * matrixFamilyEntryL1 A) ^ n := by
      gcongr with i
      exact (Complex.re_le_norm _).trans (norm_freeFockPower_apply_le A i i [] n)
    _ = (2 * matrixFamilyEntryL1 A) ^ n := by
      simp [hcard.ne']

omit [DecidableEq I] [DecidableEq K] in
theorem freeFockTraceMoment_even_le_radius [Nonempty I]
    (A : K → Matrix I I ℂ) (n : ℕ) :
    freeFockTraceMoment A (2 * n) ≤ (2 * matrixFamilyEntryL1 A + 1) ^ (2 * n) := by
  refine (freeFockTraceMoment_le_power A (2 * n)).trans ?_
  exact pow_le_pow_left₀ (mul_nonneg (by positivity) (matrixFamilyEntryL1_nonneg A))
    (by linarith) _

def freeFockSpectralRadius (A : K → Matrix I I ℂ) : ℝ :=
  2 * matrixFamilyEntryL1 A + 1

omit [DecidableEq I] [DecidableEq K] in
theorem freeFockSpectralRadius_pos (A : K → Matrix I I ℂ) :
    0 < freeFockSpectralRadius A := by
  rw [freeFockSpectralRadius]
  have := matrixFamilyEntryL1_nonneg A
  linarith

theorem exists_freeFockTraceSpectralLaw_carried [Nonempty I]
    (A : K → Matrix I I ℂ) (hA : ∀ k, (A k)ᴴ = A k)
    (hker : HasTrivialCommonKernel A) :
    ∃ μ : ProbabilityMeasure ℝ,
      HasHamburgerMoments (freeFockTraceMoment A) (μ : Measure ℝ) ∧
        (μ : Measure ℝ)
          (Set.Icc (-freeFockSpectralRadius A) (freeFockSpectralRadius A))ᶜ = 0 := by
  obtain ⟨μ, hμ⟩ := HTGeometry.exists_hasHamburgerMoments_of_moment_zero_eq_one
    (freeFockTraceMoment_positiveMomentForm A hA hker)
    (freeFockTraceMoment_zero A)
  let R := freeFockSpectralRadius A
  have hR : 0 < R := freeFockSpectralRadius_pos A
  let f : ℝ → ℝ := fun x => (x / R) ^ 2
  have hfmeas : Measurable f := by fun_prop
  have hfnn : ∀ x, 0 ≤ f x := fun x => sq_nonneg _
  have hfeq (x : ℝ) (n : ℕ) : f x ^ n = R⁻¹ ^ (2 * n) * x ^ (2 * n) := by
    dsimp only [f]
    rw [pow_mul, div_pow, inv_pow]
    ring
  have hint : ∀ n : ℕ, Integrable (fun x => f x ^ n) (μ : Measure ℝ) := by
    intro n
    refine ((hμ (2 * n)).1.const_mul (R⁻¹ ^ (2 * n))).congr
      (Filter.Eventually.of_forall fun x => ?_)
    exact (hfeq x n).symm
  have hbound : ∀ n : ℕ, ∫ x, f x ^ n ∂(μ : Measure ℝ) ≤ 1 := by
    intro n
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x => hfeq x n),
      integral_const_mul, (hμ (2 * n)).2]
    have hm := freeFockTraceMoment_even_le_radius A n
    change R⁻¹ ^ (2 * n) * freeFockTraceMoment A (2 * n) ≤ 1
    have hinvnn : 0 ≤ R⁻¹ ^ (2 * n) := pow_nonneg (inv_nonneg.mpr hR.le) _
    calc
      R⁻¹ ^ (2 * n) * freeFockTraceMoment A (2 * n) ≤
          R⁻¹ ^ (2 * n) * R ^ (2 * n) := mul_le_mul_of_nonneg_left hm hinvnn
      _ = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hR.ne', one_pow]
  have hnull : ∀ k : ℕ, (μ : Measure ℝ)
      {x | 1 + 1 / (k + 1 : ℝ) ≤ f x} = 0 := by
    intro k
    apply HTGeometry.measure_ge_eq_zero_of_pow_integral_le hfmeas hfnn hint hbound
    have : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    linarith
  have hcover : (Set.Icc (-R) R)ᶜ ⊆
      ⋃ k : ℕ, {x | 1 + 1 / (k + 1 : ℝ) ≤ f x} := by
    intro x hx
    have hgt : 1 < f x := by
      dsimp only [f]
      have h := (HTGeometry.sq_gt_one_iff_notMem_Icc (c := 0) hR).mpr
        (by simpa using hx)
      simpa using h
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < f x - 1)
    exact Set.mem_iUnion.mpr ⟨k, by simp only [Set.mem_setOf_eq]; linarith⟩
  refine ⟨μ, hμ, measure_mono_null hcover ?_⟩
  exact measure_iUnion_null hnull

end
end GaloisForLFunctions.HTGeometry
