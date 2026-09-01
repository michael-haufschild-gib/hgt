import GaloisForLFunctions.HTGeometry.StrongMarkushevichSystem
import GaloisForLFunctions.HTGeometry.PencilCauchySchwarz
import Mathlib.Tactic

open Complex
open scoped BigOperators ComplexConjugate Topology InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock

open Classical

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev E := EuclideanSpace ℂ ι

def e (i : ι) : E ι := EuclideanSpace.single i 1

def ones : E ι := ∑ i : ι, e ι i

def mean : E ι :=
  (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) • ones ι

def centered (i : ι) : E ι :=
  e ι i - (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) • mean ι

def scale : ℝ := Real.sqrt (2 - (Fintype.card ι : ℝ)⁻¹)

def primal (i : ι) : E ι :=
  ((scale ι)⁻¹ : ℂ) • (mean ι + centered ι i)

def dual (i : ι) : E ι :=
  (scale ι : ℂ) •
    ((((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) • mean ι + centered ι i)

omit [DecidableEq ι] in
theorem card_pos : 0 < Fintype.card ι := Fintype.card_pos

@[simp] theorem star_ofReal_local (x : ℝ) :
    (starRingEnd ℂ) (x : ℂ) = (x : ℂ) := by
  apply Complex.ext <;> simp

omit [Nonempty ι] in
theorem inner_e_e (i j : ι) :
    inner ℂ (e ι i) (e ι j) = if i = j then 1 else 0 := by
  simp [e, EuclideanSpace.single, PiLp.inner_apply, RCLike.inner_apply]

omit [Nonempty ι] in
theorem inner_e_ones (i : ι) : inner ℂ (e ι i) (ones ι) = 1 := by
  rw [ones]
  change inner ℂ (e ι i) (∑ j : ι, e ι j) = 1
  rw [inner_sum]
  simp [inner_e_e]

omit [Nonempty ι] in
theorem inner_ones_e (i : ι) : inner ℂ (ones ι) (e ι i) = 1 := by
  rw [ones]
  change inner ℂ (∑ j : ι, e ι j) (e ι i) = 1
  rw [sum_inner]
  simp [inner_e_e]

omit [Nonempty ι] in
theorem inner_ones_ones :
    inner ℂ (ones ι) (ones ι) = (Fintype.card ι : ℂ) := by
  calc
    inner ℂ (ones ι) (ones ι) = ∑ i : ι, inner ℂ (e ι i) (ones ι) := by
      rw [ones, sum_inner]
    _ = ∑ _i : ι, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact inner_e_ones ι i
    _ = (Fintype.card ι : ℂ) := by simp

omit [DecidableEq ι] in
theorem sqrt_card_sq :
    Real.sqrt (Fintype.card ι : ℝ) ^ 2 = (Fintype.card ι : ℝ) := by
  rw [Real.sq_sqrt]
  positivity

omit [DecidableEq ι] in
theorem sqrt_card_ne : Real.sqrt (Fintype.card ι : ℝ) ≠ 0 := by
  exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast card_pos ι))

omit [DecidableEq ι] in
theorem inv_sqrt_sq :
    (Real.sqrt (Fintype.card ι : ℝ))⁻¹ ^ 2 =
      (Fintype.card ι : ℝ)⁻¹ := by
  field_simp [sqrt_card_ne ι]
  nlinarith [sqrt_card_sq ι]

theorem inner_mean_mean : inner ℂ (mean ι) (mean ι) = 1 := by
  rw [mean, inner_smul_left, inner_smul_right, inner_ones_ones]
  simp only [star_ofReal_local]
  norm_cast
  rw [← mul_assoc, ← pow_two, inv_sqrt_sq]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt (card_pos ι)))

omit [Nonempty ι] in
theorem inner_mean_e (i : ι) :
    inner ℂ (mean ι) (e ι i) =
      (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) := by
  rw [mean, inner_smul_left, inner_ones_e]
  simp

omit [Nonempty ι] in
theorem inner_e_mean (i : ι) :
    inner ℂ (e ι i) (mean ι) =
      (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) := by
  rw [mean, inner_smul_right, inner_e_ones]
  simp

theorem inner_mean_centered (i : ι) :
    inner ℂ (mean ι) (centered ι i) = 0 := by
  rw [centered, inner_sub_right, inner_smul_right,
    inner_mean_e, inner_mean_mean]
  simp

theorem inner_centered_mean (i : ι) :
    inner ℂ (centered ι i) (mean ι) = 0 := by
  have h := inner_conj_symm (𝕜 := ℂ) (mean ι) (centered ι i)
  rw [inner_mean_centered] at h
  apply (starRingEnd ℂ).injective
  simpa using h

theorem inner_centered_centered (i j : ι) :
    inner ℂ (centered ι i) (centered ι j) =
      (if i = j then 1 else 0) - ((Fintype.card ι : ℝ)⁻¹ : ℂ) := by
  change inner ℂ
    (e ι i - (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) • mean ι)
    (e ι j - (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) • mean ι) = _
  simp only [inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, inner_e_e, inner_e_mean,
    inner_mean_e, inner_mean_mean]
  simp only [star_ofReal_local]
  ring_nf
  have hc' : ((((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ)) ^ 2 =
      ((Fintype.card ι : ℝ) : ℂ)⁻¹ := by
    calc
      _ = ((((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) ^ 2 : ℝ) : ℂ) := by
        norm_cast
      _ = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) := by
        exact congrArg (fun x : ℝ => (x : ℂ)) (inv_sqrt_sq ι)
      _ = ((Fintype.card ι : ℝ) : ℂ)⁻¹ := Complex.ofReal_inv _
  rw [hc']

omit [DecidableEq ι] in
theorem scale_sq : (scale ι) ^ 2 = 2 - (Fintype.card ι : ℝ)⁻¹ := by
  rw [scale, Real.sq_sqrt]
  have hm : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast card_pos ι
  have hi : (Fintype.card ι : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by exact_mod_cast card_pos ι)]
    exact_mod_cast hm
  linarith

omit [DecidableEq ι] in
theorem scale_pos : 0 < scale ι := by
  rw [scale, Real.sqrt_pos]
  have hm : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast card_pos ι
  have hi : (Fintype.card ι : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by exact_mod_cast card_pos ι)]
    exact_mod_cast hm
  linarith

theorem inner_raw_primal_self (i : ι) :
    inner ℂ (mean ι + centered ι i) (mean ι + centered ι i) =
      ((scale ι) ^ 2 : ℝ) := by
  rw [inner_add_left, inner_add_right, inner_add_right,
    inner_mean_mean, inner_mean_centered, inner_centered_mean,
    inner_centered_centered, if_pos rfl]
  norm_cast
  rw [scale_sq]
  ring

theorem inner_raw_primal_dual (i j : ι) :
    inner ℂ (mean ι + centered ι i)
      ((((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) • mean ι + centered ι j) =
        if i = j then 1 else 0 := by
  rw [inner_add_left, inner_add_right, inner_smul_right,
    inner_mean_mean, inner_mean_centered, inner_add_right,
    inner_smul_right, inner_centered_mean, inner_centered_centered]
  split_ifs <;> push_cast <;> ring

theorem inner_primal_primal (i : ι) : inner ℂ (primal ι i) (primal ι i) = 1 := by
  rw [primal, inner_smul_left, inner_smul_right, inner_raw_primal_self]
  rw [map_inv₀, star_ofReal_local]
  norm_cast
  field_simp [(scale_pos ι).ne']

theorem inner_primal_dual (i j : ι) :
    inner ℂ (primal ι i) (dual ι j) = if i = j then 1 else 0 := by
  rw [primal, dual, inner_smul_left, inner_smul_right,
    inner_raw_primal_dual]
  have hs : ((scale ι : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (scale_pos ι).ne'
  rw [map_inv₀, star_ofReal_local]
  rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

theorem sum_centered : ∑ i : ι, centered ι i = 0 := by
  have hcoef :
      ((Fintype.card ι : ℕ) : ℂ) *
          (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) = 1 := by
    norm_cast
    rw [mul_assoc, ← pow_two, inv_sqrt_sq]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt (card_pos ι)))
  rw [show (∑ i : ι, centered ι i) =
      (∑ i : ι, e ι i) -
        ∑ _i : ι, (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) • mean ι by
    simp [centered, Finset.sum_sub_distrib]]
  rw [show (∑ i : ι, e ι i) = ones ι by rfl,
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, mean,
    smul_smul, smul_smul, hcoef, one_smul, sub_self]

omit [Nonempty ι] in
theorem e_eq_centered_add_mean (i : ι) :
    e ι i = centered ι i +
      (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) • mean ι := by
  simp [centered]

omit [Nonempty ι] in
theorem inner_e_apply (i : ι) (x : E ι) :
    inner ℂ (e ι i) x = x i := by
  simp [e, EuclideanSpace.single, PiLp.inner_apply, RCLike.inner_apply]

theorem isCompleteSystem_mean_centered
    (a : ℂ) (ha : a ≠ 0) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ
      (fun i : ι => a • mean ι + centered ι i) := by
  rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero]
  intro x hx
  have hsum : inner ℂ (∑ i : ι, (a • mean ι + centered ι i)) x = 0 := by
    rw [sum_inner]
    simp [hx]
  have hsumvec : (∑ i : ι, (a • mean ι + centered ι i)) =
      ((Fintype.card ι : ℕ) : ℂ) • (a • mean ι) := by
    rw [Finset.sum_add_distrib, sum_centered, add_zero]
    rw [Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [hsumvec, inner_smul_left] at hsum
  have hca : ((Fintype.card ι : ℕ) : ℂ) * a ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt (card_pos ι))) ha
  have hmean : inner ℂ (mean ι) x = 0 := by
    rw [inner_smul_left] at hsum
    rw [← mul_assoc] at hsum
    exact (mul_eq_zero.mp hsum).resolve_left
      (mul_ne_zero
        (star_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt (card_pos ι))))
        (star_ne_zero.mpr ha))
  apply PiLp.ext
  intro i
  have hi := hx i
  rw [inner_add_left, inner_smul_left, hmean, mul_zero, zero_add] at hi
  have hei : inner ℂ (e ι i) x = 0 := by
    rw [e_eq_centered_add_mean, inner_add_left, inner_smul_left, hmean,
      mul_zero, add_zero]
    exact hi
  rw [inner_e_apply] at hei
  exact hei

/-- A regular-simplex family remains complete when its mean coefficient varies with the index,
provided the total coefficient does not vanish. -/
theorem isCompleteSystem_variable_mean_centered
    (a : ι → ℂ) (ha : (∑ i : ι, a i) ≠ 0) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ
      (fun i : ι => a i • mean ι + centered ι i) := by
  rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero]
  intro x hx
  have hsum : inner ℂ (∑ i : ι, (a i • mean ι + centered ι i)) x = 0 := by
    rw [sum_inner]
    simp [hx]
  have hsumvec : (∑ i : ι, (a i • mean ι + centered ι i)) =
      (∑ i : ι, a i) • mean ι := by
    rw [Finset.sum_add_distrib, sum_centered, add_zero, Finset.sum_smul]
  rw [hsumvec, inner_smul_left] at hsum
  have hmean : inner ℂ (mean ι) x = 0 :=
    (mul_eq_zero.mp hsum).resolve_left (star_ne_zero.mpr ha)
  apply PiLp.ext
  intro i
  have hi := hx i
  rw [inner_add_left, inner_smul_left, hmean, mul_zero, zero_add] at hi
  have hei : inner ℂ (e ι i) x = 0 := by
    rw [e_eq_centered_add_mean, inner_add_left, inner_smul_left, hmean,
      mul_zero, add_zero]
    exact hi
  rw [inner_e_apply] at hei
  exact hei

theorem isCompleteSystem_primal :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ (primal ι) := by
  have hraw := isCompleteSystem_mean_centered ι 1 one_ne_zero
  rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero] at hraw ⊢
  intro x hx
  apply hraw
  intro i
  have hi := hx i
  rw [primal, inner_smul_left] at hi
  simpa using (mul_eq_zero.mp hi).resolve_left
    (star_ne_zero.mpr
      (inv_ne_zero (Complex.ofReal_ne_zero.mpr (scale_pos ι).ne')))

theorem isCompleteSystem_dual :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ (dual ι) := by
  have ha : (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (inv_ne_zero (by exact_mod_cast (ne_of_gt (card_pos ι))))
  have hraw := isCompleteSystem_mean_centered ι
    (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) ha
  rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero] at hraw ⊢
  intro x hx
  apply hraw
  intro i
  have hi := hx i
  rw [dual, inner_smul_left] at hi
  exact (mul_eq_zero.mp hi).resolve_left
    (star_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (scale_pos ι).ne'))

def phasePrimal (z : ι → ℂ) (i : ι) : E ι := z i • primal ι i

def phaseDual (z : ι → ℂ) (i : ι) : E ι := z i • dual ι i

theorem inner_phasePrimal_phaseDual
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (i j : ι) :
    inner ℂ (phasePrimal ι z i) (phaseDual ι z j) =
      if i = j then 1 else 0 := by
  rw [phasePrimal, phaseDual, inner_smul_left, inner_smul_right,
    inner_primal_dual]
  split_ifs with hij
  · subst j
    rw [mul_one, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      hz]
    norm_num
  · simp

theorem norm_phasePrimal
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (i : ι) :
    ‖phasePrimal ι z i‖ = 1 := by
  rw [phasePrimal, norm_smul, hz]
  have hn2 : ‖primal ι i‖ ^ 2 = 1 := by
    have h := inner_primal_primal ι i
    rw [inner_self_eq_norm_sq_to_K] at h
    have hre := congrArg Complex.re h
    norm_cast at hre
  have hn : ‖primal ι i‖ = 1 := by
    nlinarith [norm_nonneg (primal ι i)]
  rw [hn, mul_one]

theorem inner_dual_dual (i : ι) :
    inner ℂ (dual ι i) (dual ι i) =
      ((1 + (1 - (Fintype.card ι : ℝ)⁻¹) ^ 3 : ℝ) : ℂ) := by
  rw [dual]
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    star_ofReal_local, inner_mean_mean, inner_mean_centered,
    inner_centered_mean, inner_centered_centered, if_pos]
  norm_cast
  ring_nf
  rw [scale_sq]
  ring

theorem norm_dual_sq (i : ι) :
    ‖dual ι i‖ ^ 2 = 1 + (1 - (Fintype.card ι : ℝ)⁻¹) ^ 3 := by
  have h : ((‖dual ι i‖ ^ 2 : ℝ) : ℂ) =
      ((1 + (1 - (Fintype.card ι : ℝ)⁻¹) ^ 3 : ℝ) : ℂ) := by
    calc
      ((‖dual ι i‖ ^ 2 : ℝ) : ℂ) =
          inner ℂ (dual ι i) (dual ι i) := by
            rw [inner_self_eq_norm_sq_to_K]
            norm_cast
      _ = _ := inner_dual_dual ι i
  exact Complex.ofReal_injective h

theorem norm_dual_sq_le_two (i : ι) : ‖dual ι i‖ ^ 2 ≤ 2 := by
  rw [norm_dual_sq]
  have hm : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast card_pos ι
  have hq0 : 0 ≤ (Fintype.card ι : ℝ)⁻¹ := by positivity
  have hq1 : (Fintype.card ι : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by exact_mod_cast card_pos ι)]
    exact hm
  have hpow : (1 - (Fintype.card ι : ℝ)⁻¹) ^ 3 ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr hq1) (by linarith)
  linarith

theorem norm_phaseDual_sq_le_two
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (i : ι) :
    ‖phaseDual ι z i‖ ^ 2 ≤ 2 := by
  rw [phaseDual, norm_smul, hz, one_mul]
  exact norm_dual_sq_le_two ι i

theorem isCompleteSystem_phasePrimal
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ (phasePrimal ι z) := by
  rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero]
  intro x hx
  have hp := isCompleteSystem_primal ι
  rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero] at hp
  apply hp
  intro i
  have hi := hx i
  rw [phasePrimal, inner_smul_left] at hi
  exact (mul_eq_zero.mp hi).resolve_left
    (star_ne_zero.mpr (norm_ne_zero_iff.mp (by rw [hz]; norm_num)))

theorem isCompleteSystem_phaseDual
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ (phaseDual ι z) := by
  rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero]
  intro x hx
  have hd := isCompleteSystem_dual ι
  rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero] at hd
  apply hd
  intro i
  have hi := hx i
  rw [phaseDual, inner_smul_left] at hi
  exact (mul_eq_zero.mp hi).resolve_left
    (star_ne_zero.mpr (norm_ne_zero_iff.mp (by rw [hz]; norm_num)))

def mixedRawCoefficient (s : Set ι) (i : ι) : ℂ :=
  if i ∈ s then 1 else (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ)

def mixedRaw (s : Set ι) (i : ι) : E ι :=
  mixedRawCoefficient ι s i • mean ι + centered ι i

omit [DecidableEq ι] in
theorem sum_mixedRawCoefficient_ne_zero (s : Set ι) :
    (∑ i : ι, mixedRawCoefficient ι s i) ≠ 0 := by
  let ar : ι → ℝ := fun i => if i ∈ s then 1 else (Fintype.card ι : ℝ)⁻¹
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast card_pos ι
  have har : ∀ i, 0 < ar i := by
    intro i
    simp only [ar]
    split_ifs <;> positivity
  have hsum : 0 < ∑ i : ι, ar i :=
    Finset.sum_pos (fun i _ => har i) Finset.univ_nonempty
  have heq : (∑ i : ι, mixedRawCoefficient ι s i) =
      ((∑ i : ι, ar i : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mixedRawCoefficient, ar]
    split_ifs <;> simp
  rw [heq]
  exact Complex.ofReal_ne_zero.mpr hsum.ne'

theorem isCompleteSystem_mixedRaw (s : Set ι) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ (mixedRaw ι s) := by
  exact isCompleteSystem_variable_mean_centered ι
    (mixedRawCoefficient ι s) (sum_mixedRawCoefficient_ne_zero ι s)

theorem isCompleteSystem_phaseMixed
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (s : Set ι) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ
      (GaloisForLFunctions.HTGeometry.strongMarkushevichMixed
        (phasePrimal ι z) (phaseDual ι z) s) := by
  let c : ι → ℂ := fun i =>
    if i ∈ s then z i * ((scale ι : ℂ)⁻¹) else z i * (scale ι : ℂ)
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    have hz0 : z i ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
    have hs0 : (scale ι : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (scale_pos ι).ne'
    simp only [c]
    split_ifs <;> exact mul_ne_zero hz0 (by simp [hs0])
  have hscaled := GaloisForLFunctions.HTGeometry.IsCompleteSystem.smul_of_ne
    (isCompleteSystem_mixedRaw ι s) c hc
  rw [show (fun i => c i • mixedRaw ι s i) =
      GaloisForLFunctions.HTGeometry.strongMarkushevichMixed
        (phasePrimal ι z) (phaseDual ι z) s by
    funext i
    by_cases hi : i ∈ s
    · simp [c, mixedRaw, mixedRawCoefficient, hi,
        GaloisForLFunctions.HTGeometry.strongMarkushevichMixed,
        phasePrimal, primal, smul_smul]
    · simp [c, mixedRaw, mixedRawCoefficient, hi,
        GaloisForLFunctions.HTGeometry.strongMarkushevichMixed,
        phaseDual, dual, smul_smul]
      module] at hscaled
  exact hscaled

theorem isStrongMarkushevichPair_phase
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    GaloisForLFunctions.HTGeometry.IsStrongMarkushevichPair ℂ
      (phasePrimal ι z) (phaseDual ι z) := by
  refine ⟨?_, isCompleteSystem_phaseMixed ι z hz⟩
  apply GaloisForLFunctions.HTGeometry.IsDualSystem.symm
  constructor
  · intro i
    simpa using inner_phasePrimal_phaseDual ι z hz i i
  · intro i j hij
    simpa [hij] using inner_phasePrimal_phaseDual ι z hz i j

def average (d : ι → ℂ) : ℂ :=
  ((Fintype.card ι : ℂ)⁻¹) * ∑ i : ι, d i

def deviation (d : ι → ℂ) : E ι :=
  ∑ i : ι, (d i - average ι d) • e ι i

def solution (d : ι → ℂ) : E ι :=
  (scale ι : ℂ) • (average ι d • mean ι + deviation ι d)

omit [DecidableEq ι] in
theorem sum_sub_average (d : ι → ℂ) :
    ∑ i : ι, (d i - average ι d) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_eq_mul, average]
  rw [← mul_assoc, mul_inv_cancel₀
    (Nat.cast_ne_zero.mpr (ne_of_gt (card_pos ι))), one_mul, sub_self]

theorem inner_mean_deviation (d : ι → ℂ) :
    inner ℂ (mean ι) (deviation ι d) = 0 := by
  rw [deviation, inner_sum]
  simp_rw [inner_smul_right, inner_mean_e]
  rw [← Finset.sum_mul, sum_sub_average, zero_mul]

theorem inner_centered_deviation (d : ι → ℂ) (i : ι) :
    inner ℂ (centered ι i) (deviation ι d) = d i - average ι d := by
  rw [centered, inner_sub_left, inner_smul_left, inner_mean_deviation,
    mul_zero, sub_zero, deviation, inner_e_apply]
  simp [e, EuclideanSpace.single, Pi.single_apply]

theorem inner_primal_solution (d : ι → ℂ) (i : ι) :
    inner ℂ (primal ι i) (solution ι d) = d i := by
  rw [primal, solution, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, inner_smul_right,
    inner_mean_mean, inner_mean_deviation, inner_add_right,
    inner_smul_right, inner_centered_mean, inner_centered_deviation]
  have hs : ((scale ι : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (scale_pos ι).ne'
  rw [map_inv₀, star_ofReal_local]
  simp only [mul_one, mul_zero, add_zero, zero_add, add_sub_cancel]
  rw [← mul_assoc,
    inv_mul_cancel₀ hs, one_mul]

omit [Nonempty ι] in
theorem orthonormal_e : Orthonormal ℂ (e ι) := by
  rw [orthonormal_iff_ite]
  exact inner_e_e ι

omit [Nonempty ι] in
theorem norm_deviation_sq (d : ι → ℂ) :
    ‖deviation ι d‖ ^ 2 = ∑ i : ι, ‖d i - average ι d‖ ^ 2 := by
  simpa [deviation, LinearIsometry.toSpanSingleton_apply] using
    (orthonormal_e ι).orthogonalFamily.norm_sum
      (fun i => d i - average ι d) Finset.univ

omit [DecidableEq ι] [Nonempty ι] in
theorem norm_sum_sq_le_card_mul_sum_sq (w : ι → ℂ) :
    ‖∑ i : ι, w i‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i : ι, ‖w i‖ ^ 2 := by
  exact GaloisForLFunctions.HTGeometry.norm_sum_sq_le_card_mul w

omit [DecidableEq ι] in
theorem card_mul_norm_average_sq_le_sum (d : ι → ℂ) :
    (Fintype.card ι : ℝ) * ‖average ι d‖ ^ 2 ≤
      ∑ i : ι, ‖d i‖ ^ 2 := by
  have hm0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast card_pos ι
  have hsum := norm_sum_sq_le_card_mul_sum_sq ι d
  have hmnorm : ‖(Fintype.card ι : ℂ)‖ = (Fintype.card ι : ℝ) := by
    simp
  rw [average, norm_mul, norm_inv, hmnorm]
  calc
    (Fintype.card ι : ℝ) *
        ((Fintype.card ι : ℝ)⁻¹ * ‖∑ i : ι, d i‖) ^ 2 =
      (Fintype.card ι : ℝ)⁻¹ * ‖∑ i : ι, d i‖ ^ 2 := by
        field_simp [hm0.ne']
    _ ≤ (Fintype.card ι : ℝ)⁻¹ *
        ((Fintype.card ι : ℝ) * ∑ i : ι, ‖d i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hm0.le)
    _ = ∑ i : ι, ‖d i‖ ^ 2 := by field_simp [hm0.ne']

theorem norm_sub_sq_le_two (x y : ℂ) :
    ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := norm_sub_le x y
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x - y),
    sq_nonneg (‖x‖ - ‖y‖)]

omit [DecidableEq ι] in
theorem sum_norm_sub_average_sq_le (d : ι → ℂ) :
    ∑ i : ι, ‖d i - average ι d‖ ^ 2 ≤
      4 * ∑ i : ι, ‖d i‖ ^ 2 := by
  calc
    _ ≤ ∑ i : ι, 2 * (‖d i‖ ^ 2 + ‖average ι d‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => norm_sub_sq_le_two (d i) (average ι d)
    _ = 2 * ∑ i : ι, ‖d i‖ ^ 2 +
        2 * (Fintype.card ι : ℝ) * ‖average ι d‖ ^ 2 := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    _ ≤ 4 * ∑ i : ι, ‖d i‖ ^ 2 := by
      have hscaled := card_mul_norm_average_sq_le_sum ι d
      nlinarith

theorem norm_mean : ‖mean ι‖ = 1 := by
  have h := inner_mean_mean ι
  rw [inner_self_eq_norm_sq_to_K] at h
  have hre := congrArg Complex.re h
  have hn2 : ‖mean ι‖ ^ 2 = 1 := by exact_mod_cast hre
  nlinarith [norm_nonneg (mean ι)]

omit [DecidableEq ι] in
theorem scale_sq_le_two : (scale ι) ^ 2 ≤ 2 := by
  rw [scale_sq]
  exact sub_le_self _ (by positivity)

theorem norm_solution_sq_le (d : ι → ℂ) :
    ‖solution ι d‖ ^ 2 ≤ 20 * ∑ i : ι, ‖d i‖ ^ 2 := by
  let S : ℝ := ∑ i : ι, ‖d i‖ ^ 2
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => sq_nonneg ‖d i‖
  have hm : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast card_pos ι
  have havgScaled := card_mul_norm_average_sq_le_sum ι d
  have havg : ‖average ι d‖ ^ 2 ≤ S := by
    have ha0 := sq_nonneg ‖average ι d‖
    dsimp [S] at havgScaled ⊢
    nlinarith
  have hdev : ‖deviation ι d‖ ^ 2 ≤ 4 * S := by
    rw [norm_deviation_sq]
    exact sum_norm_sub_average_sq_le ι d
  have hmeanNorm := norm_mean ι
  have hadd := norm_add_le (average ι d • mean ι) (deviation ι d)
  rw [norm_smul, hmeanNorm, mul_one] at hadd
  have hinside :
      ‖average ι d • mean ι + deviation ι d‖ ^ 2 ≤ 10 * S := by
    nlinarith [norm_nonneg (average ι d), norm_nonneg (deviation ι d),
      norm_nonneg (average ι d • mean ι + deviation ι d),
      sq_nonneg (‖average ι d‖ - ‖deviation ι d‖)]
  rw [solution, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (scale_pos ι)]
  have hs0 := (scale_pos ι).le
  have hn0 := norm_nonneg (average ι d • mean ι + deviation ι d)
  have hs2 := scale_sq_le_two ι
  dsimp [S] at hinside hS ⊢
  nlinarith [sq_nonneg (scale ι *
    ‖average ι d • mean ι + deviation ι d‖)]

end GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock
