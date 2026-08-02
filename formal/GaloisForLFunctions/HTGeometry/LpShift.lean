import Mathlib.Analysis.InnerProductSpace.l2Space
import GaloisForLFunctions.HTGeometry.SphereContractible

/-!
# The unilateral shift and the contractible sphere of `ℓ²`

Inserting a zero in front of a square-summable sequence is a linear isometry of `ℓ²(ℕ, ℝ)` whose
range is orthogonal to the first basis vector, and which sends no nonzero sequence to its negative:
the equation `shift x = −x` forces `x₀ = 0` and then `x_{n+1} = −x_n = 0` by induction.

So the hypotheses of the sphere contraction are inhabited, and the unit sphere of `ℓ²(ℕ, ℝ)` is
contractible.

* `lpShift` : **the unilateral shift, as a linear isometry.**
* `contractibleSpace_sphere_lp` : **the unit sphere of `ℓ²(ℕ, ℝ)` is contractible.**
-/

open scoped InnerProductSpace ENNReal

noncomputable section

namespace GaloisForLFunctions

/-- The sequence space `ℓ²(ℕ, ℝ)`. -/
abbrev LpTwo : Type := lp (fun _ : ℕ => ℝ) 2

/-! ## The shift of a sequence -/

/-- Insert a zero in front of a sequence. -/
def shiftSeq (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => f n

@[simp] theorem shiftSeq_zero (f : ℕ → ℝ) : shiftSeq f 0 = 0 := rfl

@[simp] theorem shiftSeq_succ (f : ℕ → ℝ) (n : ℕ) : shiftSeq f (n + 1) = f n := rfl

theorem toReal_two : (2 : ℝ≥0∞).toReal = 2 := by norm_num

theorem summable_shiftSeq {f : ℕ → ℝ} (hf : Summable fun n => ‖f n‖ ^ (2 : ℝ)) :
    Summable fun n => ‖shiftSeq f n‖ ^ (2 : ℝ) := by
  rw [← summable_nat_add_iff 1]
  refine hf.congr fun n => ?_
  rw [shiftSeq_succ]

theorem memℓp_shiftSeq {f : ℕ → ℝ} (hf : Memℓp f 2) : Memℓp (shiftSeq f) 2 := by
  refine memℓp_gen ?_
  rw [toReal_two]
  refine summable_shiftSeq ?_
  have h := hf.summable (by rw [toReal_two]; norm_num)
  rw [toReal_two] at h
  exact h

theorem tsum_shiftSeq {f : ℕ → ℝ} (hf : Summable fun n => ‖f n‖ ^ (2 : ℝ)) :
    ∑' n, ‖shiftSeq f n‖ ^ (2 : ℝ) = ∑' n, ‖f n‖ ^ (2 : ℝ) := by
  have hs : Summable fun n => ‖shiftSeq f n‖ ^ (2 : ℝ) := summable_shiftSeq hf
  rw [hs.tsum_eq_zero_add]
  have hzero : ‖shiftSeq f 0‖ ^ (2 : ℝ) = 0 := by
    rw [shiftSeq_zero, norm_zero]
    simp
  rw [hzero, zero_add]
  refine tsum_congr fun n => ?_
  rw [shiftSeq_succ]

/-! ## The shift as a linear isometry -/

/-- **The unilateral shift on `ℓ²(ℕ, ℝ)`**, as a linear isometry. -/
def lpShift : LpTwo →ₗᵢ[ℝ] LpTwo where
  toFun f := ⟨shiftSeq (f : ℕ → ℝ), memℓp_shiftSeq f.2⟩
  map_add' f g := by
    refine lp.ext ?_
    funext n
    cases n with
    | zero =>
      show shiftSeq ((f + g : LpTwo) : ℕ → ℝ) 0 = _
      rw [shiftSeq_zero]
      show (0 : ℝ) = shiftSeq (f : ℕ → ℝ) 0 + shiftSeq (g : ℕ → ℝ) 0
      rw [shiftSeq_zero, shiftSeq_zero, add_zero]
    | succ m =>
      show shiftSeq ((f + g : LpTwo) : ℕ → ℝ) (m + 1) = _
      rw [shiftSeq_succ]
      show ((f + g : LpTwo) : ℕ → ℝ) m
        = shiftSeq (f : ℕ → ℝ) (m + 1) + shiftSeq (g : ℕ → ℝ) (m + 1)
      rw [shiftSeq_succ, shiftSeq_succ, lp.coeFn_add]
      rfl
  map_smul' c f := by
    refine lp.ext ?_
    funext n
    cases n with
    | zero =>
      show shiftSeq ((c • f : LpTwo) : ℕ → ℝ) 0 = _
      rw [shiftSeq_zero]
      show (0 : ℝ) = c * shiftSeq (f : ℕ → ℝ) 0
      rw [shiftSeq_zero, mul_zero]
    | succ m =>
      show shiftSeq ((c • f : LpTwo) : ℕ → ℝ) (m + 1) = _
      rw [shiftSeq_succ]
      show ((c • f : LpTwo) : ℕ → ℝ) m = c * shiftSeq (f : ℕ → ℝ) (m + 1)
      rw [shiftSeq_succ, lp.coeFn_smul]
      rfl
  norm_map' f := by
    have hpos : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by
      rw [toReal_two]
      norm_num
    have hsum := f.2.summable hpos
    rw [toReal_two] at hsum
    rw [lp.norm_eq_tsum_rpow hpos, lp.norm_eq_tsum_rpow hpos]
    congr 1
    rw [toReal_two]
    show ∑' n, ‖shiftSeq (f : ℕ → ℝ) n‖ ^ (2 : ℝ) = ∑' n, ‖(f : ℕ → ℝ) n‖ ^ (2 : ℝ)
    exact tsum_shiftSeq hsum

@[simp] theorem lpShift_apply (f : LpTwo) (n : ℕ) :
    (lpShift f : ℕ → ℝ) n = shiftSeq (f : ℕ → ℝ) n := rfl

/-! ## The first basis vector -/

/-- The first standard basis vector of `ℓ²(ℕ, ℝ)`. -/
def lpBasisZero : LpTwo := lp.single 2 0 (1 : ℝ)

theorem norm_lpBasisZero : ‖lpBasisZero‖ = 1 := by
  rw [lpBasisZero, lp.norm_single (by norm_num), norm_one]

theorem lpBasisZero_apply (n : ℕ) : (lpBasisZero : ℕ → ℝ) n = if n = 0 then 1 else 0 := by
  rw [lpBasisZero, lp.single_apply]
  by_cases h : n = 0
  · rw [if_pos h, h]
    simp
  · rw [if_neg h]
    simp [h]

/-! ## The three hypotheses of the contraction -/

theorem inner_lpShift_lpBasisZero (f : LpTwo) : ⟪lpShift f, lpBasisZero⟫_ℝ = 0 := by
  rw [lp.inner_eq_tsum]
  have hzero : (fun n : ℕ => ⟪(lpShift f : ℕ → ℝ) n, (lpBasisZero : ℕ → ℝ) n⟫_ℝ)
      = fun _ : ℕ => (0 : ℝ) := by
    funext n
    cases n with
    | zero =>
      show ⟪shiftSeq (f : ℕ → ℝ) 0, (lpBasisZero : ℕ → ℝ) 0⟫_ℝ = 0
      rw [shiftSeq_zero]
      simp
    | succ m =>
      show ⟪shiftSeq (f : ℕ → ℝ) (m + 1), (lpBasisZero : ℕ → ℝ) (m + 1)⟫_ℝ = 0
      rw [lpBasisZero_apply, if_neg (Nat.succ_ne_zero m)]
      simp
  rw [hzero, tsum_zero]

theorem lpShift_eq_neg_imp_zero (f : LpTwo) (hf : lpShift f = -f) : f = 0 := by
  have hpt : ∀ n : ℕ, shiftSeq (f : ℕ → ℝ) n = -((f : ℕ → ℝ) n) := by
    intro n
    have := congrArg (fun g : LpTwo => (g : ℕ → ℝ) n) hf
    simpa using this
  have hzero : ∀ n : ℕ, (f : ℕ → ℝ) n = 0 := by
    intro n
    induction n with
    | zero =>
      have h0 := hpt 0
      rw [shiftSeq_zero] at h0
      have : -((f : ℕ → ℝ) 0) = 0 := h0.symm
      linarith [neg_eq_zero.mp this]
    | succ m ih =>
      have hm := hpt (m + 1)
      rw [shiftSeq_succ, ih] at hm
      have : -((f : ℕ → ℝ) (m + 1)) = 0 := hm.symm
      exact neg_eq_zero.mp this
  refine lp.ext ?_
  funext n
  rw [hzero n]
  rfl

/-! ## The sphere of `ℓ²` is contractible -/

/-- **The unit sphere of `ℓ²(ℕ, ℝ)` is contractible.** -/
theorem contractibleSpace_sphere_lp :
    ContractibleSpace (Metric.sphere (0 : LpTwo) 1) :=
  contractibleSpace_sphere_of_isometry lpShift norm_lpBasisZero
    inner_lpShift_lpBasisZero lpShift_eq_neg_imp_zero

end GaloisForLFunctions

end
