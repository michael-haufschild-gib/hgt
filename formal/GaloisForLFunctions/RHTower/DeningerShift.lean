import GaloisForLFunctions.RHTower.DeningerSphereContractible
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The unilateral shift on `ℓ²(ℕ, ℝ)`

The shift sends a square-summable sequence to the sequence with a zero prepended.  It is a linear
isometry, it has no eigenvector, and the first basis vector is orthogonal to its range.  These are
exactly the hypotheses under which the unit sphere is contractible.

* `deningerShift` : the shift, as a linear isometry.
* `deningerShift_no_eigenvector` : it has no eigenvector.
* `deningerShift_perp` : the first basis vector is orthogonal to its range.
* `deningerL2SeqSphere_contractible` : hence the unit sphere of `ℓ²(ℕ, ℝ)` is contractible.
-/

namespace RHTower

open scoped InnerProductSpace ENNReal

/-- Square-summable real sequences. -/
abbrev DeningerL2Seq : Type := lp (fun _ : ℕ => ℝ) 2

section ShiftFun

/-- Prepend a zero to a sequence. -/
def deningerShiftFun (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => x n

@[simp] theorem deningerShiftFun_zero (x : ℕ → ℝ) : deningerShiftFun x 0 = 0 := rfl

@[simp] theorem deningerShiftFun_succ (x : ℕ → ℝ) (n : ℕ) :
    deningerShiftFun x (n + 1) = x n := rfl

private theorem deningerShiftFun_vanish (x : ℕ → ℝ) :
    ∀ n ∉ Set.range (Nat.succ), ‖deningerShiftFun x n‖ ^ (2 : ℝ) = 0 := by
  intro n hn
  match n with
  | 0 => simp
  | (m + 1) => exact absurd ⟨m, rfl⟩ hn

private theorem deningerShiftFun_support (x : ℕ → ℝ) :
    Function.support (fun n => ‖deningerShiftFun x n‖ ^ (2 : ℝ)) ⊆ Set.range (Nat.succ) := by
  intro n hn
  by_contra hcon
  exact hn (deningerShiftFun_vanish x n hcon)

theorem deningerShiftFun_memℓp {x : ℕ → ℝ} (hx : Memℓp x 2) :
    Memℓp (deningerShiftFun x) 2 := by
  have htwo : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine (memℓp_gen_iff htwo).mpr ?_
  refine (Nat.succ_injective.summable_iff (deningerShiftFun_vanish x)).mp ?_
  exact ((memℓp_gen_iff htwo).mp hx).congr fun n => by simp

end ShiftFun

section Shift

/-- **The unilateral shift** on square-summable real sequences. -/
noncomputable def deningerShift : DeningerL2Seq →ₗᵢ[ℝ] DeningerL2Seq where
  toFun x := ⟨deningerShiftFun (x : ℕ → ℝ), deningerShiftFun_memℓp x.2⟩
  map_add' x y := by
    refine lp.ext ?_
    funext n
    match n with
    | 0 => simp
    | (m + 1) => simp
  map_smul' c x := by
    refine lp.ext ?_
    funext n
    match n with
    | 0 => simp
    | (m + 1) => simp
  norm_map' x := by
    have htwo : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
    rw [lp.norm_eq_tsum_rpow htwo, lp.norm_eq_tsum_rpow htwo]
    congr 1
    refine (Nat.succ_injective.tsum_eq (deningerShiftFun_support (x : ℕ → ℝ))).symm.trans ?_
    exact tsum_congr fun n => by simp

@[simp] theorem deningerShift_apply (x : DeningerL2Seq) (n : ℕ) :
    (deningerShift x : ℕ → ℝ) n = deningerShiftFun (x : ℕ → ℝ) n := rfl

/-- **The shift has no eigenvector.**  Comparing coordinates, the zeroth is killed and each
further one is determined by the previous, so an eigenvector vanishes identically. -/
theorem deningerShift_no_eigenvector (x : DeningerL2Seq) (c : ℝ) (hx : x ≠ 0) :
    deningerShift x ≠ c • x := by
  intro heq
  refine hx ?_
  have hcoord : ∀ n : ℕ, deningerShiftFun (x : ℕ → ℝ) n = c * (x : ℕ → ℝ) n := by
    intro n
    have := congrArg (fun z : DeningerL2Seq => (z : ℕ → ℝ) n) heq
    simpa using this
  have hall : ∀ n : ℕ, (x : ℕ → ℝ) n = 0 := by
    by_cases hc : c = 0
    · intro n
      have hm := hcoord (n + 1)
      rw [deningerShiftFun_succ, hc, zero_mul] at hm
      exact hm
    · have hx0 : (x : ℕ → ℝ) 0 = 0 := by
        have h0 := hcoord 0
        rw [deningerShiftFun_zero] at h0
        exact (mul_eq_zero.mp h0.symm).resolve_left hc
      intro n
      induction n with
      | zero => exact hx0
      | succ m ih =>
        have hm := hcoord (m + 1)
        rw [deningerShiftFun_succ, ih] at hm
        exact (mul_eq_zero.mp hm.symm).resolve_left hc
  refine lp.ext ?_
  funext n
  simpa using hall n

/-- The first basis vector. -/
noncomputable def deningerE0 : DeningerL2Seq := lp.single 2 0 (1 : ℝ)

theorem deningerE0_norm : ‖deningerE0‖ = 1 := by
  rw [deningerE0, lp.norm_single (by norm_num)]
  simp

/-- **The first basis vector is orthogonal to the range of the shift**, since every shifted
sequence vanishes at zero. -/
theorem deningerShift_perp (x : DeningerL2Seq) : ⟪deningerShift x, deningerE0⟫_ℝ = 0 := by
  rw [deningerE0, lp.inner_single_right]
  simp

/-- **The unit sphere of `ℓ²(ℕ, ℝ)` is contractible.**  The shift supplies the eigenvector-free
isometry and the first basis vector the orthogonal unit vector, so the two deformations apply. -/
theorem deningerL2SeqSphere_contractible :
    ContractibleSpace (Metric.sphere (0 : DeningerL2Seq) 1) :=
  deningerSphere_contractible deningerShift deningerShift_no_eigenvector
    deningerE0_norm deningerShift_perp

end Shift

end RHTower
