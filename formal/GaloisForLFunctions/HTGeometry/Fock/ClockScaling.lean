import GaloisForLFunctions.HTGeometry.LinearAlgebra.ScalingNilpotence
import GaloisForLFunctions.HTGeometry.GomesFockTaylorGauge

/-!
# The scaling boundary between the two finite jet clocks

Diagonal jet dilation conjugates the truncated derivative clock to any nonzero
scalar multiple. The degree clock, realized by creation after differentiation,
admits a complex scaling under similarity exactly when that scale is one
or the jet space has dimension at most one. Thus the existing finite jets
exhibit both sides of the nilpotence boundary of time-scale rigidity.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Multiply the jet of order `j` by the `j`th power of a nonzero scale. -/
def fockDilation (N : ℕ) (q : ℂˣ) : (Fin N → ℂ) ≃ₗ[ℂ] (Fin N → ℂ) where
  toFun x j := (q : ℂ) ^ j.val * x j
  invFun x j := ((q⁻¹ : ℂˣ) : ℂ) ^ j.val * x j
  left_inv x := by
    funext j
    change ((q⁻¹ : ℂˣ) : ℂ) ^ j.val * ((q : ℂ) ^ j.val * x j) = x j
    rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  right_inv x := by
    funext j
    change (q : ℂ) ^ j.val * (((q⁻¹ : ℂˣ) : ℂ) ^ j.val * x j) = x j
    rw [← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
  map_add' x y := by funext j; exact mul_add _ _ _
  map_smul' c x := by
    funext j
    change (q : ℂ) ^ j.val * (c * x j) = c * ((q : ℂ) ^ j.val * x j)
    ring

/-- The derivative clock gains one power of the dilation parameter. -/
theorem fockShift_dilation (N : ℕ) (q : ℂˣ) (x : Fin N → ℂ) :
    fockShiftLinear N (fockDilation N q x) =
      (q : ℂ) • fockDilation N q (fockShiftLinear N x) := by
  funext j
  change jetExt (fockDilation N q x) (j.val + 1) =
    (q : ℂ) * ((q : ℂ) ^ j.val * jetExt x (j.val + 1))
  by_cases hj : j.val + 1 < N
  · rw [jetExt_of_lt hj, jetExt_of_lt hj]
    change (q : ℂ) ^ (j.val + 1) * x ⟨_, hj⟩ = _
    rw [pow_succ]
    ring
  · rw [jetExt_of_le (Nat.le_of_not_gt hj), jetExt_of_le (Nat.le_of_not_gt hj),
      mul_zero, mul_zero]

/-- The nilpotent derivative clock admits every nonzero scale under similarity. -/
theorem fockDilation_symm_conj_shift (N : ℕ) (q : ℂˣ) :
    (fockDilation N q).symm.conj (fockShiftLinear N) = (q : ℂ) • fockShiftLinear N := by
  apply LinearMap.ext
  intro x
  change (fockDilation N q).symm (fockShiftLinear N (fockDilation N q x)) = _
  rw [fockShift_dilation, map_smul, LinearEquiv.symm_apply_apply]
  rfl

/-- The jet degree clock multiplies each coordinate by its order. -/
def fockNumberLinear (N : ℕ) : Module.End ℂ (Fin N → ℂ) where
  toFun x j := (j.val : ℂ) * x j
  map_add' x y := by funext j; exact mul_add _ _ _
  map_smul' c x := by
    funext j
    change (j.val : ℂ) * (c * x j) = c * ((j.val : ℂ) * x j)
    ring

/-- The degree clock is the source creation operator after the derivative clock. -/
theorem fockNumberLinear_apply (N : ℕ) (x : Fin N → ℂ) :
    fockNumberLinear N x = createOp (shiftOp x) := by
  funext j
  exact (createOp_shiftOp_apply x j).symm

theorem fockNumberLinear_coordOne (N : ℕ) :
    fockNumberLinear N (coordVec 1) = coordVec 1 := by
  funext j
  change (j.val : ℂ) * (if j.val = 1 then 1 else 0) = if j.val = 1 then 1 else 0
  by_cases hj : j.val = 1
  · simp only [hj, if_true, Nat.cast_one, one_mul]
  · simp only [if_neg hj, mul_zero]

/-- The first-order coordinate survives every power of the degree clock. -/
theorem fockNumberLinear_not_nilpotent (N : ℕ) (hN : 2 ≤ N) :
    ¬ IsNilpotent (fockNumberLinear N) := by
  rintro ⟨k, hk⟩
  have hp : ∀ k : ℕ, (fockNumberLinear N ^ k) (coordVec 1) = coordVec 1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, fockNumberLinear_coordOne, ih]
  have h := hp k
  rw [hk] at h
  have hz : (0 : ℂ) = 1 := by
    simpa only [LinearMap.zero_apply, Pi.zero_apply, coordVec, if_true] using
      congrFun h (⟨1, by omega⟩ : Fin N)
  exact zero_ne_one hz

/-- A nonzero degree clock has no nontrivial positive time scale under similarity. -/
theorem fockNumberLinear_scale_rigid (N : ℕ) (hN : 2 ≤ N)
    (e : (Fin N → ℂ) ≃ₗ[ℂ] (Fin N → ℂ)) (q : ℝ) (hq : 0 < q)
    (hscale : e.conj (fockNumberLinear N) = (q : ℂ) • fockNumberLinear N) : q = 1 :=
  (complex_conj_scale_eq_one_or_nilpotent e (fockNumberLinear N) q hq hscale).resolve_right
    (fockNumberLinear_not_nilpotent N hN)

/-- The degree clock has trace equal to the sum of its coordinate orders. -/
theorem fockNumberLinear_trace (N : ℕ) :
    LinearMap.trace ℂ (Fin N → ℂ) (fockNumberLinear N) = ∑ j : Fin N, (j.val : ℂ) := by
  have he : fockNumberLinear N = Matrix.toLin' (Matrix.diagonal (fun j : Fin N => (j.val : ℂ))) := by
    apply LinearMap.ext
    intro x
    funext j
    change (j.val : ℂ) * x j = (Matrix.diagonal (fun i : Fin N => (i.val : ℂ)) *ᵥ x) j
    rw [Matrix.mulVec_diagonal]
  rw [he, Matrix.trace_toLin'_eq]
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_apply_eq]

/-- In every nontrivial degree clock the trace is nonzero. -/
theorem fockNumberLinear_trace_ne_zero (N : ℕ) (hN : 2 ≤ N) :
    LinearMap.trace ℂ (Fin N → ℂ) (fockNumberLinear N) ≠ 0 := by
  have hp : 0 < ∑ j : Fin N, j.val := Finset.sum_pos'
    (fun _ _ => Nat.zero_le _) ⟨⟨1, by omega⟩, Finset.mem_univ _, Nat.zero_lt_one⟩
  rw [fockNumberLinear_trace]
  exact_mod_cast (Nat.ne_of_gt hp)

/-- Nonzero trace excludes even complex roots of unity as nontrivial scales. -/
theorem fockNumberLinear_complex_scale_rigid (N : ℕ) (hN : 2 ≤ N)
    (e : (Fin N → ℂ) ≃ₗ[ℂ] (Fin N → ℂ)) (q : ℂ)
    (hscale : e.conj (fockNumberLinear N) = q • fockNumberLinear N) : q = 1 := by
  have ht := congrArg (LinearMap.trace ℂ (Fin N → ℂ)) hscale
  rw [LinearMap.trace_conj', map_smul, smul_eq_mul] at ht
  apply mul_right_cancel₀ (fockNumberLinear_trace_ne_zero N hN)
  simpa only [one_mul] using ht.symm

/-- Exact complex scaling classification, including both dimensions where the clock vanishes. -/
theorem exists_fockNumberLinear_complex_scale_iff (N : ℕ) (q : ℂ) :
    (∃ e : (Fin N → ℂ) ≃ₗ[ℂ] (Fin N → ℂ),
      e.conj (fockNumberLinear N) = q • fockNumberLinear N) ↔ q = 1 ∨ N ≤ 1 := by
  constructor
  · rintro ⟨e, he⟩
    by_cases hN : 2 ≤ N
    · exact Or.inl (fockNumberLinear_complex_scale_rigid N hN e q he)
    · exact Or.inr (by omega)
  · intro h
    refine ⟨LinearEquiv.refl ℂ (Fin N → ℂ), ?_⟩
    rw [LinearEquiv.conj_refl]
    rcases h with rfl | hN
    · simp only [one_smul]
    · have hz : fockNumberLinear N = 0 := by
        apply LinearMap.ext
        intro x
        funext j
        have hj : j.val = 0 := by omega
        change (j.val : ℂ) * x j = 0
        rw [hj, Nat.cast_zero, zero_mul]
      rw [hz, smul_zero]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock

#print axioms GaloisForLFunctions.HTGeometry.GammaFactorialFock.fockDilation_symm_conj_shift
#print axioms GaloisForLFunctions.HTGeometry.GammaFactorialFock.fockNumberLinear_apply
#print axioms GaloisForLFunctions.HTGeometry.GammaFactorialFock.exists_fockNumberLinear_complex_scale_iff
#print axioms GaloisForLFunctions.HTGeometry.GammaFactorialFock.fockNumberLinear_scale_rigid
