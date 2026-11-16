import GaloisForLFunctions.HTGeometry.RiemannGaussian.HermitianRankTrace.TracefreeAperture
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.AThinEndIsLogarithmicallyStiffAndAFloorExtendsTheBoundRange

/-!
# Trace-free target stress in every domain and target dimension

Stacking symmetric trace-free Hessians transfers the scalar spectral aperture
into the target space. In domain dimension `n`, the target stress is bounded
by `(n - 1)/n` times its trace. The symmetric trace-free parts are constructed
from arbitrary input matrices, so the final bound needs no symmetry or trace
premise. This is the target-stress mechanism of Luchese's Theorem 3
(https://arxiv.org/abs/2611.17317).
-/

open Matrix Finset RiemannGaussian.HermitianRankTrace
open scoped BigOperators ComplexOrder

namespace HTGeometry.TracefreeFamilyStress
noncomputable section

variable {N : ℕ}

/-- The trace-free symmetric part, scaled by the domain dimension to avoid division. -/
def centered (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (N + 1 : ℝ) • (A + Aᵀ) - (A + Aᵀ).trace • 1

theorem centered_isHermitian (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    (centered A).IsHermitian := by
  change (centered A)ᴴ = centered A
  simp only [conjTranspose_eq_transpose_of_trivial, centered, transpose_sub,
    transpose_smul, transpose_add, transpose_transpose, transpose_one]
  rw [add_comm Aᵀ A]

theorem centered_trace (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    (centered A).trace = 0 := by
  simp only [centered, trace_sub, trace_smul, trace_one, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one, smul_eq_mul]
  ring

variable {J : Type*} [Fintype J]

/-- Hessian columns stacked over every target component. -/
def frame (A : J → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    Matrix (J × Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun ji k => centered (A ji.1) ji.2 k

/-- Total squared Hessian energy. -/
def energy (A : J → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  ∑ j, frobSq (centered (A j))

/-- The full target Gram matrix. -/
def stress (A : J → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    Matrix (J × Fin (N + 1)) (J × Fin (N + 1)) ℝ := frame A * (frame A)ᵀ

theorem energy_nonneg (A : J → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    0 ≤ energy A := by
  apply sum_nonneg
  intro j _
  rw [frobSq_hermitian_eq_sum_sq_eigenvalues (centered_isHermitian (A j))]
  exact sum_nonneg fun _ _ => sq_nonneg _

theorem stress_trace (A : J → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    (stress A).trace = energy A := by
  change (∑ ji : J × Fin (N + 1), ∑ k, centered (A ji.1) ji.2 k *
      centered (A ji.1) ji.2 k) =
    ∑ j, ∑ k, ∑ i, centered (A j) i k * centered (A j) i k
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro j _
  exact sum_comm

private theorem centered_vector_bound (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (e : Fin (N + 1) → ℝ) :
    (N + 1 : ℝ) * ((centered A *ᵥ e) ⬝ᵥ (centered A *ᵥ e)) ≤
      (N : ℝ) * frobSq (centered A) * (e ⬝ᵥ e) := by
  have h := tracefree_aperture (centered_isHermitian A) (centered_trace A)
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at h
  have hd := h.dotProduct_mulVec_nonneg e
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, conjTranspose_eq_transpose_of_trivial] at hd
  have he : e ⬝ᵥ (((centered A)ᵀ * centered A) *ᵥ e) =
      (centered A *ᵥ e) ⬝ᵥ (centered A *ᵥ e) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.transpose_transpose]
  rw [he] at hd
  exact sub_nonneg.mp hd

/-- The dimension-improved operator bound in the original domain. -/
theorem domain_bound (A : J → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (e : Fin (N + 1) → ℝ) :
    (frame A *ᵥ e) ⬝ᵥ (frame A *ᵥ e) ≤
      ((N : ℝ) / (N + 1) * energy A) * (e ⬝ᵥ e) := by
  have hsum := sum_le_sum (fun j (_ : j ∈ (univ : Finset J)) => centered_vector_bound (A j) e)
  have he : (frame A *ᵥ e) ⬝ᵥ (frame A *ᵥ e) =
      ∑ j, (centered (A j) *ᵥ e) ⬝ᵥ (centered (A j) *ᵥ e) := by
    simp only [dotProduct, Matrix.mulVec, frame, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul] at hsum
  rw [← he] at hsum
  have hn : (0 : ℝ) < N + 1 := by positivity
  have hc : ((N : ℝ) / (N + 1) * energy A) * (e ⬝ᵥ e) =
      ((N : ℝ) * energy A * (e ⬝ᵥ e)) / (N + 1) := by ring
  rw [hc, le_div_iff₀ hn]
  simpa only [energy, mul_comm ((frame A *ᵥ e) ⬝ᵥ (frame A *ᵥ e))] using hsum

/-- Cauchy--Schwarz transfers the domain bound to the target without a rank assumption. -/
theorem target_bound (A : J → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (m : J × Fin (N + 1) → ℝ) :
    ((frame A)ᵀ *ᵥ m) ⬝ᵥ ((frame A)ᵀ *ᵥ m) ≤
      ((N : ℝ) / (N + 1) * energy A) * (m ⬝ᵥ m) := by
  have hc : 0 ≤ (N : ℝ) / (N + 1) * energy A :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity)) (energy_nonneg A)
  have hP (v : J × Fin (N + 1) → ℝ) (e : Fin (N + 1) → ℝ) :
      (v ⬝ᵥ (frame A *ᵥ e))^2 ≤
        (Real.sqrt ((N : ℝ) / (N + 1) * energy A))^2 * ((v ⬝ᵥ v) * (e ⬝ᵥ e)) := by
    have hcs : (v ⬝ᵥ (frame A *ᵥ e))^2 ≤
        (v ⬝ᵥ v) * ((frame A *ᵥ e) ⬝ᵥ (frame A *ᵥ e)) := by
      simpa only [dotProduct, pow_two] using
        Finset.sum_mul_sq_le_sq_mul_sq univ v (frame A *ᵥ e)
    have hv : 0 ≤ v ⬝ᵥ v := dotProduct_self_star_nonneg (v := v)
    refine (hcs.trans (mul_le_mul_of_nonneg_left (domain_bound A e) hv)).trans_eq ?_
    rw [Real.sq_sqrt hc]
    ring
  simpa only [Real.sq_sqrt hc] using
    GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.transpose_mulVec_sq_le hP m

variable [DecidableEq J]

/-- The normalized positive target complement. -/
theorem normalized_aperture (A : J → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ((((N : ℝ) / (N + 1) * energy A) •
      (1 : Matrix (J × Fin (N + 1)) (J × Fin (N + 1)) ℝ)) - stress A).PosSemidef := by
  have hs : (stress A).IsHermitian := by
    simpa only [stress, conjTranspose_eq_transpose_of_trivial] using
      isHermitian_mul_conjTranspose_self (frame A)
  have hc : (((N : ℝ) / (N + 1) * energy A) •
      (1 : Matrix (J × Fin (N + 1)) (J × Fin (N + 1)) ℝ)).IsHermitian :=
    isHermitian_one.smul (by change star _ = _; exact star_trivial _)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc.sub hs)
  intro m
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have he : m ⬝ᵥ (stress A *ᵥ m) = ((frame A)ᵀ *ᵥ m) ⬝ᵥ ((frame A)ᵀ *ᵥ m) := by
    rw [stress, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  rw [he]
  exact sub_nonneg.mpr (target_bound A m)

/-- Target stress pays the sharp trace-free fraction in every dimension. -/
theorem stress_aperture (A : J → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    (((N : ℝ) * (stress A).trace) •
        (1 : Matrix (J × Fin (N + 1)) (J × Fin (N + 1)) ℝ) -
      (N + 1 : ℝ) • stress A).PosSemidef := by
  have h := (normalized_aperture A).smul (show (0 : ℝ) ≤ N + 1 by positivity)
  rw [smul_sub, smul_smul] at h
  have hc : (N + 1 : ℝ) * ((N : ℝ) / (N + 1) * energy A) = (N : ℝ) * energy A := by
    have hn : (N + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hc] at h
  simpa only [stress_trace] using h

#print axioms stress_aperture

end
end HTGeometry.TracefreeFamilyStress
