import GaloisForLFunctions.HTGeometry.CofinalCholeskyFiniteFrame

/-!
# Bounded-realization comparison of finite packet capacities

Scalar minimum-response comparison upgrades to an exact two-sided Loewner comparison for every
finite Hermitian response packet.  The resulting multiplicative order bound is precisely the
finite-bound content of the Thompson metric.  This file also records positivity of the concrete
inverse-Cholesky packet capacity and the coordinate-cocycle descent law.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix
open scoped ComplexOrder

noncomputable section

/-- Loewner order on finite complex Hermitian matrices. -/
def Matrix.LoewnerLE {n : Type*} [Fintype n]
    (K L : Matrix n n ℂ) : Prop :=
  (L - K).PosSemidef

/-- A finite two-sided multiplicative Loewner bound.  This is the order-theoretic content of a
finite Thompson-distance bound. -/
def Matrix.HasTwoSidedMultiplicativeBound {n : Type*} [Fintype n]
    (K L : Matrix n n ℂ) (c d : ℝ) : Prop :=
  Matrix.LoewnerLE L ((c : ℂ) • K) ∧
    Matrix.LoewnerLE K ((d : ℂ) • L)

theorem Matrix.loewnerLE_smul_of_quadratic_bound
    {n : Type*} [Fintype n]
    (K L : Matrix n n ℂ) (hK : K.IsHermitian) (hL : L.IsHermitian)
    (c : ℝ)
    (hbound : ∀ x : n → ℂ,
      star x ⬝ᵥ (L *ᵥ x) ≤ (c : ℂ) * (star x ⬝ᵥ (K *ᵥ x))) :
    Matrix.LoewnerLE L ((c : ℂ) • K) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (hK.smul (Complex.conj_ofReal c)).sub hL
  · intro x
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul]
    exact sub_nonneg.mpr (hbound x)

/-- Exact two-sided Loewner comparison of packet capacity forms under a bounded
response-intertwining equivalence. -/
theorem minimumResponseCapacity_loewnerComparison
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {r : ℕ}
    (e : E ≃L[ℂ] F)
    (A : E → (Fin r → ℂ)) (B : F → (Fin r → ℂ))
    (hresp : ∀ x, B (e x) = A x)
    (mE : (Fin r → ℂ) → E) (mF : (Fin r → ℂ) → F)
    (hEresp : ∀ t, A (mE t) = t)
    (hFresp : ∀ t, B (mF t) = t)
    (hEmin : ∀ t x, A x = t → ‖mE t‖ ≤ ‖x‖)
    (hFmin : ∀ t x, B x = t → ‖mF t‖ ≤ ‖x‖)
    (KE KF : Matrix (Fin r) (Fin r) ℂ)
    (hKE : KE.IsHermitian) (hKF : KF.IsHermitian)
    (henergyE : ∀ t, star t ⬝ᵥ (KE *ᵥ t) = (‖mE t‖ ^ 2 : ℝ))
    (henergyF : ∀ t, star t ⬝ᵥ (KF *ᵥ t) = (‖mF t‖ ^ 2 : ℝ)) :
    Matrix.LoewnerLE KF ((((‖(e : E →L[ℂ] F)‖ ^ 2 : ℝ)) : ℂ) • KE) ∧
      Matrix.LoewnerLE KE ((((‖(e.symm : F →L[ℂ] E)‖ ^ 2 : ℝ)) : ℂ) • KF) := by
  let cE : ℝ := ‖(e : E →L[ℂ] F)‖ ^ 2
  let cF : ℝ := ‖(e.symm : F →L[ℂ] E)‖ ^ 2
  change Matrix.LoewnerLE KF ((cE : ℂ) • KE) ∧
    Matrix.LoewnerLE KE ((cF : ℂ) • KF)
  constructor
  · have hbound : ∀ t : Fin r → ℂ,
        star t ⬝ᵥ (KF *ᵥ t) ≤
          (cE : ℂ) * (star t ⬝ᵥ (KE *ᵥ t)) := by
      intro t
      have hnorm := (minimumResponseNorm_boundedComparison e A B hresp mE mF
        hEresp hFresp hEmin hFmin t).1
      have hsq : ‖mF t‖ ^ 2 ≤ ‖(e : E →L[ℂ] F)‖ ^ 2 * ‖mE t‖ ^ 2 := by
        calc
          ‖mF t‖ ^ 2 ≤ (‖(e : E →L[ℂ] F)‖ * ‖mE t‖) ^ 2 :=
            (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
          _ = ‖(e : E →L[ℂ] F)‖ ^ 2 * ‖mE t‖ ^ 2 := by ring
      rw [henergyE, henergyF]
      dsimp [cE]
      exact_mod_cast hsq
    exact Matrix.loewnerLE_smul_of_quadratic_bound KE KF hKE hKF cE hbound
  · have hbound : ∀ t : Fin r → ℂ,
        star t ⬝ᵥ (KE *ᵥ t) ≤
          (cF : ℂ) * (star t ⬝ᵥ (KF *ᵥ t)) := by
      intro t
      have hnorm := (minimumResponseNorm_boundedComparison e A B hresp mE mF
        hEresp hFresp hEmin hFmin t).2
      have hsq : ‖mE t‖ ^ 2 ≤ ‖(e.symm : F →L[ℂ] E)‖ ^ 2 * ‖mF t‖ ^ 2 := by
        calc
          ‖mE t‖ ^ 2 ≤ (‖(e.symm : F →L[ℂ] E)‖ * ‖mF t‖) ^ 2 :=
            (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
          _ = ‖(e.symm : F →L[ℂ] E)‖ ^ 2 * ‖mF t‖ ^ 2 := by ring
      rw [henergyE, henergyF]
      dsimp [cF]
      exact_mod_cast hsq
    exact Matrix.loewnerLE_smul_of_quadratic_bound KF KE hKF hKE cF hbound

/-- The same theorem packaged as a finite two-sided multiplicative order bound. -/
theorem minimumResponseCapacity_hasTwoSidedMultiplicativeBound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {r : ℕ}
    (e : E ≃L[ℂ] F)
    (A : E → (Fin r → ℂ)) (B : F → (Fin r → ℂ))
    (hresp : ∀ x, B (e x) = A x)
    (mE : (Fin r → ℂ) → E) (mF : (Fin r → ℂ) → F)
    (hEresp : ∀ t, A (mE t) = t)
    (hFresp : ∀ t, B (mF t) = t)
    (hEmin : ∀ t x, A x = t → ‖mE t‖ ≤ ‖x‖)
    (hFmin : ∀ t x, B x = t → ‖mF t‖ ≤ ‖x‖)
    (KE KF : Matrix (Fin r) (Fin r) ℂ)
    (hKE : KE.IsHermitian) (hKF : KF.IsHermitian)
    (henergyE : ∀ t, star t ⬝ᵥ (KE *ᵥ t) = (‖mE t‖ ^ 2 : ℝ))
    (henergyF : ∀ t, star t ⬝ᵥ (KF *ᵥ t) = (‖mF t‖ ^ 2 : ℝ)) :
    Matrix.HasTwoSidedMultiplicativeBound KE KF
      (‖(e : E →L[ℂ] F)‖ ^ 2) (‖(e.symm : F →L[ℂ] E)‖ ^ 2) :=
  minimumResponseCapacity_loewnerComparison e A B hresp mE mF hEresp hFresp
    hEmin hFmin KE KF hKE hKF henergyE henergyF

/-- Every finite packet capacity matrix is positive semidefinite. -/
theorem inverseCholeskyPacketCapacity_posSemidef {N r : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (target : Fin N → Fin r → ℂ) :
    (inverseCholeskyPacketCapacity C target).PosSemidef := by
  rw [inverseCholeskyPacketCapacity_eq_conjTranspose_mul]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Congruence covariance satisfies the exact coordinate-cocycle descent law. -/
theorem capacityCongruence_cocycle {r s t : ℕ}
    (K : Matrix (Fin r) (Fin r) ℂ)
    (Rab : Matrix (Fin r) (Fin s) ℂ)
    (Rbc : Matrix (Fin s) (Fin t) ℂ)
    (Rac : Matrix (Fin r) (Fin t) ℂ)
    (hcocycle : Rab * Rbc = Rac) :
    Rbcᴴ * (Rabᴴ * K * Rab) * Rbc = Racᴴ * K * Rac := by
  calc
    Rbcᴴ * (Rabᴴ * K * Rab) * Rbc = (Rab * Rbc)ᴴ * K * (Rab * Rbc) := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = Racᴴ * K * Rac := by rw [hcocycle]

end

end GaloisForLFunctions.HTGeometry
