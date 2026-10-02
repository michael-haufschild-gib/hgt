import GaloisForLFunctions.RHTower.PrimeBurnolThetaModularHolonomy

/-!
# Two theta channels of the complete Burnol cubic

The same quarter turn complements the neutral and rotated theta projections while commuting
with the full prime-depth Gram. It therefore negates the density-weighted cubic. Each complete
prime-depth block is symmetric and traceless in its two theta coordinates, including off-diagonal
prime entries. Every prime-mixing reporter acting identically on both theta coordinates has zero
ordinary trace. The two remaining theta channels reconstruct the complete cubic matrix.
-/

open Matrix
open scoped Kronecker
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

private theorem framed_complement {A : Type*} [Ring A] (k p : A) (u : Aˣ)
    (hu : Commute k (u : A)) (hp : k * p = (1-p)*k) :
    k * sourceFramedElement u p = (1-sourceFramedElement u p)*k := by
  have hi := hu.units_inv_right
  dsimp only [sourceFramedElement]
  calc
    k * ((u : A)*p*(↑u⁻¹ : A)) = (u : A)*(k*p)*(↑u⁻¹ : A) := by
      rw [← mul_assoc, ← mul_assoc, hu.eq]
      simp only [mul_assoc]
    _ = (u : A)*((1-p)*k)*(↑u⁻¹ : A) := by rw [hp]
    _ = (u : A)*(1-p)*(k*(↑u⁻¹ : A)) := by simp only [mul_assoc]
    _ = (u : A)*(1-p)*((↑u⁻¹ : A)*k) := by rw [hi.eq]
    _ = (1-(u : A)*p*(↑u⁻¹ : A))*k := by
      simp [mul_sub, sub_mul, mul_assoc]

private theorem cube_anticommute {A : Type*} [Ring A] (k x : A)
    (h : k*x = -x*k) : k*x^3 = -(x^3)*k := by
  calc
    k*x^3 = ((k*x)*x)*x := by noncomm_ring
    _ = ((-x*k)*x)*x := by rw [h]
    _ = -x*(k*x)*x := by noncomm_ring
    _ = -x*(-x*k)*x := by rw [h]
    _ = (x*x)*(k*x) := by noncomm_ring
    _ = (x*x)*(-x*k) := by rw [h]
    _ = -(x^3)*k := by noncomm_ring

private theorem cubic_complement {A : Type*} [Ring A] (k r q p : A)
    (hr : k*r=(1-r)*k) (hq : k*q=(1-q)*k) (hp : k*p=(1-p)*k) :
    k*cubicProjectionAssociatorAlgebra r q p =
      -cubicProjectionAssociatorAlgebra r q p*k := by
  have h (x y : A) (hx : k*x=(1-x)*k) (hy : k*y=(1-y)*k) :
      k*(x-y)^3 = -((x-y)^3)*k := by
    apply cube_anticommute
    rw [mul_sub, hx, hy]
    noncomm_ring
  dsimp only [cubicProjectionAssociatorAlgebra]
  rw [mul_sub, mul_sub, h r p hr hp, h r q hr hq, h q p hq hp]
  noncomm_ring

/-- Quarter turn on the two theta coordinates. -/
def burnolThetaQuarterTurn : Matrix (Fin 2) (Fin 2) ℂ := !![0,-1;1,0]

/-- The quarter turn acts identically at every prime-depth label. -/
def burnolThetaQuarterTurnLift (N : ℕ) :
    Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ :=
  (1 : Matrix (Fin N) (Fin N) ℂ) ⊗ₖ burnolThetaQuarterTurn

private theorem quarter_left {N : ℕ}
    (A : Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ)
    (i j : Fin N) (r s : Fin 2) :
    (burnolThetaQuarterTurnLift N*A) (i,r) (j,s) =
      ∑ t : Fin 2, burnolThetaQuarterTurn r t * A (i,t) (j,s) := by
  simp [burnolThetaQuarterTurnLift, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, ite_mul]

private theorem quarter_right {N : ℕ}
    (A : Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ)
    (i j : Fin N) (r s : Fin 2) :
    (A*burnolThetaQuarterTurnLift N) (i,r) (j,s) =
      ∑ t : Fin 2, A (i,r) (j,t) * burnolThetaQuarterTurn t s := by
  simp [burnolThetaQuarterTurnLift, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite]

private theorem quarter_commutes_frame {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) :
    Commute (burnolThetaQuarterTurnLift N) (primeBurnolThetaFrameMatrix pe a) := by
  ext ⟨i,r⟩ ⟨j,s⟩
  rw [quarter_left, quarter_right]
  by_cases hij : i=j
  · subst j
    fin_cases r <;> fin_cases s <;>
      simp [Fin.sum_univ_two, burnolThetaQuarterTurn, primeBurnolThetaFrameMatrix,
        primeBurnolThetaBlock]
  · simp [primeBurnolThetaFrameMatrix, hij]

private theorem quarter_complements_neutral (N : ℕ) :
    burnolThetaQuarterTurnLift N * primeBurnolThetaNeutralProjection N =
      (1-primeBurnolThetaNeutralProjection N)*burnolThetaQuarterTurnLift N := by
  ext ⟨i,r⟩ ⟨j,s⟩
  rw [quarter_left, quarter_right]
  fin_cases r <;> fin_cases s <;>
    simp [Fin.sum_univ_two, burnolThetaQuarterTurn, primeBurnolThetaNeutralProjection,
      modularTwoBlockCornerProjection, Matrix.one_apply,
      Matrix.sub_apply]

private theorem quarter_commutes_prime_matrix {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) :
    Commute (burnolThetaQuarterTurnLift N) (G ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  dsimp only [Commute, SemiconjBy, burnolThetaQuarterTurnLift]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

/-- The complete density-weighted source cubic is odd under the theta quarter turn. -/
private theorem burnolTheta_weightedCubic_anticommute {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (a : ℝ) :
    let c := (primeBurnolDoubledGramUnit pe hpe kappa :
      Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ)
    burnolThetaQuarterTurnLift N * (c * primeBurnolThetaCubicDefect pe hpe kappa a) =
      -(c * primeBurnolThetaCubicDefect pe hpe kappa a) * burnolThetaQuarterTurnLift N := by
  let c := primeBurnolDoubledGramUnit pe hpe kappa
  let u := primeBurnolThetaFrameUnit pe a
  let p := primeBurnolThetaNeutralProjection N
  let q := sourceFramedElement u p
  let k := burnolThetaQuarterTurnLift N
  have hc : Commute k (c : Matrix _ _ ℂ) := by
    dsimp [k,c]
    rw [coe_primeBurnolDoubledGramUnit]
    exact quarter_commutes_prime_matrix _
  have hu : Commute k (u : Matrix _ _ ℂ) := quarter_commutes_frame pe a
  have hp : k*p=(1-p)*k := quarter_complements_neutral N
  have hq : k*q=(1-q)*k := framed_complement k p u hu hp
  have hr : k*sourceModularAutomorphism c q = (1-sourceModularAutomorphism c q)*k :=
    framed_complement k q c⁻¹ hc.units_inv_right hq
  have hC := cubic_complement k (sourceModularAutomorphism c q) q p hr hq hp
  change k*((c : Matrix _ _ ℂ)*cubicProjectionAssociatorAlgebra
    (sourceModularAutomorphism c q) q p) = _
  rw [← mul_assoc, hc.eq, mul_assoc, hC]
  simp only [mul_neg, neg_mul, mul_assoc]
  rfl

end
end RHTower

namespace RHTower
noncomputable section

/-- The full Burnol density times its theta-frame cubic defect. -/
def primeBurnolThetaWeightedCubic {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ)
    (kappa : Fin N → ℝ) (a : ℝ) :
    Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ :=
  (primeBurnolDoubledGramUnit pe pe.injective kappa : Matrix _ _ ℂ) *
    primeBurnolThetaCubicDefect pe pe.injective kappa a

/-- Opposite theta diagonal entries cancel separately for every pair of prime-depth labels. -/
theorem primeBurnolThetaWeightedCubic_diagonal {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ)
    (kappa : Fin N → ℝ) (a : ℝ) (i j : Fin N) :
    primeBurnolThetaWeightedCubic pe kappa a (i,1) (j,1) =
      -primeBurnolThetaWeightedCubic pe kappa a (i,0) (j,0) := by
  have h := congrArg (fun M : Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ =>
    M (i,0) (j,1)) (burnolTheta_weightedCubic_anticommute pe pe.injective kappa a)
  change (burnolThetaQuarterTurnLift N * primeBurnolThetaWeightedCubic pe kappa a)
    (i,0) (j,1) =
    (-primeBurnolThetaWeightedCubic pe kappa a * burnolThetaQuarterTurnLift N)
      (i,0) (j,1) at h
  rw [quarter_left, quarter_right] at h
  simp [Fin.sum_univ_two, burnolThetaQuarterTurn] at h
  linear_combination -h

/-- The two off-diagonal theta channels agree at each complete prime-depth matrix entry. -/
theorem primeBurnolThetaWeightedCubic_offDiagonal {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ)
    (kappa : Fin N → ℝ) (a : ℝ) (i j : Fin N) :
    primeBurnolThetaWeightedCubic pe kappa a (i,1) (j,0) =
      primeBurnolThetaWeightedCubic pe kappa a (i,0) (j,1) := by
  have h := congrArg (fun M : Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ =>
    M (i,0) (j,0)) (burnolTheta_weightedCubic_anticommute pe pe.injective kappa a)
  change (burnolThetaQuarterTurnLift N * primeBurnolThetaWeightedCubic pe kappa a)
    (i,0) (j,0) =
    (-primeBurnolThetaWeightedCubic pe kappa a * burnolThetaQuarterTurnLift N)
      (i,0) (j,0) at h
  rw [quarter_left, quarter_right] at h
  simpa [Fin.sum_univ_two, burnolThetaQuarterTurn] using h

/-- Exact two-channel form, with no prime or depth entry discarded. -/
theorem primeBurnolThetaWeightedCubic_block {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ)
    (kappa : Fin N → ℝ) (a : ℝ) (i j : Fin N) :
    (fun r s : Fin 2 => primeBurnolThetaWeightedCubic pe kappa a (i,r) (j,s)) =
      !![primeBurnolThetaWeightedCubic pe kappa a (i,0) (j,0),
        primeBurnolThetaWeightedCubic pe kappa a (i,0) (j,1);
        primeBurnolThetaWeightedCubic pe kappa a (i,0) (j,1),
        -primeBurnolThetaWeightedCubic pe kappa a (i,0) (j,0)] := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp
  · exact primeBurnolThetaWeightedCubic_offDiagonal pe kappa a i j
  · exact primeBurnolThetaWeightedCubic_diagonal pe kappa a i j

/-- Every theta-neutral prime-mixing reporter has zero ordinary cubic trace. -/
theorem primeBurnolTheta_primeMatrix_trace_eq_zero {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ)
    (kappa : Fin N → ℝ) (a : ℝ) (W : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.trace ((W ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      primeBurnolThetaWeightedCubic pe kappa a) = 0 := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply]
  simp only [ite_true, mul_one]
  simp_rw [primeBurnolThetaWeightedCubic_diagonal pe kappa a]
  simp

/-- Any matrix reporter sees exactly two theta channels of the complete source current. -/
theorem primeBurnolThetaWeightedCubic_trace_pairing {N : ℕ}
    (pe : Fin N ↪ Nat.Primes × ℕ) (kappa : Fin N → ℝ) (a : ℝ)
    (E : Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) :
    Matrix.trace (E * primeBurnolThetaWeightedCubic pe kappa a) =
      Finset.univ.sum (fun i : Fin N => Finset.univ.sum (fun j : Fin N =>
        (E (i,0) (j,0) - E (i,1) (j,1)) *
            primeBurnolThetaWeightedCubic pe kappa a (j,0) (i,0) +
        (E (i,0) (j,1) + E (i,1) (j,0)) *
            primeBurnolThetaWeightedCubic pe kappa a (j,0) (i,1))) := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.mul_apply]
  simp_rw [primeBurnolThetaWeightedCubic_diagonal pe kappa a,
    primeBurnolThetaWeightedCubic_offDiagonal pe kappa a]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end RHTower
