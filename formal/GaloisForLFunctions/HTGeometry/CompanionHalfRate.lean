import GaloisForLFunctions.HTGeometry.TwistedChainRateIdentification
import GaloisForLFunctions.HTGeometry.InvertibleLeadingChainVanishes

/-!
# Exact half-integral rate of the companion witness

The invertible companion matrix of `t³ + ∂t + 1` loses its degree-one leading chain after one
step.  Restarting at two steps exposes a degree-one block whose leading matrix has a persistent
rank-two diagonal part.  Consequently the even powers have exact degree `n`, and their cofinal
subsequence identifies the full asymptotic twisted-chain rate as `1/2`.
-/

open scoped Differential
open Filter Topology

namespace GaloisForLFunctions.HTGeometry
namespace DiffOp

noncomputable section

set_option maxHeartbeats 1000000

variable {K : Type u} [Field K] [Differential K]

private theorem chainProd_const_eq_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι (DiffOp K)) (n : ℕ) :
    chainProd (K := K) (fun _ => C) n = C ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [chainProd_succ, ih, pow_succ]

/-- The two-step restart block of the companion witness. -/
def companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K) :=
  companionMatrix * companionMatrix

/-- Explicit form of the two-step restart block. -/
theorem companionSquare_eq :
    (companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) =
      !![0, -1, 0; 0, -partialElt, -1; 1, 0, -partialElt] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companionSquare, companionMatrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- The two-step restart block has operator-matrix degree one. -/
theorem matDeg_companionSquare :
    matDeg (companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) = 1 := by
  rw [companionSquare_eq]
  refine le_antisymm (matDeg_le fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;>
      simp [degree_zero, degree_one, degree_neg, degree_partialElt]
  · have h : degree
        ((!![0, -1, 0; 0, -partialElt, -1; 1, 0, -partialElt] :
          Matrix (Fin 3) (Fin 3) (DiffOp K)) 1 1) = 1 := by
      simp [degree_neg, degree_partialElt]
    have hle := degree_le_matDeg
      ((!![0, -1, 0; 0, -partialElt, -1; 1, 0, -partialElt] :
        Matrix (Fin 3) (Fin 3) (DiffOp K))) 1 1
    omega

/-- The restart block's leading matrix is diagonal of rank two. -/
theorem topCoeffMatrix_companionSquare :
    topCoeffMatrix (companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) 1 =
      !![0, 0, 0; 0, -1, 0; 0, 0, -1] := by
  rw [companionSquare_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [topCoeffMatrix, one_def, coeff_mono_of_ne]

private theorem companionSquare_leading_chain_entry (n : ℕ) :
    chainProdK (fun _ : ℕ =>
      topCoeffMatrix (companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) 1) n 1 1 =
        (-1 : K) ^ n := by
  rw [show (fun _ : ℕ =>
      topCoeffMatrix (companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) 1) =
      (fun _ : ℕ => (!![0, 0, 0; 0, -1, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K)) by
    funext _
    exact topCoeffMatrix_companionSquare]
  induction n with
  | zero => simp [chainProdK]
  | succ n ih =>
      rw [chainProdK_succ, Matrix.mul_apply]
      simp [Fin.sum_univ_three, ih, pow_succ]

private theorem companionSquare_leading_chain_ne_zero (n : ℕ) :
    chainProdK (fun _ : ℕ =>
      topCoeffMatrix (companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) 1) n ≠ 0 := by
  intro hzero
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 1) hzero
  rw [companionSquare_leading_chain_entry, Matrix.zero_apply] at hentry
  exact (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)) hentry

/-- Every power of the two-step restart block attains the expected degree. -/
theorem matDeg_companionSquare_pow (n : ℕ) :
    matDeg ((companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) ^ n) = n := by
  rw [← chainProd_const_eq_pow]
  simpa using matDeg_chainProd_eq
    (fun _ : ℕ => (companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K))) 1
    (fun _ i j => by
      have hle := degree_le_matDeg
        (companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) i j
      rw [matDeg_companionSquare (K := K)] at hle
      exact hle)
    companionSquare_leading_chain_ne_zero n

/-- The `2n`-th power of the companion matrix has exact degree `n`. -/
theorem matDeg_companionMatrix_even_pow (n : ℕ) :
    matDeg ((companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) ^ (2 * n)) = n := by
  rw [pow_mul]
  simpa only [companionSquare, pow_two] using
    matDeg_companionSquare_pow (K := K) n

private theorem topCoeffMatrix_companionSquare_pow_entry (n : ℕ) :
    topCoeffMatrix
      ((companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) ^ n) n 1 1 =
        (-1 : K) ^ n := by
  induction n with
  | zero =>
      have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 1)
        (topCoeffMatrix_one_zero (K := K) (ι := Fin 3))
      simpa [topCoeffMatrix] using h
  | succ n ih =>
      rw [pow_succ, topCoeffMatrix_mul]
      · rw [topCoeffMatrix_companionSquare]
        simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ]
        simpa only [topCoeffMatrix_apply] using ih
      · intro i j
        have h := degree_le_matDeg
          ((companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) ^ n) i j
        rwa [matDeg_companionSquare_pow] at h
      · intro i j
        have h := degree_le_matDeg
          (companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) i j
        rwa [matDeg_companionSquare] at h

private theorem companionSquare_pow_top_mul_companion_top_ne_zero (n : ℕ) :
    topCoeffMatrix
      ((companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) ^ n) n *
        topCoeffMatrix (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) 1 ≠ 0 := by
  intro hzero
  have hentry := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 2) hzero
  rw [Matrix.mul_apply, topCoeffMatrix_companionMatrix, Matrix.zero_apply] at hentry
  simp [Fin.sum_univ_three] at hentry
  have hlead := topCoeffMatrix_companionSquare_pow_entry (K := K) n
  rw [topCoeffMatrix_apply] at hlead
  rw [hlead] at hentry
  exact (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)) hentry

/-- The `(2n+1)`-st power of the companion matrix has exact degree `n+1`. -/
theorem matDeg_companionMatrix_odd_pow (n : ℕ) :
    matDeg ((companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) ^ (2 * n + 1)) =
      n + 1 := by
  have hpow :
      (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) ^ (2 * n + 1) =
        (companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) ^ n * companionMatrix := by
    rw [pow_add, pow_mul]
    simp only [pow_one, companionSquare, pow_two]
  rw [hpow]
  apply le_antisymm
  · exact (matDeg_mul_le _ _).trans_eq (by
      rw [matDeg_companionSquare_pow, matDeg_companionMatrix])
  · obtain ⟨i, j, hij⟩ := exists_degree_eq_of_topCoeffMatrix_mul_ne_zero
        ((companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) ^ n)
        (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) n 1
        (fun i j => by
          have h := degree_le_matDeg
            ((companionSquare : Matrix (Fin 3) (Fin 3) (DiffOp K)) ^ n) i j
          rwa [matDeg_companionSquare_pow] at h)
        (fun i j => by
          have h := degree_le_matDeg
            (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) i j
          rwa [matDeg_companionMatrix] at h)
        (companionSquare_pow_top_mul_companion_top_ne_zero n)
    rw [← hij]
    exact degree_le_matDeg _ i j

/-- Every companion power has the exact ceiling-half degree. -/
theorem matDeg_companionMatrix_pow (k : ℕ) :
    matDeg ((companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) ^ k) =
      (k + 1) / 2 := by
  rcases Nat.even_or_odd k with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · rw [show n + n = 2 * n by omega, matDeg_companionMatrix_even_pow]
    omega
  · rw [show 2 * n + 1 = 2 * n + 1 by rfl, matDeg_companionMatrix_odd_pow]
    omega

private theorem iterHom_id_private (n : ℕ) :
    iterHom (RingHom.id (DiffOp K)) n = RingHom.id (DiffOp K) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterHom_succ, ih, RingHom.id_comp]

private theorem twistedFamily_id_private
    (C : Matrix (Fin 3) (Fin 3) (DiffOp K)) (n : ℕ) :
    twistedFamily (RingHom.id (DiffOp K)) C n = C := by
  rw [twistedFamily, iterHom_id_private]
  ext i j
  rfl

private theorem twistedChain_id_eq_pow_private
    (C : Matrix (Fin 3) (Fin 3) (DiffOp K)) (n : ℕ) :
    twistedChain (RingHom.id (DiffOp K)) C n = C ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [twistedChain_succ, twistedFamily_id_private, ih, pow_succ]

/-- **The invertible companion witness has exact half-integral asymptotic degree rate.** -/
theorem twistedChainRate_companionMatrix :
    twistedChainRate (RingHom.id (DiffOp K)) (fun _ => rfl)
      (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) = (1 / 2 : ℝ) := by
  let hdeg : ∀ p : DiffOp K,
      degree ((RingHom.id (DiffOp K)) p) = degree p := fun _ => rfl
  have htwo : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    exact Filter.eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hsub := (tendsto_matDeg_twistedChain (RingHom.id (DiffOp K)) hdeg
    (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K))).comp htwo
  have heq : ((fun n : ℕ =>
      (matDeg (twistedChain (RingHom.id (DiffOp K))
        (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) n) : ℝ) / n) ∘
      (fun n : ℕ => 2 * n)) =ᶠ[atTop] (fun _ : ℕ => (1 / 2 : ℝ)) := by
    apply Filter.eventually_atTop.2
    refine ⟨1, fun n hn => ?_⟩
    change (matDeg (twistedChain (RingHom.id (DiffOp K))
      (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) (2 * n)) : ℝ) /
        ((2 * n : ℕ) : ℝ) = (1 / 2 : ℝ)
    have hchain := congrArg matDeg (twistedChain_id_eq_pow_private (K := K)
      (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) (2 * n))
    rw [matDeg_companionMatrix_even_pow (K := K)] at hchain
    have hchainR : (matDeg (twistedChain (RingHom.id (DiffOp K))
        (companionMatrix : Matrix (Fin 3) (Fin 3) (DiffOp K)) (2 * n)) : ℝ) = n := by
      exact_mod_cast hchain
    rw [hchainR]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    push_cast
    field_simp
  have hr := tendsto_nhds_unique_of_eventuallyEq hsub tendsto_const_nhds heq
  simpa [hdeg] using hr

end

end DiffOp
end GaloisForLFunctions.HTGeometry
