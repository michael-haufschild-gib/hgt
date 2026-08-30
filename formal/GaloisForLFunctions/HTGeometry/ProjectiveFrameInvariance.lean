import GaloisForLFunctions.HTGeometry.DeterminantDerivation
import GaloisForLFunctions.HTGeometry.ProjectiveFrameCompanion

/-!
# Normalization and gauge invariance of the projective moving frame

Three facts about the normalized projective frame of a lift `v` with `δ^N v = ∑_j q_j δ^j v`:

* the trace of the companion matrix is the top coefficient `q_{N-1}`, so a frame of determinant one
  forces `q_{N-1} = 0` — this is the statement that the missing coefficient of the normalized
  Wilczynski relation is the logarithmic derivative of the Wronskian;
* a constant linear change of the homogeneous lift multiplies the frame on the left and leaves the
  relation, hence the coefficients, unchanged;
* when the frame is invertible the coefficients are uniquely determined by the lift.

Together these say the `q_j` are projective differential invariants of the lift.
-/

open scoped Differential
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F : Type*} [Field F] [Differential F]

/-! ### The trace of the companion matrix -/

omit [Differential F] in
/-- The trace of a companion matrix is its top coefficient. -/
theorem trace_companionMatrix {N : ℕ} (q : Fin N → F) (k : Fin N) (hk : (k : ℕ) + 1 = N) :
    (companionMatrix q).trace = q k := by
  classical
  rw [Matrix.trace, Finset.sum_eq_single k]
  · simp only [Matrix.diag_apply, companionMatrix, Matrix.of_apply]
    rw [if_neg (by omega)]
  · intro b _ hb
    have hblt : (b : ℕ) + 1 < N := by
      have h1 : (b : ℕ) < N := b.isLt
      have h2 : (b : ℕ) ≠ (k : ℕ) := fun h => hb (Fin.ext h)
      omega
    simp only [Matrix.diag_apply, companionMatrix, Matrix.of_apply]
    rw [if_pos hblt, if_neg (by omega)]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Entrywise form of the fundamental-matrix identity for the moving frame. -/
theorem deriv_frameMatrix_apply {N : ℕ} (v q : Fin N → F)
    (hrel : ∀ i, (vecDeriv^[N] v) i = ∑ j, q j * (vecDeriv^[(j : ℕ)] v) i) (i j : Fin N) :
    ((frameMatrix v) i j)′ = (frameMatrix v * companionMatrix q) i j := by
  have h := deriv_frameMatrix v q hrel
  have := congrFun (congrFun h i) j
  simpa using this

/-- **The normalized Wilczynski relation has no top coefficient.**  A moving frame of determinant
one forces the coefficient of `δ^{N-1} v` to vanish. -/
theorem top_coefficient_eq_zero_of_det_eq_one {N : ℕ} (v q : Fin N → F)
    (hrel : ∀ i, (vecDeriv^[N] v) i = ∑ j, q j * (vecDeriv^[(j : ℕ)] v) i)
    (hdet : (frameMatrix v).det = 1) (k : Fin N) (hk : (k : ℕ) + 1 = N) : q k = 0 := by
  have htr : (companionMatrix q).trace = 0 :=
    trace_eq_zero_of_det_eq_one (frameMatrix v) (companionMatrix q)
      (deriv_frameMatrix_apply v q hrel) hdet
  rw [trace_companionMatrix q k hk] at htr
  exact htr

/-! ### Constant gauge transformations of the lift -/

/-- A constant matrix commutes with componentwise differentiation of a vector. -/
theorem vecDeriv_mulVec {N : ℕ} (g : Matrix (Fin N) (Fin N) F)
    (hg : ∀ i j, (g i j)′ = 0) (v : Fin N → F) :
    vecDeriv (g *ᵥ v) = g *ᵥ vecDeriv v := by
  funext i
  show Differential.deriv (∑ k, g i k * v k) = ∑ k, g i k * Differential.deriv (v k)
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.leibniz, hg i k, smul_eq_mul, smul_zero, add_zero]

/-- A constant gauge transformation commutes with every iterated derivative of the lift. -/
theorem vecDeriv_iterate_mulVec {N : ℕ} (g : Matrix (Fin N) (Fin N) F)
    (hg : ∀ i j, (g i j)′ = 0) (v : Fin N → F) (m : ℕ) :
    vecDeriv^[m] (g *ᵥ v) = g *ᵥ vecDeriv^[m] v := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, vecDeriv_mulVec g hg v, ih]

/-- **The moving frame of a gauged lift is the gauged moving frame.** -/
theorem frameMatrix_mulVec {N : ℕ} (g : Matrix (Fin N) (Fin N) F)
    (hg : ∀ i j, (g i j)′ = 0) (v : Fin N → F) :
    frameMatrix (g *ᵥ v) = g * frameMatrix v := by
  ext i j
  simp only [frameMatrix, Matrix.of_apply, Matrix.mul_apply]
  rw [vecDeriv_iterate_mulVec g hg v]
  simp [Matrix.mulVec, dotProduct]

/-- **The Wilczynski coefficients are constant-gauge invariants.**  A constant linear change of the
homogeneous lift satisfies the same normalized relation. -/
theorem rel_mulVec_of_rel {N : ℕ} (g : Matrix (Fin N) (Fin N) F)
    (hg : ∀ i j, (g i j)′ = 0) (v q : Fin N → F)
    (hrel : ∀ i, (vecDeriv^[N] v) i = ∑ j, q j * (vecDeriv^[(j : ℕ)] v) i) :
    ∀ i, (vecDeriv^[N] (g *ᵥ v)) i = ∑ j, q j * (vecDeriv^[(j : ℕ)] (g *ᵥ v)) i := by
  intro i
  rw [vecDeriv_iterate_mulVec g hg v]
  simp only [Matrix.mulVec, dotProduct]
  have hleft : ∑ k, g i k * (vecDeriv^[N] v) k
      = ∑ k, g i k * ∑ j, q j * (vecDeriv^[(j : ℕ)] v) k :=
    Finset.sum_congr rfl fun k _ => by rw [hrel k]
  rw [hleft]
  have hswap : ∑ k, g i k * ∑ j, q j * (vecDeriv^[(j : ℕ)] v) k
      = ∑ j, q j * ∑ k, g i k * (vecDeriv^[(j : ℕ)] v) k := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hswap]
  exact Finset.sum_congr rfl fun j _ => by
    congr 1
    rw [vecDeriv_iterate_mulVec g hg v]
    simp [Matrix.mulVec, dotProduct]

/-! ### Uniqueness of the coefficients -/

/-- **The Wilczynski coefficients are determined by the lift** whenever the moving frame is
invertible. -/
theorem coefficients_unique {N : ℕ} (v q q' : Fin N → F) (hdet : IsUnit (frameMatrix v).det)
    (hrel : ∀ i, (vecDeriv^[N] v) i = ∑ j, q j * (vecDeriv^[(j : ℕ)] v) i)
    (hrel' : ∀ i, (vecDeriv^[N] v) i = ∑ j, q' j * (vecDeriv^[(j : ℕ)] v) i) : q = q' := by
  have hzero : frameMatrix v *ᵥ (q - q') = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.zero_apply, frameMatrix,
      Matrix.of_apply]
    have h1 : ∑ j : Fin N, (vecDeriv^[(j : ℕ)] v) i * (q j - q' j)
        = (∑ j : Fin N, q j * (vecDeriv^[(j : ℕ)] v) i)
          - ∑ j : Fin N, q' j * (vecDeriv^[(j : ℕ)] v) i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, ← hrel i, ← hrel' i, sub_self]
  have hinv : (frameMatrix v)⁻¹ *ᵥ (frameMatrix v *ᵥ (q - q')) = q - q' := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  rw [hzero, Matrix.mulVec_zero] at hinv
  funext i
  have h := congrFun hinv i
  simp only [Pi.zero_apply, Pi.sub_apply] at h
  exact sub_eq_zero.mp h.symm

end

end GaloisForLFunctions.HTGeometry
