import GaloisForLFunctions.HTGeometry.SiegelFiniteness

/-!
# The Jacobi decomposition is determined by the form

Reading `A = Uᵀ D U` at the entry `(i, j)` and separating the diagonal term gives

`dᵢ Uᵢⱼ = Aᵢⱼ − Σ_{m < i} dₘ Uₘᵢ Uₘⱼ`,

a recursion that computes the unipotent factor row by row from the form and the diagonal.  Since the
diagonal is already determined by the leading minors, the whole decomposition is determined, and the
recursion is what makes it depend continuously on the form.

* `JacobiData.form_apply` : the entries of the form.
* `JacobiData.ldl_recursion` : **the recursion.**
* `JacobiData.U_unique` : **the unipotent factor is determined by the form.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The entries of a Jacobi form. -/
theorem JacobiData.form_apply (J : JacobiData n) (i j : Fin n) :
    J.form i j = ∑ m, J.d m * J.U m i * J.U m j := by
  classical
  have hmul : ∀ a b : Fin n, (J.Uᵀ * Matrix.diagonal J.d) a b = J.U b a * J.d b := by
    intro a b
    rw [Matrix.mul_apply,
      Finset.sum_eq_single b (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
        (fun hcon => absurd (Finset.mem_univ b) hcon),
      Matrix.transpose_apply, Matrix.diagonal_apply_eq]
  show (J.Uᵀ * Matrix.diagonal J.d * J.U) i j = _
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hmul]
  ring

/-- **The recursion computing the unipotent factor from the form.** -/
theorem JacobiData.ldl_recursion (J : JacobiData n) (i j : Fin n) :
    J.d i * J.U i j
      = J.form i j
        - ∑ m ∈ Finset.univ.filter (fun m : Fin n => m < i), J.d m * J.U m i * J.U m j := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
    (fun m : Fin n => m < i) (fun m => J.d m * J.U m i * J.U m j)
  have htail : (∑ m ∈ Finset.univ.filter (fun m : Fin n => ¬ m < i),
      J.d m * J.U m i * J.U m j) = J.d i * J.U i j := by
    refine (Finset.sum_eq_single i (fun m hm hmi => ?_) (fun hcon => ?_)).trans ?_
    · rw [Finset.mem_filter] at hm
      have hlt : i < m := lt_of_le_of_ne (not_lt.1 hm.2) (Ne.symm hmi)
      rw [J.upper m i hlt, mul_zero, zero_mul]
    · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ i, by simp⟩) hcon
    · rw [J.unit i, mul_one]
  rw [J.form_apply i j, ← hsplit, htail]
  ring

/-- **The unipotent factor is determined by the form.** -/
theorem JacobiData.U_unique {J J' : JacobiData n} (hform : J.form = J'.form) : J.U = J'.U := by
  classical
  have hd : J.d = J'.d := JacobiData.d_unique hform
  have key : ∀ k : ℕ, ∀ i : Fin n, (i : ℕ) = k → ∀ j : Fin n, J.U i j = J'.U i j := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
        intro i hi j
        have hrec := J.ldl_recursion i j
        have hrec' := J'.ldl_recursion i j
        have hsum : (∑ m ∈ Finset.univ.filter (fun m : Fin n => m < i),
              J.d m * J.U m i * J.U m j)
            = ∑ m ∈ Finset.univ.filter (fun m : Fin n => m < i),
              J'.d m * J'.U m i * J'.U m j := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [Finset.mem_filter] at hm
          have hmk : (m : ℕ) < k := by
            have := Fin.lt_def.1 hm.2
            omega
          rw [ih (m : ℕ) hmk m rfl i, ih (m : ℕ) hmk m rfl j, hd]
        have hdi : J.d i = J'.d i := by rw [hd]
        have h1 : J.d i * J.U i j = J'.d i * J'.U i j := by
          rw [hrec, hrec', hform, hsum]
        rw [hdi] at h1
        exact mul_left_cancel₀ (ne_of_gt (J'.pos i)) h1
  funext i j
  exact key (i : ℕ) i rfl j

end GaloisForLFunctions.HTGeometry
