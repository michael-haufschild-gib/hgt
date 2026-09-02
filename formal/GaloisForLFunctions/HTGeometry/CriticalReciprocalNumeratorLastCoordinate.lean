import GaloisForLFunctions.HTGeometry.CriticalReciprocalNumerator

/-!
# Last-coordinate linearity of reciprocal numerators

The cleared `k`-th reciprocal coefficient only uses raw coordinates through index `k`, and its
dependence on the last coordinate is affine-linear.  At `x₀ = 1`, changing `x_k` by `d` changes
the reciprocal numerator by `-d`.  This triangular identity gives literal raw-coordinate
meridians around either marked divisor.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- The `k`-th cleared reciprocal numerator depends only on coordinates of index at most `k`. -/
theorem aeval_criticalReciprocalNumerator_congr_le
    (K : Type*) [Field K] {L k : ℕ} (hk : k < L)
    (v w : Fin L → K)
    (h : ∀ i : Fin L, (i : ℕ) ≤ k → v i = w i) :
    MvPolynomial.aeval v (criticalReciprocalNumerator K L k) =
      MvPolynomial.aeval w (criticalReciprocalNumerator K L k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | k
      · simp [criticalReciprocalNumerator]
      · rw [criticalReciprocalNumerator, map_neg, map_neg, map_sum, map_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        simp only [map_mul, map_pow]
        have hxi : (i : ℕ) + 1 < L := by omega
        have hx0 : 0 < L := by omega
        simp only [finiteRawX, dif_pos hxi, dif_pos hx0,
          MvPolynomial.aeval_X]
        have hcoord : v ⟨(i : ℕ) + 1, hxi⟩ = w ⟨(i : ℕ) + 1, hxi⟩ :=
          h _ (by simp; omega)
        have hzero : v ⟨0, hx0⟩ = w ⟨0, hx0⟩ := h _ (by simp)
        rw [hcoord, hzero]
        rw [ih (k - (i : ℕ)) (by omega) (by omega)]
        intro j hj
        exact h j (le_trans hj (by omega))

/-- The `k+1`-st cleared reciprocal numerator is affine-linear in the `k+1`-st raw
coordinate, with coefficient `-x₀^k`. -/
theorem aeval_criticalReciprocalNumerator_update_last
    (K : Type*) [Field K] {L k : ℕ} (hk : k + 1 < L)
    (v : Fin L → K) :
    let j : Fin L := ⟨k + 1, hk⟩
    let w : Fin L → K := fun i ↦ if i = j then 0 else v i
    MvPolynomial.aeval v (criticalReciprocalNumerator K L (k + 1)) =
      MvPolynomial.aeval w (criticalReciprocalNumerator K L (k + 1)) -
        v j * v ⟨0, by omega⟩ ^ k := by
  dsimp only
  set j : Fin L := ⟨k + 1, hk⟩ with hj
  set w : Fin L → K := (fun i ↦ if i = j then 0 else v i) with hw
  have hw_le : ∀ i : Fin L, (i : ℕ) ≤ k → v i = w i := by
    intro i hi
    rw [hw]
    simp only
    rw [if_neg]
    intro hij
    have := congrArg Fin.val hij
    simp only [j] at this
    omega
  have hprefix :
      ∑ i : Fin k,
          MvPolynomial.aeval v (finiteRawX K L ((i.castSucc : ℕ) + 1)) *
              MvPolynomial.aeval v
                (criticalReciprocalNumerator K L (k - (i.castSucc : ℕ))) *
                MvPolynomial.aeval v (finiteRawX K L 0) ^ (i.castSucc : ℕ) =
        ∑ i : Fin k,
          MvPolynomial.aeval w (finiteRawX K L ((i.castSucc : ℕ) + 1)) *
              MvPolynomial.aeval w
                (criticalReciprocalNumerator K L (k - (i.castSucc : ℕ))) *
                MvPolynomial.aeval w (finiteRawX K L 0) ^ (i.castSucc : ℕ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hxi : (i.castSucc : ℕ) + 1 < L := by omega
    have hx0 : 0 < L := by omega
    simp only [finiteRawX, dif_pos hxi, dif_pos hx0, MvPolynomial.aeval_X]
    have hcoord : v ⟨(i.castSucc : ℕ) + 1, hxi⟩ =
        w ⟨(i.castSucc : ℕ) + 1, hxi⟩ := hw_le _ (by
          change (i : ℕ) + 1 ≤ k
          omega)
    have hzero : v ⟨0, hx0⟩ = w ⟨0, hx0⟩ := hw_le _ (by simp)
    rw [hcoord, hzero,
      aeval_criticalReciprocalNumerator_congr_le K (by omega) v w]
    intro a ha
    exact hw_le a (le_trans ha (by omega))
  rw [criticalReciprocalNumerator, map_neg, map_sum, map_neg, map_sum]
  simp only [map_mul, map_pow]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hprefix]
  have hx0 : 0 < L := by omega
  simp only [Fin.val_last, Nat.sub_self, criticalReciprocalNumerator, map_one,
    finiteRawX, dif_pos hk, dif_pos hx0, MvPolynomial.aeval_X]
  have hwj : w j = 0 := by simp [hw]
  have hw0 : w ⟨0, hx0⟩ = v ⟨0, hx0⟩ := by
    symm
    exact hw_le _ (by simp)
  change -(_ + v j * 1 * v ⟨0, hx0⟩ ^ k) =
    -(_ + w j * 1 * w ⟨0, hx0⟩ ^ k) - v j * v ⟨0, hx0⟩ ^ k
  rw [hwj, hw0]
  ring

/-- Positive-index form of last-coordinate linearity, indexed directly by the changed
coordinate. -/
theorem aeval_criticalReciprocalNumerator_update_index
    (K : Type*) [Field K] {L k : ℕ} (hk0 : 0 < k) (hk : k < L)
    (v : Fin L → K) :
    let j : Fin L := ⟨k, hk⟩
    let w : Fin L → K := fun i ↦ if i = j then 0 else v i
    MvPolynomial.aeval v (criticalReciprocalNumerator K L k) =
      MvPolynomial.aeval w (criticalReciprocalNumerator K L k) -
        v j * v ⟨0, by omega⟩ ^ (k - 1) := by
  have hsucc : k - 1 + 1 = k := by omega
  simpa only [hsucc] using
    (aeval_criticalReciprocalNumerator_update_last K (k := k - 1) (by omega) v)

end

end GaloisForLFunctions.HTGeometry
