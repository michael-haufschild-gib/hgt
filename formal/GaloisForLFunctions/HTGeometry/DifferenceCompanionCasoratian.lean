import GaloisForLFunctions.HTGeometry.DifferenceSolutionSpace

/-!
# The companion matrix of a scalar difference equation is invertible in every rank

A scalar linear difference equation of order `n` is turned into a first-order system by its
companion matrix, and the whole difference Galois theory of the equation needs that system to be
invertible.  This holds in every rank exactly when the trailing coefficient is nonzero: the
companion matrix shifts coordinates up and reads the equation off in the last row, so its kernel is
determined by the trailing coefficient alone.

The corpus previously had this only for rank two, computed from the explicit `2 x 2` determinant.
Here it is proved for arbitrary rank without computing a determinant, by showing directly that
multiplication by the companion matrix is injective.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

theorem differenceCompanion_mulVec_of_lt {n : ℕ} (a u : Fin n → K) (i : Fin n)
    (hi : (i : ℕ) + 1 < n) :
    (differenceCompanion a).mulVec u i = u ⟨(i : ℕ) + 1, hi⟩ := by
  classical
  have hrow : ∀ j : Fin n, differenceCompanion a i j
      = if (j : ℕ) = (i : ℕ) + 1 then 1 else 0 := by
    intro j
    simp [differenceCompanion, hi]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, hi⟩ : Fin n)]
  · rw [hrow]
    simp
  · intro j _ hj
    rw [hrow]
    have hne : (j : ℕ) ≠ (i : ℕ) + 1 := fun hcon => hj (Fin.ext hcon)
    simp [hne]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

theorem differenceCompanion_mulVec_of_last {n : ℕ} (a u : Fin n → K) (i : Fin n)
    (hi : ¬ ((i : ℕ) + 1 < n)) :
    (differenceCompanion a).mulVec u i = ∑ j, a j * u j := by
  classical
  have hrow : ∀ j : Fin n, differenceCompanion a i j = a j := by
    intro j
    simp [differenceCompanion, hi]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by rw [hrow]

/-- The kernel of the companion matrix is trivial as soon as the trailing coefficient is. -/
theorem differenceCompanion_mulVec_eq_zero {n : ℕ} (hn : 0 < n) {a : Fin n → K}
    (ha : a ⟨0, hn⟩ ≠ 0) {u : Fin n → K}
    (hu : (differenceCompanion a).mulVec u = 0) : u = 0 := by
  classical
  have htail : ∀ j : Fin n, 0 < (j : ℕ) → u j = 0 := by
    intro j hj
    have hlt : (j : ℕ) - 1 + 1 < n := by
      have := j.isLt
      omega
    set i : Fin n := ⟨(j : ℕ) - 1, by omega⟩ with hidef
    have hi : (i : ℕ) + 1 < n := by
      simp only [hidef]
      omega
    have hval := congrFun hu i
    rw [differenceCompanion_mulVec_of_lt a u i hi] at hval
    have hji : (⟨(i : ℕ) + 1, hi⟩ : Fin n) = j := by
      apply Fin.ext
      simp only [hidef]
      omega
    rw [hji] at hval
    exact hval
  have hlast : ∀ i : Fin n, ¬ ((i : ℕ) + 1 < n) → (∑ j, a j * u j) = 0 := by
    intro i hi
    have hval := congrFun hu i
    rw [differenceCompanion_mulVec_of_last a u i hi] at hval
    exact hval
  have hex : ∃ i : Fin n, ¬ ((i : ℕ) + 1 < n) := by
    refine ⟨⟨n - 1, by omega⟩, ?_⟩
    simp only []
    omega
  obtain ⟨i, hi⟩ := hex
  have hsum := hlast i hi
  have hsum' : (∑ j, a j * u j) = a ⟨0, hn⟩ * u ⟨0, hn⟩ := by
    refine Finset.sum_eq_single (⟨0, hn⟩ : Fin n) ?_ ?_
    · intro j _ hj
      have hjpos : 0 < (j : ℕ) := by
        rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
        · exact absurd (Fin.ext h0 : j = ⟨0, hn⟩) hj
        · exact hpos
      rw [htail j hjpos, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  rw [hsum'] at hsum
  have hu0 : u ⟨0, hn⟩ = 0 := by
    rcases mul_eq_zero.mp hsum with h | h
    · exact absurd h ha
    · exact h
  funext j
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
  · have : j = ⟨0, hn⟩ := Fin.ext h0
    rw [this, hu0]
    rfl
  · rw [htail j hpos]
    rfl

/-- **The companion matrix is invertible in every rank.**  A scalar linear difference equation with
nonzero trailing coefficient becomes an invertible first-order system. -/
theorem isUnit_det_differenceCompanion {n : ℕ} (hn : 0 < n) {a : Fin n → K}
    (ha : a ⟨0, hn⟩ ≠ 0) : IsUnit (differenceCompanion a).det := by
  classical
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  have hz : (differenceCompanion a).mulVec (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  have := differenceCompanion_mulVec_eq_zero hn ha hz
  exact sub_eq_zero.mp this

/-! ### The Casoratian criterion -/

/-- The Casoratian matrix of a family of scalar solutions: its rows are successive shifts. -/
def casoratian {n : ℕ} (σ : K ≃+* K) (y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (⇑σ)^[(i : ℕ)] (y j)

theorem casoratian_apply {n : ℕ} (σ : K ≃+* K) (y : Fin n → K) (i j : Fin n) :
    casoratian σ y i j = differenceScalarVec σ (y j) i := rfl

/-- **A constant relation kills the Casoratian.** -/
theorem det_casoratian_eq_zero_of_constant_relation {n : ℕ} (σ : K ≃+* K) (y : Fin n → K)
    {c : Fin n → K} (hc : ∀ j, σ (c j) = c j) (hc0 : c ≠ 0)
    (hrel : ∑ j, c j * y j = 0) :
    (casoratian σ y).det = 0 := by
  classical
  have hiter : ∀ (i : ℕ) (j : Fin n), (⇑σ)^[i] (c j) = c j := by
    intro i j
    induction i with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hc j]
  have hmul : (casoratian σ y).mulVec c = 0 := by
    funext i
    have hstep : ∑ j, (⇑σ)^[(i : ℕ)] (y j) * c j
        = (⇑σ)^[(i : ℕ)] (∑ j, c j * y j) := by
      have hhom : ∀ x z : K, (⇑σ)^[(i : ℕ)] (x * z)
          = (⇑σ)^[(i : ℕ)] x * (⇑σ)^[(i : ℕ)] z := by
        intro x z
        induction (i : ℕ) with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
            Function.iterate_succ_apply', ih, map_mul]
      have hsum : (⇑σ)^[(i : ℕ)] (∑ j, c j * y j) = ∑ j, (⇑σ)^[(i : ℕ)] (c j * y j) := by
        induction (i : ℕ) with
        | zero => rfl
        | succ k ih =>
            rw [Function.iterate_succ_apply', ih, map_sum]
            exact Finset.sum_congr rfl fun j _ => (Function.iterate_succ_apply' (⇑σ) k _).symm
      rw [hsum]
      exact (Finset.sum_congr rfl fun j _ => by rw [hhom, hiter, mul_comm]).symm
    simp only [Matrix.mulVec, dotProduct, casoratian, Matrix.of_apply, Pi.zero_apply]
    rw [hstep, hrel]
    clear hstep
    induction (i : ℕ) with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hc0, hmul⟩

/-- **A vanishing Casoratian produces a constant relation.**  For solutions of a scalar equation
with invertible companion matrix, a vanishing Casoratian forces a nontrivial relation with
shift-invariant coefficients. -/
theorem exists_constant_relation_of_det_casoratian_eq_zero {n : ℕ} (hn : 0 < n)
    (σ : K ≃+* K) {a : Fin n → K} (ha : a ⟨0, hn⟩ ≠ 0) {y : Fin n → K}
    (hy : ∀ j, (⇑σ)^[n] (y j) = ∑ k, a k * (⇑σ)^[(k : ℕ)] (y j))
    (hdet : (casoratian σ y).det = 0) :
    ∃ c : Fin n → K, (∀ j, σ (c j) = c j) ∧ c ≠ 0 ∧ ∑ j, c j * y j = 0 := by
  classical
  obtain ⟨b, hb0, hbmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨j₀, hj₀⟩ : ∃ j, b j ≠ 0 := by
    by_contra hcon
    exact hb0 (funext fun j => not_not.mp fun h => hcon ⟨j, h⟩)
  have hsol : ∀ j, IsDifferenceSystemSolution σ (differenceCompanion a)
      (differenceScalarVec σ (y j)) := fun j =>
    isDifferenceSystemSolution_differenceScalarVec σ (hy j)
  have hrel : ∀ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)),
      b j * (differenceScalarVec (n := n) σ (y j)) i = 0 := by
    intro i
    have := congrFun hbmul i
    simp only [Matrix.mulVec, dotProduct, casoratian, Matrix.of_apply, Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]; rfl
  obtain ⟨t, d, htne, hconst, hnz, hdrel⟩ :=
    exists_differenceConstants_relation_of_ne_zero σ
      (isUnit_det_differenceCompanion hn ha) hsol Finset.univ b (Finset.mem_univ j₀) hj₀ hrel
  refine ⟨fun j => if j ∈ t then d j else 0, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ t
    · simp only [hj, if_true]
      exact hconst j hj
    · simp only [hj, if_false, map_zero]
  · obtain ⟨j₁, hj₁⟩ := htne
    intro hzero
    have := congrFun hzero j₁
    simp only [hj₁, if_true, Pi.zero_apply] at this
    exact hnz j₁ hj₁ this
  · have hzero := hdrel ⟨0, hn⟩
    have hval : ∀ j : Fin n, (differenceScalarVec (n := n) σ (y j)) ⟨0, hn⟩ = y j := fun j => rfl
    have hsum : ∑ j ∈ (Finset.univ : Finset (Fin n)),
        (if j ∈ t then d j else 0) * y j = ∑ j ∈ t, d j * y j := by
      rw [← Finset.sum_subset (Finset.subset_univ t) (fun x _ hx => by simp [hx])]
      exact Finset.sum_congr rfl fun j hj => by simp [hj]
    rw [hsum]
    calc ∑ j ∈ t, d j * y j
        = ∑ j ∈ t, d j * (differenceScalarVec (n := n) σ (y j)) ⟨0, hn⟩ :=
          Finset.sum_congr rfl fun j _ => by rw [hval]
      _ = 0 := hzero


end

end GaloisForLFunctions.HTGeometry
