import GaloisForLFunctions.HTGeometry.JacobiContinuity

/-!
# Sign normalisation of the reducing matrix

Conjugating a Jacobi datum by a diagonal sign matrix conjugates its unipotent factor by the same
signs and leaves its diagonal alone, so it preserves both Siegel bounds.  A reducing matrix of
determinant `−1` can therefore be corrected to one of determinant `1` without leaving the Siegel set.

* `JacobiData.flip` : the sign conjugate.
* `exists_siegel_inOrbit_det_one` : **the covering with a unimodular matrix of determinant one.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The sign conjugate of a Jacobi datum. -/
def JacobiData.flip (J : JacobiData n) (s : Fin n → ℝ) (hs : ∀ i, s i * s i = 1) :
    JacobiData n where
  U := fun i j => s i * J.U i j * s j
  d := J.d
  pos := J.pos
  upper := fun i j hji => by
    show s i * J.U i j * s j = 0
    rw [J.upper i j hji]
    ring
  unit := fun i => by
    show s i * J.U i i * s i = 1
    rw [J.unit i, mul_one]
    exact hs i

theorem abs_eq_one_of_sq_eq_one {x : ℝ} (hx : x * x = 1) : |x| = 1 := by
  have h : |x| * |x| = 1 := by rw [← abs_mul, hx, abs_one]
  nlinarith [abs_nonneg x, h]

theorem JacobiData.flip_form (J : JacobiData n) (s : Fin n → ℝ) (hs : ∀ i, s i * s i = 1) :
    (J.flip s hs).form = Matrix.diagonal s * J.form * Matrix.diagonal s := by
  classical
  ext i j
  have hL : (J.flip s hs).form i j = s i * (J.form i j) * s j := by
    rw [(J.flip s hs).form_apply i j, J.form_apply i j, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    show J.d m * (s m * J.U m i * s i) * (s m * J.U m j * s j) = _
    linear_combination (s i * s j * J.d m * J.U m i * J.U m j) * hs m
  have hR : (Matrix.diagonal s * J.form * Matrix.diagonal s) i j = s i * (J.form i j) * s j := by
    rw [Matrix.mul_apply,
      Finset.sum_eq_single j (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
        (fun hcon => absurd (Finset.mem_univ j) hcon), Matrix.diagonal_apply_eq, Matrix.mul_apply,
      Finset.sum_eq_single i
        (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ (Ne.symm hp), zero_mul])
        (fun hcon => absurd (Finset.mem_univ i) hcon), Matrix.diagonal_apply_eq]
  rw [hL, hR]

theorem JacobiData.flip_isSiegel (J : JacobiData n) (s : Fin n → ℝ) (hs : ∀ i, s i * s i = 1)
    {t u : ℝ} (hS : J.IsSiegel t u) : (J.flip s hs).IsSiegel t u := by
  refine ⟨hS.1, fun i j => ?_⟩
  have habs : |(J.flip s hs).U i j| = |J.U i j| := by
    show |s i * J.U i j * s j| = _
    rw [abs_mul, abs_mul, abs_eq_one_of_sq_eq_one (hs i), abs_eq_one_of_sq_eq_one (hs j),
      one_mul, mul_one]
  rw [habs]
  exact hS.2 i j

/-- **Every positive definite form is equivalent, by an integral matrix of determinant one, to one
satisfying the Siegel bounds.** -/
theorem exists_siegel_inOrbit_det_one {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ (g : Matrix (Fin n) (Fin n) ℤ) (J : JacobiData n), g.det = 1 ∧
      J.form = (g.map (fun z : ℤ => (z : ℝ)))ᵀ * A * (g.map (fun z : ℤ => (z : ℝ)))
      ∧ J.IsSiegel 2 1 := by
  classical
  obtain ⟨J, ⟨γ, ⟨g, hgu, hg⟩, hJγ⟩, hS⟩ := exists_siegel_inOrbit hA
  have hγeq : γ = g.map (fun z : ℤ => (z : ℝ)) := by
    ext a b
    exact hg a b
  have hdet : g.det = 1 ∨ g.det = -1 := Int.isUnit_iff.1 (hgu.map (Matrix.detMonoidHom))
  rcases hdet with hd | hd
  · exact ⟨g, J, hd, by rw [← hγeq]; exact hJγ, hS⟩
  · have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        rw [Matrix.det_isEmpty] at hd
        exact absurd hd (by norm_num)
      · exact h0
    set z : Fin n → ℤ := fun i => if (i : ℕ) = 0 then -1 else 1 with hzdef
    set s : Fin n → ℝ := fun i => if (i : ℕ) = 0 then -1 else 1 with hsdef
    have hs : ∀ i, s i * s i = 1 := by
      intro i
      rw [hsdef]
      by_cases hi : (i : ℕ) = 0 <;> simp [hi]
    have hzprod : (Matrix.diagonal z).det = -1 := by
      rw [Matrix.det_diagonal]
      refine (Finset.prod_eq_single (⟨0, hn⟩ : Fin n) (fun m _ hm => ?_) (fun hcon => ?_)).trans ?_
      · rw [hzdef]
        have : (m : ℕ) ≠ 0 := fun hcon => hm (Fin.ext hcon)
        simp [this]
      · exact absurd (Finset.mem_univ _) hcon
      · rw [hzdef]
        simp
    have hcast : (Matrix.diagonal z).map (fun w : ℤ => (w : ℝ)) = Matrix.diagonal s := by
      ext a b
      by_cases hab : a = b
      · subst hab
        rw [Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hzdef, hsdef]
        by_cases ha : (a : ℕ) = 0 <;> simp [ha]
      · rw [Matrix.map_apply, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab]
        simp
    refine ⟨g * Matrix.diagonal z, J.flip s hs, ?_, ?_, J.flip_isSiegel s hs hS⟩
    · rw [Matrix.det_mul, hzprod, hd]
      norm_num
    · have hmapmul : (g * Matrix.diagonal z).map (fun w : ℤ => (w : ℝ))
          = (g.map (fun w : ℤ => (w : ℝ))) * Matrix.diagonal s := by
        rw [← hcast]
        exact (RingHom.map_mul (Int.castRingHom ℝ).mapMatrix g (Matrix.diagonal z))
      rw [hmapmul, J.flip_form s hs, hJγ, hγeq, Matrix.transpose_mul, Matrix.diagonal_transpose]
      simp only [Matrix.mul_assoc]

end GaloisForLFunctions.HTGeometry
