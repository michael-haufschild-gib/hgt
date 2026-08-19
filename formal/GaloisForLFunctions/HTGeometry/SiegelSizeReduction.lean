import GaloisForLFunctions.HTGeometry.SiegelQuasiDiagonal

/-!
# Size reduction of the unipotent part

Changing the lattice basis by an integral unipotent upper triangular matrix replaces the unipotent
factor `U` of a Jacobi decomposition by `U γ` and leaves the diagonal untouched.  Sweeping the
superdiagonals outwards, each one can be brought into `[-1/2, 1/2]` by a single integral shear that
does not disturb the ones already reduced.

This is the half of reduction theory that produces the bound `|Uᵢⱼ| ≤ u` of a Siegel set.

* `IsUnipotentUpper`, `IsIntUnipotent` : the real and integral unipotent upper triangular matrices.
* `exists_size_reduction` : **every unipotent upper triangular matrix is size reduced by an
  integral one.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- Unipotent upper triangular. -/
def IsUnipotentUpper (U : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, j < i → U i j = 0) ∧ (∀ i, U i i = 1)

/-- Integral unipotent upper triangular. -/
def IsIntUnipotent (γ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∃ g : Matrix (Fin n) (Fin n) ℤ, ∀ i j, γ i j = (g i j : ℝ)) ∧ IsUnipotentUpper γ

theorem upper_mul_diag {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j : Fin n, j < i → M i j = 0) (hN : ∀ i j : Fin n, j < i → N i j = 0) (i : Fin n) :
    (M * N) i i = M i i * N i i := by
  classical
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun hcon => absurd (Finset.mem_univ i) hcon)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hM i k h, zero_mul]
  · rw [hN k i h, mul_zero]

theorem IsUnipotentUpper.mul {U V : Matrix (Fin n) (Fin n) ℝ}
    (hU : IsUnipotentUpper U) (hV : IsUnipotentUpper V) : IsUnipotentUpper (U * V) := by
  classical
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rcases lt_or_ge m i with h | h
    · rw [hU.1 i m h, zero_mul]
    · rw [hV.1 m j (lt_of_lt_of_le hji h), mul_zero]
  · rw [upper_mul_diag hU.1 hV.1, hU.2 i, hV.2 i, one_mul]

theorem IsIntUnipotent.mul {γ δ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : IsIntUnipotent γ) (hδ : IsIntUnipotent δ) : IsIntUnipotent (γ * δ) := by
  obtain ⟨g, hg⟩ := hγ.1
  obtain ⟨h, hh⟩ := hδ.1
  refine ⟨⟨g * h, fun i j => ?_⟩, hγ.2.mul hδ.2⟩
  rw [Matrix.mul_apply, Matrix.mul_apply]
  push_cast
  exact Finset.sum_congr rfl fun m _ => by rw [hg i m, hh m j]

theorem isIntUnipotent_one : IsIntUnipotent (1 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨⟨1, fun i j => ?_⟩, fun i j hji => ?_, fun i => ?_⟩
  · by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · rw [Matrix.one_apply_ne (fun hcon => absurd hji (by rw [hcon]; exact lt_irrefl j))]
  · rw [Matrix.one_apply_eq]

/-- The superdiagonals of offset at most `k` are reduced. -/
def SizeReduced (k : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, i < j → (j : ℕ) ≤ (i : ℕ) + k → |U i j| ≤ 1 / 2

theorem sizeReduced_zero (U : Matrix (Fin n) (Fin n) ℝ) : SizeReduced 0 U := by
  intro i j hij hle
  exact absurd hij (by simp only [Nat.add_zero] at hle; exact not_lt.2 hle)

/-- **One sweep**: an integral shear at offset `k+1` reduces that superdiagonal and leaves the
smaller offsets alone. -/
theorem exists_sweep {V : Matrix (Fin n) (Fin n) ℝ} (hV : IsUnipotentUpper V) (k : ℕ)
    (hk : SizeReduced k V) :
    ∃ γ : Matrix (Fin n) (Fin n) ℝ, IsIntUnipotent γ ∧ SizeReduced (k + 1) (V * γ) := by
  classical
  set e : Fin n → ℤ := fun i =>
    if h : (i : ℕ) + (k + 1) < n then -round (V i ⟨(i : ℕ) + (k + 1), h⟩) else 0 with he
  set E : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => if (j : ℕ) = (i : ℕ) + (k + 1) then ((e i : ℤ) : ℝ) else 0 with hE
  have hEzero : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) + (k + 1) → E i j = 0 := by
    intro i j hne
    rw [hE]
    simp [hne]
  have hEval : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + (k + 1) → E i j = ((e i : ℤ) : ℝ) := by
    intro i j hij
    rw [hE]
    simp [hij]
  set γ : Matrix (Fin n) (Fin n) ℝ := 1 + E with hγ
  set g : Matrix (Fin n) (Fin n) ℤ :=
    1 + Matrix.of (fun i j : Fin n => if (j : ℕ) = (i : ℕ) + (k + 1) then e i else 0) with hg
  have hone : ∀ i j : Fin n,
      (1 : Matrix (Fin n) (Fin n) ℝ) i j = ((1 : Matrix (Fin n) (Fin n) ℤ) i j : ℝ) := by
    intro i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hγint : IsIntUnipotent γ := by
    refine ⟨⟨g, fun i j => ?_⟩, ?_, ?_⟩
    · rw [hγ, hg]
      by_cases hij : (j : ℕ) = (i : ℕ) + (k + 1)
      · rw [Matrix.add_apply, Matrix.add_apply, hEval i j hij]
        push_cast
        simp only [Matrix.of_apply, if_pos hij]
        rw [hone i j]
      · rw [Matrix.add_apply, Matrix.add_apply, hEzero i j hij]
        push_cast
        simp only [Matrix.of_apply, if_neg hij, Int.cast_zero, add_zero]
        rw [hone i j]
    · intro i j hji
      rw [hγ, Matrix.add_apply, hEzero i j (by omega), add_zero,
        Matrix.one_apply_ne (fun hcon => absurd hji (by rw [hcon]; exact lt_irrefl j))]
    · intro i
      rw [hγ, Matrix.add_apply, hEzero i i (by omega), add_zero, Matrix.one_apply_eq]
  refine ⟨γ, hγint, ?_⟩
  have hprod : ∀ i j : Fin n, (V * γ) i j = V i j + (V * E) i j := by
    intro i j
    rw [hγ, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  have hlow : ∀ i j : Fin n, i < j → (j : ℕ) ≤ (i : ℕ) + k → (V * E) i j = 0 := by
    intro i j hij hle
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : (j : ℕ) = (m : ℕ) + (k + 1)
    · have hmi : (m : ℕ) < (i : ℕ) := by omega
      rw [hV.1 i m (by exact hmi), zero_mul]
    · rw [hEzero m j hm, mul_zero]
  have hnew : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + (k + 1) → (V * E) i j = ((e i : ℤ) : ℝ) := by
    intro i j hij
    rw [Matrix.mul_apply]
    refine (Finset.sum_eq_single i (fun m _ hm => ?_)
      (fun hcon => absurd (Finset.mem_univ i) hcon)).trans ?_
    · by_cases hmj : (j : ℕ) = (m : ℕ) + (k + 1)
      · exact absurd (Fin.ext (by omega) : m = i) hm
      · rw [hEzero m j hmj, mul_zero]
    · rw [hEval i j hij, hV.2 i, one_mul]
  intro i j hij hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · rw [hprod, hlow i j hij (by omega), add_zero]
    exact hk i j hij (by omega)
  · have hij' : (j : ℕ) = (i : ℕ) + (k + 1) := heq
    rw [hprod, hnew i j hij']
    have hlt' : (i : ℕ) + (k + 1) < n := by
      have := j.isLt
      omega
    have hjeq : j = ⟨(i : ℕ) + (k + 1), hlt'⟩ := Fin.ext (by omega)
    rw [he]
    simp only [dif_pos hlt']
    rw [hjeq]
    push_cast
    calc |V i ⟨(i : ℕ) + (k + 1), hlt'⟩ + -(round (V i ⟨(i : ℕ) + (k + 1), hlt'⟩) : ℝ)|
        = |V i ⟨(i : ℕ) + (k + 1), hlt'⟩ - (round (V i ⟨(i : ℕ) + (k + 1), hlt'⟩) : ℝ)| := by
          rw [sub_eq_add_neg]
      _ ≤ 1 / 2 := abs_sub_round _

/-- **Size reduction.**  Every unipotent upper triangular matrix becomes size reduced after
multiplication by an integral unipotent upper triangular matrix. -/
theorem exists_size_reduction {U : Matrix (Fin n) (Fin n) ℝ} (hU : IsUnipotentUpper U) :
    ∃ γ : Matrix (Fin n) (Fin n) ℝ, IsIntUnipotent γ ∧
      ∀ i j : Fin n, i < j → |(U * γ) i j| ≤ 1 / 2 := by
  have hstep : ∀ k : ℕ, ∃ γ : Matrix (Fin n) (Fin n) ℝ, IsIntUnipotent γ ∧
      SizeReduced k (U * γ) := by
    intro k
    induction k with
    | zero => exact ⟨1, isIntUnipotent_one, by rw [Matrix.mul_one]; exact sizeReduced_zero U⟩
    | succ k ih =>
        obtain ⟨γ, hγ, hred⟩ := ih
        obtain ⟨δ, hδ, hred'⟩ := exists_sweep (hU.mul hγ.2) k hred
        exact ⟨γ * δ, hγ.mul hδ, by rw [← Matrix.mul_assoc]; exact hred'⟩
  obtain ⟨γ, hγ, hred⟩ := hstep n
  refine ⟨γ, hγ, fun i j hij => hred i j hij ?_⟩
  have := j.isLt
  omega

/-- The unipotent factor of Jacobi data is unipotent upper triangular. -/
theorem JacobiData.isUnipotentUpper (J : JacobiData n) : IsUnipotentUpper J.U :=
  ⟨J.upper, J.unit⟩

/-- The Jacobi data obtained by an integral unipotent basis change. -/
def JacobiData.shear (J : JacobiData n) {γ : Matrix (Fin n) (Fin n) ℝ} (hγ : IsIntUnipotent γ) :
    JacobiData n where
  U := J.U * γ
  d := J.d
  pos := J.pos
  upper := (J.isUnipotentUpper.mul hγ.2).1
  unit := (J.isUnipotentUpper.mul hγ.2).2

@[simp]
theorem JacobiData.shear_d (J : JacobiData n) {γ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : IsIntUnipotent γ) : (J.shear hγ).d = J.d := rfl

@[simp]
theorem JacobiData.shear_U (J : JacobiData n) {γ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : IsIntUnipotent γ) : (J.shear hγ).U = J.U * γ := rfl

/-- **A shear is a congruence of the form.** -/
theorem JacobiData.shear_form (J : JacobiData n) {γ : Matrix (Fin n) (Fin n) ℝ}
    (hγ : IsIntUnipotent γ) : (J.shear hγ).form = γᵀ * J.form * γ := by
  show (J.U * γ)ᵀ * Matrix.diagonal J.d * (J.U * γ) = γᵀ * (J.Uᵀ * Matrix.diagonal J.d * J.U) * γ
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- **Every form has a size reduced Jacobi datum in its integral unipotent orbit**, with the same
diagonal. -/
theorem exists_sizeReduced_shear (J : JacobiData n) :
    ∃ (γ : Matrix (Fin n) (Fin n) ℝ) (hγ : IsIntUnipotent γ),
      (J.shear hγ).d = J.d ∧ ∀ i j : Fin n, i < j → |(J.shear hγ).U i j| ≤ 1 / 2 := by
  obtain ⟨γ, hγ, hred⟩ := exists_size_reduction J.isUnipotentUpper
  exact ⟨γ, hγ, rfl, hred⟩

/-- The entries of a size reduced Jacobi datum are bounded by `1/2` off the diagonal and equal to
`1` on it, hence bounded by `1`. -/
theorem JacobiData.entries_le_one {J : JacobiData n}
    (h : ∀ i j : Fin n, i < j → |J.U i j| ≤ 1 / 2) (i j : Fin n) : |J.U i j| ≤ 1 := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact le_trans (h i j hij) (by norm_num)
  · rw [hij, J.unit j, abs_one]
  · rw [J.upper i j hij, abs_zero]
    norm_num

end GaloisForLFunctions.HTGeometry
