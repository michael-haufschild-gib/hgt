import GaloisForLFunctions.CollectiveDiophantineGeometry.CollectiveAuxiliaryConstruction

/-!
# Bounded elimination onto coordinate subspaces

Clearing a nonsingular pivot minor eliminates coordinates without losing
the rational span of the surviving forms. A pivot of order `q` multiplies
coefficient height by at most `(q+1)! H^q` and the value of any real
linear functional by at most the same factor.
-/

noncomputable section
namespace GaloisForLFunctions.CollectiveDiophantineGeometry
open Finset Matrix

set_option autoImplicit false

/-- Rational vectors supported on the selected coordinates. -/
def coordinateSubspace {k : ℕ} (J : Finset (Fin k)) : Submodule ℚ (Fin k → ℚ) where
  carrier := {v | ∀ j, j ∉ J → v j = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy j hj; simp [hx j hj, hy j hj]
  smul_mem' := by intro a x hx j hj; simp [hx j hj]

/-- The rational span of a finite family of integer coefficient rows. -/
def integerRowSpan {k : ℕ} (S : Finset (Fin k → ℤ)) : Submodule ℚ (Fin k → ℚ) :=
  Submodule.span ℚ ((fun v : Fin k → ℤ => fun j => (v j : ℚ)) '' (S : Set (Fin k → ℤ)))

private theorem det_height_bound {q : ℕ} (A : Matrix (Fin q) (Fin q) ℤ)
    {H : ℝ} (hA : ∀ i j, |(A i j : ℝ)| ≤ H) :
    |(A.det : ℝ)| ≤ (q.factorial : ℝ) * H ^ q := by
  have h := Matrix.det_le (A := (Int.castRingHom ℝ).mapMatrix A)
    (abv := AbsoluteValue.abs) hA
  rw [← (Int.castRingHom ℝ).map_det] at h
  simp only [Fintype.card_fin, nsmul_eq_mul] at h
  change |(A.det : ℝ)| ≤ (q.factorial : ℝ) * H ^ q at h
  exact h

private theorem cramer_height_bound {q : ℕ} (A : Matrix (Fin q) (Fin q) ℤ)
    (v : Fin q → ℤ) {H : ℝ} (hA : ∀ i j, |(A i j : ℝ)| ≤ H)
    (hv : ∀ i, |(v i : ℝ)| ≤ H) (i : Fin q) :
    |(A.cramer v i : ℝ)| ≤ (q.factorial : ℝ) * H ^ q := by
  rw [Matrix.cramer_apply]
  apply det_height_bound
  intro a b
  by_cases hb : b = i
  · subst b; simpa only [Matrix.updateCol_self] using hv a
  · simpa only [Matrix.updateCol_ne hb] using hA a b

/-- The eliminated row is an integer combination of the original row and
the pivot rows; its coefficients are transposed Cramer numerators. -/
theorem collectiveGamma_eq_rowCombination {q k : ℕ}
    (M : Matrix (Fin q) (Fin k) ℤ) (s : Fin q → Fin k) (v : Fin k → ℤ) (j : Fin k) :
    collectiveGamma M s v j = (M.submatrix id s).det * v j -
      ∑ a, ((M.submatrix id s)ᵀ.cramer (fun i => v (s i)) a) * M a j := by
  simp only [collectiveGamma, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  congr 1
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Elimination by a `q` by `q` minor keeps coefficient height below
`(q+1)! H^(q+1)`. -/
theorem collectiveGamma_height_bound {q k : ℕ}
    (M : Matrix (Fin q) (Fin k) ℤ) (s : Fin q → Fin k) (v : Fin k → ℤ)
    {H : ℝ} (hH : 0 ≤ H) (hM : ∀ i j, |(M i j : ℝ)| ≤ H)
    (hv : ∀ j, |(v j : ℝ)| ≤ H) (j : Fin k) :
    |(collectiveGamma M s v j : ℝ)| ≤ ((q + 1).factorial : ℝ) * H ^ (q + 1) := by
  rw [collectiveGamma_eq_rowCombination]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum]
  calc
    _ ≤ |((M.submatrix id s).det : ℝ) * v j| +
        ∑ a, |(((M.submatrix id s)ᵀ.cramer (fun i => v (s i)) a : ℤ) : ℝ) * M a j| :=
      (abs_sub _ _).trans (add_le_add_right (abs_sum_le_sum_abs _ _) _)
    _ ≤ (q.factorial : ℝ) * H ^ q * H +
        ∑ _a : Fin q, (q.factorial : ℝ) * H ^ q * H := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul (det_height_bound _ (fun i a => hM i (s a))) (hv j)
          (abs_nonneg _) (by positivity)
      · apply Finset.sum_le_sum
        intro a _
        rw [abs_mul]
        exact mul_le_mul (cramer_height_bound _ _ (fun i b => hM b (s i))
          (fun i => hv (s i)) a) (hM a j) (abs_nonneg _) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

/-- Evaluation commutes with the integral row combination. -/
theorem collectiveGamma_row_evaluation {q k : ℕ}
    (M : Matrix (Fin q) (Fin k) ℤ) (s : Fin q → Fin k)
    (v : Fin k → ℤ) (x : Fin k → ℝ) :
    (∑ j, (collectiveGamma M s v j : ℝ) * x j) =
      ((M.submatrix id s).det : ℝ) * (∑ j, (v j : ℝ) * x j) -
        ∑ a, (((M.submatrix id s)ᵀ.cramer (fun i => v (s i)) a : ℤ) : ℝ) *
          (∑ j, (M a j : ℝ) * x j) := by
  simp_rw [collectiveGamma_eq_rowCombination]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, sub_mul, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

/-- Small values remain small after elimination, with loss `(q+1)! H^q`.
The nonzero pivot preserves the strict inequality. -/
theorem collectiveGamma_value_bound {q k : ℕ}
    (M : Matrix (Fin q) (Fin k) ℤ) (s : Fin q → Fin k)
    (hdet : (M.submatrix id s).det ≠ 0) (v : Fin k → ℤ) (x : Fin k → ℝ)
    {H ε : ℝ} (hH : 0 ≤ H) (hε : 0 < ε)
    (hM : ∀ i j, |(M i j : ℝ)| ≤ H) (hv : ∀ j, |(v j : ℝ)| ≤ H)
    (hMv : ∀ a, |∑ j, (M a j : ℝ) * x j| < ε)
    (hvv : |∑ j, (v j : ℝ) * x j| < ε) :
    |∑ j, (collectiveGamma M s v j : ℝ) * x j| <
      ((q + 1).factorial : ℝ) * H ^ q * ε := by
  have hD : 0 < |((M.submatrix id s).det : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast hdet)
  have hfirst : |((M.submatrix id s).det : ℝ) * (∑ j, (v j : ℝ) * x j)| <
      (q.factorial : ℝ) * H ^ q * ε := by
    rw [abs_mul]
    exact (mul_lt_mul_of_pos_left hvv hD).trans_le
      (mul_le_mul_of_nonneg_right (det_height_bound _ (fun i a => hM i (s a))) hε.le)
  rw [collectiveGamma_row_evaluation]
  calc
    _ ≤ |((M.submatrix id s).det : ℝ) * (∑ j, (v j : ℝ) * x j)| +
        ∑ a, |(((M.submatrix id s)ᵀ.cramer (fun i => v (s i)) a : ℤ) : ℝ) *
          (∑ j, (M a j : ℝ) * x j)| :=
      (abs_sub _ _).trans (add_le_add_right (abs_sum_le_sum_abs _ _) _)
    _ < (q.factorial : ℝ) * H ^ q * ε +
        ∑ _a : Fin q, (q.factorial : ℝ) * H ^ q * ε := by
      apply add_lt_add_of_lt_of_le hfirst
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul (cramer_height_bound _ _ (fun i b => hM b (s i))
        (fun i => hv (s i)) a) (hMv a).le (abs_nonneg _) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- Rational extension of integral elimination. -/
def coordinateEliminationMap {q k : ℕ}
    (M : Matrix (Fin q) (Fin k) ℤ) (s : Fin q → Fin k) :
    (Fin k → ℚ) →ₗ[ℚ] (Fin k → ℚ) where
  toFun v j := ((M.submatrix id s).det : ℚ) * v j -
    ∑ i, v (s i) * ((M.submatrix id s).cramer (fun h => M h j) i : ℚ)
  map_add' v w := by
    ext j
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' a v := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sub, Finset.mul_sum]
    simp only [mul_assoc, mul_left_comm a]

@[simp] theorem coordinateEliminationMap_int {q k : ℕ}
    (M : Matrix (Fin q) (Fin k) ℤ) (s : Fin q → Fin k) (v : Fin k → ℤ) :
    coordinateEliminationMap M s (fun j => (v j : ℚ)) =
      fun j => (collectiveGamma M s v j : ℚ) := by
  ext j
  simp only [coordinateEliminationMap, LinearMap.coe_mk, AddHom.coe_mk,
    collectiveGamma, Int.cast_sub, Int.cast_mul, Int.cast_sum]

theorem coordinateEliminationMap_pivot {q k : ℕ}
    (M : Matrix (Fin q) (Fin k) ℤ) (s : Fin q → Fin k)
    (v : Fin k → ℚ) (i : Fin q) : coordinateEliminationMap M s v (s i) = 0 := by
  have hcol := Matrix.cramer_row_self (M.submatrix id s) (fun h => M h (s i)) i
    (fun _ => rfl)
  change ((M.submatrix id s).det : ℚ) * v (s i) -
    ∑ a, v (s a) * ((M.submatrix id s).cramer (fun h => M h (s i)) a : ℚ) = 0
  rw [hcol]
  simp only [Pi.single_apply, Int.cast_ite, Int.cast_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem coordinateEliminationMap_of_pivot_zero {q k : ℕ}
    (M : Matrix (Fin q) (Fin k) ℤ) (s : Fin q → Fin k)
    (v : Fin k → ℚ) (hv : ∀ i, v (s i) = 0) :
    coordinateEliminationMap M s v = ((M.submatrix id s).det : ℚ) • v := by
  ext j
  simp only [coordinateEliminationMap, LinearMap.coe_mk, AddHom.coe_mk, hv,
    zero_mul, Finset.sum_const_zero, sub_zero, Pi.smul_apply, smul_eq_mul]

/-- Elimination stays in every rational subspace containing the pivot rows. -/
theorem coordinateEliminationMap_mem {q k : ℕ}
    (M : Matrix (Fin q) (Fin k) ℤ) (s : Fin q → Fin k)
    (V : Submodule ℚ (Fin k → ℚ)) (hM : ∀ a, (fun j => (M a j : ℚ)) ∈ V)
    (v : Fin k → ℚ) (hv : v ∈ V) : coordinateEliminationMap M s v ∈ V := by
  have heq : coordinateEliminationMap M s v = ((M.submatrix id s).det : ℚ) • v -
      ∑ i, v (s i) • (∑ a, ((M.submatrix id s).adjugate i a : ℚ) •
        (fun j => (M a j : ℚ))) := by
    ext j
    simp only [coordinateEliminationMap, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec, dotProduct,
      Int.cast_sum, Int.cast_mul]
  rw [heq]
  exact V.sub_mem (V.smul_mem _ hv) (V.sum_mem fun i _ =>
    V.smul_mem _ (V.sum_mem fun a _ => V.smul_mem _ (hM a)))

/-- Pivot cancellation kills the whole restricted row span, not only the
selected pivot coordinates. -/
theorem collectiveGamma_restriction_zero {q k : ℕ} {I : Type*} [Fintype I]
    (M : Matrix (Fin q) (Fin k) ℤ) (out : I → Fin k) (t : Fin q → I)
    (hdet : (M.submatrix id (out ∘ t)).det ≠ 0) (v : Fin k → ℤ)
    (hv : (fun j => (v (out j) : ℚ)) ∈ Submodule.span ℚ
      (Set.range (fun a j => (M a (out j) : ℚ)))) :
    ∀ j, collectiveGamma M (out ∘ t) v (out j) = 0 := by
  classical
  let W : Submodule ℚ (I → ℚ) := Submodule.span ℚ
    (Set.range (fun a j => (M a (out j) : ℚ)))
  let R := LinearMap.funLeft ℚ ℚ out
  have hrows : ∀ a, (fun j => (M a j : ℚ)) ∈ W.comap R := fun a =>
    Submodule.subset_span ⟨a, rfl⟩
  have hz := coordinateEliminationMap_mem M (out ∘ t) (W.comap R) hrows
    (fun j => (v j : ℚ)) hv
  change (fun j => coordinateEliminationMap M (out ∘ t) (fun a => (v a : ℚ)) (out j)) ∈ W at hz
  rw [coordinateEliminationMap_int] at hz
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hz
  let B : Matrix (Fin q) (Fin q) ℚ :=
    (Int.castRingHom ℚ).mapMatrix (M.submatrix id (out ∘ t))
  have hB : Bᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]
    change ((Int.castRingHom ℚ).mapMatrix (M.submatrix id (out ∘ t))).det ≠ 0
    rw [← (Int.castRingHom ℚ).map_det]
    change ((M.submatrix id (out ∘ t)).det : ℚ) ≠ 0
    exact_mod_cast hdet
  have hc0 : Bᵀ.mulVec c = 0 := by
    ext i
    have hi := congrFun hc (t i)
    have hp := coordinateEliminationMap_pivot M (out ∘ t) (fun j => (v j : ℚ)) i
    rw [coordinateEliminationMap_int] at hp
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
    change ∑ a, (M a (out (t i)) : ℚ) * c a = 0
    have hp' : (collectiveGamma M (out ∘ t) v (out (t i)) : ℚ) = 0 := hp
    rw [hp'] at hi
    simpa only [mul_comm] using hi
  have hc' : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hB hc0
  intro j
  have hj := congrFun hc j
  rw [hc'] at hj
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, Pi.zero_apply] at hj
  exact_mod_cast hj.symm

/-- If the eliminated generators vanish outside `J`, they span exactly the
coordinate intersection, since elimination acts there by a nonzero scalar. -/
theorem integerRowSpan_elimination_eq {q k : ℕ}
    (S : Finset (Fin k → ℤ)) (J : Finset (Fin k))
    (M : Matrix (Fin q) (Fin k) ℤ) (hM : ∀ a, M a ∈ S)
    (s : Fin q → Fin k) (hs : ∀ i, s i ∉ J)
    (hdet : (M.submatrix id s).det ≠ 0)
    (hzero : ∀ v ∈ S, ∀ j, j ∉ J → collectiveGamma M s v j = 0) :
    integerRowSpan (S.image (collectiveGamma M s)) =
      integerRowSpan S ⊓ coordinateSubspace J := by
  classical
  let V := integerRowSpan S
  let T := integerRowSpan (S.image (collectiveGamma M s))
  have hrow : ∀ a, (fun j => (M a j : ℚ)) ∈ V := fun a =>
    Submodule.subset_span ⟨M a, hM a, rfl⟩
  have hgen : ∀ v ∈ S, (fun j => (collectiveGamma M s v j : ℚ)) ∈ T := by
    intro v hv
    exact Submodule.subset_span ⟨collectiveGamma M s v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    constructor
    · change (fun j => (collectiveGamma M s v j : ℚ)) ∈ V
      rw [← coordinateEliminationMap_int]
      exact coordinateEliminationMap_mem M s V hrow _
        (Submodule.subset_span ⟨v, hv, rfl⟩)
    · intro j hj
      change (collectiveGamma M s v j : ℚ) = 0
      exact_mod_cast hzero v hv j hj
  · intro v hv
    have hP : coordinateEliminationMap M s v ∈ T := by
      have hle : V ≤ T.comap (coordinateEliminationMap M s) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨w, hw, rfl⟩
        change coordinateEliminationMap M s (fun j => (w j : ℚ)) ∈ T
        rw [coordinateEliminationMap_int]
        exact hgen w hw
      exact hle hv.1
    have hfix := coordinateEliminationMap_of_pivot_zero M s v (fun i => hv.2 (s i) (hs i))
    rw [hfix] at hP
    have hD : ((M.submatrix id s).det : ℚ) ≠ 0 := by exact_mod_cast hdet
    have hmem := T.smul_mem (((M.submatrix id s).det : ℚ)⁻¹) hP
    simpa only [smul_smul, inv_mul_cancel₀ hD, one_smul] using hmem

private theorem exists_restriction_pivot {k : ℕ} {I : Type*} [Fintype I]
    (S : Finset (Fin k → ℤ)) (out : I → Fin k) :
    ∃ (q : ℕ) (M : Matrix (Fin q) (Fin k) ℤ) (t : Fin q → I),
      q ≤ Fintype.card I ∧ (∀ a, M a ∈ S) ∧
      (M.submatrix id (out ∘ t)).det ≠ 0 ∧
      ∀ v ∈ S, (fun j => (v (out j) : ℚ)) ∈ Submodule.span ℚ
        (Set.range (fun a j => (M a (out j) : ℚ))) := by
  classical
  let T : Set (I → ℚ) := (fun v : Fin k → ℤ => fun j => (v (out j) : ℚ)) ''
    (S : Set (Fin k → ℤ))
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent ℚ T
  have hbfin : b.Finite := (S.finite_toSet.image _).subset hbsub
  letI : Fintype b := hbfin.fintype
  let q := Fintype.card b
  let e : Fin q ≃ b := (Fintype.equivFin b).symm
  have hchoice : ∀ a : Fin q, ∃ v ∈ S, (fun j => (v (out j) : ℚ)) = (e a : I → ℚ) := by
    intro a
    exact hbsub (e a).property
  choose M hM hMeq using hchoice
  have heq : (fun a j => (M a (out j) : ℚ)) = (Subtype.val ∘ e) := funext hMeq
  have hind : LinearIndependent ℚ (fun a j => (M a (out j) : ℚ)) := by
    rw [heq]
    exact hbind.comp e e.injective
  have hrange : Set.range (fun a j => (M a (out j) : ℚ)) = b := by
    rw [heq, Set.range_comp, e.surjective.range_eq, Set.image_univ, Subtype.range_coe]
  have hq : q ≤ Fintype.card I := by
    have hd := finrank_span_eq_card hbind
    rw [Subtype.range_coe] at hd
    have hle := (Submodule.span ℚ b).finrank_le
    simpa [hd] using hle
  obtain ⟨t, -, ht⟩ := HTGeometry.exists_injective_det_submatrix_ne_zero hind
  refine ⟨q, M, t, hq, hM, ?_, ?_⟩
  · intro hz
    apply ht
    change ((Int.castRingHom ℚ).mapMatrix (Matrix.submatrix M id (out ∘ t))).det = 0
    rw [← (Int.castRingHom ℚ).map_det, hz, map_zero]
  · intro v hv
    rw [hrange, hbspan]
    exact Submodule.subset_span ⟨v, hv, rfl⟩

/-- Every coordinate intersection of a bounded family of small integer
forms has a bounded integer spanning family. The loss is uniform in the
coordinate set and in the real linear functional. -/
theorem exists_bounded_coordinate_elimination {k : ℕ}
    (S : Finset (Fin k → ℤ)) (J : Finset (Fin k)) (x : Fin k → ℝ)
    {H ε : ℝ} (hH : 1 ≤ H) (hε : 0 < ε)
    (hheight : ∀ v ∈ S, ∀ j, |(v j : ℝ)| ≤ H)
    (hvalue : ∀ v ∈ S, |∑ j, (v j : ℝ) * x j| < ε) :
    ∃ T : Finset (Fin k → ℤ),
      integerRowSpan T = integerRowSpan S ⊓ coordinateSubspace J ∧
      (∀ v ∈ T, ∀ j, j ∉ J → v j = 0) ∧
      (∀ v ∈ T, ∀ j, |(v j : ℝ)| ≤ (k.factorial : ℝ) * H ^ k) ∧
      ∀ v ∈ T, |∑ j, (v j : ℝ) * x j| <
        (k.factorial : ℝ) * H ^ (k - 1) * ε := by
  classical
  by_cases hJ : J = ∅
  · subst J
    have hcoord : coordinateSubspace (∅ : Finset (Fin k)) = ⊥ := by
      ext v
      change (∀ j, j ∉ (∅ : Finset (Fin k)) → v j = 0) ↔ v = 0
      exact ⟨fun h => funext (fun j => h j (by simp)), fun h j _ => congrFun h j⟩
    refine ⟨∅, ?_, by simp, by simp, by simp⟩
    simp only [integerRowSpan, Finset.coe_empty, Set.image_empty, Submodule.span_empty,
      hcoord, inf_bot_eq]
  have hJpos : 0 < J.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hJ)
  obtain ⟨q, M, t, hq, hM, hdet, hspan⟩ :=
    exists_restriction_pivot S (Subtype.val : (Jᶜ : Finset (Fin k)) → Fin k)
  have hJle : J.card ≤ k := by simpa using Finset.card_le_univ J
  have hqk : q + 1 ≤ k := by
    simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin] at hq
    omega
  let s : Fin q → Fin k := Subtype.val ∘ t
  have hs : ∀ i, s i ∉ J := fun i => Finset.mem_compl.mp (t i).property
  have hzero : ∀ v ∈ S, ∀ j, j ∉ J → collectiveGamma M s v j = 0 := by
    intro v hv j hj
    exact collectiveGamma_restriction_zero M Subtype.val t hdet v (hspan v hv)
      ⟨j, Finset.mem_compl.mpr hj⟩
  refine ⟨S.image (collectiveGamma M s),
    integerRowSpan_elimination_eq S J M hM s hs hdet hzero, ?_, ?_, ?_⟩
  · intro v hv j hj
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact hzero w hw j hj
  · intro v hv j
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    have hfac : ((q + 1).factorial : ℝ) ≤ k.factorial := by
      exact_mod_cast Nat.factorial_le hqk
    exact (collectiveGamma_height_bound M s w (by positivity)
      (fun a b => hheight (M a) (hM a) b) (hheight w hw) j).trans
        (mul_le_mul hfac (pow_le_pow_right₀ hH hqk) (by positivity) (by positivity))
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    have hfac : ((q + 1).factorial : ℝ) ≤ k.factorial := by
      exact_mod_cast Nat.factorial_le hqk
    exact (collectiveGamma_value_bound M s hdet w x (by positivity) hε
      (fun a b => hheight (M a) (hM a) b) (hheight w hw)
      (fun a => hvalue (M a) (hM a)) (hvalue w hw)).trans_le
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hfac (pow_le_pow_right₀ hH (show q ≤ k - 1 by omega))
            (by positivity) (by positivity)) hε.le)

/-- The exact coordinate intersection has a rational basis consisting of
bounded integer rows. Elimination loses no surviving rank. -/
theorem exists_bounded_coordinate_basis {k : ℕ}
    (S : Finset (Fin k → ℤ)) (J : Finset (Fin k)) (x : Fin k → ℝ)
    {H ε : ℝ} (hH : 1 ≤ H) (hε : 0 < ε)
    (hheight : ∀ v ∈ S, ∀ j, |(v j : ℝ)| ≤ H)
    (hvalue : ∀ v ∈ S, |∑ j, (v j : ℝ) * x j| < ε) :
    ∃ (r : ℕ) (M : Matrix (Fin r) (Fin k) ℤ),
      r = Module.finrank ℚ ↥(integerRowSpan S ⊓ coordinateSubspace J) ∧
      LinearIndependent ℚ (fun a j => (M a j : ℚ)) ∧
      Submodule.span ℚ (Set.range (fun a j => (M a j : ℚ))) =
        integerRowSpan S ⊓ coordinateSubspace J ∧
      (∀ a j, j ∉ J → M a j = 0) ∧
      (∀ a j, |(M a j : ℝ)| ≤ (k.factorial : ℝ) * H ^ k) ∧
      ∀ a, |∑ j, (M a j : ℝ) * x j| <
        (k.factorial : ℝ) * H ^ (k - 1) * ε := by
  classical
  obtain ⟨T, hTspan, hTsupp, hTheight, hTvalue⟩ :=
    exists_bounded_coordinate_elimination S J x hH hε hheight hvalue
  let A : Set (Fin k → ℚ) := (fun v : Fin k → ℤ => fun j => (v j : ℚ)) ''
    (T : Set (Fin k → ℤ))
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent ℚ A
  have hbfin : b.Finite := (T.finite_toSet.image _).subset hbsub
  letI : Fintype b := hbfin.fintype
  let r := Fintype.card b
  let e : Fin r ≃ b := (Fintype.equivFin b).symm
  have hchoice : ∀ a : Fin r, ∃ v ∈ T, (fun j => (v j : ℚ)) = (e a : Fin k → ℚ) := by
    intro a
    exact hbsub (e a).property
  choose M hM hMeq using hchoice
  have heq : (fun a j => (M a j : ℚ)) = (Subtype.val ∘ e) := funext hMeq
  have hrange : Set.range (fun a j => (M a j : ℚ)) = b := by
    rw [heq, Set.range_comp, e.surjective.range_eq, Set.image_univ, Subtype.range_coe]
  have hspan : Submodule.span ℚ (Set.range (fun a j => (M a j : ℚ))) =
      integerRowSpan S ⊓ coordinateSubspace J := by
    rw [hrange, hbspan]
    exact hTspan
  have hind : LinearIndependent ℚ (fun a j => (M a j : ℚ)) := by
    rw [heq]
    exact hbind.comp e e.injective
  refine ⟨r, M, ?_, hind, hspan, (fun a => hTsupp _ (hM a)),
    (fun a => hTheight _ (hM a)), (fun a => hTvalue _ (hM a))⟩
  rw [← hspan, finrank_span_eq_card hind, Fintype.card_fin]

end GaloisForLFunctions.CollectiveDiophantineGeometry
