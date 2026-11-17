import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyJordanInverse

/-!
# The sharp positivity boundary for diagonal Jordan multiplication

Inverse Jordan multiplication preserves positive matrices. The forward map
has a different boundary: its image of the all-ones Gram is positive exactly
when all diagonal rates coincide. Every unequal pair has an explicitly
negative principal determinant.
-/

noncomputable section
open Matrix
open scoped ComplexOrder
namespace GaloisForLFunctions.HilbertMetric.CauchyJordan

/-- The Jordan image of the constant rank-one Gram. -/
def jordanSymbol {n : ℕ} (r : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  jordan r (fun _ _ => 1)

theorem jordanSymbol_apply {n : ℕ} (r : Fin n → ℝ) (i j : Fin n) :
    jordanSymbol r i j = ((rate r i : ℂ) + (rate r j : ℂ)) / 2 := by
  rw [jordanSymbol, jordan_apply, mul_one]

/-- Every two-coordinate determinant measures exactly the squared rate mismatch. -/
theorem jordanSymbol_pair_det {n : ℕ} (r : Fin n → ℝ) (i j : Fin n) :
    ((jordanSymbol r).submatrix ![i, j] ![i, j]).det =
      ((-(rate r i - rate r j) ^ 2 / 4 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    jordanSymbol_apply, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_ofNat]
  ring

/-- A two-coordinate minor is strictly negative exactly when its rates differ. -/
theorem jordanSymbol_pair_det_neg_iff {n : ℕ} (r : Fin n → ℝ) (i j : Fin n) :
    (((jordanSymbol r).submatrix ![i, j] ![i, j]).det).re < 0 ↔ r i ≠ r j := by
  rw [jordanSymbol_pair_det, Complex.ofReal_re]
  have he : rate r i = rate r j ↔ r i = r j := Real.exp_injective.eq_iff
  rw [← he]
  constructor
  · intro h hz
    rw [hz, sub_self, zero_pow (by decide), neg_zero, zero_div] at h
    exact (lt_irrefl 0) h
  · intro h
    have hs : 0 < (rate r i - rate r j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
    linarith only [hs]

/-- The all-ones matrix is an explicit Gram in every dimension. -/
theorem constantOneGram_posSemidef (n : ℕ) :
    (fun _ _ : Fin n => (1 : ℂ)).PosSemidef := by
  have heq : (fun _ _ : Fin n => (1 : ℂ)) =
      (fun (_ : Fin 1) (_ : Fin n) => (1 : ℂ))ᴴ *
        (fun (_ : Fin 1) (_ : Fin n) => (1 : ℂ)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_one, one_mul,
      Fin.sum_univ_one]
  rw [heq]
  exact posSemidef_conjTranspose_mul_self _

/-- Forward Jordan averaging preserves this positive Gram exactly at equal rates. -/
theorem jordanSymbol_posSemidef_iff {n : ℕ} (r : Fin n → ℝ) :
    (jordanSymbol r).PosSemidef ↔ ∀ i j, r i = r j := by
  constructor
  · intro h i j
    have hd := (h.submatrix ![i, j]).det_nonneg
    rw [jordanSymbol_pair_det] at hd
    have hr : 0 ≤ -(rate r i - rate r j) ^ 2 / 4 := by exact_mod_cast hd
    have he : rate r i = rate r j := by
      have hs := sq_nonneg (rate r i - rate r j)
      have hz : (rate r i - rate r j) ^ 2 = 0 := by linarith only [hr, hs]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    exact Real.exp_injective he
  · intro h
    cases n with
    | zero =>
      have heq : jordanSymbol r = 0 := by ext i; exact Fin.elim0 i
      rw [heq]
      exact Matrix.PosSemidef.zero
    | succ n =>
      have heq : jordanSymbol r = (rate r 0 : ℂ) • (fun _ _ : Fin (n + 1) => (1 : ℂ)) := by
        ext i j
        rw [jordanSymbol_apply]
        simp only [rate, h i 0, h j 0, Matrix.smul_apply, smul_eq_mul, mul_one]
        ring
      rw [heq]
      exact (constantOneGram_posSemidef (n + 1)).smul (by exact_mod_cast (rate_pos r 0).le)

/-- Unequal rates give a positive input whose Jordan image is not positive. -/
theorem jordan_has_positive_counterexample_iff {n : ℕ} (r : Fin n → ℝ) :
    (∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef ∧ ¬ (jordan r A).PosSemidef) ↔
      ¬ ∀ i j, r i = r j := by
  constructor
  · rintro ⟨A, hA, hbad⟩ heq
    apply hbad
    cases n with
    | zero =>
      have hz : jordan r A = 0 := by ext i; exact Fin.elim0 i
      rw [hz]
      exact Matrix.PosSemidef.zero
    | succ n =>
      have hj : jordan r A = (rate r 0 : ℂ) • A := by
        ext i j
        rw [jordan_apply]
        simp only [rate, heq i 0, heq j 0, Matrix.smul_apply, smul_eq_mul]
        ring
      rw [hj]
      exact hA.smul (by exact_mod_cast (rate_pos r 0).le)
  · intro h
    exact ⟨fun _ _ => 1, constantOneGram_posSemidef n,
      fun hp => h ((jordanSymbol_posSemidef_iff r).mp hp)⟩

#print axioms jordanSymbol_pair_det
#print axioms jordanSymbol_pair_det_neg_iff
#print axioms jordanSymbol_posSemidef_iff
#print axioms jordan_has_positive_counterexample_iff

end GaloisForLFunctions.HilbertMetric.CauchyJordan
