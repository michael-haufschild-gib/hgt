import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanMomentCounts

/-!
# The explicit hyperplane contribution to Kloosterman moments

Deleting the leading coordinate identifies a torus hyperplane with the complement
of the smaller hyperplane. The resulting recurrence determines its point count and
isolates its contribution from the double-zero locus in the global moment identity.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem normalizedCoordinateZeroTorus_card_zero :
    (normalizedCoordinateZeroTorus (F := F) 0).card = 0 := by
  simp [normalizedCoordinateZeroTorus]

/-- Deleting the leading coordinate identifies the hyperplane with the complement
of the smaller hyperplane: the deleted coordinate is forced and must be nonzero. -/
theorem normalizedCoordinateZeroTorus_card_complement (m : ℕ) :
    (normalizedCoordinateZeroTorus (F := F) (m + 1)).card =
      ((univ : Finset (MomentTorus F m)) \ normalizedCoordinateZeroTorus m).card := by
  apply card_bij (fun (x : MomentTorus F (m + 1)) _ => Fin.tail x)
  · intro x hx
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro ht
    have hx' := (mem_filter.mp hx).2
    have ht' := (mem_filter.mp ht).2
    rw [Fin.sum_univ_succ] at hx'
    change 1 + ∑ j : Fin m, (x j.succ : F) = 0 at ht'
    apply (x 0).property
    linear_combination hx' - ht'
  · intro x hx y hy htail
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    rw [Fin.sum_univ_succ] at hx' hy'
    have hs := congrArg (fun t : MomentTorus F m => ∑ j, (t j : F)) htail
    change (∑ j : Fin m, (x j.succ : F)) = ∑ j : Fin m, (y j.succ : F) at hs
    have hzero : (x 0 : F) = (y 0 : F) := by linear_combination hx' - hy' - hs
    funext j
    refine Fin.cases (Subtype.ext hzero) (fun j => congrFun htail j) j
  · intro y hy
    have hy0 : 1 + ∑ j, (y j : F) ≠ 0 := by
      intro h
      exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
    let x : MomentTorus F (m + 1) :=
      Fin.cons ⟨-(1 + ∑ j, (y j : F)), neg_ne_zero.mpr hy0⟩ y
    refine ⟨x, ?_, rfl⟩
    simp only [normalizedCoordinateZeroTorus, mem_filter, mem_univ, true_and,
      x, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    ring

/-- The deletion recurrence for the normalized torus hyperplane. -/
theorem normalizedCoordinateZeroTorus_card_recurrence (m : ℕ) :
    (normalizedCoordinateZeroTorus (F := F) (m + 1)).card +
      (normalizedCoordinateZeroTorus (F := F) m).card = (Fintype.card F - 1) ^ m := by
  rw [normalizedCoordinateZeroTorus_card_complement,
    card_sdiff_add_card_eq_card (subset_univ _), card_univ]
  simp only [MomentTorus, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_subtype_compl (fun r : F => r = 0), Fintype.card_subtype_eq]

/-- The hyperplane count is the integral polynomial determined by deletion. -/
theorem normalizedCoordinateZeroTorus_card_formula (m : ℕ) :
    (Fintype.card F : ℤ) * (normalizedCoordinateZeroTorus (F := F) m).card =
      ((Fintype.card F : ℤ) - 1) ^ m - (-1) ^ m := by
  induction m with
  | zero => simp [normalizedCoordinateZeroTorus_card_zero]
  | succ m ih =>
      have hrec : ((normalizedCoordinateZeroTorus (F := F) (m + 1)).card : ℤ) +
          (normalizedCoordinateZeroTorus (F := F) m).card = ((Fintype.card F : ℤ) - 1) ^ m := by
        have h := congrArg (fun n : ℕ => (n : ℤ)) (normalizedCoordinateZeroTorus_card_recurrence (F := F) m)
        simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_sub Fintype.card_pos, Nat.cast_one] using h
      rw [pow_succ, pow_succ]
      linear_combination (Fintype.card F : ℤ) * hrec - ih

/-- Only the double-zero count remains after the explicit hyperplane contribution is removed. -/
theorem kloosterman_moment_double_count {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) (m : ℕ) :
    ∑ a : F, SignedSuccessorArithmetic.kloosterman ψ a b ^ (m + 1) =
      (Fintype.card F : ℂ) ^ 2 * (normalizedDoubleZeroTorus (F := F) m).card -
        ((Fintype.card F : ℂ) - 1) ^ m + (-1) ^ m := by
  have hB : (Fintype.card F : ℂ) * (normalizedCoordinateZeroTorus (F := F) m).card =
      ((Fintype.card F : ℂ) - 1) ^ m - (-1) ^ m := by
    exact_mod_cast normalizedCoordinateZeroTorus_card_formula (F := F) m
  rw [kloosterman_moment_projective_counts hψ hb, mul_sub, hB]
  ring

/-- The integral polynomial counting a normalized torus hyperplane. -/
def hyperplanePolynomial : ℕ → Polynomial ℤ
  | 0 => 0
  | m + 1 => (Polynomial.X - 1) ^ m - hyperplanePolynomial m

/-- Multiplication by the field-size variable removes the apparent denominator. -/
theorem hyperplanePolynomial_mul_X (m : ℕ) :
    Polynomial.X * hyperplanePolynomial m =
      (Polynomial.X - 1) ^ m - (-1 : Polynomial ℤ) ^ m := by
  induction m with
  | zero => simp [hyperplanePolynomial]
  | succ m ih =>
      rw [hyperplanePolynomial, mul_sub, ih, pow_succ, pow_succ]
      ring

/-- A hyperplane in an `(m+1)`-dimensional torus has a count polynomial of degree at most `m`. -/
theorem hyperplanePolynomial_natDegree_succ_le (m : ℕ) :
    (hyperplanePolynomial (m + 1)).natDegree ≤ m := by
  induction m with
  | zero => simp [hyperplanePolynomial]
  | succ m ih =>
      rw [hyperplanePolynomial]
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · rw [Polynomial.natDegree_pow]
        have hlin : (Polynomial.X - 1 : Polynomial ℤ).natDegree = 1 := by
          simpa using Polynomial.natDegree_X_sub_C (1 : ℤ)
        rw [hlin, mul_one]
      · exact ih.trans (Nat.le_succ m)

/-- Only Tate exponents strictly below the number of torus coordinates occur. -/
theorem hyperplanePolynomial_support_lt {m j : ℕ}
    (hj : j ∈ (hyperplanePolynomial m).support) : j < m := by
  cases m with
  | zero => simp [hyperplanePolynomial] at hj
  | succ m =>
      exact Nat.lt_succ_iff.mpr ((Polynomial.le_natDegree_of_mem_supp j hj).trans
        (hyperplanePolynomial_natDegree_succ_le m))

/-- Evaluation of the count polynomial is the actual finite-field point count. -/
theorem hyperplanePolynomial_eval_count (m : ℕ) :
    (hyperplanePolynomial m).eval (Fintype.card F : ℤ) =
      (normalizedCoordinateZeroTorus (F := F) m).card := by
  have h : (Fintype.card F : ℤ) * (hyperplanePolynomial m).eval (Fintype.card F : ℤ) =
      ((Fintype.card F : ℤ) - 1) ^ m - (-1) ^ m := by
    simpa using congrArg (Polynomial.eval (Fintype.card F : ℤ)) (hyperplanePolynomial_mul_X m)
  have hq : (Fintype.card F : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := F)
  exact mul_left_cancel₀ hq (h.trans (normalizedCoordinateZeroTorus_card_formula (F := F) m).symm)

private theorem hyperplanePolynomial_eval₂_count (m : ℕ) :
    (hyperplanePolynomial m).eval₂ (Int.castRingHom ℂ) (Fintype.card F : ℂ) =
      ((normalizedCoordinateZeroTorus (F := F) m).card : ℂ) := by
  calc (hyperplanePolynomial m).eval₂ (Int.castRingHom ℂ) (Fintype.card F : ℂ)
      = (Int.castRingHom ℂ) ((hyperplanePolynomial m).eval (Fintype.card F : ℤ)) :=
        Polynomial.eval₂_at_apply (Int.castRingHom ℂ) (Fintype.card F : ℤ)
    _ = _ := by rw [hyperplanePolynomial_eval_count]; rfl

/-- A finite signed trace whose eigenvalues are integral powers of the field size. -/
def hyperplaneTateTrace (m : ℕ) (q : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ (hyperplanePolynomial m).support,
    ((hyperplanePolynomial m).coeff j : ℂ) * (q ^ j) ^ n

theorem hyperplaneTateTrace_eq_eval₂ (m : ℕ) (q : ℂ) (n : ℕ) :
    hyperplaneTateTrace m q n = (hyperplanePolynomial m).eval₂ (Int.castRingHom ℂ) (q ^ n) := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply sum_congr rfl
  intro j _
  change ((hyperplanePolynomial m).coeff j : ℂ) * (q ^ j) ^ n =
    ((hyperplanePolynomial m).coeff j : ℂ) * (q ^ n) ^ j
  rw [← pow_mul, ← pow_mul, Nat.mul_comm j n]

omit [DecidableEq F] in
/-- The explicit signed trace recovers the point count over every finite extension. -/
theorem hyperplaneTateTrace_extension_count (m : ℕ) (E : Type*) [Field E] [Fintype E]
    [DecidableEq E] [Algebra F E] :
    hyperplaneTateTrace m (Fintype.card F : ℂ) (Module.finrank F E) =
      ((normalizedCoordinateZeroTorus (F := E) m).card : ℂ) := by
  rw [hyperplaneTateTrace_eq_eval₂, ← Nat.cast_pow,
    ← Module.card_eq_pow_finrank (K := F) (V := E)]
  exact hyperplanePolynomial_eval₂_count (F := E) m

omit [DecidableEq F] in
/-- Every eigenvalue in the hyperplane trace has the explicit geometric weight bound. -/
theorem hyperplaneTateTrace_weight_bound {m j : ℕ}
    (hj : j ∈ (hyperplanePolynomial m).support) :
    ‖(Fintype.card F : ℂ) ^ j‖ ≤ (Fintype.card F : ℝ) ^ (m - 1) := by
  rw [norm_pow, Complex.norm_natCast]
  have hjm := hyperplanePolynomial_support_lt hj
  exact pow_le_pow_right₀ (by exact_mod_cast Fintype.card_pos (α := F)) (by omega)

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
