import GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo.RationalPolynomials

/-!
# Rational quadratic forms and their certificates

Matrices are lists of rows of rationals, read through `matQ`. This module proves the soundness of
three Boolean checks evaluated by `decide`:

* `domCheck K M`: `M` is symmetric and `2 M i i ≥ ∑_j |M i j|`; then `M` is positive semidefinite
  (`quad_nonneg_of_domCheck`);
* comparison `Q ⪯ Q'` through `domCheck` of `Q' - Q` (`quad_le_of_domCheck_sub`);
* `ldlCheck K C L d`: `d ≥ 0` and `C - L diag(d) Lᵀ` passes `domCheck`; then `C` is positive
  semidefinite (`quad_nonneg_of_ldlCheck`).
-/

open Real Finset
open scoped BigOperators

namespace GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo

/-- Entry `(i, j)` of a matrix given by its rows (zero outside the list). -/
def matQ (M : List (List ℚ)) (i j : ℕ) : ℚ := (M.getD i []).getD j 0

/-- Entry `i` of a vector (zero outside the list). -/
def vecQ (v : List ℚ) (i : ℕ) : ℚ := v.getD i 0

/-- The real quadratic form `∑ᵢⱼ M i j mᵢ mⱼ` over `Fin K`. -/
noncomputable def quadR (K : ℕ) (M : List (List ℚ)) (m : Fin K → ℝ) : ℝ :=
  ∑ i : Fin K, ∑ j : Fin K, (matQ M i j : ℝ) * m i * m j

/-- Tabulate `f` as a `K × K` matrix. -/
def tabQ (K : ℕ) (f : ℕ → ℕ → ℚ) : List (List ℚ) :=
  (List.range K).map fun i => (List.range K).map fun j => f i j

theorem matQ_tabQ {K : ℕ} (f : ℕ → ℕ → ℚ) {i j : ℕ} (hi : i < K) (hj : j < K) :
    matQ (tabQ K f) i j = f i j := by
  simp [matQ, tabQ, List.getD_eq_getElem?_getD, hi, hj]

/-- Symmetry and weak diagonal dominance `∑_j |M i j| ≤ 2 M i i`. -/
def domCheck (K : ℕ) (M : List (List ℚ)) : Bool :=
  (List.range K).all fun i =>
    decide (((List.range K).map fun j => |matQ M i j|).sum ≤ 2 * matQ M i i) &&
      (List.range K).all fun j => decide (matQ M i j = matQ M j i)

theorem list_sum_range_eq {α : Type*} [AddCommMonoid α] (K : ℕ) (f : ℕ → α) :
    ((List.range K).map f).sum = ∑ j : Fin K, f j := by
  rw [← Finset.sum_range f, Finset.sum_eq_multiset_sum]
  rfl

theorem quad_nonneg_of_domCheck {K : ℕ} {M : List (List ℚ)} (h : domCheck K M = true)
    (m : Fin K → ℝ) : 0 ≤ quadR K M m := by
  simp only [domCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  have hsym : ∀ i j : Fin K, (matQ M i j : ℝ) = matQ M j i := fun i j => by
    exact_mod_cast (h i i.2).2 j j.2
  have hdom : ∀ i : Fin K,
      (∑ j ∈ Finset.univ.erase i, |(matQ M i j : ℝ)|) ≤ (matQ M i i : ℝ) := fun i => by
    have h1 := (h i i.2).1
    rw [list_sum_range_eq K (fun j => |matQ M i j|)] at h1
    have h1' : (∑ j : Fin K, |(matQ M i j : ℝ)|) ≤ 2 * (matQ M i i : ℝ) := by exact_mod_cast h1
    have hsplit := Finset.add_sum_erase Finset.univ (fun j : Fin K => |(matQ M i j : ℝ)|)
      (Finset.mem_univ i)
    have hii : |(matQ M i i : ℝ)| ≤ ∑ j : Fin K, |(matQ M i j : ℝ)| :=
      Finset.single_le_sum (f := fun j : Fin K => |(matQ M i j : ℝ)|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have hpos : 0 ≤ (matQ M i i : ℝ) := by linarith [abs_nonneg (matQ M i i : ℝ)]
    rw [abs_of_nonneg hpos] at hsplit
    linarith
  have hr := WindowTowerOfSpecZ.symm_quad_round_le (fun _ _ => (0 : ℝ))
    (fun i j : Fin K => (matQ M i j : ℝ)) (fun i j => by simp [hsym i j])
    (fun i => by simpa [abs_neg] using hdom i) m
  simpa [quadR] using hr

/-- Entrywise difference of two matrices on `K × K`. -/
def subMat (K : ℕ) (A B : List (List ℚ)) : List (List ℚ) := tabQ K fun i j => matQ A i j - matQ B i j

theorem quadR_sub {K : ℕ} (A B : List (List ℚ)) (m : Fin K → ℝ) :
    quadR K (subMat K A B) m = quadR K A m - quadR K B m := by
  simp only [quadR, subMat, matQ_tabQ _ (Fin.is_lt _) (Fin.is_lt _), Rat.cast_sub, sub_mul,
    Finset.sum_sub_distrib]

/-- `Q ⪯ Q'` whenever `Q' - Q` passes `domCheck`. -/
theorem quad_le_of_domCheck_sub {K : ℕ} {Q Q' : List (List ℚ)}
    (h : domCheck K (subMat K Q' Q) = true) (m : Fin K → ℝ) : quadR K Q m ≤ quadR K Q' m := by
  have := quad_nonneg_of_domCheck h m
  rw [quadR_sub] at this
  linarith

/-- `C - L diag(d) Lᵀ` on `K × K`. -/
def ldlResidual (K : ℕ) (C L : List (List ℚ)) (d : List ℚ) : List (List ℚ) :=
  tabQ K fun i j => matQ C i j -
    ((List.range K).map fun r => matQ L i r * vecQ d r * matQ L j r).sum

/-- `d ≥ 0` and the `LDLᵀ` residual passes `domCheck`. -/
def ldlCheck (K : ℕ) (C L : List (List ℚ)) (d : List ℚ) : Bool :=
  (List.range K).all (fun r => decide (0 ≤ vecQ d r)) && domCheck K (ldlResidual K C L d)

theorem quad_nonneg_of_ldlCheck {K : ℕ} {C L : List (List ℚ)} {d : List ℚ}
    (h : ldlCheck K C L d = true) (m : Fin K → ℝ) : 0 ≤ quadR K C m := by
  simp only [ldlCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  have hE := quad_nonneg_of_domCheck h.2 m
  have hdec : ∀ i j : Fin K, (matQ C i j : ℝ) =
      (∑ r : Fin K, (matQ L i r : ℝ) * (vecQ d r : ℝ) * (matQ L j r : ℝ)) +
        (matQ (ldlResidual K C L d) i j : ℝ) := fun i j => by
    rw [ldlResidual, matQ_tabQ _ i.2 j.2, list_sum_range_eq]
    push_cast; ring
  have hL : 0 ≤ ∑ i : Fin K, ∑ j : Fin K,
      (∑ r : Fin K, (matQ L i r : ℝ) * (vecQ d r : ℝ) * (matQ L j r : ℝ)) * m i * m j := by
    have heq : (∑ i : Fin K, ∑ j : Fin K,
        (∑ r : Fin K, (matQ L i r : ℝ) * (vecQ d r : ℝ) * (matQ L j r : ℝ)) * m i * m j) =
        ∑ r : Fin K, (vecQ d r : ℝ) * (∑ i : Fin K, (matQ L i r : ℝ) * m i) ^ 2 := by
      have h1 : ∀ i j : Fin K,
          (∑ r : Fin K, (matQ L i r : ℝ) * (vecQ d r : ℝ) * (matQ L j r : ℝ)) * m i * m j =
            ∑ r : Fin K, (vecQ d r : ℝ) * ((matQ L i r : ℝ) * m i) * ((matQ L j r : ℝ) * m j) :=
        fun i j => by
          rw [Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun r _ => by ring
      simp_rw [h1]
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [heq]
    exact Finset.sum_nonneg fun r _ =>
      mul_nonneg (by exact_mod_cast h.1 r r.2) (sq_nonneg _)
  have hsplit : quadR K C m = (∑ i : Fin K, ∑ j : Fin K,
      (∑ r : Fin K, (matQ L i r : ℝ) * (vecQ d r : ℝ) * (matQ L j r : ℝ)) * m i * m j) +
      quadR K (ldlResidual K C L d) m := by
    simp only [quadR, hdec, add_mul, Finset.sum_add_distrib]
  linarith

end GaloisForLFunctions.WindowTowerOfSpecZ.ApertureLogTwo
