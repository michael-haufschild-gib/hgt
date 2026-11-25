import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedPresentations
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Abel

/-! A homogeneous element vanishes after setting a variable equal to one exactly when
a power of that variable kills it. -/

open DirectSum MvPolynomial

namespace GlobalTheory

theorem exists_pow_smul_eq_add_sub_one_smul {S M : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] (x : S) (k : ℕ) (y : M) :
    ∃ w : M, x ^ k • y = y + (x - 1) • w := by
  refine ⟨(∑ j ∈ Finset.range k, x ^ j) • y, ?_⟩
  rw [smul_smul, mul_geom_sum, sub_smul, one_smul]
  abel

section

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (D : ℤ → Submodule R M) [PolyGradedSMul ι D] [Decomposition D] (i : ι)

private theorem proj_x_sub_one (w : M) (j : ℤ) :
    gradedProj D (j + 1) ((X i - 1 : MvPolynomial ι R) • w) =
      (X i : MvPolynomial ι R) • gradedProj D j w - gradedProj D (j + 1) w := by
  rw [sub_smul, one_smul, map_sub, proj_smul_of_mem (X_mem_polyGrading i)]

omit [IsScalarTower R (MvPolynomial ι R) M] [PolyGradedSMul ι D] in
private theorem proj_vanish_outside (w : M) :
    ∃ l u : ℤ, ∀ j : ℤ, j < l ∨ u < j → gradedProj D j w = 0 := by
  classical
  obtain ⟨l, hl⟩ := (decompose D w).support.bddBelow
  obtain ⟨u, hu⟩ := (decompose D w).support.bddAbove
  refine ⟨l, u, fun j hj => ?_⟩
  have h : j ∉ (decompose D w).support := fun hj' => by
    exact hj.elim (not_lt_of_ge (hl hj')) (not_lt_of_ge (hu hj'))
  change (decompose D w j : M) = 0
  rw [DFinsupp.notMem_support_iff.1 h, Submodule.coe_zero]

include i in
omit [Module R M] [IsScalarTower R (MvPolynomial ι R) M] in
private theorem recurrence_zero_below {v : ℤ → M} {l c : ℤ}
    (hl : ∀ j < l, v j = 0)
    (h : ∀ m < c, v (m + 1) = (X i : MvPolynomial ι R) • v m) : v c = 0 := by
  have iterate (k : ℕ) : v c = (X i : MvPolynomial ι R) ^ k • v (c - k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have he : c - (k : ℤ) = c - ((k + 1 : ℕ) : ℤ) + 1 := by omega
      rw [ih, he, h _ (by omega), ← mul_smul, ← pow_succ]
  rw [iterate (c - l + 1).toNat, hl _ (by omega), smul_zero]

include D in
/-- Multiplication by `X i - 1` is injective, by the least degree of the support. -/
theorem eq_zero_of_X_sub_one_smul_eq_zero {w : M}
    (hw : (X i - 1 : MvPolynomial ι R) • w = 0) : w = 0 := by
  classical
  obtain ⟨l, _, hvanish⟩ := proj_vanish_outside D w
  have hrec (j : ℤ) : gradedProj D (j + 1) w = (X i : MvPolynomial ι R) • gradedProj D j w := by
    have he := proj_x_sub_one D i w j
    rw [hw, map_zero] at he
    exact (sub_eq_zero.1 he.symm).symm
  rw [← sum_support_gradedProj D w]
  exact Finset.sum_eq_zero fun c _ =>
    recurrence_zero_below i (fun j hj => hvanish j (Or.inl hj)) (fun m _ => hrec m)

theorem exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul {n : ℤ} {z w : M}
    (hz : z ∈ D n) (h : z = (X i - 1 : MvPolynomial ι R) • w) :
    ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z = 0 := by
  have hcomp (j : ℤ) := (congrArg (gradedProj D (j + 1)) h).trans (proj_x_sub_one D i w j)
  have hrec (j : ℤ) (hj : j + 1 ≠ n) :
      gradedProj D (j + 1) w = (X i : MvPolynomial ι R) • gradedProj D j w := by
    have he := hcomp j
    rw [gradedProj_of_mem_ne D hz hj.symm] at he
    exact (sub_eq_zero.1 he.symm).symm
  obtain ⟨l, u, hvanish⟩ := proj_vanish_outside D w
  have hprev : gradedProj D (n - 1) w = 0 :=
    recurrence_zero_below i (fun j hj => hvanish j (Or.inl hj))
      (fun j hj => hrec j (by omega))
  have hzn : z = -gradedProj D n w := by
    have he := hcomp (n - 1)
    rw [sub_add_cancel, gradedProj_of_mem D hz, hprev, smul_zero, zero_sub] at he
    exact he
  have iterate (k : ℕ) : gradedProj D (n + k) w =
      (X i : MvPolynomial ι R) ^ k • gradedProj D n w := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc, hrec _ (by omega), ih, ← mul_smul, ← pow_succ']
  refine ⟨(u - n + 1).toNat, ?_⟩
  rw [hzn, smul_neg, ← iterate, hvanish _ (Or.inr (by omega)), neg_zero]

omit [Decomposition D] [IsScalarTower R (MvPolynomial ι R) M] in
theorem X_pow_smul_mem_add {n : ℤ} {m : M} (hm : m ∈ D n) (k : ℕ) :
    (X i : MvPolynomial ι R) ^ k • m ∈ D (n + k) := by
  induction k with
  | zero => simpa using hm
  | succ k ih =>
    rw [pow_succ', mul_smul, Nat.cast_succ, ← add_assoc]
    exact grSMul_mem D (X_mem_polyGrading i) ih

omit [IsScalarTower R (MvPolynomial ι R) M] in
/-- After setting `X i = 1`, a class has homogeneous representatives in all
sufficiently large degrees. -/
theorem exists_homogeneous_add_X_sub_one_smul (y : M) :
    ∃ l : ℤ, ∀ n ≥ l, ∃ a ∈ D n, ∃ w, y = a + (X i - 1 : MvPolynomial ι R) • w := by
  induction y using Decomposition.inductionOn D with
  | zero => exact ⟨0, fun n _ => ⟨0, zero_mem _, 0, by simp⟩⟩
  | @homogeneous d m =>
    refine ⟨d, fun n hn => ?_⟩
    have hd : d + ((n - d).toNat : ℤ) = n := by omega
    obtain ⟨w, hw⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) (n - d).toNat (m : M)
    refine ⟨_, hd ▸ X_pow_smul_mem_add D i m.2 (n - d).toNat, -w, ?_⟩
    rw [smul_neg, hw]
    abel
  | add a b ha hb =>
    obtain ⟨la, ha⟩ := ha
    obtain ⟨lb, hb⟩ := hb
    refine ⟨max la lb, fun n hn => ?_⟩
    obtain ⟨a', ha', x, hx⟩ := ha n ((le_max_left _ _).trans hn)
    obtain ⟨b', hb', y, hy⟩ := hb n ((le_max_right _ _).trans hn)
    exact ⟨a' + b', add_mem ha' hb', x + y, by rw [hx, hy, smul_add, add_add_add_comm]⟩

end

end GlobalTheory
