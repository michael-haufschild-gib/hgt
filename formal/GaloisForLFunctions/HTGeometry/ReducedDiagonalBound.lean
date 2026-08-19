import GaloisForLFunctions.HTGeometry.OrderSizeReduction

/-!
# Bounding the Jacobi diagonal of a reduced form of bounded determinant

For a Siegel-reduced form whose determinant is bounded above and whose leading minors are bounded
below, every entry of the Jacobi diagonal is bounded above: the leading minor lower bound controls
the head of the product, the Siegel ordering controls the tail by the entry itself, and the
determinant bound closes the loop.

* `prod_filter_lt_eq_det_leadingBlock` : the head of the diagonal product is a leading minor.
* `d_le_of_det_le_of_siegel` : the entries of the diagonal are bounded, in exponentiated form.
* `d_le_bound_of_siegel` : **the entries of the diagonal are bounded.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {k : ℕ}

theorem prod_filter_lt_eq_det_leadingBlock (J : JacobiData k) (i : Fin k) :
    (∏ m ∈ Finset.univ.filter (fun m : Fin k => m < i), J.d m)
      = (leadingBlock (le_of_lt i.isLt) J.form).det := by
  classical
  rw [det_leadingBlock_form (le_of_lt i.isLt) J]
  have hinj : Set.InjOn (Fin.castLE (le_of_lt i.isLt))
      ((Finset.univ : Finset (Fin (i : ℕ))) : Set (Fin (i : ℕ))) := by
    intro a _ b _ hab
    exact Fin.ext (by simpa using congrArg Fin.val hab)
  rw [← Finset.prod_image (f := fun m : Fin k => J.d m) hinj]
  congr 1
  ext m
  constructor
  · intro hm
    rw [Finset.mem_filter] at hm
    refine Finset.mem_image.2 ⟨⟨(m : ℕ), Fin.lt_def.1 hm.2⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro hm
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hm
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    refine Fin.lt_def.2 ?_
    rw [← ha]
    simp

theorem prod_filter_split (J : JacobiData k) (i : Fin k) :
    (∏ m ∈ Finset.univ.filter (fun m : Fin k => m < i), J.d m)
        * (∏ m ∈ Finset.univ.filter (fun m : Fin k => ¬ m < i), J.d m)
      = J.form.det := by
  classical
  rw [J.det_form]
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m : Fin k => m < i) J.d

/-- **The entries of the Jacobi diagonal of a reduced form of bounded determinant are bounded.** -/
theorem d_le_of_det_le_of_siegel {J : JacobiData k} {lam B : ℝ} (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hS : J.IsSiegel 2 1)
    (hlow : ∀ (j : ℕ) (hj : j ≤ k), lam ^ j ≤ (leadingBlock hj J.form).det)
    (hdet : J.form.det ≤ B) (i : Fin k) :
    J.d i ^ (Finset.univ.filter (fun m : Fin k => ¬ m < i)).card
      ≤ 2 ^ (k * k) * B / lam ^ k := by
  classical
  have hlamk : (0 : ℝ) < lam ^ k := pow_pos hlam k
  have hhead : lam ^ k ≤ ∏ m ∈ Finset.univ.filter (fun m : Fin k => m < i), J.d m := by
    rw [prod_filter_lt_eq_det_leadingBlock]
    refine le_trans ?_ (hlow (i : ℕ) (le_of_lt i.isLt))
    exact pow_le_pow_of_le_one hlam.le hlam1 (le_of_lt i.isLt)
  have htailpos : (0 : ℝ) < ∏ m ∈ Finset.univ.filter (fun m : Fin k => ¬ m < i), J.d m :=
    Finset.prod_pos fun m _ => J.pos m
  have hsplit := prod_filter_split J i
  have htail : (∏ m ∈ Finset.univ.filter (fun m : Fin k => ¬ m < i), J.d m) ≤ B / lam ^ k := by
    rw [le_div_iff₀ hlamk]
    calc (∏ m ∈ Finset.univ.filter (fun m : Fin k => ¬ m < i), J.d m) * lam ^ k
        ≤ (∏ m ∈ Finset.univ.filter (fun m : Fin k => ¬ m < i), J.d m)
            * (∏ m ∈ Finset.univ.filter (fun m : Fin k => m < i), J.d m) :=
          mul_le_mul_of_nonneg_left hhead htailpos.le
      _ = J.form.det := by rw [mul_comm]; exact hsplit
      _ ≤ B := hdet
  -- each tail factor is at least `2 ^ (-k) * J.d i`
  have hfac : ∀ m ∈ Finset.univ.filter (fun m : Fin k => ¬ m < i),
      J.d i ≤ 2 ^ k * J.d m := by
    intro m hm
    rw [Finset.mem_filter] at hm
    exact J.d_le_pow_n (by norm_num) hS (Fin.le_def.1 (not_lt.1 hm.2))
  set c : ℕ := (Finset.univ.filter (fun m : Fin k => ¬ m < i)).card with hc
  have hprod : J.d i ^ c ≤ (2 ^ k) ^ c
      * ∏ m ∈ Finset.univ.filter (fun m : Fin k => ¬ m < i), J.d m := by
    have hc1 : (J.d i) ^ c
        = ∏ _m ∈ Finset.univ.filter (fun m : Fin k => ¬ m < i), J.d i := by
      rw [Finset.prod_const, hc]
    have hc2 : ((2 : ℝ) ^ k) ^ c
          * ∏ m ∈ Finset.univ.filter (fun m : Fin k => ¬ m < i), J.d m
        = ∏ m ∈ Finset.univ.filter (fun m : Fin k => ¬ m < i), (2 ^ k * J.d m) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, hc]
    rw [hc1, hc2]
    exact Finset.prod_le_prod (fun m _ => (J.pos i).le) (fun m hm => hfac m hm)
  have hck : c ≤ k := by
    rw [hc]
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin k)) _
  have h2 : ((2 : ℝ) ^ k) ^ c ≤ 2 ^ (k * k) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left k hck)
  have hB0 : (0 : ℝ) ≤ B / lam ^ k := le_trans htailpos.le htail
  calc J.d i ^ c ≤ (2 ^ k) ^ c
        * ∏ m ∈ Finset.univ.filter (fun m : Fin k => ¬ m < i), J.d m := hprod
    _ ≤ 2 ^ (k * k) * (B / lam ^ k) := by
        refine mul_le_mul h2 htail htailpos.le (by positivity)
    _ = 2 ^ (k * k) * B / lam ^ k := by ring

/-- **The entries of the Jacobi diagonal of a reduced form of bounded determinant are bounded.** -/
theorem d_le_bound_of_siegel {J : JacobiData k} {lam B : ℝ} (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hS : J.IsSiegel 2 1)
    (hlow : ∀ (j : ℕ) (hj : j ≤ k), lam ^ j ≤ (leadingBlock hj J.form).det)
    (hdet : J.form.det ≤ B) (i : Fin k) :
    J.d i ≤ max 1 (2 ^ (k * k) * B / lam ^ k) := by
  classical
  have hpow := d_le_of_det_le_of_siegel hlam hlam1 hS hlow hdet i
  have hmem : i ∈ Finset.univ.filter (fun m : Fin k => ¬ m < i) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ i, lt_irrefl i⟩
  have hc1 : (Finset.univ.filter (fun m : Fin k => ¬ m < i)).card ≠ 0 :=
    (Finset.card_pos.2 ⟨i, hmem⟩).ne'
  by_cases h : J.d i ≤ 1
  · exact le_trans h (le_max_left _ _)
  · have h1 : (1 : ℝ) ≤ J.d i := le_of_lt (not_le.1 h)
    have hself : J.d i ≤ J.d i ^ (Finset.univ.filter (fun m : Fin k => ¬ m < i)).card :=
      le_self_pow₀ h1 hc1
    exact le_trans hself (le_trans hpow (le_max_right _ _))

end GaloisForLFunctions.HTGeometry
