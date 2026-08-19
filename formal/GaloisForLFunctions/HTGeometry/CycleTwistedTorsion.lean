import Mathlib

/-!
# Twisted torsion of a weighted cycle

The twisted differential of an oriented cycle with edge weights `w j` and transports `u j` is

`(d_u f) j = w j * (f (j + 1) - u j * f j)`,

with indices read cyclically.  Only two permutations contribute to its determinant — the identity
and the cyclic shift — so the determinant is the holonomy defect

`det d_u = (-1) ^ (n + 1) * (∏ j, w j) * (Hol u - 1)`,

and the associated Hodge determinant is its squared modulus.  Twisted cohomology is therefore
nonzero exactly at holonomy one: a cycle, unlike a tree, carries phase.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-- The cyclic index model of a cycle with `n + 1` edges. -/
abbrev CycleIndex (n : ℕ) : Type := ZMod (n + 1)

/-- The tautological identification of the cyclic index model with `Fin (n + 1)`. -/
def cycleIndexEquivFin (n : ℕ) : CycleIndex n ≃ Fin (n + 1) := Equiv.refl _

/-- The twisted cycle differential `(d_u f) j = w j * (f (j + 1) - u j * f j)`. -/
def cycleDifferential (n : ℕ) (w u : CycleIndex n → ℂ) :
    Matrix (CycleIndex n) (CycleIndex n) ℂ :=
  fun j k => (if k = j + 1 then w j else 0) - (if k = j then w j * u j else 0)

/-- The holonomy of a transport family around the cycle. -/
def cycleHolonomy (u : CycleIndex n → ℂ) : ℂ := ∏ j, u j

theorem cycleDifferential_apply_ne_zero {w u : CycleIndex n → ℂ} {j k : CycleIndex n}
    (h : cycleDifferential n w u j k ≠ 0) : k = j + 1 ∨ k = j := by
  by_contra hcon
  have h1 : k ≠ j + 1 := fun hk => hcon (Or.inl hk)
  have h2 : k ≠ j := fun hk => hcon (Or.inr hk)
  exact h (by simp [cycleDifferential, h1, h2])

theorem one_ne_zero_cycleIndex (hn : 1 ≤ n) : (1 : CycleIndex n) ≠ 0 := by
  intro hcon
  have hval : ((1 : ℕ) : ZMod (n + 1)) = ((0 : ℕ) : ZMod (n + 1)) := by
    simpa using hcon
  have := (ZMod.natCast_eq_natCast_iff' 1 0 (n + 1)).mp hval
  rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at this
  exact one_ne_zero this

/-- A permutation moving every index by at most one step backwards along a cycle of length at
least two is either the identity or the cyclic shift. -/
theorem perm_eq_subRight_of_forall (hn : 1 ≤ n) (σ : Equiv.Perm (CycleIndex n))
    (h : ∀ i, σ i = i ∨ σ i = i - 1) (hne : σ ≠ 1) :
    σ = Equiv.subRight (1 : CycleIndex n) := by
  have hone : (1 : CycleIndex n) ≠ 0 := one_ne_zero_cycleIndex hn
  obtain ⟨i₀, hi₀⟩ : ∃ i, σ i ≠ i := by
    by_contra hcon
    refine hne (Equiv.ext fun i => ?_)
    have hi : σ i = i := not_not.mp fun hni => hcon ⟨i, hni⟩
    simpa using hi
  have hstep : ∀ k : ℕ, σ (i₀ - (k : CycleIndex n)) = i₀ - (k : CycleIndex n) - 1 := by
    intro k
    induction k with
    | zero =>
      have h0 := (h i₀).resolve_left hi₀
      simpa using h0
    | succ k ih =>
      have hy := h (i₀ - (k : CycleIndex n) - 1)
      have hxy : σ (i₀ - (k : CycleIndex n) - 1) = i₀ - (k : CycleIndex n) - 1 - 1 := by
        rcases hy with hy | hy
        · exfalso
          have hinj : i₀ - (k : CycleIndex n) - 1 = i₀ - (k : CycleIndex n) :=
            σ.injective (by rw [hy, ih])
          have hzero : (1 : CycleIndex n) = 0 := by
            have := sub_eq_self.mp hinj
            simpa using this
          exact hone hzero
        · exact hy
      have hcast : i₀ - ((k + 1 : ℕ) : CycleIndex n) = i₀ - (k : CycleIndex n) - 1 := by
        push_cast
        ring
      rw [hcast, hxy]
  refine Equiv.ext fun j => ?_
  have hk : (((i₀ - j).val : ℕ) : CycleIndex n) = i₀ - j := ZMod.natCast_zmod_val _
  have hj := hstep ((i₀ - j).val)
  rw [hk] at hj
  have hjj : i₀ - (i₀ - j) = j := by ring
  rw [hjj] at hj
  simpa [Equiv.subRight_apply] using hj

theorem sign_subRight_one_cycleIndex :
    Equiv.Perm.sign (Equiv.subRight (1 : CycleIndex n)) = (-1) ^ n := by
  have h2 : (cycleIndexEquivFin n).permCongr (Equiv.addRight (1 : CycleIndex n))
      = finRotate (n + 1) := by
    ext i
    rw [finRotate_apply]
    rfl
  have h1 : (Equiv.subRight (1 : CycleIndex n)) = (Equiv.addRight (1 : CycleIndex n))⁻¹ := by
    ext i
    simp [Equiv.subRight_apply, sub_eq_add_neg]
  rw [h1, map_inv,
    ← Equiv.Perm.sign_permCongr (cycleIndexEquivFin n) (Equiv.addRight (1 : CycleIndex n)), h2,
    sign_finRotate]
  rfl

/-- **Cycle torsion determinant.**  Only the identity and the cyclic shift contribute, so the
determinant of the twisted cycle differential is the holonomy defect weighted by the edge
weights. -/
theorem det_cycleDifferential (w u : CycleIndex n → ℂ) :
    (cycleDifferential n w u).det = (-1) ^ (n + 1) * (∏ j, w j) * (cycleHolonomy u - 1) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hcard : Fintype.card (CycleIndex 0) = 1 := by simp [CycleIndex]
    have hsub : ∀ i j : CycleIndex 0, i = j := by
      intro i j
      exact Fintype.card_le_one_iff.mp (le_of_eq hcard) i j
    rw [Matrix.det_eq_elem_of_card_eq_one hcard 0]
    have hprodw : (∏ j : CycleIndex 0, w j) = w 0 := by
      rw [Finset.prod_eq_single (0 : CycleIndex 0) (fun b _ hb => absurd (hsub b 0) hb)
        (fun h => absurd (Finset.mem_univ _) h)]
    have hprodu : cycleHolonomy u = u 0 := by
      rw [cycleHolonomy, Finset.prod_eq_single (0 : CycleIndex 0)
        (fun b _ hb => absurd (hsub b 0) hb) (fun h => absurd (Finset.mem_univ _) h)]
    rw [hprodw, hprodu]
    simp only [cycleDifferential, hsub ((0 : CycleIndex 0) + 1) 0, if_true]
    ring
  · have hone : (1 : CycleIndex n) ≠ 0 := one_ne_zero_cycleIndex hn
    have hne_succ : ∀ i : CycleIndex n, (i : CycleIndex n) ≠ i + 1 := by
      intro i hcon
      exact hone (by linear_combination -hcon)
    have hne_pred : ∀ i : CycleIndex n, (i : CycleIndex n) ≠ i - 1 := by
      intro i hcon
      exact hone (by linear_combination hcon)
    set τ : Equiv.Perm (CycleIndex n) := Equiv.subRight (1 : CycleIndex n) with hτ
    have hτne : τ ≠ 1 := by
      intro hcon
      have h0 : τ 0 = (0 : CycleIndex n) := by rw [hcon]; rfl
      have h0' : (0 : CycleIndex n) - 1 = 0 := by
        simpa [hτ, Equiv.subRight_apply] using h0
      exact hne_pred 0 h0'.symm
    have hvanish : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (CycleIndex n))),
        σ ∉ ({1, τ} : Finset (Equiv.Perm (CycleIndex n))) →
        Equiv.Perm.sign σ • ∏ i, cycleDifferential n w u (σ i) i = 0 := by
      intro σ _ hσ
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hσ
      have hprod : ∏ i, cycleDifferential n w u (σ i) i = 0 := by
        by_contra hcon
        have hall : ∀ i : CycleIndex n, cycleDifferential n w u (σ i) i ≠ 0 := fun i =>
          Finset.prod_ne_zero_iff.mp hcon i (Finset.mem_univ i)
        have hstep : ∀ i : CycleIndex n, σ i = i ∨ σ i = i - 1 := by
          intro i
          rcases cycleDifferential_apply_ne_zero (hall i) with h | h
          · right
            linear_combination -h
          · left
            exact h.symm
        exact hσ.2 (perm_eq_subRight_of_forall hn σ hstep hσ.1)
      rw [hprod, smul_zero]
    rw [Matrix.det_apply, ← Finset.sum_subset (Finset.subset_univ ({1, τ} :
      Finset (Equiv.Perm (CycleIndex n)))) hvanish, Finset.sum_pair (Ne.symm hτne)]
    have hdiag : ∏ i, cycleDifferential n w u ((1 : Equiv.Perm (CycleIndex n)) i) i
        = (-1) ^ (n + 1) * (∏ j, w j) * cycleHolonomy u := by
      have hentry : ∀ i : CycleIndex n, cycleDifferential n w u i i = -(w i * u i) := by
        intro i
        simp [cycleDifferential, (hne_succ i)]
      simp only [Equiv.Perm.one_apply, hentry]
      rw [Finset.prod_neg, Finset.prod_mul_distrib, cycleHolonomy, Finset.card_univ,
        ZMod.card]
      ring
    have hshift : ∏ i, cycleDifferential n w u (τ i) i = ∏ j, w j := by
      have hval : ∀ i : CycleIndex n, cycleDifferential n w u (τ i) i = w (i - 1) := by
        intro i
        have h1 : (i : CycleIndex n) = (i - 1) + 1 := by ring
        have h2 : (i : CycleIndex n) ≠ i - 1 := hne_pred i
        simp [cycleDifferential, hτ, Equiv.subRight_apply, ← h1, h2]
      simp only [hval]
      exact Equiv.prod_comp (Equiv.subRight (1 : CycleIndex n)) w
    rw [hdiag, hshift, sign_subRight_one_cycleIndex, Equiv.Perm.sign_one]
    have hcast : ((((-1 : ℤˣ) ^ n : ℤˣ) : ℤ) : ℂ) = (-1 : ℂ) ^ n := by
      have h : ((((-1 : ℤˣ) ^ n : ℤˣ) : ℤ)) = ((-1 : ℤ)) ^ n := Units.val_pow_eq_pow_val _ _
      rw [h]
      push_cast
      ring
    simp only [Units.smul_def, zsmul_eq_mul, Units.val_one, Int.cast_one, one_mul, hcast]
    ring

/-- **Hodge determinant of the twisted cycle.**  It is the squared modulus of the torsion. -/
theorem det_conjTranspose_mul_cycleDifferential (w u : CycleIndex n → ℂ) :
    ((cycleDifferential n w u)ᴴ * cycleDifferential n w u).det
      = ((∏ j, ‖w j‖ ^ 2 : ℝ) : ℂ) * ((‖1 - cycleHolonomy u‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, det_cycleDifferential]
  rw [← Complex.ofReal_mul]
  congr 1
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_prod,
    ← norm_neg (cycleHolonomy u - 1), neg_sub]
  rw [mul_pow, ← Finset.prod_pow]

/-- **Twisted cohomology of a cycle is nonzero exactly at holonomy one.** -/
theorem det_cycleDifferential_eq_zero_iff {w u : CycleIndex n → ℂ} (hw : ∀ j, w j ≠ 0) :
    (cycleDifferential n w u).det = 0 ↔ cycleHolonomy u = 1 := by
  rw [det_cycleDifferential]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact absurd h3 (pow_ne_zero _ (by norm_num))
      · exact absurd h4 (Finset.prod_ne_zero_iff.mpr fun j _ => hw j)
    · linear_combination h2
  · intro h
    rw [h]
    ring

/-- **Hodge determinant with positive conductances.**  Writing the edge weights as square roots of
conductances, the twisted Hodge determinant is the product of the conductances times the squared
modulus of the holonomy defect. -/
theorem det_cycleHodge_of_conductances (c : CycleIndex n → ℝ) (hc : ∀ j, 0 ≤ c j)
    (u : CycleIndex n → ℂ) :
    ((cycleDifferential n (fun j => (Real.sqrt (c j) : ℂ)) u)ᴴ *
        cycleDifferential n (fun j => (Real.sqrt (c j) : ℂ)) u).det
      = ((∏ j, c j : ℝ) : ℂ) * ((‖1 - cycleHolonomy u‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_conjTranspose_mul_cycleDifferential]
  congr 2
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hc j)]

end GaloisForLFunctions.HTGeometry
