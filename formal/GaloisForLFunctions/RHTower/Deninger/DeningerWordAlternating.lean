import GaloisForLFunctions.RHTower.Deninger.DeningerBarSlice

/-!
# The blockwise alternating projector on the entire word-height source

Permuting the letters of a word preserves both its length and the product of its letter heights,
so reindexing a weighted word series by a permutation is an isometry of every length slice.  The
blockwise antisymmetrizer is the average of the `r!` signed reindexings, so it decreases every
seminorm:

`p_k(Alt a) ≤ p_k(a)`.

The entire exterior completion of the source is its range, hence a closed complemented subspace of
a complete nuclear space.

* `deningerPermuteAt`, `deningerPermEquiv` : the permutation action on words of a fixed length.
* `deningerAltCoe`, `deningerAlt` : the blockwise antisymmetrizer.
* `deningerBarSeminormR_alt_le` : **it decreases every seminorm.**
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## The permutation action -/

/-- Permute the letters of a word of a fixed length. -/
def deningerPermuteAt {r : ℕ} (σ : Equiv.Perm (Fin (r + 1)))
    (f : Fin (r + 1) → DeningerPrimeLattice) : DeningerBarWord :=
  ⟨r, f ∘ σ⟩

@[simp]
theorem deningerPermuteAt_length {r : ℕ} (σ : Equiv.Perm (Fin (r + 1)))
    (f : Fin (r + 1) → DeningerPrimeLattice) :
    deningerBarLength (deningerPermuteAt σ f)
      = deningerBarLength (⟨r, f⟩ : DeningerBarWord) := rfl

theorem deningerPermuteAt_height {r : ℕ} (σ : Equiv.Perm (Fin (r + 1)))
    (f : Fin (r + 1) → DeningerPrimeLattice) :
    deningerBarHeight (deningerPermuteAt σ f)
      = deningerBarHeight (⟨r, f⟩ : DeningerBarWord) := by
  show (∏ j, deningerHeight (f (σ j))) = ∏ j, deningerHeight (f j)
  exact Equiv.prod_comp σ (fun j => deningerHeight (f j))

/-- Precomposition with a permutation, as an equivalence of coefficient tuples. -/
def deningerPermEquiv {r : ℕ} (σ : Equiv.Perm (Fin (r + 1))) :
    (Fin (r + 1) → DeningerPrimeLattice) ≃ (Fin (r + 1) → DeningerPrimeLattice) :=
  Equiv.arrowCongr σ.symm (Equiv.refl DeningerPrimeLattice)

@[simp]
theorem deningerPermEquiv_apply {r : ℕ} (σ : Equiv.Perm (Fin (r + 1)))
    (f : Fin (r + 1) → DeningerPrimeLattice) :
    deningerPermEquiv σ f = f ∘ σ := rfl

theorem deningerBarWeightR_permute (k : ℕ) (R : ℝ) {r : ℕ}
    (σ : Equiv.Perm (Fin (r + 1))) (f : Fin (r + 1) → DeningerPrimeLattice) :
    deningerBarWeightR k R (deningerPermuteAt σ f)
      = deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) := by
  rw [deningerBarWeightR, deningerBarWeightR, deningerPermuteAt_height,
    deningerPermuteAt_length]

/-! ## The antisymmetrizer -/

/-- **The blockwise antisymmetrizer** of the entire word-height source. -/
def deningerAltCoe (a : DeningerBarWord → ℂ) : DeningerBarWord → ℂ := fun w =>
  ((Nat.factorial (w.1 + 1) : ℂ))⁻¹ *
    ∑ σ : Equiv.Perm (Fin (w.1 + 1)),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * a (deningerPermuteAt σ w.2)

theorem deningerAltCoe_norm_le (a : DeningerBarWord → ℂ) (w : DeningerBarWord) :
    ‖deningerAltCoe a w‖
      ≤ ((Nat.factorial (w.1 + 1) : ℝ))⁻¹ *
        ∑ σ : Equiv.Perm (Fin (w.1 + 1)), ‖a (deningerPermuteAt σ w.2)‖ := by
  rw [deningerAltCoe, norm_mul]
  have hfac : ‖((Nat.factorial (w.1 + 1) : ℂ))⁻¹‖ = ((Nat.factorial (w.1 + 1) : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hfac]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [norm_mul]
  have hsign : ‖(((Equiv.Perm.sign σ : ℤ)) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num
  rw [hsign, one_mul]

/-! ## The seminorm estimate -/

private theorem deningerAlt_permuted_slice {k : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (c : DeningerBarKothe) (r : ℕ) (σ : Equiv.Perm (Fin (r + 1))) :
    (Summable fun f : Fin (r + 1) → DeningerPrimeLattice =>
        deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
          ‖(c : DeningerBarWord → ℂ) (deningerPermuteAt σ f)‖) ∧
      (∑' f : Fin (r + 1) → DeningerPrimeLattice,
          deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
            ‖(c : DeningerBarWord → ℂ) (deningerPermuteAt σ f)‖)
        = deningerBarSliceR k R (c : DeningerBarWord → ℂ) r := by
  have hterm : ∀ f : Fin (r + 1) → DeningerPrimeLattice,
      deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
          ‖(c : DeningerBarWord → ℂ) (deningerPermuteAt σ f)‖
        = (fun g : Fin (r + 1) → DeningerPrimeLattice =>
            deningerBarWeightR k R (⟨r, g⟩ : DeningerBarWord) *
              ‖(c : DeningerBarWord → ℂ) (⟨r, g⟩ : DeningerBarWord)‖)
          (deningerPermEquiv σ f) := by
    intro f
    show _ = deningerBarWeightR k R (⟨r, f ∘ σ⟩ : DeningerBarWord) *
      ‖(c : DeningerBarWord → ℂ) (⟨r, f ∘ σ⟩ : DeningerBarWord)‖
    rw [show (⟨r, f ∘ σ⟩ : DeningerBarWord) = deningerPermuteAt σ f from rfl,
      deningerBarWeightR_permute]
  constructor
  · refine ((deningerPermEquiv σ).summable_iff
      (f := fun g : Fin (r + 1) → DeningerPrimeLattice =>
        deningerBarWeightR k R (⟨r, g⟩ : DeningerBarWord) *
          ‖(c : DeningerBarWord → ℂ) (⟨r, g⟩ : DeningerBarWord)‖)).mpr
      (deningerBarSlice_summable hR c r) |>.congr ?_
    intro f
    exact (hterm f).symm
  · rw [tsum_congr hterm,
      (deningerPermEquiv σ).tsum_eq (fun g : Fin (r + 1) → DeningerPrimeLattice =>
        deningerBarWeightR k R (⟨r, g⟩ : DeningerBarWord) *
          ‖(c : DeningerBarWord → ℂ) (⟨r, g⟩ : DeningerBarWord)‖),
      deningerBarSliceR]

/-- **The antisymmetrizer decreases every seminorm.** -/
theorem deningerAlt_slice_le {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerBarKothe) (r : ℕ) :
    (Summable fun f : Fin (r + 1) → DeningerPrimeLattice =>
        deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
          ‖deningerAltCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖) ∧
      (∑' f : Fin (r + 1) → DeningerPrimeLattice,
          deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
            ‖deningerAltCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖)
        ≤ deningerBarSliceR k R (c : DeningerBarWord → ℂ) r := by
  classical
  have hRpos : (0 : ℝ) < R := by linarith
  have hfacpos : (0 : ℝ) < (Nat.factorial (r + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (r + 1)
  set G : Equiv.Perm (Fin (r + 1)) → (Fin (r + 1) → DeningerPrimeLattice) → ℝ := fun σ f =>
    ((Nat.factorial (r + 1) : ℝ))⁻¹ *
      (deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
        ‖(c : DeningerBarWord → ℂ) (deningerPermuteAt σ f)‖) with hG
  have hGsummable : ∀ σ, Summable (G σ) := fun σ =>
    ((deningerAlt_permuted_slice hR c r σ).1).mul_left _
  have hmaj : Summable fun f : Fin (r + 1) → DeningerPrimeLattice =>
      ∑ σ : Equiv.Perm (Fin (r + 1)), G σ f :=
    summable_sum fun σ _ => hGsummable σ
  have hpointwise : ∀ f : Fin (r + 1) → DeningerPrimeLattice,
      deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
          ‖deningerAltCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖
        ≤ ∑ σ : Equiv.Perm (Fin (r + 1)), G σ f := by
    intro f
    have hb := deningerAltCoe_norm_le (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)
    have hwnn : 0 ≤ deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) :=
      deningerBarWeightR_nonneg k hRpos.le _
    calc deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
          ‖deningerAltCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖
        ≤ deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
            (((Nat.factorial (r + 1) : ℝ))⁻¹ *
              ∑ σ : Equiv.Perm (Fin (r + 1)),
                ‖(c : DeningerBarWord → ℂ) (deningerPermuteAt σ f)‖) :=
          mul_le_mul_of_nonneg_left hb hwnn
      _ = ∑ σ : Equiv.Perm (Fin (r + 1)), G σ f := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [hG]
          ring
  have hsummable : Summable fun f : Fin (r + 1) → DeningerPrimeLattice =>
      deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
        ‖deningerAltCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖ :=
    Summable.of_nonneg_of_le
      (fun f => mul_nonneg (deningerBarWeightR_nonneg k hRpos.le _) (norm_nonneg _))
      hpointwise hmaj
  refine ⟨hsummable, ?_⟩
  have hstep : (∑' f : Fin (r + 1) → DeningerPrimeLattice,
        deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
          ‖deningerAltCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖)
      ≤ ∑' f : Fin (r + 1) → DeningerPrimeLattice, ∑ σ : Equiv.Perm (Fin (r + 1)), G σ f :=
    Summable.tsum_le_tsum hpointwise hsummable hmaj
  have hswap : (∑' f : Fin (r + 1) → DeningerPrimeLattice,
        ∑ σ : Equiv.Perm (Fin (r + 1)), G σ f)
      = ∑ σ : Equiv.Perm (Fin (r + 1)), ∑' f : Fin (r + 1) → DeningerPrimeLattice, G σ f :=
    Summable.tsum_finsetSum fun σ _ => hGsummable σ
  have hone : ∀ σ : Equiv.Perm (Fin (r + 1)),
      (∑' f : Fin (r + 1) → DeningerPrimeLattice, G σ f)
        = ((Nat.factorial (r + 1) : ℝ))⁻¹ *
          deningerBarSliceR k R (c : DeningerBarWord → ℂ) r := by
    intro σ
    rw [hG, Summable.tsum_mul_left _ ((deningerAlt_permuted_slice hR c r σ).1),
      (deningerAlt_permuted_slice hR c r σ).2]
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin (r + 1)))).card
      = Nat.factorial (r + 1) := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [hswap, Finset.sum_congr rfl fun σ _ => hone σ, Finset.sum_const, hcard,
    nsmul_eq_mul] at hstep
  have hfin : ((Nat.factorial (r + 1) : ℝ)) *
      (((Nat.factorial (r + 1) : ℝ))⁻¹ *
        deningerBarSliceR k R (c : DeningerBarWord → ℂ) r)
      = deningerBarSliceR k R (c : DeningerBarWord → ℂ) r := by
    field_simp
  rw [hfin] at hstep
  exact hstep

/-! ## The antisymmetrizer as an operator of the source -/

private theorem deningerBarKotheData_weightR (k : ℕ) (w : DeningerBarWord) :
    deningerBarKotheData.w k w = deningerBarWeightR k ((k : ℝ) + 1) w := by
  rw [deningerBarKotheData_w, deningerBarWeightR]
  ring

theorem deningerAltCoe_mem (c : DeningerBarKothe) :
    deningerAltCoe (c : DeningerBarWord → ℂ) ∈ DeningerBarKothe := by
  intro k
  have hR : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hnn : ∀ w : DeningerBarWord,
      0 ≤ deningerBarKotheData.w k w *
        ‖deningerAltCoe (c : DeningerBarWord → ℂ) w‖ := fun w =>
    mul_nonneg (deningerBarKotheData.pos k w).le (norm_nonneg _)
  refine (summable_sigma_of_nonneg hnn).mpr ⟨fun r => ?_, ?_⟩
  · refine ((deningerAlt_slice_le (k := k) hR c r).1).congr fun f => ?_
    rw [deningerBarKotheData_weightR]
  · refine Summable.of_nonneg_of_le (fun r => tsum_nonneg fun f => hnn _) (fun r => ?_)
      (deningerBarSliceR_summable (k := k) hR c)
    have hcongr : (∑' f : Fin (r + 1) → DeningerPrimeLattice,
        deningerBarKotheData.w k (⟨r, f⟩ : DeningerBarWord) *
          ‖deningerAltCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖)
        = ∑' f : Fin (r + 1) → DeningerPrimeLattice,
            deningerBarWeightR k ((k : ℝ) + 1) (⟨r, f⟩ : DeningerBarWord) *
              ‖deningerAltCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖ := by
      refine tsum_congr fun f => ?_
      rw [deningerBarKotheData_weightR]
    rw [hcongr]
    exact (deningerAlt_slice_le (k := k) hR c r).2

/-- **The blockwise antisymmetrizer** as an operator of the entire word-height source. -/
def deningerAlt : DeningerBarKothe →ₗ[ℂ] DeningerBarKothe where
  toFun c := ⟨deningerAltCoe (c : DeningerBarWord → ℂ), deningerAltCoe_mem c⟩
  map_add' a b := by
    ext w
    show deningerAltCoe ((a + b : DeningerBarKothe) : DeningerBarWord → ℂ) w = _
    simp only [Submodule.coe_add, Pi.add_apply, deningerAltCoe]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  map_smul' t a := by
    ext w
    show deningerAltCoe ((t • a : DeningerBarKothe) : DeningerBarWord → ℂ) w = _
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, deningerAltCoe,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    show ((Nat.factorial (w.1 + 1) : ℂ))⁻¹ *
        (((Equiv.Perm.sign σ : ℤ) : ℂ) *
          (t * (a : DeningerBarWord → ℂ) (deningerPermuteAt σ w.2)))
      = t * (((Nat.factorial (w.1 + 1) : ℂ))⁻¹ *
          (((Equiv.Perm.sign σ : ℤ) : ℂ) *
            (a : DeningerBarWord → ℂ) (deningerPermuteAt σ w.2)))
    ring

@[simp]
theorem deningerAlt_coe (c : DeningerBarKothe) (w : DeningerBarWord) :
    ((deningerAlt c : DeningerBarKothe) : DeningerBarWord → ℂ) w
      = deningerAltCoe (c : DeningerBarWord → ℂ) w := rfl

/-- **The antisymmetrizer has seminorm at most one.** -/
theorem deningerBarSeminormR_alt_le {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerBarKothe) :
    deningerBarSeminormR k R (deningerAlt c) ≤ deningerBarSeminormR k R c := by
  rw [deningerBarSeminormR_eq_tsum_slice hR (deningerAlt c),
    deningerBarSeminormR_eq_tsum_slice hR c]
  refine Summable.tsum_le_tsum (fun r => ?_)
    (deningerBarSliceR_summable (k := k) hR (deningerAlt c))
    (deningerBarSliceR_summable (k := k) hR c)
  exact (deningerAlt_slice_le (k := k) hR c r).2

/-- Permuting the letters preserves the total arithmetic character, so the antisymmetrizer is
supported on the same characters. -/
theorem deningerPermuteAt_char {r : ℕ} (σ : Equiv.Perm (Fin (r + 1)))
    (f : Fin (r + 1) → DeningerPrimeLattice) :
    deningerBarChar (deningerPermuteAt σ f)
      = deningerBarChar (⟨r, f⟩ : DeningerBarWord) := by
  show (∑ j, f (σ j)) = ∑ j, f j
  exact Equiv.sum_comp σ (fun j => f j)

end

end RHTower
