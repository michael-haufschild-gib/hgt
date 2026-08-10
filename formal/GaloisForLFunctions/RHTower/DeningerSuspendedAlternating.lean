import GaloisForLFunctions.RHTower.DeningerSuspendedSource

/-!
# The blockwise alternating projector on the suspended source

Permuting the letters of a suspended word preserves its letter count, the product of its letter
heights, its ancestral length, and its total arithmetic character.  Reindexing a weighted series by
a permutation is therefore an isometry of every length slice, and the blockwise antisymmetrizer —
the average of the `r!` signed reindexings — decreases every seminorm.

The entire exterior completion of the suspended source is its range, hence a closed complemented
subspace of a complete nuclear space.

* `deningerSuspWeightR`, `deningerSuspSliceR` : the two-parameter weight and its length slices.
* `deningerSuspPermute` : the permutation action.
* `deningerSuspAlt` : **the blockwise antisymmetrizer**, of seminorm at most one.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## The two-parameter weight -/

/-- The two-parameter suspended word weight `R^{|w|} h(w)^k`. -/
def deningerSuspWeightR (k : ℕ) (R : ℝ) (w : DeningerSuspWord) : ℝ :=
  R ^ deningerSuspWordLength w * deningerSuspWordHeight w ^ k

theorem deningerSuspWeightR_nonneg (k : ℕ) {R : ℝ} (hR : 0 ≤ R) (w : DeningerSuspWord) :
    0 ≤ deningerSuspWeightR k R w :=
  mul_nonneg (pow_nonneg hR _) (pow_nonneg (deningerSuspWordHeight_pos w).le _)

/-- Every two-parameter weight is dominated by a canonical one. -/
theorem deningerSuspWeight_le {k : ℕ} {R : ℝ} (hR : 1 ≤ R) {k' : ℕ} (hk : k ≤ k')
    (hRk : R ≤ (k' : ℝ) + 1) (w : DeningerSuspWord) :
    deningerSuspWeightR k R w ≤ deningerSuspWordKotheData.w k' w := by
  rw [deningerSuspWordKotheData_w, deningerSuspWeightR]
  have h1 : deningerSuspWordHeight w ^ k ≤ deningerSuspWordHeight w ^ k' :=
    pow_le_pow_right₀ (one_le_deningerSuspWordHeight w) hk
  have h2 : R ^ deningerSuspWordLength w ≤ ((k' : ℝ) + 1) ^ deningerSuspWordLength w :=
    pow_le_pow_left₀ (by linarith) hRk _
  have hR0 : (0 : ℝ) ≤ R ^ deningerSuspWordLength w := pow_nonneg (by linarith) _
  calc R ^ deningerSuspWordLength w * deningerSuspWordHeight w ^ k
      ≤ R ^ deningerSuspWordLength w * deningerSuspWordHeight w ^ k' :=
        mul_le_mul_of_nonneg_left h1 hR0
    _ ≤ ((k' : ℝ) + 1) ^ deningerSuspWordLength w * deningerSuspWordHeight w ^ k' :=
        mul_le_mul_of_nonneg_right h2 (pow_nonneg (deningerSuspWordHeight_pos w).le _)
    _ = deningerSuspWordHeight w ^ k' * ((k' : ℝ) + 1) ^ deningerSuspWordLength w := by ring

/-- The two-parameter seminorms of the suspended source. -/
def deningerSuspSeminormR (k : ℕ) (R : ℝ) (c : DeningerSuspKothe) : ℝ :=
  ∑' w, deningerSuspWeightR k R w * ‖(c : DeningerSuspWord → ℂ) w‖

/-- **Every two-parameter seminorm is finite** on the suspended source. -/
theorem deningerSuspSeminormR_summable {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerSuspKothe) :
    Summable fun w => deningerSuspWeightR k R w * ‖(c : DeningerSuspWord → ℂ) w‖ := by
  obtain ⟨k', hk'⟩ := exists_nat_gt R
  refine Summable.of_nonneg_of_le
    (fun w => mul_nonneg (deningerSuspWeightR_nonneg k (by linarith) w) (norm_nonneg _))
    (fun w => mul_le_mul_of_nonneg_right
      (deningerSuspWeight_le hR (le_max_left k k') ?_ w) (norm_nonneg _))
    (c.2 (max k k'))
  have hk'le : ((k' : ℝ)) ≤ ((max k k' : ℕ) : ℝ) := by
    exact_mod_cast le_max_right k k'
  linarith

/-! ## Length slices -/

/-- The length-`r` slice of a weighted suspended series. -/
def deningerSuspSliceR (k : ℕ) (R : ℝ) (c : DeningerSuspWord → ℂ) (r : ℕ) : ℝ :=
  ∑' f : Fin r → DeningerSusp,
    deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) * ‖c (⟨r, f⟩ : DeningerSuspWord)‖

theorem deningerSuspSlice_summable {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerSuspKothe)
    (r : ℕ) :
    Summable fun f : Fin r → DeningerSusp =>
      deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) *
        ‖(c : DeningerSuspWord → ℂ) (⟨r, f⟩ : DeningerSuspWord)‖ :=
  ((summable_sigma_of_nonneg
    (fun w => mul_nonneg (deningerSuspWeightR_nonneg k (by linarith) w) (norm_nonneg _))).mp
      (deningerSuspSeminormR_summable hR c)).1 r

theorem deningerSuspSliceR_summable {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerSuspKothe) :
    Summable (deningerSuspSliceR k R (c : DeningerSuspWord → ℂ)) :=
  ((summable_sigma_of_nonneg
    (fun w => mul_nonneg (deningerSuspWeightR_nonneg k (by linarith) w) (norm_nonneg _))).mp
      (deningerSuspSeminormR_summable hR c)).2

theorem deningerSuspSeminormR_eq_tsum_slice {k : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (c : DeningerSuspKothe) :
    deningerSuspSeminormR k R c
      = ∑' r, deningerSuspSliceR k R (c : DeningerSuspWord → ℂ) r :=
  (deningerSuspSeminormR_summable hR c).tsum_sigma

/-! ## The permutation action -/

/-- Permute the letters of a suspended word of a fixed length. -/
def deningerSuspPermute {r : ℕ} (σ : Equiv.Perm (Fin r)) (f : Fin r → DeningerSusp) :
    DeningerSuspWord :=
  ⟨r, f ∘ σ⟩

@[simp]
theorem deningerSuspPermute_length {r : ℕ} (σ : Equiv.Perm (Fin r)) (f : Fin r → DeningerSusp) :
    deningerSuspWordLength (deningerSuspPermute σ f)
      = deningerSuspWordLength (⟨r, f⟩ : DeningerSuspWord) := rfl

theorem deningerSuspPermute_height {r : ℕ} (σ : Equiv.Perm (Fin r)) (f : Fin r → DeningerSusp) :
    deningerSuspWordHeight (deningerSuspPermute σ f)
      = deningerSuspWordHeight (⟨r, f⟩ : DeningerSuspWord) :=
  Equiv.prod_comp σ fun j => deningerSuspHeight (f j)

theorem deningerSuspPermute_char {r : ℕ} (σ : Equiv.Perm (Fin r)) (f : Fin r → DeningerSusp) :
    deningerSuspWordChar (deningerSuspPermute σ f)
      = deningerSuspWordChar (⟨r, f⟩ : DeningerSuspWord) :=
  Equiv.sum_comp σ fun j => deningerSuspChar (f j)

theorem deningerSuspPermute_ancestral {r : ℕ} (σ : Equiv.Perm (Fin r))
    (f : Fin r → DeningerSusp) :
    deningerSuspWordAncestral (deningerSuspPermute σ f)
      = deningerSuspWordAncestral (⟨r, f⟩ : DeningerSuspWord) :=
  Equiv.sum_comp σ fun j => deningerSuspAncestral (f j)

/-- Precomposition with a permutation, as an equivalence of coefficient tuples. -/
def deningerSuspPermEquiv {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    (Fin r → DeningerSusp) ≃ (Fin r → DeningerSusp) :=
  Equiv.arrowCongr σ.symm (Equiv.refl DeningerSusp)

@[simp]
theorem deningerSuspPermEquiv_apply {r : ℕ} (σ : Equiv.Perm (Fin r))
    (f : Fin r → DeningerSusp) : deningerSuspPermEquiv σ f = f ∘ σ := rfl

theorem deningerSuspWeightR_permute (k : ℕ) (R : ℝ) {r : ℕ} (σ : Equiv.Perm (Fin r))
    (f : Fin r → DeningerSusp) :
    deningerSuspWeightR k R (deningerSuspPermute σ f)
      = deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) := by
  rw [deningerSuspWeightR, deningerSuspWeightR, deningerSuspPermute_height,
    deningerSuspPermute_length]

/-! ## The antisymmetrizer -/

/-- **The blockwise antisymmetrizer** of the suspended source. -/
def deningerSuspAltCoe (a : DeningerSuspWord → ℂ) : DeningerSuspWord → ℂ := fun w =>
  ((Nat.factorial w.1 : ℂ))⁻¹ *
    ∑ σ : Equiv.Perm (Fin w.1), ((Equiv.Perm.sign σ : ℤ) : ℂ) * a (deningerSuspPermute σ w.2)

theorem deningerSuspAltCoe_norm_le (a : DeningerSuspWord → ℂ) (w : DeningerSuspWord) :
    ‖deningerSuspAltCoe a w‖
      ≤ ((Nat.factorial w.1 : ℝ))⁻¹ *
        ∑ σ : Equiv.Perm (Fin w.1), ‖a (deningerSuspPermute σ w.2)‖ := by
  rw [deningerSuspAltCoe, norm_mul]
  have hfac : ‖((Nat.factorial w.1 : ℂ))⁻¹‖ = ((Nat.factorial w.1 : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hfac]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [norm_mul]
  have hsign : ‖(((Equiv.Perm.sign σ : ℤ)) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num
  rw [hsign, one_mul]

private theorem deningerSuspAlt_permuted_slice {k : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (c : DeningerSuspKothe) (r : ℕ) (σ : Equiv.Perm (Fin r)) :
    (Summable fun f : Fin r → DeningerSusp =>
        deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) *
          ‖(c : DeningerSuspWord → ℂ) (deningerSuspPermute σ f)‖) ∧
      (∑' f : Fin r → DeningerSusp,
          deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) *
            ‖(c : DeningerSuspWord → ℂ) (deningerSuspPermute σ f)‖)
        = deningerSuspSliceR k R (c : DeningerSuspWord → ℂ) r := by
  have hterm : ∀ f : Fin r → DeningerSusp,
      deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) *
          ‖(c : DeningerSuspWord → ℂ) (deningerSuspPermute σ f)‖
        = (fun g : Fin r → DeningerSusp =>
            deningerSuspWeightR k R (⟨r, g⟩ : DeningerSuspWord) *
              ‖(c : DeningerSuspWord → ℂ) (⟨r, g⟩ : DeningerSuspWord)‖)
          (deningerSuspPermEquiv σ f) := by
    intro f
    show _ = deningerSuspWeightR k R (⟨r, f ∘ σ⟩ : DeningerSuspWord) *
      ‖(c : DeningerSuspWord → ℂ) (⟨r, f ∘ σ⟩ : DeningerSuspWord)‖
    rw [show (⟨r, f ∘ σ⟩ : DeningerSuspWord) = deningerSuspPermute σ f from rfl,
      deningerSuspWeightR_permute]
  constructor
  · refine ((deningerSuspPermEquiv σ).summable_iff
      (f := fun g : Fin r → DeningerSusp =>
        deningerSuspWeightR k R (⟨r, g⟩ : DeningerSuspWord) *
          ‖(c : DeningerSuspWord → ℂ) (⟨r, g⟩ : DeningerSuspWord)‖)).mpr
      (deningerSuspSlice_summable hR c r) |>.congr ?_
    intro f
    exact (hterm f).symm
  · rw [tsum_congr hterm,
      (deningerSuspPermEquiv σ).tsum_eq (fun g : Fin r → DeningerSusp =>
        deningerSuspWeightR k R (⟨r, g⟩ : DeningerSuspWord) *
          ‖(c : DeningerSuspWord → ℂ) (⟨r, g⟩ : DeningerSuspWord)‖),
      deningerSuspSliceR]

/-- **The antisymmetrizer decreases every length slice.** -/
theorem deningerSuspAlt_slice_le {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerSuspKothe) (r : ℕ) :
    (Summable fun f : Fin r → DeningerSusp =>
        deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) *
          ‖deningerSuspAltCoe (c : DeningerSuspWord → ℂ) (⟨r, f⟩ : DeningerSuspWord)‖) ∧
      (∑' f : Fin r → DeningerSusp,
          deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) *
            ‖deningerSuspAltCoe (c : DeningerSuspWord → ℂ) (⟨r, f⟩ : DeningerSuspWord)‖)
        ≤ deningerSuspSliceR k R (c : DeningerSuspWord → ℂ) r := by
  classical
  have hRpos : (0 : ℝ) < R := by linarith
  have hfacpos : (0 : ℝ) < (Nat.factorial r : ℝ) := by
    exact_mod_cast Nat.factorial_pos r
  set G : Equiv.Perm (Fin r) → (Fin r → DeningerSusp) → ℝ := fun σ f =>
    ((Nat.factorial r : ℝ))⁻¹ *
      (deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) *
        ‖(c : DeningerSuspWord → ℂ) (deningerSuspPermute σ f)‖) with hG
  have hGsummable : ∀ σ, Summable (G σ) := fun σ =>
    ((deningerSuspAlt_permuted_slice hR c r σ).1).mul_left _
  have hmaj : Summable fun f : Fin r → DeningerSusp =>
      ∑ σ : Equiv.Perm (Fin r), G σ f :=
    summable_sum fun σ _ => hGsummable σ
  have hpointwise : ∀ f : Fin r → DeningerSusp,
      deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) *
          ‖deningerSuspAltCoe (c : DeningerSuspWord → ℂ) (⟨r, f⟩ : DeningerSuspWord)‖
        ≤ ∑ σ : Equiv.Perm (Fin r), G σ f := by
    intro f
    have hb := deningerSuspAltCoe_norm_le (c : DeningerSuspWord → ℂ)
      (⟨r, f⟩ : DeningerSuspWord)
    have hwnn : 0 ≤ deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) :=
      deningerSuspWeightR_nonneg k hRpos.le _
    calc deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) *
          ‖deningerSuspAltCoe (c : DeningerSuspWord → ℂ) (⟨r, f⟩ : DeningerSuspWord)‖
        ≤ deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) *
            (((Nat.factorial r : ℝ))⁻¹ *
              ∑ σ : Equiv.Perm (Fin r),
                ‖(c : DeningerSuspWord → ℂ) (deningerSuspPermute σ f)‖) :=
          mul_le_mul_of_nonneg_left hb hwnn
      _ = ∑ σ : Equiv.Perm (Fin r), G σ f := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [hG]
          ring
  have hsummable : Summable fun f : Fin r → DeningerSusp =>
      deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) *
        ‖deningerSuspAltCoe (c : DeningerSuspWord → ℂ) (⟨r, f⟩ : DeningerSuspWord)‖ :=
    Summable.of_nonneg_of_le
      (fun f => mul_nonneg (deningerSuspWeightR_nonneg k hRpos.le _) (norm_nonneg _))
      hpointwise hmaj
  refine ⟨hsummable, ?_⟩
  have hstep : (∑' f : Fin r → DeningerSusp,
        deningerSuspWeightR k R (⟨r, f⟩ : DeningerSuspWord) *
          ‖deningerSuspAltCoe (c : DeningerSuspWord → ℂ) (⟨r, f⟩ : DeningerSuspWord)‖)
      ≤ ∑' f : Fin r → DeningerSusp, ∑ σ : Equiv.Perm (Fin r), G σ f :=
    Summable.tsum_le_tsum hpointwise hsummable hmaj
  have hswap : (∑' f : Fin r → DeningerSusp, ∑ σ : Equiv.Perm (Fin r), G σ f)
      = ∑ σ : Equiv.Perm (Fin r), ∑' f : Fin r → DeningerSusp, G σ f :=
    Summable.tsum_finsetSum fun σ _ => hGsummable σ
  have hone : ∀ σ : Equiv.Perm (Fin r),
      (∑' f : Fin r → DeningerSusp, G σ f)
        = ((Nat.factorial r : ℝ))⁻¹ * deningerSuspSliceR k R (c : DeningerSuspWord → ℂ) r := by
    intro σ
    rw [hG, Summable.tsum_mul_left _ ((deningerSuspAlt_permuted_slice hR c r σ).1),
      (deningerSuspAlt_permuted_slice hR c r σ).2]
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin r))).card = Nat.factorial r := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [hswap, Finset.sum_congr rfl fun σ _ => hone σ, Finset.sum_const, hcard,
    nsmul_eq_mul] at hstep
  have hfin : ((Nat.factorial r : ℝ)) *
      (((Nat.factorial r : ℝ))⁻¹ * deningerSuspSliceR k R (c : DeningerSuspWord → ℂ) r)
      = deningerSuspSliceR k R (c : DeningerSuspWord → ℂ) r := by
    field_simp
  rw [hfin] at hstep
  exact hstep

/-! ## The antisymmetrizer as an operator of the source -/

theorem deningerSuspWordKotheData_weightR (k : ℕ) (w : DeningerSuspWord) :
    deningerSuspWordKotheData.w k w = deningerSuspWeightR k ((k : ℝ) + 1) w := by
  rw [deningerSuspWordKotheData_w, deningerSuspWeightR]
  ring

theorem deningerSuspAltCoe_mem (c : DeningerSuspKothe) :
    deningerSuspAltCoe (c : DeningerSuspWord → ℂ) ∈ DeningerSuspKothe := by
  intro k
  have hR : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hnn : ∀ w : DeningerSuspWord,
      0 ≤ deningerSuspWordKotheData.w k w *
        ‖deningerSuspAltCoe (c : DeningerSuspWord → ℂ) w‖ := fun w =>
    mul_nonneg (deningerSuspWordKotheData.pos k w).le (norm_nonneg _)
  refine (summable_sigma_of_nonneg hnn).mpr ⟨fun r => ?_, ?_⟩
  · refine ((deningerSuspAlt_slice_le (k := k) hR c r).1).congr fun f => ?_
    rw [deningerSuspWordKotheData_weightR]
  · refine Summable.of_nonneg_of_le (fun r => tsum_nonneg fun f => hnn _) (fun r => ?_)
      (deningerSuspSliceR_summable (k := k) hR c)
    have hcongr : (∑' f : Fin r → DeningerSusp,
        deningerSuspWordKotheData.w k (⟨r, f⟩ : DeningerSuspWord) *
          ‖deningerSuspAltCoe (c : DeningerSuspWord → ℂ) (⟨r, f⟩ : DeningerSuspWord)‖)
        = ∑' f : Fin r → DeningerSusp,
            deningerSuspWeightR k ((k : ℝ) + 1) (⟨r, f⟩ : DeningerSuspWord) *
              ‖deningerSuspAltCoe (c : DeningerSuspWord → ℂ) (⟨r, f⟩ : DeningerSuspWord)‖ := by
      refine tsum_congr fun f => ?_
      rw [deningerSuspWordKotheData_weightR]
    rw [hcongr]
    exact (deningerSuspAlt_slice_le (k := k) hR c r).2

/-- **The blockwise antisymmetrizer** as an operator of the suspended source. -/
def deningerSuspAlt : DeningerSuspKothe →ₗ[ℂ] DeningerSuspKothe where
  toFun c := ⟨deningerSuspAltCoe (c : DeningerSuspWord → ℂ), deningerSuspAltCoe_mem c⟩
  map_add' a b := by
    ext w
    show deningerSuspAltCoe ((a + b : DeningerSuspKothe) : DeningerSuspWord → ℂ) w = _
    simp only [Submodule.coe_add, Pi.add_apply, deningerSuspAltCoe]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  map_smul' t a := by
    ext w
    show deningerSuspAltCoe ((t • a : DeningerSuspKothe) : DeningerSuspWord → ℂ) w = _
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, deningerSuspAltCoe,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    show ((Nat.factorial w.1 : ℂ))⁻¹ *
        (((Equiv.Perm.sign σ : ℤ) : ℂ) *
          (t * (a : DeningerSuspWord → ℂ) (deningerSuspPermute σ w.2)))
      = t * (((Nat.factorial w.1 : ℂ))⁻¹ *
          (((Equiv.Perm.sign σ : ℤ) : ℂ) *
            (a : DeningerSuspWord → ℂ) (deningerSuspPermute σ w.2)))
    ring

@[simp]
theorem deningerSuspAlt_coe (c : DeningerSuspKothe) (w : DeningerSuspWord) :
    ((deningerSuspAlt c : DeningerSuspKothe) : DeningerSuspWord → ℂ) w
      = deningerSuspAltCoe (c : DeningerSuspWord → ℂ) w := rfl

/-- **The antisymmetrizer has seminorm at most one**, so the entire exterior completion of the
suspended source is a closed complemented subspace of a complete nuclear space. -/
theorem deningerSuspSeminormR_alt_le {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerSuspKothe) :
    deningerSuspSeminormR k R (deningerSuspAlt c) ≤ deningerSuspSeminormR k R c := by
  rw [deningerSuspSeminormR_eq_tsum_slice hR (deningerSuspAlt c),
    deningerSuspSeminormR_eq_tsum_slice hR c]
  refine Summable.tsum_le_tsum (fun r => ?_)
    (deningerSuspSliceR_summable (k := k) hR (deningerSuspAlt c))
    (deningerSuspSliceR_summable (k := k) hR c)
  exact (deningerSuspAlt_slice_le (k := k) hR c r).2

end

end RHTower
