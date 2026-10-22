import GaloisForLFunctions.RHTower.ZetaZeroDensitySeparatedSelection
import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorSchwarzMonodromy

/-!
# Counting zeros by folded real part and absolute ordinate

The zeros of `ξ` are symmetric under `ρ ↦ ρ̄` and `ρ ↦ 1 - ρ`, with multiplicity.  Hence the zeros
with `max(β, 1-β) ≥ σ` and `T ≤ |γ| ≤ 2T` are covered by four copies of the upper box
`{β ≥ σ, T ≤ γ ≤ 2T}`:

`#{σ ≤ max(β, 1-β), T ≤ |γ| ≤ 2T} ≤ 4 · #{σ ≤ β, T ≤ γ ≤ 2T}`.

Slicing `[1/2, 1)` into `M` slabs `σ_m = 1/2 + m/(2M)` then bounds a power sum over any finite set of
zeros in the folded box by the upper-box counts:

`Σ_{ρ ∈ G} x^{β-1} ≤ 4 Σ_{m < M} x^{σ_{m+1}-1} #{σ_m ≤ β, T ≤ γ ≤ 2T}`   (`x ≥ 1`).
-/

namespace RHTower

noncomputable section

open Complex Finset

/-- The folded real part `max(β, 1 - β)`. -/
def foldedRe (q : XiZeroCopy) : ℝ := max ((q.1 : ℂ).re) (1 - (q.1 : ℂ).re)

theorem half_le_foldedRe (q : XiZeroCopy) : 1 / 2 ≤ foldedRe q := by
  rw [foldedRe]
  rcases le_total ((q.1 : ℂ).re) (1 / 2) with h | h
  · exact le_trans (by linarith) (le_max_right _ _)
  · exact le_trans h (le_max_left _ _)

theorem foldedRe_lt_one (q : XiZeroCopy) : foldedRe q < 1 := by
  rw [foldedRe]
  exact max_lt (xiZeroCopy_re_lt_one q) (by linarith [xiZeroCopy_re_pos q])

theorem re_le_foldedRe (q : XiZeroCopy) : (q.1 : ℂ).re ≤ foldedRe q := le_max_left _ _

/-- Zeros with folded real part at least `σ` and `T ≤ |γ| ≤ 2T`. -/
def foldedHeightBox (σ T : ℝ) : Set XiZeroCopy :=
  {q | σ ≤ foldedRe q ∧ T ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * T}

theorem foldedHeightBox_finite (σ T : ℝ) : (foldedHeightBox σ T).Finite := by
  refine (finite_xiOrdinateWindow (2 * T) 0).subset ?_
  intro q hq
  rw [mem_xiOrdinateWindow_iff, sub_zero]
  exact hq.2.2

theorem foldedHeightBox_subset (σ T : ℝ) :
    foldedHeightBox σ T ⊆ ((zeroHeightBox σ T ∪ xiZeroCopyConjEquiv ⁻¹' zeroHeightBox σ T) ∪
      (xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv) ⁻¹' zeroHeightBox σ T) ∪
      xiZeroCopyReflectEquiv ⁻¹' zeroHeightBox σ T := by
  intro q hq
  obtain ⟨hσ, hT, hT2⟩ := hq
  have hc : ((xiZeroCopyConjEquiv q).1 : ℂ) = (starRingEnd ℂ) (q.1 : ℂ) := rfl
  have hr : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := rfl
  have hcr : (((xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv) q).1 : ℂ)
      = 1 - (starRingEnd ℂ) (q.1 : ℂ) := rfl
  rw [foldedRe, le_max_iff] at hσ
  rcases hσ with hσ | hσ <;> rcases le_total 0 ((q.1 : ℂ).im) with hγ | hγ
  · left; left; left
    rw [abs_of_nonneg hγ] at hT hT2
    exact ⟨hσ, hT, hT2⟩
  · left; left; right
    rw [abs_of_nonpos hγ] at hT hT2
    show σ ≤ ((xiZeroCopyConjEquiv q).1 : ℂ).re ∧ T ≤ ((xiZeroCopyConjEquiv q).1 : ℂ).im ∧
      ((xiZeroCopyConjEquiv q).1 : ℂ).im ≤ 2 * T
    rw [hc, Complex.conj_re, Complex.conj_im]
    exact ⟨hσ, hT, hT2⟩
  · left; right
    rw [abs_of_nonneg hγ] at hT hT2
    show σ ≤ (((xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv) q).1 : ℂ).re ∧
      T ≤ (((xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv) q).1 : ℂ).im ∧
      (((xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv) q).1 : ℂ).im ≤ 2 * T
    rw [hcr, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
      Complex.one_im]
    exact ⟨hσ, by linarith, by linarith⟩
  · right
    rw [abs_of_nonpos hγ] at hT hT2
    show σ ≤ ((xiZeroCopyReflectEquiv q).1 : ℂ).re ∧ T ≤ ((xiZeroCopyReflectEquiv q).1 : ℂ).im ∧
      ((xiZeroCopyReflectEquiv q).1 : ℂ).im ≤ 2 * T
    rw [hr, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    exact ⟨hσ, by linarith, by linarith⟩

theorem ncard_preimage_equiv (e : XiZeroCopy ≃ XiZeroCopy) (S : Set XiZeroCopy) :
    (e ⁻¹' S).ncard = S.ncard :=
  Set.ncard_preimage_of_injective_subset_range e.injective (by rw [e.surjective.range_eq]; exact Set.subset_univ _)

/-- **The folded count.** -/
theorem ncard_foldedHeightBox_le (σ T : ℝ) :
    (foldedHeightBox σ T).ncard ≤ 4 * (zeroHeightBox σ T).ncard := by
  have hfin := zeroHeightBox_finite σ T
  have hpre : ∀ e : XiZeroCopy ≃ XiZeroCopy, (e ⁻¹' zeroHeightBox σ T).Finite :=
    fun e => hfin.preimage e.injective.injOn
  have hU : (((zeroHeightBox σ T ∪ xiZeroCopyConjEquiv ⁻¹' zeroHeightBox σ T) ∪
      (xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv) ⁻¹' zeroHeightBox σ T) ∪
      xiZeroCopyReflectEquiv ⁻¹' zeroHeightBox σ T).Finite :=
    ((hfin.union (hpre _)).union (hpre _)).union (hpre _)
  refine le_trans (Set.ncard_le_ncard (foldedHeightBox_subset σ T) hU) ?_
  refine le_trans (Set.ncard_union_le _ _) ?_
  refine le_trans (Nat.add_le_add_right (Set.ncard_union_le _ _) _) ?_
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_union_le _ _) _) _) ?_
  rw [ncard_preimage_equiv, ncard_preimage_equiv, ncard_preimage_equiv]
  omega

/-- The slab abscissae `σ_m = 1/2 + m/(2M)`. -/
def slabAbscissa (M m : ℕ) : ℝ := 1 / 2 + (m : ℝ) / (2 * M)

/-- One slab above any folded real part. -/
theorem rpow_le_sum_slabs {x : ℝ} (hx : 1 ≤ x) {M : ℕ} (hM : 0 < M) {y : ℝ} (hy1 : 1 / 2 ≤ y)
    (hy2 : y < 1) :
    x ^ (y - 1) ≤ ∑ m ∈ Finset.range M,
      if slabAbscissa M m ≤ y then x ^ (slabAbscissa M (m + 1) - 1) else 0 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set j := ⌊(y - 1 / 2) * (2 * M)⌋₊ with hj
  have hnn : 0 ≤ (y - 1 / 2) * (2 * M) := by
    have : 0 ≤ y - 1 / 2 := by linarith
    positivity
  have hjle : (j : ℝ) ≤ (y - 1 / 2) * (2 * M) := Nat.floor_le hnn
  have hjlt : (y - 1 / 2) * (2 * M) < j + 1 := Nat.lt_floor_add_one _
  have hjM : j < M := by
    have : (j : ℝ) < M := by nlinarith
    exact_mod_cast this
  have hlow : slabAbscissa M j ≤ y := by
    rw [slabAbscissa]
    have : (j : ℝ) / (2 * M) ≤ y - 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hup : y ≤ slabAbscissa M (j + 1) := by
    rw [slabAbscissa]
    push_cast
    rw [← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
    linarith
  have hterm : x ^ (y - 1) ≤ x ^ (slabAbscissa M (j + 1) - 1) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  set f : ℕ → ℝ := fun m => if slabAbscissa M m ≤ y then
    x ^ (slabAbscissa M (m + 1) - 1) else 0 with hf
  have hfj : f j = x ^ (slabAbscissa M (j + 1) - 1) := by rw [hf]; exact if_pos hlow
  have hf0 : ∀ m ∈ Finset.range M, 0 ≤ f m := by
    intro m _
    rw [hf]
    dsimp only
    split_ifs
    · exact Real.rpow_nonneg (by linarith) _
    · exact le_rfl
  calc x ^ (y - 1) ≤ f j := by rw [hfj]; exact hterm
    _ ≤ ∑ m ∈ Finset.range M, f m := Finset.single_le_sum hf0 (Finset.mem_range.mpr hjM)

/-- **The folded layer cake.** -/
theorem sum_rpow_re_le_zeroHeightBox {x : ℝ} (hx : 1 ≤ x) {M : ℕ} (hM : 0 < M) {T : ℝ}
    (G : Finset XiZeroCopy) (hG : ∀ q ∈ G, T ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * T) :
    ∑ q ∈ G, x ^ ((q.1 : ℂ).re - 1)
      ≤ 4 * ∑ m ∈ Finset.range M,
          x ^ (slabAbscissa M (m + 1) - 1) * ((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ) := by
  classical
  have hpt : ∀ q ∈ G, x ^ ((q.1 : ℂ).re - 1) ≤ ∑ m ∈ Finset.range M,
      if slabAbscissa M m ≤ foldedRe q then x ^ (slabAbscissa M (m + 1) - 1) else 0 := by
    intro q _
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hx (by linarith [re_le_foldedRe q]))
      (rpow_le_sum_slabs hx hM (half_le_foldedRe q) (foldedRe_lt_one q))
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hxp : 0 ≤ x ^ (slabAbscissa M (m + 1) - 1) := Real.rpow_nonneg (by linarith) _
  have hcard : ((G.filter fun q => slabAbscissa M m ≤ foldedRe q).card : ℝ)
      ≤ 4 * ((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ) := by
    have hsub : ((G.filter fun q => slabAbscissa M m ≤ foldedRe q : Finset XiZeroCopy) :
        Set XiZeroCopy) ⊆ foldedHeightBox (slabAbscissa M m) T := by
      intro q hq
      rw [Finset.coe_filter] at hq
      exact ⟨hq.2, hG q hq.1⟩
    have h1 := Set.ncard_le_ncard hsub (foldedHeightBox_finite _ _)
    rw [Set.ncard_coe_finset] at h1
    have h2 := ncard_foldedHeightBox_le (slabAbscissa M m) T
    exact_mod_cast le_trans h1 h2
  nlinarith

end

end RHTower
