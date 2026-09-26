import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriInequality

/-!
# Horizontal Lamzouri inequality without normalisations

For a horizontal packet with multiplicities `m₂ ≥ 2`, `mP ≥ 1` and no condition on the norms of
its vectors, the four-range frame gives

`4·mass − E − 2N + 2 Σ_H (1 − ‖f‖²) + Σ_M (1 + 2‖P_A f‖² − 2‖f‖²) ≤ #H`
(`four_mass_sub_energy_le`), `N = Σ m₂ + #H + #M + 2 Σ mP`.

This is the shape of the rank–trace count `4 tr Â − ‖Â‖² − 2N ≤ s₁` for sampled Weil matrices, whose
on-line vectors satisfy only `‖f‖ ≤ 1`.  A mixed point costs nothing as soon as it lies within
`1/8` of the even vector of some pair (`one_add_two_mul_overlap_sub_nonneg`), because then
`2‖f‖² − 2‖P_A f‖² ≤ 8‖f‖·‖g − f‖ ≤ 1`.  Hence `4·mass − E − 2N ≤ #H`
(`four_mass_sub_energy_le_of_near`).
-/

open scoped RealInnerProductSpace
open Finset Module

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

set_option linter.unusedSectionVars false

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace HorizontalPacket

variable {ι₂ ιH ιM ιP : Type*} [Fintype ι₂] [Fintype ιH] [Fintype ιM] [Fintype ιP]
variable (P : HorizontalPacket V ι₂ ιH ιM ιP)

/-- The number of points `Σ m₂ + #H + #M + 2 Σ mP`. -/
def count : ℝ := ∑ i, P.m₂ i + Fintype.card ιH + Fintype.card ιM + 2 * ∑ p, P.mP p

theorem mass_expand :
    P.mass = ∑ i, P.m₂ i * ‖P.f₂ i‖ ^ 2 + ∑ i, ‖P.fH i‖ ^ 2 + ∑ i, ‖P.fM i‖ ^ 2
      + ∑ p, 2 * P.mP p * (‖P.g p‖ ^ 2 - ‖P.h p‖ ^ 2) := by
  have h := P.sum_wt_mul (fun v => ‖v‖ ^ 2)
  simp only [mass] at h ⊢
  rw [h]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- The absorbing range, without normalisations. -/
theorem absorbing_sum_general (hmP : ∀ p, 0 ≤ P.mP p) :
    ∑ i, P.m₂ i * ‖P.f₂ i‖ ^ 2 + P.mixedOverlap
      + ∑ p, 2 * P.mP p * (‖P.g p‖ ^ 2 - ‖P.h p‖ ^ 2)
      ≤ ∑ j, P.diagForm ((stdOrthonormalBasis ℝ P.absorbing) j : V) := by
  rw [P.sum_diagForm_stdOrthonormalBasis, P.sum_wt_mul (fun v => ‖P.absorbing.starProjection v‖ ^ 2)]
  have e₂ : ∀ i, P.absorbing.starProjection (P.f₂ i) = P.f₂ i := fun i =>
    P.absorbing.starProjection_eq_self_iff.mpr (P.f₂_mem_absorbing i)
  have eg : ∀ p, P.absorbing.starProjection (P.g p) = P.g p := fun p =>
    P.absorbing.starProjection_eq_self_iff.mpr (P.g_mem_absorbing p)
  have eh : ∀ p, ‖P.absorbing.starProjection (P.h p)‖ ^ 2 ≤ ‖P.h p‖ ^ 2 := fun p => by
    have := Submodule.norm_sq_eq_add_norm_sq_starProjection (P.h p) P.absorbing
    have := sq_nonneg ‖P.absorbingᗮ.starProjection (P.h p)‖
    linarith
  simp only [e₂, eg]
  have hH : 0 ≤ ∑ i, ‖P.absorbing.starProjection (P.fH i)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpair : ∑ p, 2 * P.mP p * (‖P.g p‖ ^ 2 - ‖P.h p‖ ^ 2)
      ≤ ∑ p, 2 * P.mP p * ‖P.g p‖ ^ 2 - ∑ p, 2 * P.mP p * ‖P.absorbing.starProjection (P.h p)‖ ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    have := mul_le_mul_of_nonneg_left (eh p) (mul_nonneg zero_le_two (hmP p))
    nlinarith
  simp only [mixedOverlap]
  linarith

/-- **Unnormalised horizontal Lamzouri inequality.**  With multiplicities `m₂ ≥ 2`, `mP ≥ 1` and
no condition on the norms of the vectors,
`4·mass − E − 2N + 2 Σ_H (1 − ‖f‖²) + Σ_M (1 + 2‖P_A f‖² − 2‖f‖²) ≤ #H`,
`N = Σ m₂ + #H + #M + 2 Σ mP`. -/
theorem four_mass_sub_energy_le (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ p, 1 ≤ P.mP p) :
    4 * P.mass - P.energy - 2 * P.count + 2 * ∑ i, (1 - ‖P.fH i‖ ^ 2)
      + ∑ i, (1 + 2 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 2 * ‖P.fM i‖ ^ 2)
      ≤ Fintype.card ιH := by
  have hmP0 : ∀ p, 0 ≤ P.mP p := fun p => le_trans zero_le_one (hmP p)
  have hE : ∑ s, P.diagForm (P.frame s) ^ 2 ≤ P.energy :=
    sum_sq_diag_le_energy P.frame P.vec
      (fun k l => P.frame_parseval (P.vec_mem_fullSpan k) (P.vec l)) P.wt
  have hM := P.mass_eq_frame_sum
  simp only [frame, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hE hM
  have hA1 := P.absorbing_sum_general hmP0
  have hq₁ := sum_sq_ge_of_center
    (fun j => P.diagForm ((stdOrthonormalBasis ℝ P.absorbing) j : V)) 2
  have hd₁ : (finrank ℝ P.absorbing : ℝ) ≤ Fintype.card ι₂ + Fintype.card ιP := by
    exact_mod_cast P.finrank_absorbing_le
  have hq₂ := sum_sq_ge_of_center
    (fun j => P.diagForm ((stdOrthonormalBasis ℝ (P.absorbingᗮ ⊓ P.hsSpan : Submodule ℝ V)) j : V)) 1
  have hd₂ : (finrank ℝ (P.absorbingᗮ ⊓ P.hsSpan : Submodule ℝ V) : ℝ) ≤ Fintype.card ιH := by
    exact_mod_cast P.finrank_hsSpan_inf_le
  have hq₃ := sum_sq_ge_of_center
    (fun j => P.diagForm ((stdOrthonormalBasis ℝ (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V)) j : V)) 1
  have hd₃ : (finrank ℝ (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V) : ℝ) ≤ Fintype.card ιM := by
    exact_mod_cast P.finrank_positiveSpan_inf_le
  have hq₄ := P.negative_range_bound
  have hΛ : 0 ≤ ∑ p, P.mP p * ‖P.positiveSpanᗮ.starProjection (P.h p)‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => mul_nonneg (hmP0 p) (sq_nonneg _)
  have hmass := P.mass_expand
  have hm₂s : 2 * (Fintype.card ι₂ : ℝ) ≤ ∑ i, P.m₂ i := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hm₂ i
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using this
  have hmPs : (Fintype.card ιP : ℝ) ≤ ∑ p, P.mP p := by
    have := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hmP p
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have eH : ∑ i, (1 - ‖P.fH i‖ ^ 2) = Fintype.card ιH - ∑ i, ‖P.fH i‖ ^ 2 := by
    simp [Finset.sum_sub_distrib]
  have eM : ∑ i, (1 + 2 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 2 * ‖P.fM i‖ ^ 2)
      = Fintype.card ιM + 2 * P.mixedOverlap - 2 * ∑ i, ‖P.fM i‖ ^ 2 := by
    simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mixedOverlap]
  simp only [one_pow, one_mul, mul_one] at hq₂ hq₃
  norm_num at hq₁
  rw [eH, eM]
  simp only [count]
  linarith

/-- A mixed point within `1/8` of its own pair vector costs nothing:
`0 ≤ 1 + 2‖P_K f‖² − 2‖f‖²` when `‖f‖ ≤ 1`, `g ∈ K` and `‖g − f‖ ≤ 1/8`. -/
theorem one_add_two_mul_overlap_sub_nonneg {K : Submodule ℝ V} [FiniteDimensional ℝ K]
    {f g : V} (hg : g ∈ K) (hf : ‖f‖ ≤ 1) (hgf : ‖g - f‖ ≤ 1 / 8) :
    0 ≤ 1 + 2 * ‖K.starProjection f‖ ^ 2 - 2 * ‖f‖ ^ 2 := by
  set s := ‖f‖ with hs
  set η := ‖g - f‖ with hη
  have hs0 : 0 ≤ s := norm_nonneg _
  have hη0 : 0 ≤ η := norm_nonneg _
  by_cases hsmall : s ≤ 1 / 2
  · have := sq_nonneg ‖K.starProjection f‖
    nlinarith
  replace hsmall : 1 / 2 < s := lt_of_not_ge hsmall
  -- ⟨f, g⟩ ≥ s² − s η and ‖g‖ ≤ s + η
  have hinner : s ^ 2 - s * η ≤ ⟪f, g⟫ := by
    have h1 : ⟪f, g⟫ = s ^ 2 + ⟪f, g - f⟫ := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]; ring
    have h2 : |⟪f, g - f⟫| ≤ s * η := abs_real_inner_le_norm _ _
    have := neg_abs_le ⟪f, g - f⟫
    nlinarith
  have hgnorm : ‖g‖ ≤ s + η := by
    calc ‖g‖ = ‖f + (g - f)‖ := by rw [add_sub_cancel]
      _ ≤ ‖f‖ + ‖g - f‖ := norm_add_le _ _
  have hproj := inner_sq_le_norm_sq_starProjection_mul hg f
  have hpos : 0 < s - η := by linarith
  have hin0 : 0 ≤ s ^ 2 - s * η := by nlinarith
  -- t (s+η)² ≥ t ‖g‖² ≥ ⟪f,g⟫² ≥ (s² − sη)²
  set t := ‖K.starProjection f‖ ^ 2 with ht
  have ht0 : 0 ≤ t := sq_nonneg _
  have hgsq : ‖g‖ ^ 2 ≤ (s + η) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgnorm 2
  have hkey : (s ^ 2 - s * η) ^ 2 ≤ t * (s + η) ^ 2 := by
    calc (s ^ 2 - s * η) ^ 2 ≤ ⟪f, g⟫ ^ 2 := pow_le_pow_left₀ hin0 hinner 2
      _ ≤ t * ‖g‖ ^ 2 := hproj
      _ ≤ t * (s + η) ^ 2 := mul_le_mul_of_nonneg_left hgsq ht0
  -- (s²−sη)² = s²(s−η)² and s²(s+η)² − s²(s−η)² = 4 s³ η ≤ (s+η)²/2 · 8 s η … conclude
  have hsη : 0 < s + η := by linarith
  have hfinal : s ^ 2 * (s + η) ^ 2 - (s ^ 2 - s * η) ^ 2 ≤ (s + η) ^ 2 / 2 := by
    have e : s ^ 2 * (s + η) ^ 2 - (s ^ 2 - s * η) ^ 2 = 4 * s ^ 3 * η := by ring
    rw [e]
    have h8 : 8 * η ≤ 1 := by linarith
    have hs1 : s ≤ 1 := hf
    nlinarith [mul_nonneg (mul_nonneg hs0 hs0) hη0, sq_nonneg (s - η)]
  -- so (s² − t)(s+η)² ≤ (s+η)²/2
  have : (s ^ 2 - t) * (s + η) ^ 2 ≤ (s + η) ^ 2 / 2 := by nlinarith
  have hsq : 0 < (s + η) ^ 2 := by positivity
  have : s ^ 2 - t ≤ 1 / 2 := by
    by_contra hc
    replace hc : 1 / 2 < s ^ 2 - t := lt_of_not_ge hc
    nlinarith
  linarith

/-- **Horizontal criterion, unnormalised.**  If every mixed point has norm at most one and lies
within `1/8` of the even vector of some pair, and every horizontally simple point has norm at most
one, then `4·mass − E − 2N ≤ #H`. -/
theorem four_mass_sub_energy_le_of_near (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ p, 1 ≤ P.mP p)
    (hH : ∀ i, ‖P.fH i‖ ≤ 1) (hM : ∀ i, ‖P.fM i‖ ≤ 1)
    (σ : ιM → ιP) (hnear : ∀ i, ‖P.g (σ i) - P.fM i‖ ≤ 1 / 8) :
    4 * P.mass - P.energy - 2 * P.count ≤ Fintype.card ιH := by
  have h := P.four_mass_sub_energy_le hm₂ hmP
  have h1 : 0 ≤ ∑ i, (1 - ‖P.fH i‖ ^ 2) := Finset.sum_nonneg fun i _ => by
    have := hH i
    have := norm_nonneg (P.fH i)
    nlinarith
  have h2 : 0 ≤ ∑ i, (1 + 2 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 2 * ‖P.fM i‖ ^ 2) :=
    Finset.sum_nonneg fun i _ =>
      one_add_two_mul_overlap_sub_nonneg (P.g_mem_absorbing (σ i)) (hM i) (hnear i)
  linarith

end HorizontalPacket

end

end GaloisForLFunctions.HilbertMetric
