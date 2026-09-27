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

A sharper sufficient condition for a mixed point is an overlap bound on full sequences.  If the
truncated vectors `f, g` extend to sequences with `Σ f² ≤ 1`, `Σ f g = K > 0` and `Σ g² = B`, then
the truncation to any finite set has cost at least `2K²/B − 1`
(`overlap_criterion`).  This holds however much of the mass the truncation loses: the proof reduces
to `B(K − s q)² − (K² − s²B)(B − q²) = (Kq − sB)²` (`overlap_tail_identity`).
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

/-- **Horizontal criterion by cost.**  If every mixed point satisfies
`0 ≤ 1 + 2‖P_A f‖² − 2‖f‖²` and every horizontally simple point has norm at most one, then
`4·mass − E − 2N ≤ #H`. -/
theorem four_mass_sub_energy_le_of_cost (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ p, 1 ≤ P.mP p)
    (hH : ∀ i, ‖P.fH i‖ ≤ 1)
    (hcost : ∀ i, 0 ≤ 1 + 2 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 2 * ‖P.fM i‖ ^ 2) :
    4 * P.mass - P.energy - 2 * P.count ≤ Fintype.card ιH := by
  have h := P.four_mass_sub_energy_le hm₂ hmP
  have h1 : 0 ≤ ∑ i, (1 - ‖P.fH i‖ ^ 2) := Finset.sum_nonneg fun i _ => by
    have := hH i
    have := norm_nonneg (P.fH i)
    nlinarith
  have h2 : 0 ≤ ∑ i, (1 + 2 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 2 * ‖P.fM i‖ ^ 2) :=
    Finset.sum_nonneg fun i _ => hcost i

  linarith

/-- The mixed range carries only mixed and negative mass: with `K₃ = C^⊥ ⊓ B`,
`Σ_{K₃} diagForm ≤ Σ_M (‖f‖² − ‖P_A f‖²)`. -/
theorem mixed_range_trace_le (hmP : ∀ p, 0 ≤ P.mP p) :
    ∑ j, P.diagForm ((stdOrthonormalBasis ℝ (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V)) j : V)
      ≤ ∑ i, (‖P.fM i‖ ^ 2 - ‖P.absorbing.starProjection (P.fM i)‖ ^ 2) := by
  set K₃ : Submodule ℝ V := P.hsSpanᗮ ⊓ P.positiveSpan with hK₃
  rw [P.sum_diagForm_stdOrthonormalBasis K₃, P.sum_wt_mul (fun v => ‖K₃.starProjection v‖ ^ 2)]
  have hzero : ∀ v ∈ P.hsSpan, K₃.starProjection v = 0 := by
    intro v hv
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
    intro w hw
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hv (Submodule.mem_inf.mp hw).1
  have h₂ : ∀ i, K₃.starProjection (P.f₂ i) = 0 := fun i =>
    hzero _ (P.absorbing_le_hsSpan (P.f₂_mem_absorbing i))
  have hH : ∀ i, K₃.starProjection (P.fH i) = 0 := fun i => hzero _ (P.fH_mem_hsSpan i)
  have hg : ∀ p, K₃.starProjection (P.g p) = 0 := fun p =>
    hzero _ (P.absorbing_le_hsSpan (P.g_mem_absorbing p))
  have hM : ∀ i, ‖K₃.starProjection (P.fM i)‖ ^ 2
      ≤ ‖P.fM i‖ ^ 2 - ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 := by
    intro i
    set f := P.fM i
    have hsplit := Submodule.starProjection_add_starProjection_orthogonal (K := P.absorbing) f
    have hAz : K₃.starProjection (P.absorbing.starProjection f) = 0 :=
      hzero _ (P.absorbing_le_hsSpan (Submodule.starProjection_apply_mem _ _))
    have heq : K₃.starProjection f = K₃.starProjection (P.absorbingᗮ.starProjection f) := by
      conv_lhs => rw [← hsplit]
      rw [map_add, hAz, zero_add]
    have hle := K₃.norm_starProjection_apply_le (P.absorbingᗮ.starProjection f)
    have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection f P.absorbing
    rw [heq]
    have h0 := norm_nonneg (K₃.starProjection (P.absorbingᗮ.starProjection f))
    nlinarith
  simp only [h₂, hH, hg, norm_zero]
  have hneg : 0 ≤ ∑ p, 2 * P.mP p * ‖K₃.starProjection (P.h p)‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => mul_nonneg (mul_nonneg zero_le_two (hmP p)) (sq_nonneg _)
  have hMs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hM i
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero] at hMs ⊢
  linarith

/-- **Unnormalised Lamzouri inequality, trace form on the mixed range.**  With `mP ≥ 1` and any
multiplicities `m₂`, bounding the mixed range by its trace instead of its dimension gives
`4·mass − E − 2N + 2 Σ_H (1 − ‖f‖²) + Σ_M (2 + 4‖P_A f‖² − 4‖f‖²) ≤ #H + 2 Σ (2 − m₂)`.
An absorbed mixed point (`f ∈ A`, `‖f‖ = 1`) earns `2`; a simple absorbing point costs `2`. -/
theorem four_mass_sub_energy_le_trace (hmP : ∀ p, 1 ≤ P.mP p) :
    4 * P.mass - P.energy - 2 * P.count + 2 * ∑ i, (1 - ‖P.fH i‖ ^ 2)
      + ∑ i, (2 + 4 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 4 * ‖P.fM i‖ ^ 2)
      ≤ Fintype.card ιH + 2 * ∑ i, (2 - P.m₂ i) := by
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
  have hq₃ : 0 ≤ ∑ j, P.diagForm
      ((stdOrthonormalBasis ℝ (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V)) j : V) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb := P.mixed_range_trace_le hmP0
  have hq₄ := P.negative_range_bound
  have hΛ : 0 ≤ ∑ p, P.mP p * ‖P.positiveSpanᗮ.starProjection (P.h p)‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => mul_nonneg (hmP0 p) (sq_nonneg _)
  have hmass := P.mass_expand
  have hm₂s : ∑ i, (2 - P.m₂ i) = 2 * (Fintype.card ι₂ : ℝ) - ∑ i, P.m₂ i := by
    simp [Finset.sum_sub_distrib, Finset.card_univ, mul_comm]
  have hmPs : (Fintype.card ιP : ℝ) ≤ ∑ p, P.mP p := by
    have := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hmP p
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have eH : ∑ i, (1 - ‖P.fH i‖ ^ 2) = Fintype.card ιH - ∑ i, ‖P.fH i‖ ^ 2 := by
    simp [Finset.sum_sub_distrib]
  have eM : ∑ i, (2 + 4 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 4 * ‖P.fM i‖ ^ 2)
      = 2 * Fintype.card ιM + 4 * P.mixedOverlap - 4 * ∑ i, ‖P.fM i‖ ^ 2 := by
    simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mixedOverlap]
    ring
  have eb : ∑ i, (‖P.fM i‖ ^ 2 - ‖P.absorbing.starProjection (P.fM i)‖ ^ 2)
      = ∑ i, ‖P.fM i‖ ^ 2 - P.mixedOverlap := by
    simp [Finset.sum_sub_distrib, mixedOverlap]
  rw [eb] at hb
  simp only [one_pow, one_mul, mul_one] at hq₂
  norm_num at hq₁
  rw [eH, eM, hm₂s]
  simp only [count]
  linarith

end HorizontalPacket

/-! ### The overlap criterion for truncated sequences -/

open Filter Topology


/-- Key algebra: `B (K − s q)² − (K² − s² B)(B − q²) = (K q − s B)²`. -/
theorem overlap_tail_identity (K B s q : ℝ) :
    B * (K - s * q) ^ 2 - (K ^ 2 - s ^ 2 * B) * (B - q ^ 2) = (K * q - s * B) ^ 2 := by ring

/-- **Finite overlap criterion.**  Let `s ⊆ t` be finite, `Σ_t F² ≤ 1`, `K = Σ_t F G ≥ 0`,
`B = Σ_t G² > 0`.  Then the truncation to `s` satisfies
`1 + 2 (Σ_s F G)² / Σ_s G² − 2 Σ_s F² ≥ 2K²/B − 1`. -/
theorem finite_overlap_criterion {ι : Type*} [DecidableEq ι] (F G : ι → ℝ) {s t : Finset ι}
    (hst : s ⊆ t) (hF : ∑ k ∈ t, F k ^ 2 ≤ 1) (hK : 0 ≤ ∑ k ∈ t, F k * G k)
    (hB : 0 < ∑ k ∈ t, G k ^ 2) :
    2 * (∑ k ∈ t, F k * G k) ^ 2 / (∑ k ∈ t, G k ^ 2) - 1
      ≤ 1 + 2 * (∑ k ∈ s, F k * G k) ^ 2 / (∑ k ∈ s, G k ^ 2) - 2 * ∑ k ∈ s, F k ^ 2 := by
  set x := ∑ k ∈ s, F k ^ 2
  set ip := ∑ k ∈ s, F k * G k
  set gg := ∑ k ∈ s, G k ^ 2
  set a := ∑ k ∈ t \ s, F k ^ 2
  set c' := ∑ k ∈ t \ s, F k * G k
  set q2 := ∑ k ∈ t \ s, G k ^ 2
  set K := ∑ k ∈ t, F k * G k
  set B := ∑ k ∈ t, G k ^ 2
  have hsplit : ∀ f : ι → ℝ, ∑ k ∈ t, f k = ∑ k ∈ s, f k + ∑ k ∈ t \ s, f k := fun f => by
    rw [← Finset.sum_sdiff hst, add_comm]
  have hK' : K = ip + c' := hsplit _
  have hB' : B = gg + q2 := hsplit _
  have hFt : ∑ k ∈ t, F k ^ 2 = x + a := hsplit _
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq0 : 0 ≤ q2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hgg0 : 0 ≤ gg := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- finite Cauchy–Schwarz on the tail
  have hCS : c' ^ 2 ≤ a * q2 := Finset.sum_mul_sq_le_sq_mul_sq (t \ s) F G
  have hx1 : x + a ≤ 1 := hFt ▸ hF
  -- the ratio term is nonnegative
  have hratio0 : 0 ≤ 2 * ip ^ 2 / gg := div_nonneg (by positivity) hgg0
  have hKB : 0 ≤ K ^ 2 / B := div_nonneg (sq_nonneg _) hB.le
  -- main case analysis
  by_cases hgpos : 0 < gg
  · by_cases hcase : 0 ≤ K - Real.sqrt a * Real.sqrt q2
    · -- ip ≥ K − √a √q2 ≥ 0
      have hc'le : c' ≤ Real.sqrt a * Real.sqrt q2 := by
        have h1 : c' ^ 2 ≤ (Real.sqrt a * Real.sqrt q2) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt ha0, Real.sq_sqrt hq0]; exact hCS
        exact abs_le_of_sq_le_sq' h1 (by positivity) |>.2
      have hip : K - Real.sqrt a * Real.sqrt q2 ≤ ip := by linarith
      have hip2 : (K - Real.sqrt a * Real.sqrt q2) ^ 2 ≤ ip ^ 2 :=
        pow_le_pow_left₀ hcase hip 2
      -- (K − s q)² ≥ (K²/B − s²)(B − q²) with s = √a, q = √q2
      have hid := overlap_tail_identity K B (Real.sqrt a) (Real.sqrt q2)
      rw [Real.sq_sqrt ha0, Real.sq_sqrt hq0] at hid
      have hkey : (K ^ 2 / B - a) * gg ≤ ip ^ 2 := by
        have h1 : (K ^ 2 - a * B) * (B - q2) ≤ B * (K - Real.sqrt a * Real.sqrt q2) ^ 2 := by
          nlinarith [sq_nonneg (K * Real.sqrt q2 - Real.sqrt a * B)]
        have hgg : gg = B - q2 := by linarith
        rw [hgg]
        have : (K ^ 2 / B - a) * (B - q2) = (K ^ 2 - a * B) * (B - q2) / B := by
          field_simp
        rw [this, div_le_iff₀ hB]
        nlinarith
      have hratio : 2 * (K ^ 2 / B - a) ≤ 2 * ip ^ 2 / gg := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [le_div_iff₀ hgpos]; exact hkey
      have : 2 * K ^ 2 / B = 2 * (K ^ 2 / B) := by ring
      linarith
    · -- K < √a √q2 ⇒ K²/B < a
      have hcase' : K ≤ Real.sqrt a * Real.sqrt q2 := by linarith [lt_of_not_ge hcase]
      have hK2 : K ^ 2 ≤ a * B := by
        have h1 : K ^ 2 ≤ (Real.sqrt a * Real.sqrt q2) ^ 2 := pow_le_pow_left₀ hK hcase' 2
        rw [mul_pow, Real.sq_sqrt ha0, Real.sq_sqrt hq0] at h1
        nlinarith
      have : K ^ 2 / B ≤ a := by rw [div_le_iff₀ hB]; linarith
      have : 2 * K ^ 2 / B = 2 * (K ^ 2 / B) := by ring
      linarith
  · -- gg = 0: then G vanishes on s, so ip = 0 and K = c'
    have hgg0' : gg = 0 := le_antisymm (not_lt.mp hgpos) hgg0
    have hGs : ∀ k ∈ s, G k = 0 := by
      intro k hk
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (G k))).mp hgg0' k hk
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have hip0 : ip = 0 := Finset.sum_eq_zero fun k hk => by rw [hGs k hk, mul_zero]
    have hK2 : K ^ 2 ≤ a * B := by
      rw [hK', hip0, zero_add, hB', hgg0', zero_add]; exact hCS
    have : K ^ 2 / B ≤ a := by rw [div_le_iff₀ hB]; linarith
    have : 2 * K ^ 2 / B = 2 * (K ^ 2 / B) := by ring
    rw [hgg0', div_zero]
    linarith

/-- **Overlap criterion.**  If every partial sum of `F²` is at most `1`, `Σ F G = K > 0` and
`Σ G² = B`, then every finite truncation satisfies
`1 + 2 (Σ_s F G)² / Σ_s G² − 2 Σ_s F² ≥ 2K²/B − 1`. -/
theorem overlap_criterion {ι : Type*} [DecidableEq ι] {F G : ι → ℝ} {K B : ℝ}
    (hF : ∀ t : Finset ι, ∑ k ∈ t, F k ^ 2 ≤ 1)
    (hFG : HasSum (fun k => F k * G k) K) (hG : HasSum (fun k => G k ^ 2) B) (hK : 0 < K)
    (s : Finset ι) :
    2 * K ^ 2 / B - 1
      ≤ 1 + 2 * (∑ k ∈ s, F k * G k) ^ 2 / (∑ k ∈ s, G k ^ 2) - 2 * ∑ k ∈ s, F k ^ 2 := by
  have tFG : Tendsto (fun t : Finset ι => ∑ k ∈ t, F k * G k) atTop (𝓝 K) := hFG
  have tG : Tendsto (fun t : Finset ι => ∑ k ∈ t, G k ^ 2) atTop (𝓝 B) := hG
  -- K² ≤ B from the partial Cauchy–Schwarz inequalities
  have hKB : K ^ 2 ≤ B := by
    have hev : ∀ t : Finset ι, (∑ k ∈ t, F k * G k) ^ 2 ≤ ∑ k ∈ t, G k ^ 2 := fun t => by
      have h1 := Finset.sum_mul_sq_le_sq_mul_sq t F G
      have h2 : 0 ≤ ∑ k ∈ t, G k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      nlinarith [hF t]
    exact le_of_tendsto_of_tendsto' (tFG.pow 2) tG hev
  have hB : 0 < B := lt_of_lt_of_le (by positivity) hKB
  have hlim : Tendsto (fun t : Finset ι => 2 * (∑ k ∈ t, F k * G k) ^ 2 / (∑ k ∈ t, G k ^ 2) - 1)
      atTop (𝓝 (2 * K ^ 2 / B - 1)) :=
    (((tFG.pow 2).const_mul 2).div tG hB.ne').sub_const 1
  refine le_of_tendsto hlim ?_
  have hKev : ∀ᶠ t in atTop, 0 < ∑ k ∈ t, F k * G k := tFG.eventually (lt_mem_nhds hK)
  have hBev : ∀ᶠ t in atTop, 0 < ∑ k ∈ t, G k ^ 2 := tG.eventually (lt_mem_nhds hB)
  filter_upwards [hKev, hBev, eventually_ge_atTop s] with t hKt hBt hst
  exact finite_overlap_criterion F G hst (hF t) hKt.le hBt


end

end GaloisForLFunctions.HilbertMetric
