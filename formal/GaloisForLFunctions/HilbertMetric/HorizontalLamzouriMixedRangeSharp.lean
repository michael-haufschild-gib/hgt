import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriUnnormalized

/-!
# The mixed range in the four-trace bound, with its quadratic gain

The unnormalised horizontal Lamzouri inequality (`HorizontalPacket.four_mass_sub_energy_le`)
bounds the mixed range by the tangent line `4α − α² ≤ 2α + 1` at `α = 1`. Keeping the exact
square instead (`four_mass_sub_energy_le_add_mixedRange`) and applying Cauchy–Schwarz to the
`d ≤ #M` diagonal values of that range gives a nonnegative gain:

`4·mass − E − 2N + 2Σ_H(1 − ‖f‖²) + Σ_M(1 + 2‖P_A f‖² − 2‖f‖²) + (#M − S)²/#M ≤ #H`,

with `S = Σ_{x∈M}(‖f_x‖² − ‖P_A f_x‖²)` the unabsorbed mass of the mixed points
(`four_mass_sub_energy_le_sharp`, for `‖f_x‖ ≤ 1`). In terms of the absorbed fractions
`t_x = ‖P_A f_x‖²` of unit vectors, the mixed cost `Σ(1 − 2t_x)` becomes `#M(1 − 2t̄ − t̄²)`,
`t̄` the mean absorbed fraction: a mixed point costs nothing on average once `t̄ ≥ √2 − 1`.
-/

open scoped RealInnerProductSpace
open Finset Module

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace HorizontalPacket

variable {ι₂ ιH ιM ιP : Type*} [Fintype ι₂] [Fintype ιH] [Fintype ιM] [Fintype ιP]
variable (P : HorizontalPacket V ι₂ ιH ιM ιP)

/-- On `C^⊥` the diagonal form sees only the mixed vectors, minus the odd vectors. -/
theorem diagForm_le_of_mem_orthogonal_hsSpan' (hmP : ∀ p, 0 ≤ P.mP p) {ψ : V}
    (hψ : ψ ∈ P.hsSpanᗮ) : P.diagForm ψ ≤ ∑ i, ⟪P.fM i, ψ⟫ ^ 2 := by
  rw [P.diagForm_eq]
  have h1 : ∀ i, ⟪P.f₂ i, ψ⟫ = 0 := fun i =>
    Submodule.inner_right_of_mem_orthogonal (P.absorbing_le_hsSpan (P.f₂_mem_absorbing i)) hψ
  have h2 : ∀ i, ⟪P.fH i, ψ⟫ = 0 := fun i =>
    Submodule.inner_right_of_mem_orthogonal (P.fH_mem_hsSpan i) hψ
  have h3 : ∀ p, ⟪P.g p, ψ⟫ = 0 := fun p =>
    Submodule.inner_right_of_mem_orthogonal (P.absorbing_le_hsSpan (P.g_mem_absorbing p)) hψ
  simp only [h1, h2, h3, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero]
  have : 0 ≤ ∑ p, 2 * P.mP p * ⟪P.h p, ψ⟫ ^ 2 := Finset.sum_nonneg fun p _ =>
    mul_nonneg (mul_nonneg zero_le_two (hmP p)) (sq_nonneg _)
  linarith

/-- **The mixed range** carries at most the unabsorbed mixed mass `Σ_M (‖f‖² − ‖P_A f‖²)`. -/
theorem mixed_range_sum_le_unabsorbed (hmP : ∀ p, 0 ≤ P.mP p) :
    ∑ j, P.diagForm ((stdOrthonormalBasis ℝ (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V)) j : V)
      ≤ ∑ i, (‖P.fM i‖ ^ 2 - ‖P.absorbing.starProjection (P.fM i)‖ ^ 2) := by
  set K₃ : Submodule ℝ V := P.hsSpanᗮ ⊓ P.positiveSpan
  calc ∑ j, P.diagForm ((stdOrthonormalBasis ℝ K₃) j : V)
        ≤ ∑ j, ∑ i, ⟪P.fM i, ((stdOrthonormalBasis ℝ K₃) j : V)⟫ ^ 2 :=
        Finset.sum_le_sum fun j _ => P.diagForm_le_of_mem_orthogonal_hsSpan' hmP
          (Submodule.mem_inf.mp ((stdOrthonormalBasis ℝ K₃) j).2).1
    _ = ∑ i, ‖K₃.starProjection (P.fM i)‖ ^ 2 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => sum_sq_inner_stdOrthonormalBasis K₃ (P.fM i)
    _ ≤ ∑ i, (‖P.fM i‖ ^ 2 - ‖P.absorbing.starProjection (P.fM i)‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hv := P.vec_mem_fullSpan (Sum.inr (Sum.inr (Sum.inl i)))
        simp only [vec, Sum.elim_inr, Sum.elim_inl] at hv
        have h := P.norm_sq_split hv
        have := sq_nonneg ‖(P.absorbingᗮ ⊓ P.hsSpan : Submodule ℝ V).starProjection (P.fM i)‖
        have := sq_nonneg ‖(P.positiveSpanᗮ ⊓ P.fullSpan : Submodule ℝ V).starProjection (P.fM i)‖
        linarith

/-- **Four-trace bound with the exact mixed-range slack.** With `α_j` the diagonal values of the
mixed range, `Σ_j α_j² − 2Σ_j α_j + #M ≥ 0` is added to the left side. -/
theorem four_mass_sub_energy_le_add_mixedRange (hm₂ : ∀ i, 2 ≤ P.m₂ i)
    (hmP : ∀ p, 1 ≤ P.mP p) :
    4 * P.mass - P.energy - 2 * P.count + 2 * ∑ i, (1 - ‖P.fH i‖ ^ 2)
      + ∑ i, (1 + 2 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 2 * ‖P.fM i‖ ^ 2)
      + (∑ j, P.diagForm ((stdOrthonormalBasis ℝ
            (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V)) j : V) ^ 2
        - 2 * ∑ j, P.diagForm ((stdOrthonormalBasis ℝ
            (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V)) j : V) + Fintype.card ιM)
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
  simp only [one_pow, one_mul, mul_one] at hq₂
  norm_num at hq₁
  rw [eH, eM]
  simp only [count]
  linarith

/-- **Four-trace bound with the quadratic mixed gain.** For `‖f_x‖ ≤ 1`, with
`S = Σ_M (‖f‖² − ‖P_A f‖²)`, the mixed points gain `(#M − S)²/#M`. -/
theorem four_mass_sub_energy_le_sharp (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ p, 1 ≤ P.mP p)
    (hMn : ∀ i, ‖P.fM i‖ ≤ 1) :
    4 * P.mass - P.energy - 2 * P.count + 2 * ∑ i, (1 - ‖P.fH i‖ ^ 2)
      + ∑ i, (1 + 2 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 2 * ‖P.fM i‖ ^ 2)
      + (Fintype.card ιM - ∑ i, (‖P.fM i‖ ^ 2 - ‖P.absorbing.starProjection (P.fM i)‖ ^ 2)) ^ 2
          / Fintype.card ιM
      ≤ Fintype.card ιH := by
  have hmP0 : ∀ p, 0 ≤ P.mP p := fun p => le_trans zero_le_one (hmP p)
  have hbase := P.four_mass_sub_energy_le_add_mixedRange hm₂ hmP
  have hs := P.mixed_range_sum_le_unabsorbed hmP0
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i, (‖P.fM i‖ ^ 2 - ‖P.absorbing.starProjection (P.fM i)‖ ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s, s = ∑ j, P.diagForm ((stdOrthonormalBasis ℝ
      (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V)) j : V) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = ∑ j, P.diagForm ((stdOrthonormalBasis ℝ
      (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V)) j : V) ^ 2 := ⟨_, rfl⟩
  rw [← hS] at hs ⊢
  rw [← hsdef] at hs hbase
  rw [← hX] at hbase
  have hSn : S ≤ Fintype.card ιM := by
    have : ∀ i, ‖P.fM i‖ ^ 2 - ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 ≤ 1 := fun i => by
      have := hMn i
      have := sq_nonneg ‖P.absorbing.starProjection (P.fM i)‖
      nlinarith [norm_nonneg (P.fM i)]
    have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => this i
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← hS] at h
    exact h
  have hd : (finrank ℝ (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V) : ℝ) ≤ Fintype.card ιM := by
    exact_mod_cast P.finrank_positiveSpan_inf_le
  have hX0 : 0 ≤ X := hX ▸ Finset.sum_nonneg fun j _ => sq_nonneg _
  have hCS : s ^ 2 ≤ (Fintype.card ιM : ℝ) * X := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin (finrank ℝ (P.hsSpanᗮ ⊓ P.positiveSpan :
        Submodule ℝ V))))) (f := fun j => P.diagForm ((stdOrthonormalBasis ℝ
          (P.hsSpanᗮ ⊓ P.positiveSpan : Submodule ℝ V)) j : V))
    simp only [Finset.card_univ, Fintype.card_fin] at h
    rw [← hsdef, ← hX] at h
    exact h.trans (mul_le_mul_of_nonneg_right hd hX0)
  have hgain : ((Fintype.card ιM : ℝ) - S) ^ 2 / Fintype.card ιM ≤
      X - 2 * s + Fintype.card ιM := by
    rcases eq_or_lt_of_le (Nat.cast_nonneg (Fintype.card ιM) : (0 : ℝ) ≤ Fintype.card ιM)
      with h0 | hpos
    · rw [← h0, div_zero]
      have hs0 : s ^ 2 ≤ 0 := by rw [← h0, zero_mul] at hCS; exact hCS
      have : s = 0 := by nlinarith [sq_nonneg s]
      rw [this]; linarith
    · rw [div_le_iff₀ hpos]
      have h1 : ((Fintype.card ιM : ℝ) - S) ^ 2 ≤ ((Fintype.card ιM : ℝ) - s) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      nlinarith
  linarith

/-- **Sharp deficits.** If each mixed point has a deficit `d_x` with
`−d_x ≤ 1 + 2‖P_A f_x‖² − 2‖f_x‖²`, then for every `b ≥ 0`
`4·mass − E − 2N ≤ #H + Σ_M ((1 + b)d_x − b + b²)`. With `b = 0` this is the plain deficit count;
`b > 0` spends the quadratic mixed gain `(#M − S)²/#M ≥ bΣ(1 − d_x) − b²#M`. -/
theorem four_mass_sub_energy_le_add_sharp_deficit (hm₂ : ∀ i, 2 ≤ P.m₂ i)
    (hmP : ∀ p, 1 ≤ P.mP p) (hH : ∀ i, ‖P.fH i‖ ≤ 1) (hMn : ∀ i, ‖P.fM i‖ ≤ 1)
    (dfc : ιM → ℝ)
    (hcost : ∀ i, -dfc i ≤ 1 + 2 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 2 * ‖P.fM i‖ ^ 2)
    {b : ℝ} (hb : 0 ≤ b) :
    4 * P.mass - P.energy - 2 * P.count ≤
      Fintype.card ιH + ∑ i, ((1 + b) * dfc i - b + b ^ 2) := by
  have h := P.four_mass_sub_energy_le_sharp hm₂ hmP hMn
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i, (‖P.fM i‖ ^ 2 - ‖P.absorbing.starProjection (P.fM i)‖ ^ 2) :=
    ⟨_, rfl⟩
  rw [← hS] at h
  have h1 : 0 ≤ ∑ i, (1 - ‖P.fH i‖ ^ 2) := Finset.sum_nonneg fun i _ => by
    have := hH i
    have := norm_nonneg (P.fH i)
    nlinarith
  have h2 : -∑ i, dfc i ≤
      ∑ i, (1 + 2 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 2 * ‖P.fM i‖ ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => hcost i
  -- `2S ≤ #M + Σ d`
  have hS2 : 2 * S ≤ Fintype.card ιM + ∑ i, dfc i := by
    have : ∀ i, 2 * (‖P.fM i‖ ^ 2 - ‖P.absorbing.starProjection (P.fM i)‖ ^ 2) ≤ 1 + dfc i :=
      fun i => by linarith [hcost i]
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => this i
    rw [← Finset.mul_sum, ← hS, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] at hs
    exact hs
  -- the gain dominates `b Σ(1 − d) − b² #M`
  have hgain : 2 * b * ((Fintype.card ιM : ℝ) - S) - b ^ 2 * Fintype.card ιM ≤
      ((Fintype.card ιM : ℝ) - S) ^ 2 / Fintype.card ιM := by
    rcases eq_or_lt_of_le (Nat.cast_nonneg (Fintype.card ιM) : (0 : ℝ) ≤ Fintype.card ιM)
      with h0 | hpos
    · have hS0 : S = 0 := by
        rw [hS]
        have hempty : IsEmpty ιM := Fintype.card_eq_zero_iff.mp (by exact_mod_cast h0.symm)
        exact Finset.sum_of_isEmpty _
      rw [← h0, hS0]; simp
    · rw [le_div_iff₀ hpos]
      nlinarith [sq_nonneg (((Fintype.card ιM : ℝ) - S) - b * Fintype.card ιM)]
  have e : ∑ i, ((1 + b) * dfc i - b + b ^ 2) =
      (1 + b) * ∑ i, dfc i - b * Fintype.card ιM + b ^ 2 * Fintype.card ιM := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hS2 hb]

end HorizontalPacket

end GaloisForLFunctions.HilbertMetric
