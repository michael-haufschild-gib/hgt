import GaloisForLFunctions.CompactHyperbolicSurfaces.CocompactGroups

/-!
# Automorphic kernels on a cocompact quotient

For a profile `k ≥ 0` the automorphic kernel is `K(z, w) = Σ_{γ ∈ Γ} k(u(z, γw))` (`autK`).  It is
`Γ`-invariant in each variable and symmetric, and it unfolds against a fundamental domain:
`∫_F K(z, w) dw = ∫_ℍ k(u(z, w)) dw` (`setLIntegral_autK`).

Counting gives `Σ_γ (1 + u(z, γw))^{−σ} ≤ M` uniformly in `z, w` for `σ > 1`
(`exists_tsum_rpow_le`, by the dyadic bound `x^{−σ} ≤ Σ_{j : x < 2^{j+1}} 2^{−jσ}`), and with
`1 + u(z, γw) ≥ e^{−2D}/4 · (1 + u(z₀, γw₀))` near `(z₀, w₀)` the real automorphic kernel of a
continuous profile with `|k(u)| ≤ C(1 + u)^{−σ}` is continuous (`continuous_autR`).
-/

open MeasureTheory Set Filter UpperHalfPlane Metric
open scoped ENNReal MatrixGroups Pointwise

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry

noncomputable section

variable (Γ : Subgroup SL(2, ℝ))

/-- The automorphic kernel `K(z, w) = Σ_γ k(u(z, γw))` of a nonnegative profile. -/
def autK (k : ℝ → ℝ≥0∞) (z w : ℍ) : ℝ≥0∞ := ∑' γ : Γ, k (pairU z ((γ : SL(2, ℝ)) • w))

/-- The automorphic kernel `Σ_γ k(u(z, γw))` of a real profile. -/
def autR (k : ℝ → ℝ) (z w : ℍ) : ℝ := ∑' γ : Γ, k (pairU z ((γ : SL(2, ℝ)) • w))

variable {Γ}

theorem autK_smul_right (k : ℝ → ℝ≥0∞) (z w : ℍ) (δ : Γ) :
    autK Γ k z ((δ : SL(2, ℝ)) • w) = autK Γ k z w := by
  unfold autK
  rw [← (Equiv.mulRight δ).tsum_eq]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, mul_smul]

theorem autK_smul_left (k : ℝ → ℝ≥0∞) (z w : ℍ) (δ : Γ) :
    autK Γ k ((δ : SL(2, ℝ)) • z) w = autK Γ k z w := by
  unfold autK
  rw [← (Equiv.mulLeft δ).tsum_eq]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, mul_smul, pairU_smul]

theorem autK_comm (k : ℝ → ℝ≥0∞) (z w : ℍ) : autK Γ k z w = autK Γ k w z := by
  unfold autK
  rw [← (Equiv.inv Γ).tsum_eq]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.inv_apply, Subgroup.coe_inv]
  rw [pairU_comm, pairU_smul_left, inv_inv]

theorem measurable_autK [Countable Γ] {k : ℝ → ℝ≥0∞} (hk : Measurable k) :
    Measurable (Function.uncurry (autK Γ k)) := by
  refine Measurable.ennreal_tsum fun γ => hk.comp ?_
  exact (continuous_pairU.comp (continuous_fst.prodMk
    ((continuous_const_smul ((γ : SL(2, ℝ)))).comp continuous_snd))).measurable

/-- **Unfolding.**  `∫_F K(z, w) dw = ∫_ℍ k(u(z, w)) dw`. -/
theorem setLIntegral_autK [Countable Γ] {F : Set ℍ} (hF : IsFundamentalDomain Γ F volume)
    {k : ℝ → ℝ≥0∞} (hk : Measurable k) (z : ℍ) :
    ∫⁻ w in F, autK Γ k z w = ∫⁻ w, k (pairU z w) := by
  rw [hF.lintegral_eq_tsum'' (fun w => k (pairU z w)), autK, lintegral_tsum]
  · rfl
  · intro γ
    exact (hk.comp (continuous_pairU.comp (continuous_const.prodMk
      (continuous_const_smul ((γ : SL(2, ℝ)))))).measurable).aemeasurable

theorem lintegral_pairU_eq_I (k : ℝ → ℝ≥0∞) (z : ℍ) :
    ∫⁻ w, k (pairU z w) = ∫⁻ w, k (pairU I w) := lintegral_pairU_eq k z

/-! ### Uniform summability -/

/-- `x^{−σ} ≤ Σ_{j : x < 2^{j+1}} 2^{−jσ}` for `x ≥ 1`, `σ ≥ 0`. -/
theorem rpow_neg_le_tsum {x σ : ℝ} (hx : 1 ≤ x) (hσ : 0 ≤ σ) :
    ENNReal.ofReal (x ^ (-σ)) ≤ ∑' j : ℕ, {j : ℕ | x < 2 ^ (j + 1)}.indicator
      (fun j => ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-σ))) j := by
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hx one_lt_two
  refine le_trans ?_ (ENNReal.le_tsum j)
  rw [indicator_of_mem (show j ∈ {j : ℕ | x < 2 ^ (j + 1)} from hj2)]
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_nonpos (by positivity) hj1 (by linarith))

namespace IsCocompactFree

variable (hΓ : IsCocompactFree Γ)
include hΓ

/-- **Uniform summability.**  `Σ_γ (1 + u(z, γw))^{−σ} ≤ M` for all `z, w`, when `σ > 1`. -/
theorem exists_tsum_rpow_le {σ : ℝ} (hσ : 1 < σ) : ∃ M : ℝ≥0∞, M < ∞ ∧ ∀ z w : ℍ,
    ∑' γ : Γ, ENNReal.ofReal ((1 + pairU z ((γ : SL(2, ℝ)) • w)) ^ (-σ)) ≤ M := by
  obtain ⟨C, hC0, hC⟩ := hΓ.exists_card_le
  set q : ℝ := 2 ^ (1 - σ) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hq1' : ENNReal.ofReal q < 1 := by rw [ENNReal.ofReal_lt_one]; exact hq1
  refine ⟨ENNReal.ofReal (2 * C) * (1 - ENNReal.ofReal q)⁻¹,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hq1')),
    fun z w => ?_⟩
  set S : ℕ → Set Γ := fun j => {γ : Γ | pairU z ((γ : SL(2, ℝ)) • w) ≤ 2 ^ (j + 1) - 1}
  have hpt : ∀ γ : Γ, ENNReal.ofReal ((1 + pairU z ((γ : SL(2, ℝ)) • w)) ^ (-σ)) ≤
      ∑' j : ℕ, (S j).indicator (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-σ))) γ := by
    intro γ
    refine (rpow_neg_le_tsum (by linarith [pairU_nonneg z ((γ : SL(2, ℝ)) • w)])
      (by linarith)).trans (ENNReal.tsum_le_tsum fun j => ?_)
    by_cases h : 1 + pairU z ((γ : SL(2, ℝ)) • w) < 2 ^ (j + 1)
    · rw [indicator_of_mem (show j ∈ {j : ℕ | 1 + pairU z ((γ : SL(2, ℝ)) • w) < 2 ^ (j + 1)}
        from h), indicator_of_mem (show γ ∈ S j by show _ ≤ _; linarith)]
    · rw [indicator_of_notMem (show j ∉ {j : ℕ | 1 + pairU z ((γ : SL(2, ℝ)) • w) < 2 ^ (j + 1)}
        from h)]
      exact zero_le
  have hcount : ∀ j : ℕ, ∑' γ : Γ, (S j).indicator
      (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-σ))) γ ≤
      ENNReal.ofReal (2 * C) * ENNReal.ofReal q ^ j := by
    intro j
    have hU : (0 : ℝ) ≤ 2 ^ (j + 1) - 1 := by
      have : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ one_le_two
      linarith
    obtain ⟨hfin, hcard⟩ := hC z w _ hU
    rw [← tsum_subtype, ENNReal.tsum_set_const, ← hfin.cast_ncard_eq]
    have h1 : ((S j).ncard : ℝ≥0∞) ≤ ENNReal.ofReal (C * (1 + (2 ^ (j + 1) - 1))) := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hcard
    calc ((S j).ncard : ℝ≥0∞) * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-σ))
        ≤ ENNReal.ofReal (C * (1 + (2 ^ (j + 1) - 1))) * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-σ)) :=
          mul_le_mul_right' h1 _
      _ = ENNReal.ofReal (2 * C) * ENNReal.ofReal q ^ j := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hq0,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul (by norm_num)]
          have : (2 : ℝ) ^ (j + 1 : ℕ) = 2 * 2 ^ (j : ℝ) := by
            rw [pow_succ, Real.rpow_natCast]; ring
          rw [show (1 + (2 ^ (j + 1) - 1) : ℝ) = 2 ^ (j + 1 : ℕ) by ring, this]
          rw [show (2 : ℝ) * C * 2 ^ ((1 - σ) * (j : ℝ)) =
            C * (2 * (2 ^ (j : ℝ) * 2 ^ ((j : ℝ) * -σ))) by
              rw [← Real.rpow_add (by norm_num)]; ring_nf]
  calc ∑' γ : Γ, ENNReal.ofReal ((1 + pairU z ((γ : SL(2, ℝ)) • w)) ^ (-σ))
      ≤ ∑' γ : Γ, ∑' j : ℕ, (S j).indicator
          (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-σ))) γ := ENNReal.tsum_le_tsum hpt
    _ = ∑' j : ℕ, ∑' γ : Γ, (S j).indicator
          (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-σ))) γ := ENNReal.tsum_comm
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (2 * C) * ENNReal.ofReal q ^ j := ENNReal.tsum_le_tsum hcount
    _ = ENNReal.ofReal (2 * C) * (1 - ENNReal.ofReal q)⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

theorem summable_rpow {σ : ℝ} (hσ : 1 < σ) (z w : ℍ) :
    Summable fun γ : Γ => (1 + pairU z ((γ : SL(2, ℝ)) • w)) ^ (-σ) := by
  obtain ⟨M, hM, hle⟩ := hΓ.exists_tsum_rpow_le hσ
  have hne : ∑' γ : Γ, ENNReal.ofReal ((1 + pairU z ((γ : SL(2, ℝ)) • w)) ^ (-σ)) ≠ ∞ :=
    ((hle z w).trans_lt hM).ne
  have := ENNReal.summable_toReal hne
  refine this.congr fun γ => ?_
  rw [ENNReal.toReal_ofReal (by have := pairU_nonneg z ((γ : SL(2, ℝ)) • w); positivity)]

end IsCocompactFree

/-- Near `(z₀, w₀)`: `1 + u(z, gw) ≥ e^{−2D}/4 · (1 + u(z₀, gw₀))`. -/
theorem one_add_pairU_ge {z₀ w₀ z w : ℍ} {D : ℝ} (hz : dist z z₀ ≤ D) (hw : dist w w₀ ≤ D)
    (g : SL(2, ℝ)) :
    Real.exp (-(2 * D)) / 4 * (1 + pairU z₀ (g • w₀)) ≤ 1 + pairU z (g • w) := by
  rw [pairU_eq_cosh, pairU_eq_cosh]
  set d₀ := dist z₀ (g • w₀)
  set d := dist z (g • w)
  have htri : d₀ ≤ d + 2 * D := by
    have h1 : dist (g • w) (g • w₀) = dist w w₀ := dist_smul _ _ _
    calc d₀ ≤ dist z₀ z + dist z (g • w) + dist (g • w) (g • w₀) := dist_triangle4 _ _ _ _
      _ ≤ D + d + D := by rw [dist_comm z₀ z, h1]; linarith
      _ = d + 2 * D := by ring
  have hc0 : Real.cosh d₀ ≤ Real.exp (d + 2 * D) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp d₀ ≤ Real.exp (d + 2 * D) := Real.exp_le_exp.mpr htri
    have h2 : Real.exp (-d₀) ≤ Real.exp (d + 2 * D) :=
      Real.exp_le_exp.mpr (by have := dist_nonneg (x := z) (y := g • w); have := dist_nonneg (x := z₀) (y := g • w₀); linarith)
    linarith
  have hD : 0 ≤ D := le_trans dist_nonneg hz
  have he : Real.exp (-(2 * D)) * Real.exp (d + 2 * D) = Real.exp d := by
    rw [← Real.exp_add]; congr 1; ring
  have hed : Real.exp (-(2 * D)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hcd : Real.exp d ≤ 2 * Real.cosh d := by rw [Real.cosh_eq]; linarith [Real.exp_pos (-d)]
  have hpos := Real.exp_pos (-(2 * D))
  nlinarith [Real.one_le_cosh d₀, Real.one_le_cosh d]

namespace IsCocompactFree

variable (hΓ : IsCocompactFree Γ)
include hΓ

/-- **Continuity.**  The real automorphic kernel of a continuous profile with
`|k(u)| ≤ C (1 + u)^{−σ}`, `σ > 1`, is continuous on `ℍ × ℍ`. -/
theorem continuous_autR {k : ℝ → ℝ} (hk : Continuous k) {σ C : ℝ} (hσ : 1 < σ)
    (hkC : ∀ u, 0 ≤ u → |k u| ≤ C * (1 + u) ^ (-σ)) :
    Continuous fun p : ℍ × ℍ => autR Γ k p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨z₀, w₀⟩
  set s : Set (ℍ × ℍ) := closedBall z₀ 1 ×ˢ closedBall w₀ 1
  have hs : s ∈ nhds (z₀, w₀) :=
    prod_mem_nhds (closedBall_mem_nhds _ one_pos) (closedBall_mem_nhds _ one_pos)
  have hC0 : 0 ≤ C := by
    have := hkC 0 le_rfl
    have h1 : 0 < (1 + (0 : ℝ)) ^ (-σ) := by positivity
    nlinarith [abs_nonneg (k 0)]
  set c : ℝ := Real.exp (-(2 * 1)) / 4
  have hc : 0 < c := by positivity
  refine ContinuousOn.continuousAt ?_ hs
  refine continuousOn_tsum (u := fun γ : Γ => C * c ^ (-σ) *
    (1 + pairU z₀ ((γ : SL(2, ℝ)) • w₀)) ^ (-σ)) (fun γ => ?_)
    ((hΓ.summable_rpow hσ z₀ w₀).mul_left _) (fun γ p hp => ?_)
  · exact (hk.comp (continuous_pairU.comp (continuous_fst.prodMk
      ((continuous_const_smul ((γ : SL(2, ℝ)))).comp continuous_snd)))).continuousOn
  · have hz : dist p.1 z₀ ≤ 1 := hp.1
    have hw : dist p.2 w₀ ≤ 1 := hp.2
    have hcomp := one_add_pairU_ge hz hw (γ : SL(2, ℝ))
    have h0 : 0 < 1 + pairU z₀ ((γ : SL(2, ℝ)) • w₀) := by
      have := pairU_nonneg z₀ ((γ : SL(2, ℝ)) • w₀); linarith
    rw [Real.norm_eq_abs]
    refine (hkC _ (pairU_nonneg _ _)).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    calc (1 + pairU p.1 ((γ : SL(2, ℝ)) • p.2)) ^ (-σ)
        ≤ (c * (1 + pairU z₀ ((γ : SL(2, ℝ)) • w₀))) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hcomp (by linarith)
      _ = c ^ (-σ) * (1 + pairU z₀ ((γ : SL(2, ℝ)) • w₀)) ^ (-σ) :=
          Real.mul_rpow hc.le h0.le

/-- A profile bounded by `C (1 + u)^{−σ}` has a uniformly bounded automorphic kernel. -/
theorem exists_autK_le {σ : ℝ} (hσ : 1 < σ) : ∃ M : ℝ≥0∞, M < ∞ ∧
    ∀ {k : ℝ → ℝ≥0∞} {C : ℝ}, (∀ u, 0 ≤ u → k u ≤ ENNReal.ofReal (C * (1 + u) ^ (-σ))) →
      ∀ z w : ℍ, autK Γ k z w ≤ ENNReal.ofReal C * M := by
  obtain ⟨M, hM, hle⟩ := hΓ.exists_tsum_rpow_le hσ
  refine ⟨M, hM, fun {k C} hk z w => ?_⟩
  calc autK Γ k z w ≤ ∑' γ : Γ, ENNReal.ofReal C *
        ENNReal.ofReal ((1 + pairU z ((γ : SL(2, ℝ)) • w)) ^ (-σ)) := by
        refine ENNReal.tsum_le_tsum fun γ => (hk _ (pairU_nonneg _ _)).trans ?_
        rcases le_total 0 C with hC | hC
        · rw [ENNReal.ofReal_mul hC]
        · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hC (by
            have := pairU_nonneg z ((γ : SL(2, ℝ)) • w); positivity))]
          exact zero_le
    _ = ENNReal.ofReal C * ∑' γ : Γ, ENNReal.ofReal ((1 + pairU z ((γ : SL(2, ℝ)) • w)) ^ (-σ)) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal C * M := mul_le_mul_left' (hle z w) _

end IsCocompactFree

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
