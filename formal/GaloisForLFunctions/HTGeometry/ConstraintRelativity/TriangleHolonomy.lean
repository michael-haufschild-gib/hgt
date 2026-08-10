import Mathlib

/-!
# Heterogeneous triangle identity and the singular-holonomy law

Three normed spaces with bounded transports around a cycle and three declared realizations have a
based cyclic defect that decomposes exactly into the three transported edge defects:

`Ω₀ = T₂₀T₁₂ e₀₁ + T₂₀ e₁₂ + e₂₀`.

Hence a nonzero cyclic defect cannot coexist with exactly compatible edges, and if edge accuracy
tends to zero while the cyclic defect stays bounded below, the transport norms must diverge at
least reciprocally to the edge accuracy.

The locally convex form is the same identity plus equicontinuity: equicontinuous transports send
edge-exactness to holonomy-exactness.
-/

namespace HTGeometry.ConstraintRelativity

open Filter Topology

/-! ## The exact triangle identity -/

section Algebraic

variable {R E₀ E₁ E₂ : Type*} [Ring R]
  [AddCommGroup E₀] [Module R E₀] [AddCommGroup E₁] [Module R E₁] [AddCommGroup E₂] [Module R E₂]

/-- **Theorem 3.1.**  The based cyclic defect is the sum of the transported edge defects. -/
theorem cyclicDefect_eq (T₀₁ : E₀ →ₗ[R] E₁) (T₁₂ : E₁ →ₗ[R] E₂) (T₂₀ : E₂ →ₗ[R] E₀)
    (x₀ : E₀) (x₁ : E₁) (x₂ : E₂) :
    T₂₀ (T₁₂ (T₀₁ x₀)) - x₀
      = T₂₀ (T₁₂ (T₀₁ x₀ - x₁)) + T₂₀ (T₁₂ x₁ - x₂) + (T₂₀ x₂ - x₀) := by
  simp only [map_sub]
  abel

/-- **Corollary 3.2.**  Exactly compatible edges force a flat cycle. -/
theorem cyclicDefect_eq_zero (T₀₁ : E₀ →ₗ[R] E₁) (T₁₂ : E₁ →ₗ[R] E₂) (T₂₀ : E₂ →ₗ[R] E₀)
    (x₀ : E₀) (x₁ : E₁) (x₂ : E₂)
    (h₀₁ : T₀₁ x₀ - x₁ = 0) (h₁₂ : T₁₂ x₁ - x₂ = 0) (h₂₀ : T₂₀ x₂ - x₀ = 0) :
    T₂₀ (T₁₂ (T₀₁ x₀)) - x₀ = 0 := by
  rw [cyclicDefect_eq, h₀₁, h₁₂, h₂₀, map_zero, map_zero]
  abel

end Algebraic

/-! ## The norm bound and singular amplification -/

section Normed

variable {E₀ E₁ E₂ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- **Card `(3.2)`.**  The cyclic defect is bounded by the transported edge defects. -/
theorem norm_cyclicDefect_le (T₀₁ : E₀ →L[ℝ] E₁) (T₁₂ : E₁ →L[ℝ] E₂) (T₂₀ : E₂ →L[ℝ] E₀)
    (x₀ : E₀) (x₁ : E₁) (x₂ : E₂) :
    ‖T₂₀ (T₁₂ (T₀₁ x₀)) - x₀‖
      ≤ ‖T₂₀.comp T₁₂‖ * ‖T₀₁ x₀ - x₁‖ + ‖T₂₀‖ * ‖T₁₂ x₁ - x₂‖ + ‖T₂₀ x₂ - x₀‖ := by
  have hid := cyclicDefect_eq (T₀₁ : E₀ →ₗ[ℝ] E₁) (T₁₂ : E₁ →ₗ[ℝ] E₂) (T₂₀ : E₂ →ₗ[ℝ] E₀)
    x₀ x₁ x₂
  have hrw : T₂₀ (T₁₂ (T₀₁ x₀)) - x₀
      = (T₂₀.comp T₁₂) (T₀₁ x₀ - x₁) + T₂₀ (T₁₂ x₁ - x₂) + (T₂₀ x₂ - x₀) := hid
  rw [hrw]
  refine le_trans (norm_add₃_le) ?_
  gcongr
  · exact (T₂₀.comp T₁₂).le_opNorm _
  · exact T₂₀.le_opNorm _

/-- **Theorem 4.1, `(4.3)`.**  The cyclic defect is at most three times the amplification times the
edge accuracy. -/
theorem norm_cyclicDefect_le_three_mul (T₀₁ : E₀ →L[ℝ] E₁) (T₁₂ : E₁ →L[ℝ] E₂) (T₂₀ : E₂ →L[ℝ] E₀)
    (x₀ : E₀) (x₁ : E₁) (x₂ : E₂) (M eps : ℝ)
    (hM₁ : ‖T₂₀.comp T₁₂‖ ≤ M) (hM₂ : ‖T₂₀‖ ≤ M) (hM₃ : (1 : ℝ) ≤ M)
    (he₀₁ : ‖T₀₁ x₀ - x₁‖ ≤ eps) (he₁₂ : ‖T₁₂ x₁ - x₂‖ ≤ eps) (he₂₀ : ‖T₂₀ x₂ - x₀‖ ≤ eps) :
    ‖T₂₀ (T₁₂ (T₀₁ x₀)) - x₀‖ ≤ 3 * (M * eps) := by
  have heps : 0 ≤ eps := le_trans (norm_nonneg _) he₀₁
  have hMpos : (0 : ℝ) ≤ M := le_trans zero_le_one hM₃
  have hbound := norm_cyclicDefect_le T₀₁ T₁₂ T₂₀ x₀ x₁ x₂
  have h1 : ‖T₂₀.comp T₁₂‖ * ‖T₀₁ x₀ - x₁‖ ≤ M * eps := by
    exact mul_le_mul hM₁ he₀₁ (norm_nonneg _) hMpos
  have h2 : ‖T₂₀‖ * ‖T₁₂ x₁ - x₂‖ ≤ M * eps := by
    exact mul_le_mul hM₂ he₁₂ (norm_nonneg _) hMpos
  have h3 : ‖T₂₀ x₂ - x₀‖ ≤ M * eps := by
    refine le_trans he₂₀ ?_
    nlinarith
  linarith

/-- **Theorem 4.1, item 2 / `(4.5)`.**  If the cyclic defect stays at least `κ` while the edge
accuracy is `ε > 0`, the amplification is at least `κ/(3ε)`. -/
theorem amplification_ge (T₀₁ : E₀ →L[ℝ] E₁) (T₁₂ : E₁ →L[ℝ] E₂) (T₂₀ : E₂ →L[ℝ] E₀)
    (x₀ : E₀) (x₁ : E₁) (x₂ : E₂) (M eps kappa : ℝ)
    (hM₁ : ‖T₂₀.comp T₁₂‖ ≤ M) (hM₂ : ‖T₂₀‖ ≤ M) (hM₃ : (1 : ℝ) ≤ M)
    (he₀₁ : ‖T₀₁ x₀ - x₁‖ ≤ eps) (he₁₂ : ‖T₁₂ x₁ - x₂‖ ≤ eps) (he₂₀ : ‖T₂₀ x₂ - x₀‖ ≤ eps)
    (heps : 0 < eps) (hkappa : kappa ≤ ‖T₂₀ (T₁₂ (T₀₁ x₀)) - x₀‖) :
    kappa / (3 * eps) ≤ M := by
  have hb := norm_cyclicDefect_le_three_mul T₀₁ T₁₂ T₂₀ x₀ x₁ x₂ M eps hM₁ hM₂ hM₃ he₀₁ he₁₂ he₂₀
  rw [div_le_iff₀ (by positivity)]
  nlinarith

omit [NormedSpace ℝ E₀] in
/-- **Theorem 4.1, item 1.**  Uniformly bounded amplification plus vanishing edge accuracy forces
the cyclic defect to vanish. -/
theorem cyclicDefect_tendsto_zero_of_bounded {ι : Type*} {l : Filter ι}
    (Ω : ι → E₀) (M : ℝ) (eps : ι → ℝ)
    (hbound : ∀ n, ‖Ω n‖ ≤ 3 * (M * eps n))
    (heps : Tendsto eps l (𝓝 0)) :
    Tendsto (fun n => ‖Ω n‖) l (𝓝 0) := by
  have hzero : Tendsto (fun n => 3 * (M * eps n)) l (𝓝 0) := by
    have := (heps.const_mul M).const_mul 3
    simpa using this
  refine squeeze_zero (fun n => norm_nonneg _) hbound hzero

/-! ### The barrelled diagnostic -/

/-- **Corollary 5.2.**  In complete source spaces, pointwise boundedness of the two transport
families already forces the cyclic defect to vanish along vanishing edge accuracy: Banach–Steinhaus
upgrades pointwise bounds to a uniform operator bound, and the triangle law does the rest. -/
theorem cyclicDefect_tendsto_zero_of_pointwise_bounded [CompleteSpace E₁] [CompleteSpace E₂]
    {ι : Type*} {l : Filter ι} (S : ι → E₁ →L[ℝ] E₀) (T : ι → E₂ →L[ℝ] E₀)
    (e₀₁ : ι → E₁) (e₁₂ : ι → E₂) (e₂₀ : ι → E₀)
    (hS : ∀ y : E₁, ∃ C : ℝ, ∀ n, ‖S n y‖ ≤ C)
    (hT : ∀ z : E₂, ∃ C : ℝ, ∀ n, ‖T n z‖ ≤ C)
    (h₀₁ : Filter.Tendsto e₀₁ l (nhds 0)) (h₁₂ : Filter.Tendsto e₁₂ l (nhds 0))
    (h₂₀ : Filter.Tendsto e₂₀ l (nhds 0)) :
    Filter.Tendsto (fun n => S n (e₀₁ n) + T n (e₁₂ n) + e₂₀ n) l (nhds 0) := by
  obtain ⟨CS, hCS⟩ := banach_steinhaus hS
  obtain ⟨CT, hCT⟩ := banach_steinhaus hT
  refine squeeze_zero_norm' (a := fun n => CS * ‖e₀₁ n‖ + CT * ‖e₁₂ n‖ + ‖e₂₀ n‖)
    (Filter.Eventually.of_forall fun n => ?_) ?_
  · calc ‖S n (e₀₁ n) + T n (e₁₂ n) + e₂₀ n‖
        ≤ ‖S n (e₀₁ n)‖ + ‖T n (e₁₂ n)‖ + ‖e₂₀ n‖ :=
          le_trans (norm_add_le _ _) (by gcongr; exact norm_add_le _ _)
      _ ≤ CS * ‖e₀₁ n‖ + CT * ‖e₁₂ n‖ + ‖e₂₀ n‖ := by
          gcongr
          · exact le_trans ((S n).le_opNorm _) (by gcongr; exact hCS n)
          · exact le_trans ((T n).le_opNorm _) (by gcongr; exact hCT n)
  · have g₀₁ : Filter.Tendsto (fun n => ‖e₀₁ n‖) l (nhds 0) := by
      simpa using h₀₁.norm
    have g₁₂ : Filter.Tendsto (fun n => ‖e₁₂ n‖) l (nhds 0) := by
      simpa using h₁₂.norm
    have g₂₀ : Filter.Tendsto (fun n => ‖e₂₀ n‖) l (nhds 0) := by
      simpa using h₂₀.norm
    simpa using ((g₀₁.const_mul CS).add (g₁₂.const_mul CT)).add g₂₀

/-- **Corollary 5.2, contrapositive.**  A persistent cyclic defect in complete source spaces forces
failure of pointwise boundedness of one of the two transport families. -/
theorem not_pointwise_bounded_of_cyclicDefect [CompleteSpace E₁] [CompleteSpace E₂]
    {ι : Type*} {l : Filter ι} (S : ι → E₁ →L[ℝ] E₀) (T : ι → E₂ →L[ℝ] E₀)
    (e₀₁ : ι → E₁) (e₁₂ : ι → E₂) (e₂₀ : ι → E₀)
    (h₀₁ : Filter.Tendsto e₀₁ l (nhds 0)) (h₁₂ : Filter.Tendsto e₁₂ l (nhds 0))
    (h₂₀ : Filter.Tendsto e₂₀ l (nhds 0))
    (hpersist : ¬ Filter.Tendsto (fun n => S n (e₀₁ n) + T n (e₁₂ n) + e₂₀ n) l (nhds 0)) :
    (¬ ∀ y : E₁, ∃ C : ℝ, ∀ n, ‖S n y‖ ≤ C) ∨ (¬ ∀ z : E₂, ∃ C : ℝ, ∀ n, ‖T n z‖ ≤ C) := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  exact hpersist (cyclicDefect_tendsto_zero_of_pointwise_bounded S T e₀₁ e₁₂ e₂₀
    hcon.1 hcon.2 h₀₁ h₁₂ h₂₀)

end Normed

/-! ## Cofinal divergence of the amplification -/

section Amplification

/-- **Theorem 4.1, item 2, cofinal form.**  If the edge accuracy vanishes while the amplification
is bounded below by `κ/(3ε)` at every stage, the amplification diverges: transport norms grow at
least reciprocally to edge accuracy.  This is the card's "in particular" after `(4.5)`, which the
per-stage inequality `amplification_ge` supplies stage by stage. -/
theorem amplification_tendsto_atTop {ι : Type*} {l : Filter ι} (M eps : ι → ℝ) {kappa : ℝ}
    (hkappa : 0 < kappa) (hpos : ∀ n, 0 < eps n) (hb : ∀ n, kappa / (3 * eps n) ≤ M n)
    (heps : Filter.Tendsto eps l (nhds 0)) :
    Filter.Tendsto M l Filter.atTop := by
  have h3 : Filter.Tendsto (fun n => 3 * eps n) l (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using heps.const_mul (3 : ℝ)
    · exact Filter.Eventually.of_forall fun n => by
        have h := hpos n
        exact Set.mem_Ioi.2 (by positivity)
  have hinv : Filter.Tendsto (fun n => (3 * eps n)⁻¹) l Filter.atTop :=
    h3.inv_tendsto_nhdsGT_zero
  have hmul : Filter.Tendsto (fun n => kappa * (3 * eps n)⁻¹) l Filter.atTop :=
    hinv.const_mul_atTop hkappa
  refine Filter.tendsto_atTop_mono (fun n => ?_) hmul
  have h := hb n
  rwa [div_eq_mul_inv] at h

end Amplification

/-! ## The equicontinuous completion law -/

section LocallyConvex

variable {R E₀ E₁ E₂ : Type*} [Ring R]
  [AddCommGroup E₀] [Module R E₀] [TopologicalSpace E₀] [IsTopologicalAddGroup E₀]
  [AddCommGroup E₁] [Module R E₁] [TopologicalSpace E₁]
  [AddCommGroup E₂] [Module R E₂] [TopologicalSpace E₂]

/-- **Theorem 5.1.**  Equicontinuous transports send edge-exactness to holonomy-exactness.

The equicontinuity of the two transport families is written in its defining form at the origin:
every zero-neighbourhood of the target is reached from a single zero-neighbourhood of the source,
uniformly in the family. -/
theorem cyclicDefect_tendsto_zero_of_equicontinuous {ι : Type*} {l : Filter ι}
    (S : ι → E₁ → E₀) (T : ι → E₂ → E₀) (e₀₁ : ι → E₁) (e₁₂ : ι → E₂) (e₂₀ : ι → E₀)
    (hS : ∀ U ∈ 𝓝 (0 : E₀), ∃ V ∈ 𝓝 (0 : E₁), ∀ n, ∀ y ∈ V, S n y ∈ U)
    (hT : ∀ U ∈ 𝓝 (0 : E₀), ∃ V ∈ 𝓝 (0 : E₂), ∀ n, ∀ y ∈ V, T n y ∈ U)
    (h₀₁ : Tendsto e₀₁ l (𝓝 0)) (h₁₂ : Tendsto e₁₂ l (𝓝 0)) (h₂₀ : Tendsto e₂₀ l (𝓝 0)) :
    Tendsto (fun n => S n (e₀₁ n) + T n (e₁₂ n) + e₂₀ n) l (𝓝 0) := by
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨U₁, hU₁, hsub₁⟩ := exists_nhds_zero_half hU
  obtain ⟨U₂, hU₂, hsub₂⟩ := exists_nhds_zero_half hU₁
  obtain ⟨V₁, hV₁, hSV⟩ := hS U₂ hU₂
  obtain ⟨V₂, hV₂, hTV⟩ := hT U₂ hU₂
  filter_upwards [Filter.tendsto_def.1 h₀₁ V₁ hV₁, Filter.tendsto_def.1 h₁₂ V₂ hV₂,
    Filter.tendsto_def.1 h₂₀ U₁ hU₁] with n hn₁ hn₂ hn₃
  exact hsub₁ _ (hsub₂ _ (hSV n _ hn₁) _ (hTV n _ hn₂)) _ hn₃

end LocallyConvex

/-! ## Sharpness of the amplification bound -/

section Sharpness

/-- **Countermodel 6.1.**  For every positive `n` there is a triangle of real lines whose edge
defects are `1/n`, `0`, `0`, whose cyclic defect has norm one, and whose composed transport has
norm exactly `n`.  Arbitrarily accurate edges therefore coexist with a fixed holonomy, at the cost
of reciprocal amplification. -/
theorem exists_sharp_triangle (n : ℕ) (hn : 0 < n) :
    ∃ (T₀₁ T₁₂ T₂₀ : ℝ →L[ℝ] ℝ) (x₀ x₁ x₂ : ℝ),
      ‖T₀₁ x₀ - x₁‖ = 1 / n ∧ ‖T₁₂ x₁ - x₂‖ = 0 ∧ ‖T₂₀ x₂ - x₀‖ = 0 ∧
        ‖T₂₀ (T₁₂ (T₀₁ x₀)) - x₀‖ = 1 ∧
        ‖T₂₀.comp T₁₂‖ = n ∧ ‖T₂₀‖ = 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨0, (-(n : ℝ)) • ContinuousLinearMap.id ℝ ℝ, ContinuousLinearMap.id ℝ ℝ,
    1, -(1 / n), 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ‖(0 : ℝ) - -(1 / (n : ℝ))‖ = 1 / n
    rw [zero_sub, neg_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · show ‖(-(n : ℝ)) • (-(1 / (n : ℝ))) - 1‖ = 0
    rw [smul_eq_mul]
    have : (-(n : ℝ)) * (-(1 / (n : ℝ))) = 1 := by field_simp
    rw [this, sub_self, norm_zero]
  · show ‖(1 : ℝ) - 1‖ = 0
    rw [sub_self, norm_zero]
  · show ‖(-(n : ℝ)) • (0 : ℝ) - 1‖ = 1
    rw [smul_zero, zero_sub, norm_neg, norm_one]
  · rw [ContinuousLinearMap.id_comp, norm_smul, ContinuousLinearMap.norm_id, mul_one,
      norm_neg, Real.norm_eq_abs, abs_of_nonneg hn'.le]
  · exact ContinuousLinearMap.norm_id

/-- **Sharpness of Theorem 4.1.**  No amplification bound with a constant larger than one can
hold: `amplification_ge` proves `κ/(3ε) ≤ M`, and the countermodel forbids `C·κ/ε ≤ M` for any
`C > 1`.  The universal constant therefore lies in `[1/3, 1]`. -/
theorem not_amplification_ge_of_one_lt (C : ℝ) (hC : 1 < C) :
    ¬ ∀ (T₀₁ T₁₂ T₂₀ : ℝ →L[ℝ] ℝ) (x₀ x₁ x₂ : ℝ) (M eps kappa : ℝ),
        ‖T₂₀.comp T₁₂‖ ≤ M → ‖T₂₀‖ ≤ M → (1 : ℝ) ≤ M →
        ‖T₀₁ x₀ - x₁‖ ≤ eps → ‖T₁₂ x₁ - x₂‖ ≤ eps → ‖T₂₀ x₂ - x₀‖ ≤ eps →
        0 < eps → kappa ≤ ‖T₂₀ (T₁₂ (T₀₁ x₀)) - x₀‖ →
        C * (kappa / eps) ≤ M := by
  intro h
  obtain ⟨T₀₁, T₁₂, T₂₀, x₀, x₁, x₂, he₀₁, he₁₂, he₂₀, hΩ, hcomp, hT₂₀⟩ :=
    exists_sharp_triangle 1 one_pos
  have hone : ((1 : ℕ) : ℝ) = 1 := by norm_num
  rw [hone] at hcomp
  have hbound := h T₀₁ T₁₂ T₂₀ x₀ x₁ x₂ 1 1 1 (by rw [hcomp]) (by rw [hT₂₀])
    le_rfl (by rw [he₀₁]; norm_num) (by rw [he₁₂]; norm_num) (by rw [he₂₀]; norm_num)
    one_pos (by rw [hΩ])
  rw [div_one, mul_one] at hbound
  linarith

end Sharpness

end HTGeometry.ConstraintRelativity
