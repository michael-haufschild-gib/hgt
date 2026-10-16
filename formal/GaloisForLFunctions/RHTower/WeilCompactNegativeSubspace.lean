import GaloisForLFunctions.RHTower.CHMDCompactTestSynthesis

/-!
# A finite compact Weil block gives an actual negative test subspace

A coefficient margin supplies one common support interval and a strict
ordinary-L2-relative margin on the entire range of the synthesis map.
-/

open MeasureTheory Set Filter Topology Complex Zeta23

noncomputable section

namespace RHTower

namespace CompactNegativeSubspace

private def testSynthesis {k : ℕ} (f : Fin k → ℝ → ℂ) (c : Fin k → ℂ) : ℝ → ℂ :=
  fun x => ∑ i, c i * f i x

private def testEnvelope {k : ℕ} (f : Fin k → ℝ → ℂ) : ℝ → ℝ :=
  fun x => ∑ i, ‖f i x‖

private theorem testEnvelope_compact {k : ℕ} (f : Fin k → ℝ → ℂ)
    (hc : ∀ i, HasCompactSupport (f i)) : HasCompactSupport (testEnvelope f) := by
  have he : testEnvelope f = ∑ i, fun x => ‖f i x‖ := by
    funext x
    simp only [testEnvelope, Finset.sum_apply]
  rw [he]
  exact HasCompactSupport.finset_sum fun i _ => (hc i).norm

private theorem norm_le_testEnvelope {k : ℕ} (f : Fin k → ℝ → ℂ) (i : Fin k) (x : ℝ) :
    ‖f i x‖ ≤ testEnvelope f x :=
  Finset.single_le_sum (fun j _ => norm_nonneg (f j x)) (Finset.mem_univ i)

private theorem norm_testSynthesis_le {k : ℕ} (f : Fin k → ℝ → ℂ) (c : Fin k → ℂ) (x : ℝ) :
    ‖testSynthesis f c x‖ ≤ ‖c‖ * testEnvelope f x := by
  calc ‖testSynthesis f c x‖ ≤ ∑ i, ‖c i * f i x‖ := norm_sum_le _ _
    _ = ∑ i, ‖c i‖ * ‖f i x‖ := by simp only [norm_mul]
    _ ≤ ∑ i, ‖c‖ * ‖f i x‖ :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (norm_le_pi_norm c i) (norm_nonneg _)
    _ = ‖c‖ * testEnvelope f x := by rw [← Finset.mul_sum]; rfl

private theorem exists_testSynthesis_support {k : ℕ} (f : Fin k → ℝ → ℂ)
    (hc : ∀ i, HasCompactSupport (f i)) :
    ∃ A : ℝ, 0 < A ∧ ∀ c : Fin k → ℂ, tsupport (testSynthesis f c) ⊆ Icc (-A) A := by
  classical
  obtain ⟨A, hA, hsupp⟩ :=
    (testEnvelope_compact f hc).isCompact.isBounded.subset_closedBall_lt (0 : ℝ) 0
  refine ⟨A, hA, fun c => ?_⟩
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  change (∑ i, c i * f i x) ≠ 0 at hx
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  have hfi : f i x ≠ 0 := fun hh => hi (by rw [hh, mul_zero])
  have hEx : testEnvelope f x ≠ 0 :=
    ne_of_gt ((norm_pos_iff.mpr hfi).trans_le (norm_le_testEnvelope f i x))
  have hb := hsupp (subset_tsupport (testEnvelope f) hEx)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hb
  exact abs_le.mp hb

private theorem exists_testSynthesis_L2_bound {k : ℕ} (f : Fin k → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hc : ∀ i, HasCompactSupport (f i)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : Fin k → ℂ,
      (∫ x, ‖testSynthesis f c x‖^2) ≤ ‖c‖^2 * B := by
  have hEcont : Continuous (testEnvelope f) :=
    continuous_finsetSum _ fun i _ => (hf i).continuous.norm
  have hEc2 : HasCompactSupport (fun x => (testEnvelope f x)^2) := by
    simp only [pow_two]
    exact (testEnvelope_compact f hc).mul_right (f' := testEnvelope f)
  have hEi : Integrable (fun x => (testEnvelope f x)^2) :=
    (hEcont.pow 2).integrable_of_hasCompactSupport hEc2
  refine ⟨∫ x, (testEnvelope f x)^2, integral_nonneg fun x => sq_nonneg _, fun c => ?_⟩
  have hpoint (x : ℝ) : ‖testSynthesis f c x‖^2 ≤ ‖c‖^2 * (testEnvelope f x)^2 := by
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (norm_testSynthesis_le f c x) 2
  have hg : ContDiff ℝ 2 (testSynthesis f c) ∧ HasCompactSupport (testSynthesis f c) :=
    CHMDDoobGraph.compact_synthesis f hf hc c
  have hgc2 : HasCompactSupport (fun x => ‖testSynthesis f c x‖^2) := by
    simp only [pow_two]
    exact hg.2.norm.mul_right (f' := fun x => ‖testSynthesis f c x‖)
  have hi : Integrable (fun x => ‖testSynthesis f c x‖^2) :=
    (hg.1.continuous.norm.pow 2).integrable_of_hasCompactSupport hgc2
  calc (∫ x, ‖testSynthesis f c x‖^2) ≤ ∫ x, ‖c‖^2 * (testEnvelope f x)^2 :=
      integral_mono hi (hEi.const_mul _) hpoint
    _ = ‖c‖^2 * ∫ x, (testEnvelope f x)^2 := by rw [integral_const_mul]

end CompactNegativeSubspace

open CompactNegativeSubspace

/-- A compact polar family with a coefficient gap spans the full claimed
complex dimension, with a common support interval and an L2-relative gap. -/
theorem exists_compact_negative_subspace_of_coefficient_gap {k : ℕ}
    (f : Fin k → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hc : ∀ i, HasCompactSupport (f i))
    (hp : ∀ i, paperFT (f i) (I/2) = 0 ∧ paperFT (f i) (-I/2) = 0)
    (hneg : ∀ c : Fin k → ℂ,
      (zetaZeroConfig.W (fun x => ∑ i, c i * f i x)
        (fun x => ∑ i, c i * f i x)).re ≤ -(1/2 : ℝ) * ‖c‖^2) :
    ∃ A : ℝ, 0 < A ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧ Module.finrank ℂ V = k ∧
        (∀ g ∈ V, ContDiff ℝ 2 g ∧ tsupport g ⊆ Icc (-A) A ∧
          paperFT g (I/2) = 0 ∧ paperFT g (-I/2) = 0) ∧
        ∀ g ∈ V, g ≠ 0 → (zetaZeroConfig.W g g).re < -ε * ∫ x, ‖g x‖^2 := by
  classical
  let Γ : (Fin k → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
    { toFun := fun c x => ∑ i, c i * f i x
      map_add' := fun c d => by
        funext x
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun z c => by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hΓ (c : Fin k → ℂ) : ContDiff ℝ 2 (Γ c) ∧ HasCompactSupport (Γ c) :=
    CHMDDoobGraph.compact_synthesis f hf hc c
  have hΓFT (c : Fin k → ℂ) (z : ℂ) :
      paperFT (Γ c) z = ∑ i, c i * paperFT (f i) z :=
    paperFT_finset_sum Finset.univ c (fun i => (hf i).continuous) hc z
  have hW0 : zetaZeroConfig.W 0 0 = 0 := by
    simp [ZeroConfig.W, ZeroConfig.Wsummand, paperFT_def]
  have hΓneg (c : Fin k → ℂ) (hc0 : c ≠ 0) :
      (zetaZeroConfig.W (Γ c) (Γ c)).re < 0 := by
    have hn : 0 < ‖c‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hc0)
    have he := hneg c
    change (zetaZeroConfig.W (Γ c) (Γ c)).re ≤ _ at he
    linarith
  have hinj : Function.Injective Γ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc0
    rw [LinearMap.mem_ker] at hc0
    by_contra hc'
    have hn := hΓneg c hc'
    rw [hc0, hW0, Complex.zero_re] at hn
    exact lt_irrefl _ hn
  obtain ⟨A, hA, hΓsupp⟩ := exists_testSynthesis_support f hc
  obtain ⟨B, hB0, hL2⟩ := exists_testSynthesis_L2_bound f hf hc
  let ε : ℝ := 1 / (2 * (B+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεB : ε * B < 1/2 := by
    have hfrac : B/(B+1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    have he : ε*B = (1/2 : ℝ)*(B/(B+1)) := by
      dsimp [ε]
      field_simp [show B+1 ≠ 0 by linarith only [hB0]]
    rw [he]
    linarith
  refine ⟨A, hA, ε, hε, Γ.range, inferInstance, ?_, ?_, ?_⟩
  · simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      LinearMap.finrank_range_of_inj hinj
  · rintro g ⟨c, rfl⟩
    refine ⟨(hΓ c).1, hΓsupp c, ?_, ?_⟩
    · rw [hΓFT]
      simp only [fun i => (hp i).1, mul_zero, Finset.sum_const_zero]
    · rw [hΓFT]
      simp only [fun i => (hp i).2, mul_zero, Finset.sum_const_zero]
  · rintro g ⟨c, rfl⟩ hg0
    have hc0 : c ≠ 0 := fun he => hg0 (by rw [he, map_zero])
    have hcn : 0 < ‖c‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hc0)
    have hh := mul_le_mul_of_nonneg_left (hL2 c) hε.le
    change ε * (∫ x, ‖Γ c x‖^2) ≤ ε * (‖c‖^2 * B) at hh
    have hgap := mul_lt_mul_of_pos_right hεB hcn
    have hn := hneg c
    change (zetaZeroConfig.W (Γ c) (Γ c)).re ≤ _ at hn
    nlinarith only [hh, hgap, hn]

end RHTower
