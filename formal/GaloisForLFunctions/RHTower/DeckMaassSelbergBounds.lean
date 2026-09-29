import GaloisForLFunctions.RHTower.DeckEisensteinTruncation

/-!
# Majorants and unfolding for the deck Maass–Selberg relation

For `Re s > 1`, `Y ≥ 1` and `v ∈ V_∞`, on the fundamental domain `𝒟`:

* the truncated series is bounded by a multiple of `y^{1-Re s}`: the truncated row sum is the real
  truncated row sum of the corpus, bounded below height `Y` and `O(y^{1-σ})` above it;
* the full series is `O(y^{1-Re s} + y^{Re s})`.

Products of these are dominated by `y^{β}` with `β < 1`, hence integrable on `𝒟`.  A `T`-periodic
function whose translates by the coprime-row matrices are integrable on `𝒟` with summable norms
unfolds: `∫_𝒟 Σ_{(c,d)} f(M_{c,d} z) = 2 ∫_{strip} f`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate Pointwise

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ## Integrability on `𝒟` from two power bounds -/

theorem integrableOn_fd_of_norm_le_two {g : ℍ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict fd))
    {β₁ β₂ C : ℝ} (h₁ : β₁ < 1) (h₂ : β₂ < 1)
    (hC : ∀ z ∈ fd, ‖g z‖ ≤ C * (z.im ^ β₁ + z.im ^ β₂)) : IntegrableOn g fd volume := by
  have hm : ∀ β : ℝ, β < 1 → IntegrableOn (fun z : ℍ => z.im ^ β) fd volume := fun β hβ => by
    have h : IntegrableOn (fun z : ℍ => ‖((z.im ^ β : ℝ) : ℂ)‖) fd volume :=
      (RHTower.integrableOn_fd_rpow hβ).norm
    refine h.congr_fun (fun z _ => ?_) isClosed_fd.measurableSet
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg z.im_pos.le β)]
  have hmaj : IntegrableOn (fun z : ℍ => C * (z.im ^ β₁ + z.im ^ β₂)) fd volume :=
    ((hm β₁ h₁).add (hm β₂ h₂)).const_mul C
  refine Integrable.mono' hmaj hg ?_
  exact (ae_restrict_iff' isClosed_fd.measurableSet).mpr (Filter.Eventually.of_forall hC)

theorem im_pos_of_mem_fd {z : ℍ} : 0 < z.im := z.im_pos

/-! ## The real truncated row sum -/

/-- `R_σ(z) = Σ [Im M_{c,d} z ≤ Y] Im(M_{c,d} z)^σ ≤ C y^{1-σ}` on `𝒟`. -/
theorem exists_realTruncatedRowSum_le {σ : ℝ} (hσ : 1 < σ) {Y : ℝ} (hY : 1 ≤ Y) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ fd, RHTower.realTruncatedRowSum σ Y z ≤ C * z.im ^ (1 - σ) := by
  set a := σ - 1 / 2
  have ha : 1 / 2 < a := by simp only [a]; linarith
  have hσa : σ = 1 / 2 + a := by simp only [a]; ring
  set C₁ := 2 * RHTower.rowBoundedConst a Y / ‖RHTower.msA (a : ℂ)‖
  have hC₁ : 0 ≤ C₁ := by
    have := RHTower.rowBoundedConst_nonneg a (by linarith : (0 : ℝ) ≤ Y)
    positivity
  have hYp : 0 < Y := by linarith
  refine ⟨C₁ * Y ^ (σ - 1) + RHTower.rowDecayConst a,
    add_nonneg (mul_nonneg hC₁ (Real.rpow_nonneg hYp.le _)) (RHTower.rowDecayConst_nonneg a),
    fun z hz => ?_⟩
  have hy := z.im_pos
  have hpow : 0 ≤ z.im ^ (1 - σ) := Real.rpow_nonneg hy.le _
  by_cases hzY : z.im ≤ Y
  · have h := RHTower.realTruncatedRowSum_le_of_le ha hY hz hzY
    rw [← hσa] at h
    have h2 : 1 ≤ Y ^ (σ - 1) * z.im ^ (1 - σ) := by
      have e : Y ^ (σ - 1) * Y ^ (1 - σ) = 1 := by
        rw [← Real.rpow_add hYp]; simp
      have h3 : Y ^ (σ - 1) * Y ^ (1 - σ) ≤ Y ^ (σ - 1) * z.im ^ (1 - σ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (z := 1 - σ) hy hzY (by linarith))
          (Real.rpow_nonneg hYp.le _)
      rwa [e] at h3
    calc RHTower.realTruncatedRowSum σ Y z ≤ C₁ := h
      _ ≤ C₁ * (Y ^ (σ - 1) * z.im ^ (1 - σ)) := le_mul_of_one_le_right hC₁ h2
      _ ≤ _ := by
        have := RHTower.rowDecayConst_nonneg a
        nlinarith [mul_nonneg this hpow]
  · have h := RHTower.realTruncatedRowSum_le_of_gt ha hY hz (not_le.1 hzY)
    rw [← hσa, show (1 / 2 : ℝ) - a = 1 - σ by simp only [a]; ring] at h
    have := mul_nonneg (mul_nonneg hC₁ (Real.rpow_nonneg hYp.le (σ - 1))) hpow
    nlinarith

/-! ## Norms of the truncated and full series on `𝒟` -/

theorem norm_truncRowTerm (Y : ℝ) (s : ℂ) (v : DeckSpace N) (p : gammaSet 1 1 0) (z : ℍ) :
    ‖truncRowTerm Y s v p z‖ =
      (if RHTower.rowHeight p z ≤ Y then RHTower.rowHeight p z ^ s.re else 0) * ‖v‖ := by
  unfold truncRowTerm
  split_ifs
  · exact norm_eisTerm_cpow s v p z
  · simp

theorem summable_norm_truncRowTerm {s : ℂ} (hs : 1 < s.re) (Y : ℝ) (v : DeckSpace N) (z : ℍ) :
    Summable fun p => ‖truncRowTerm Y s v p z‖ := by
  simp_rw [norm_truncRowTerm]
  exact (RHTower.summable_realTruncated_term hs Y z).mul_right _

theorem norm_tsum_truncRowTerm_le {s : ℂ} (hs : 1 < s.re) (Y : ℝ) (v : DeckSpace N) (z : ℍ) :
    ‖∑' p, truncRowTerm Y s v p z‖ ≤ RHTower.realTruncatedRowSum s.re Y z * ‖v‖ := by
  refine (norm_tsum_le_tsum_norm (summable_norm_truncRowTerm hs Y v z)).trans (le_of_eq ?_)
  simp_rw [norm_truncRowTerm]
  rw [tsum_mul_right]
  rfl

/-- `‖Λ^Y Ẽ(z, s; v)‖ ≤ C y^{1-Re s}` on `𝒟`. -/
theorem exists_norm_eisTrunc_le (hN : 2 ≤ N) {s : ℂ} (hs : 1 < s.re) {v : DeckSpace N}
    (hv : IsCuspVec v) {Y : ℝ} (hY : 1 ≤ Y) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ fd, ‖eisTrunc Y s v z‖ ≤ C * z.im ^ (1 - s.re) := by
  obtain ⟨C, hC, hR⟩ := exists_realTruncatedRowSum_le hs hY
  refine ⟨1 / 2 * (C * ‖v‖) + ‖scatVec s v‖, by positivity, fun z hz => ?_⟩
  have hy := z.im_pos
  rw [eisTrunc_eq_truncRowSum hN hs hv hY hz]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖(1 / 2 : ℂ) • ∑' p, truncRowTerm Y s v p z‖ ≤ 1 / 2 * (C * ‖v‖) * z.im ^ (1 - s.re) := by
    rw [norm_smul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have h := (norm_tsum_truncRowTerm_le hs Y v z).trans
      (mul_le_mul_of_nonneg_right (hR z hz) (norm_nonneg v))
    nlinarith
  have h2 : ‖(if Y < z.im then (z.im : ℂ) ^ (1 - s) • scatVec s v else 0)‖ ≤
      ‖scatVec s v‖ * z.im ^ (1 - s.re) := by
    split_ifs
    · rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
      simp only [Complex.sub_re, Complex.one_re]
      rw [mul_comm]
    · rw [norm_zero]; exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hy.le _)
  calc _ ≤ 1 / 2 * (C * ‖v‖) * z.im ^ (1 - s.re) + ‖scatVec s v‖ * z.im ^ (1 - s.re) :=
        add_le_add h1 h2
    _ = _ := by ring

/-- The constant term `y^s v + y^{1-s} Φ̃(s) v`. -/
def eisCT (s : ℂ) (v : DeckSpace N) (y : ℝ) : DeckSpace N :=
  ((y : ℂ) ^ s) • v + ((y : ℂ) ^ (1 - s)) • scatVec s v

theorem norm_eisCT_le (s : ℂ) (v : DeckSpace N) {y : ℝ} (hy : 0 < y) :
    ‖eisCT s v y‖ ≤ ‖v‖ * y ^ s.re + ‖scatVec s v‖ * y ^ (1 - s.re) := by
  unfold eisCT
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.sub_re, Complex.one_re]
  ring

theorem eisTrunc_def (Y : ℝ) (s : ℂ) (v : DeckSpace N) (z : ℍ) :
    eisTrunc Y s v z = eisExt s v z - if Y < z.im then eisCT s v z.im else 0 := rfl

/-- `‖Ẽ(z, s; v)‖ ≤ C (y^{1-Re s} + y^{Re s})` on `𝒟`. -/
theorem exists_norm_eisVec_le (hN : 2 ≤ N) {s : ℂ} (hs : 1 < s.re) {v : DeckSpace N}
    (hv : IsCuspVec v) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ fd, ‖eisVec s v z‖ ≤ C * (z.im ^ (1 - s.re) + z.im ^ s.re) := by
  obtain ⟨C, hC, hT⟩ := exists_norm_eisTrunc_le hN hs hv (le_refl 1)
  refine ⟨C + ‖v‖ + ‖scatVec s v‖, by positivity, fun z hz => ?_⟩
  have hy := z.im_pos
  have he : eisVec s v z = eisTrunc 1 s v z + if 1 < z.im then eisCT s v z.im else 0 := by
    rw [eisTrunc_def, ← eisVec_eq_eisExt hN hs hv]; abel
  rw [he]
  refine (norm_add_le _ _).trans ?_
  have h2 : ‖(if 1 < z.im then eisCT s v z.im else 0)‖ ≤
      ‖v‖ * z.im ^ s.re + ‖scatVec s v‖ * z.im ^ (1 - s.re) := by
    split_ifs
    · exact norm_eisCT_le s v hy
    · rw [norm_zero]; positivity
  have p1 : 0 ≤ z.im ^ (1 - s.re) := Real.rpow_nonneg hy.le _
  have p2 : 0 ≤ z.im ^ s.re := Real.rpow_nonneg hy.le _
  nlinarith [hT z hz, norm_nonneg v, norm_nonneg (scatVec s v), mul_nonneg hC p2,
    mul_nonneg (norm_nonneg v) p1, mul_nonneg (norm_nonneg (scatVec s v)) p2]

/-! ## Measurability -/

theorem measurable_eisCT_im (s : ℂ) (v : DeckSpace N) :
    Measurable fun z : ℍ => eisCT s v z.im := by
  unfold eisCT
  have hc : Continuous fun z : ℍ => ((z.im : ℝ) : ℂ) := Complex.continuous_ofReal.comp continuous_im
  refine Continuous.measurable ?_
  refine ((Continuous.cpow hc continuous_const fun z => ?_).smul continuous_const).add
    ((Continuous.cpow hc continuous_const fun z => ?_).smul continuous_const) <;>
  exact Or.inl (by simpa using z.im_pos)

theorem measurable_eisTrunc (hN : 2 ≤ N) {s : ℂ} (hs : 1 < s.re) {v : DeckSpace N}
    (hv : IsCuspVec v) (Y : ℝ) : Measurable (eisTrunc Y s v) := by
  have he : eisTrunc Y s v = fun z => eisVec s v z - if Y < z.im then eisCT s v z.im else 0 := by
    funext z; rw [eisTrunc_def, eisVec_eq_eisExt hN hs hv]
  rw [he]
  exact (continuous_eisVec hs hv.1).measurable.sub (Measurable.ite
    (measurableSet_lt measurable_const continuous_im.measurable) (measurable_eisCT_im s v)
    measurable_const)

/-! ## Unfolding -/

/-- **Unfolding with integrable translates.** A `T`-periodic `f` whose translates `f ∘ M_{c,d}` are
integrable on `𝒟` with summable norms is integrable on the strip, and
`∫_𝒟 Σ_{(c,d)} f(M_{c,d} z) = 2 ∫_{strip} f`. -/
theorem integral_fd_tsum_eq_two_mul_strip {f : ℍ → ℂ}
    (hT : ∀ (n : ℤ) (w : ℍ), f (ModularGroup.T ^ n • w) = f w)
    (hint : ∀ p : gammaSet 1 1 0, IntegrableOn (fun z => f (gammaSetMatrix p • z)) fd volume)
    (hsum : Summable fun p : gammaSet 1 1 0 => ∫ z in fd, ‖f (gammaSetMatrix p • z)‖) :
    IntegrableOn f modularStrip volume ∧
      ∫ z in fd, ∑' p : gammaSet 1 1 0, f (gammaSetMatrix p • z) = 2 * ∫ w in modularStrip, f w := by
  have hstrip : IntegrableOn f modularStrip volume := by
    have hunion : IntegrableOn f (⋃ w : gammaSetHalf, halfRep w • fd) volume := by
      refine integrableOn_iUnion_of_summable_integral_norm (fun w => ?_) ?_
      · rw [halfRep_smul_fd, integrableOn_smul_set_iff]
        exact hint w.1
      · simp_rw [RHTower.setIntegral_norm_halfRep_smul_fd]
        exact hsum.subtype _
    exact (isFundamentalDomain_modularStrip.integrableOn_iff isFundamentalDomain_iUnion_halfRep_smul_fd
      (translationSubgroup_invariant_of_periodic hT)).mpr hunion
  refine ⟨hstrip, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm hint hsum,
    tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip f hT hstrip]

end

end GaloisForLFunctions.RHTower.DeckPointPair
