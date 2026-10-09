import GaloisForLFunctions.RHTower.NonvacuousTestEnergy
import GaloisForLFunctions.RHTower.ModularLambdaCellEnergyBound

/-!
# The test field beats `h_φ(½)` on a deep enough cyclic cover

Let `δ = m_φ − h_φ(½) > 0`.  With `Q = [SL(2,ℤ) : Γ_N] = P k`, `P = [SL(2,ℤ) : Γ(2)]`,
`k = [Γ(2) : Γ_N]`:

* the mass is `∫_𝒟 ‖F‖² = Q ∫_𝒟 c_L² ≥ Q μ₀`, where `μ₀ = μ(𝒟 ∩ {Im ≤ 2})` and `L ≥ 2`
  (`integral_norm_sq_testField_ge`);
* the phase energy is at most `(2 C m_φ m_β / N²) k C_Λ ρ L²` by the energy bound and the area
  estimate `(Λ)`;
* the cutoff energy is at most `2 Q (log ρ_R / log L)² m_φ μ(𝒟)`.

Taking `L` large and then `N` large makes the Dirichlet form smaller than `2 δ ∫_𝒟 ‖F‖²`
(`exists_testField_dirichlet_lt`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped MatrixGroups InnerProductSpace ENNReal

namespace GaloisForLFunctions.RHTower.NonvacuousWitness

open GaloisForLFunctions.HTGeometry RepPointPair RepCoset ModularLambdaWinding

noncomputable section

/-! ## The mass -/

/-- The truncated cell `𝒟 ∩ {Im ≤ 2}` has positive measure. -/
theorem volume_fd_inter_im_le_two_pos : 0 < volume (fd ∩ {z : ℍ | z.im ≤ 2}) := by
  set U : Set ℍ := {z | 1 < Complex.normSq (z : ℂ) ∧ |z.re| < 1 / 2 ∧ z.im < 2}
  have hU : IsOpen U := by
    exact (isOpen_lt (continuous_const : Continuous fun _ : ℍ => (1 : ℝ))
      (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)).inter
      ((isOpen_lt (continuous_abs.comp UpperHalfPlane.continuous_re)
        (continuous_const : Continuous fun _ : ℍ => (1 / 2 : ℝ))).inter
      (isOpen_lt UpperHalfPlane.continuous_im (continuous_const : Continuous fun _ : ℍ => (2 : ℝ))))
  have hne : U.Nonempty := by
    refine ⟨⟨(3 / 2 : ℝ) * Complex.I, by simp⟩, ?_, ?_, ?_⟩
    · simp [Complex.normSq_apply]
      norm_num
    · simp [UpperHalfPlane.re]
    · simp [UpperHalfPlane.im]
      norm_num
  refine (hU.measure_pos volume hne).trans_le (measure_mono ?_)
  rintro z ⟨h1, h2, h3⟩
  exact ⟨⟨h1.le, h2.le⟩, h3.le⟩

variable (N : ℕ) [NeZero N]

/-- **The mass of the test field**: `∫_𝒟 ‖F‖² = Q ∫_𝒟 c_L²`, and `≥ Q μ₀` for `L ≥ 2`. -/
theorem integral_norm_sq_testField_ge {L : ℝ} (hL : 2 ≤ L) :
    (Fintype.card (SL(2, ℤ) ⧸ windingSubgroup N) : ℝ) *
        (volume (fd ∩ {z : ℍ | z.im ≤ 2})).toReal ≤
      ∫ z in fd, ‖testField N L z‖ ^ 2 := by
  simp_rw [norm_sq_testField]
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hmeas : MeasurableSet (fd ∩ {z : ℍ | z.im ≤ 2}) :=
    isClosed_fd.measurableSet.inter (measurableSet_le UpperHalfPlane.continuous_im.measurable
      measurable_const)
  have hint : Integrable (fun z => cuspRamp L z ^ 2) cellMeasure := by
    refine Integrable.of_bound ((continuous_cuspRamp L).pow 2).aestronglyMeasurable 1
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h0 := cuspRamp_nonneg L z
    have h1 := cuspRamp_le_one L z
    nlinarith
  calc (volume (fd ∩ {z : ℍ | z.im ≤ 2})).toReal
      = ∫ z in fd, ({z : ℍ | z.im ≤ 2}.indicator (fun _ => (1 : ℝ)) z) := by
        rw [integral_indicator (measurableSet_le UpperHalfPlane.continuous_im.measurable
          measurable_const), setIntegral_const, smul_eq_mul, mul_one, Measure.real_def,
          Measure.restrict_apply (measurableSet_le UpperHalfPlane.continuous_im.measurable
          measurable_const), Set.inter_comm]
    _ ≤ ∫ z in fd, cuspRamp L z ^ 2 := by
        refine setIntegral_mono_on ?_ hint isClosed_fd.measurableSet fun z hz => ?_
        · exact (integrable_const (μ := cellMeasure) (1 : ℝ)).indicator (measurableSet_le
            UpperHalfPlane.continuous_im.measurable measurable_const)
        · by_cases h : z.im ≤ 2
          · rw [Set.indicator_of_mem (show z ∈ {z : ℍ | z.im ≤ 2} from h),
              cuspRamp_eq_one (by linarith) hz (by linarith), one_pow]
          · rw [Set.indicator_of_notMem (show z ∉ {z : ℍ | z.im ≤ 2} from h)]
            exact sq_nonneg _


omit [NeZero N] in
theorem windingSubgroup_le_gammaTwo : windingSubgroup N ≤ Gamma 2 := fun _ hg =>
  (mem_windingSubgroup.1 hg).1

/-- **The windowed coset energy of `log λ` is controlled by the area estimate**:
`∫_𝒟 1_{Y ≤ T} Σ_{q ∈ SL(2,ℤ)/Γ_N} E(g_q⁻¹ ·) ≤ k C T` with `k = [Γ(2) : Γ_N]`. -/
theorem lintegral_cosetEnergy_window_le [Fintype (Gamma 2 ⧸ (windingSubgroup N).subgroupOf (Gamma 2))]
    {C : ℝ} (hΛ : ∀ T : ℝ, 1 ≤ T → ∫⁻ z in fd ∩ {z : ℍ | z.im ≤ T},
      ∑ p : SL(2, ℤ) ⧸ Gamma 2, ENNReal.ofReal (lambdaLogEnergy ((Quotient.out p)⁻¹ • z)) ≤
        ENNReal.ofReal (C * T)) {T : ℝ} (hT : 1 ≤ T) :
    ∫⁻ z in fd, ENNReal.ofReal ({η : ℍ | invHeight η ≤ T}.indicator
      (cosetEnergy N lambdaLogEnergy) z) ≤
      Fintype.card (Gamma 2 ⧸ (windingSubgroup N).subgroupOf (Gamma 2)) * ENNReal.ofReal (C * T) := by
  have hS : MeasurableSet {z : ℍ | z.im ≤ T} :=
    measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const
  have htower : ∀ z, cosetEnergy N lambdaLogEnergy z =
      Fintype.card (Gamma 2 ⧸ (windingSubgroup N).subgroupOf (Gamma 2)) *
        ∑ p : SL(2, ℤ) ⧸ Gamma 2, lambdaLogEnergy ((Quotient.out p)⁻¹ • z) :=
    fun z => sum_out_inv_smul_tower (windingSubgroup_le_gammaTwo N)
      (fun γ hγ η => lambdaLogEnergy_smul hγ η) z
  calc ∫⁻ z in fd, ENNReal.ofReal ({η : ℍ | invHeight η ≤ T}.indicator
        (cosetEnergy N lambdaLogEnergy) z)
      = ∫⁻ z in fd, {z : ℍ | z.im ≤ T}.indicator
          (fun z => ENNReal.ofReal (cosetEnergy N lambdaLogEnergy z)) z := by
        refine setLIntegral_congr_fun isClosed_fd.measurableSet fun z hz => ?_
        simp only [Set.indicator, Set.mem_setOf_eq, invHeight_eq_of_mem_fd hz]
        split_ifs <;> simp
    _ = ∫⁻ z in fd ∩ {z : ℍ | z.im ≤ T}, ENNReal.ofReal (cosetEnergy N lambdaLogEnergy z) := by
        rw [lintegral_indicator hS, Measure.restrict_restrict hS, Set.inter_comm]
    _ = Fintype.card (Gamma 2 ⧸ (windingSubgroup N).subgroupOf (Gamma 2)) *
          ∫⁻ z in fd ∩ {z : ℍ | z.im ≤ T}, ∑ p : SL(2, ℤ) ⧸ Gamma 2,
            ENNReal.ofReal (lambdaLogEnergy ((Quotient.out p)⁻¹ • z)) := by
        rw [← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
        refine lintegral_congr fun z => ?_
        rw [htower, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg fun p _ => lambdaLogEnergy_nonneg _]
    _ ≤ _ := by gcongr; exact hΛ T hT


end

/-! ## The final estimate -/

/-- The Bochner Dirichlet form is bounded by its `lintegral` form. -/
theorem integral_dirichlet_le_toReal {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u)
    {ι : Type} [Fintype ι] {F : ℍ → EuclideanSpace ℂ ι}
    (hFc : Continuous F) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hle : ∫⁻ z in fd, ∫⁻ w, ENNReal.ofReal (φ (pairU z w) * ‖F z - F w‖ ^ 2) ≤ B) :
    ∫ z in fd, ∫ w, φ (pairU z w) * ‖F z - F w‖ ^ 2 ≤ B.toReal := by
  have hcont : Continuous (fun q : ℍ × ℍ => φ (pairU q.1 q.2) * ‖F q.1 - F q.2‖ ^ 2) :=
    (hφc.comp continuous_pairU).mul (((hFc.comp continuous_fst).sub (hFc.comp continuous_snd)).norm.pow 2)
  have h0 : ∀ z, 0 ≤ ∫ w, φ (pairU z w) * ‖F z - F w‖ ^ 2 := fun z =>
    integral_nonneg fun w => mul_nonneg (hφ0 _) (sq_nonneg _)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0)
    hcont.aestronglyMeasurable.integral_prod_right']
  refine ENNReal.toReal_mono hB ((lintegral_mono fun z => ?_).trans hle)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun w =>
    mul_nonneg (hφ0 _) (sq_nonneg _)) (hcont.comp (Continuous.prodMk_right z)).aestronglyMeasurable]
  exact ENNReal.ofReal_toReal_le

/-- **The test field beats `h_φ(½)` on a deep enough cyclic cover.**  For a nonnegative `C³` profile `φ`
and any `δ > 0` there are `N ≥ 2` and `L ≥ 2` with
`∫_𝒟 ∫_ℍ φ(u(z, w)) ‖F_{N,L}(z) − F_{N,L}(w)‖² < 2 δ ∫_𝒟 ‖F_{N,L}‖²`. -/
theorem exists_testField_dirichlet_lt (P : SmoothProfile) (hφ0 : ∀ u, 0 ≤ P.toFun u) {δ : ℝ}
    (hδ : 0 < δ) : ∃ n : ℕ, ∃ L : ℝ, 2 ≤ L ∧
      ∫ z in fd, ∫ w, P.toFun (pairU z w) *
          ‖testField (n + 2) L z - testField (n + 2) L w‖ ^ 2 <
        2 * δ * ∫ z in fd, ‖testField (n + 2) L z‖ ^ 2 := by
  classical
  obtain ⟨C, R₂, hC, hR₂, hE⟩ := exists_normSq_sub_le_energy P.radius
  obtain ⟨CΛ, hΛ⟩ := exists_lintegral_sum_lambdaLogEnergy_le
  set M := max CΛ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hΛ' : ∀ T : ℝ, 1 ≤ T → ∫⁻ z in fd ∩ {z : ℍ | z.im ≤ T},
      ∑ p : SL(2, ℤ) ⧸ Gamma 2, ENNReal.ofReal (lambdaLogEnergy ((Quotient.out p)⁻¹ • z)) ≤
        ENNReal.ofReal (M * T) := fun T hT =>
    (hΛ T hT).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by linarith)))
  set φ := P.toFun
  set mφ := kernelMassR φ
  set mβ := kernelMassR (bumpProfile R₂)
  have hmφ : 0 ≤ mφ := integral_nonneg fun w => hφ0 _
  have hmβ : 0 ≤ mβ := integral_nonneg fun w => bumpProfile_nonneg _ _
  set ρR := heightRatio P.radius
  set ρ₂ := heightRatio (R₂ + 1)
  have hρ₂ : 1 ≤ ρ₂ := one_le_heightRatio (by linarith)
  set μ₀ := (volume (fd ∩ {z : ℍ | z.im ≤ 2})).toReal
  have hμ₀ : 0 < μ₀ := ENNReal.toReal_pos volume_fd_inter_im_le_two_pos.ne'
    (measure_ne_top_of_subset Set.inter_subset_left volume_fd_ne_top)
  set V := (volume fd).toReal
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  -- the height window `L`
  set K₁ := 2 * Real.log ρR ^ 2 * mφ * V / (δ * μ₀)
  have hK₁ : 0 ≤ K₁ := by positivity
  set sL := Real.sqrt K₁ + 1
  have hsL1 : 1 ≤ sL := by linarith [Real.sqrt_nonneg K₁]
  have hsL : K₁ < sL ^ 2 := by
    have h := Real.sq_sqrt hK₁
    nlinarith [Real.sqrt_nonneg K₁]
  set L := Real.exp sL
  have hL2 : 2 ≤ L := by linarith [Real.add_one_le_exp sL]
  have hlogL : Real.log L = sL := Real.log_exp sL
  -- the depth `N`
  set T := ρ₂ * L ^ 2
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hρ₂ (by nlinarith)
  set K₂ := 2 * C * mφ * mβ * M * T / (δ * μ₀)
  have hK₂ : 0 ≤ K₂ := by positivity
  set n := ⌈Real.sqrt K₂⌉₊
  refine ⟨n, L, hL2, ?_⟩
  set N := n + 2
  have hNK : K₂ < (N : ℝ) ^ 2 := by
    have h1 : Real.sqrt K₂ ≤ n := Nat.le_ceil _
    have h2 : (n : ℝ) + 2 = N := by push_cast [N]; ring
    have h := Real.sq_sqrt hK₂
    nlinarith [Real.sqrt_nonneg K₂]
  have hN0 : (0 : ℝ) < N := by positivity
  -- the coset counts
  set e := Subgroup.quotientEquivProdOfLE (windingSubgroup_le_gammaTwo N)
  haveI : Finite (Gamma 2 ⧸ (windingSubgroup N).subgroupOf (Gamma 2)) :=
    Finite.of_surjective (Prod.snd ∘ e) (Prod.snd_surjective.comp e.surjective)
  letI : Fintype (Gamma 2 ⧸ (windingSubgroup N).subgroupOf (Gamma 2)) := Fintype.ofFinite _
  set k : ℝ := (Fintype.card (Gamma 2 ⧸ (windingSubgroup N).subgroupOf (Gamma 2)) : ℝ)
  set Q : ℝ := (Fintype.card (SL(2, ℤ) ⧸ windingSubgroup N) : ℝ)
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hQk : k ≤ Q := by
    have hcard := Fintype.card_congr e
    rw [Fintype.card_prod] at hcard
    have hP : (1 : ℝ) ≤ (Fintype.card (SL(2, ℤ) ⧸ Gamma 2) : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.2 ⟨(QuotientGroup.mk 1 : SL(2, ℤ) ⧸ Gamma 2)⟩
    have hQeq : Q = (Fintype.card (SL(2, ℤ) ⧸ Gamma 2) : ℝ) * k := by
      simp only [Q, k]
      rw [hcard]
      push_cast
      ring
    rw [hQeq]
    exact le_mul_of_one_le_left hk0 hP
  have hQpos : 0 < Q := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨QuotientGroup.mk 1⟩)
  -- the energy bound in `lintegral` form
  have hbound := lintegral_dirichlet_testField_le N P hφ0 (L := L) (by linarith)
    lambdaLogEnergy_nonneg continuous_lambdaLogEnergy
    (fun γ hγ η => lambdaLogEnergy_smul (windingSubgroup_le_gammaTwo N hγ) η) hC
    (fun z w h => hE lambdaLog differentiableOn_lambdaLog z w h)
  have hwin := lintegral_cosetEnergy_window_le N hΛ' hT
  set a := 2 * C * mφ * mβ / (N : ℝ) ^ 2
  set b := 2 * Q * (Real.log ρR / Real.log L) ^ 2 * mφ
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hfin : ENNReal.ofReal a * ((Fintype.card (Gamma 2 ⧸ (windingSubgroup N).subgroupOf (Gamma 2)) :
      ℝ≥0∞) * ENNReal.ofReal (M * T)) + ENNReal.ofReal b * volume fd =
      ENNReal.ofReal (a * (k * (M * T)) + b * V) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul ha,
      ENNReal.ofReal_mul hk0, ENNReal.ofReal_natCast, ENNReal.ofReal_mul hb,
      ENNReal.ofReal_toReal volume_fd_ne_top]
  have hlin : ∫⁻ z in fd, ∫⁻ w, ENNReal.ofReal (φ (pairU z w) *
      ‖testField N L z - testField N L w‖ ^ 2) ≤ ENNReal.ofReal (a * (k * (M * T)) + b * V) := by
    rw [← hfin]
    refine hbound.trans (add_le_add ?_ le_rfl)
    gcongr
  have hD := integral_dirichlet_le_toReal P.contDiff.continuous hφ0
    (continuous_testField N L) ENNReal.ofReal_ne_top hlin
  rw [ENNReal.toReal_ofReal (by positivity)] at hD
  have hmass := integral_norm_sq_testField_ge N hL2
  -- the arithmetic
  have hA : a * (k * (M * T)) ≤ k * (δ * μ₀) * (K₂ / (N : ℝ) ^ 2) := by
    simp only [a, K₂]
    field_simp
    rfl
  have hB : b * V = Q * (δ * μ₀) * (K₁ / sL ^ 2) := by
    simp only [b, K₁, hlogL]
    field_simp
  have hK₂N : K₂ / (N : ℝ) ^ 2 < 1 := (div_lt_one (by positivity)).2 hNK
  have hK₁s : K₁ / sL ^ 2 < 1 := (div_lt_one (by positivity)).2 hsL
  have hδμ : 0 < δ * μ₀ := mul_pos hδ hμ₀
  have h1 : a * (k * (M * T)) ≤ k * (δ * μ₀) := by
    refine hA.trans ?_
    calc k * (δ * μ₀) * (K₂ / (N : ℝ) ^ 2) ≤ k * (δ * μ₀) * 1 :=
          mul_le_mul_of_nonneg_left hK₂N.le (by positivity)
      _ = k * (δ * μ₀) := mul_one _
  have h2 : b * V < Q * (δ * μ₀) := by
    rw [hB]
    calc Q * (δ * μ₀) * (K₁ / sL ^ 2) < Q * (δ * μ₀) * 1 :=
          mul_lt_mul_of_pos_left hK₁s (by positivity)
      _ = Q * (δ * μ₀) := mul_one _
  calc ∫ z in fd, ∫ w, P.toFun (pairU z w) * ‖testField N L z - testField N L w‖ ^ 2
      ≤ a * (k * (M * T)) + b * V := hD
    _ < k * (δ * μ₀) + Q * (δ * μ₀) := by linarith
    _ ≤ 2 * δ * (Q * μ₀) := by nlinarith
    _ ≤ 2 * δ * ∫ z in fd, ‖testField N L z‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hmass (by positivity)

end GaloisForLFunctions.RHTower.NonvacuousWitness
