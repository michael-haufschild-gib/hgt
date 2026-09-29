import GaloisForLFunctions.RHTower.DeckPointPairLaplacian
import GaloisForLFunctions.RHTower.MaassFiniteDeckDirichletDense
import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainVolume

/-!
# Point-pair operators as an approximate identity

Since `d(z, w)² ≤ 8 u(z, w)`, a profile vanishing beyond `R` only sees hyperbolic distances below
`√(8R)`.  For a central-fixed seed `ψ` compactly supported in the interior of the modular cell, a
translate by `B ≠ ±1` cannot reach the support from an interior point, so near the seed
`L_φ ψ(z) = ∫_ℍ φ(u(z, w)) ψ(w) dμ(w)`; for a nonnegative profile of unit mass the uniform
continuity of `ψ` bounds `L_φ ψ - ψ` uniformly on a set of finite measure.  With the corpus
approximation of `L²` vectors by such seeds and the Schur bound `‖L_φ‖ ≤ 1`, this gives
`‖L_φ f - f‖ ≤ ε` for every central-fixed `f` once the radius is small.  Smooth unit profiles exist
at every radius.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped MatrixGroups ENNReal

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

local instance gammaNormalPPA (N : ℕ) : (CongruenceSubgroup.Gamma (N + 1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N + 1)

/-- `d(z, w)² ≤ 8 u(z, w)`. -/
theorem dist_sq_le_pairU (z w : ℍ) : dist z w ^ 2 ≤ 8 * pairU z w := by
  have h := pairU_eq_cosh z w
  have hd : 0 ≤ dist z w := dist_nonneg
  have e1 := Real.quadratic_le_exp_of_nonneg hd
  have e2 := Real.add_one_le_exp (-dist z w)
  rw [Real.cosh_eq] at h
  nlinarith

theorem dist_lt_of_pairU_le {z w : ℍ} {R r : ℝ} (hRr : 8 * R < r ^ 2) (hr : 0 < r)
    (h : pairU z w ≤ R) : dist z w < r := by
  have h1 := dist_sq_le_pairU z w
  exact lt_of_pow_lt_pow_left₀ 2 hr.le (by nlinarith)

/-- A nonnegative profile of unit mass integrates to `1` about every centre. -/
theorem integral_pairKernel_eq_one {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hmass : ppKernelMass φ = 1) (z : ℍ) : ∫ w, φ (pairU z w) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun w => hφ0 _)
    (hφc.comp (continuous_pairU_right z)).aestronglyMeasurable]
  have h := kernelMass_centre φ z
  simp only [abs_of_nonneg (hφ0 _)] at h
  rw [h, hmass, ENNReal.toReal_one]

theorem integrable_pairKernel_real {φ : ℝ → ℝ} {R : ℝ} (hφc : Continuous φ)
    (hφR : KernelSupport φ R) (z : ℍ) : Integrable (fun w : ℍ => φ (pairU z w)) := by
  refine (integrableOn_iff_integrable_of_support_subset (s := Metric.closedBall z (1 + 2 * R))
    ?_).1 ((hφc.comp (continuous_pairU_right z)).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _))
  intro w hw
  by_contra hwK
  apply hw
  have : R < pairU z w := by
    by_contra h
    push Not at h
    exact hwK (Metric.mem_closedBall.2 (by rw [dist_comm]; exact dist_le_of_pairU_le h))
  exact hφR _ this

theorem one_ne_neg_one_SL : (1 : SL(2, ℤ)) ≠ -1 := by
  intro h
  have := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp at this

theorem deckRho_one (v : DeckSpace N) : deckRho N 1 v = v := by
  ext q
  simp [deckRho, finiteRegularUnitary_apply]

/-! ## Interior seeds -/

section Seed

variable {φ : ℝ → ℝ} {R : ℝ} {ψ : ℍ → DeckSpace N} {K : Set ℍ} {ε₀ : ℝ}

/-- Near an interior seed only the translates by `±1` contribute. -/
theorem ppTerm_eq_zero_of_seed (hφR : KernelSupport φ R) (hRε : 8 * R < ε₀ ^ 2) (hε₀ : 0 < ε₀)
    (hK : tsupport ψ ⊆ K) (hKo : Metric.thickening ε₀ K ⊆ fdo) {z : ℍ} (hz : z ∈ fdo)
    {B : SL(2, ℤ)} (hB1 : B ≠ 1) (hB2 : B ≠ -1) : ppTerm φ ψ z B = 0 := by
  unfold ppTerm
  refine setIntegral_eq_zero_of_forall_eq_zero fun z' _ => ?_
  by_cases hψ : ψ z' = 0
  · simp [hψ]
  have hz'K : z' ∈ K := hK (subset_tsupport _ hψ)
  by_cases hu : pairU z (B • z') ≤ R
  · exfalso
    have hu' : pairU (B⁻¹ • z) z' ≤ R := by
      rwa [← pairU_smul_int B, smul_inv_smul]
    have hmem : B⁻¹ • z ∈ Metric.thickening ε₀ K :=
      Metric.mem_thickening_iff.2 ⟨z', hz'K, dist_lt_of_pairU_le hRε hε₀ hu'⟩
    rcases eq_one_or_neg_one_of_mem_fdo_mem_fd hz (fdo_subset_fd (hKo hmem)) with h | h
    · exact hB1 (inv_eq_one.mp h)
    · exact hB2 (by rw [inv_eq_iff_eq_inv.mp h, inv_neg_one])
  · rw [hφR _ (not_le.1 hu)]
    simp

/-- **Local form of `L_φ` on an interior seed.** -/
theorem ppApply_eq_integral_of_seed (hφR : KernelSupport φ R) (hRε : 8 * R < ε₀ ^ 2)
    (hε₀ : 0 < ε₀) (hK : tsupport ψ ⊆ K) (hKo : Metric.thickening ε₀ K ⊆ fdo)
    (hcentral : seedCentralFixed N ψ) {z : ℍ} (hz : z ∈ fdo) :
    ppApply φ ψ z = ∫ w, ((φ (pairU z w) : ℝ) : ℂ) • ψ w := by
  have hKfd : K ⊆ fd := fun w hw =>
    fdo_subset_fd (hKo (Metric.self_subset_thickening hε₀ K hw))
  unfold ppApply
  rw [tsum_eq_sum (s := {1, -1}) fun B hB => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hB
    exact ppTerm_eq_zero_of_seed hφR hRε hε₀ hK hKo hz hB.1 hB.2,
    Finset.sum_pair one_ne_neg_one_SL]
  have hneg : ppTerm φ ψ z (-1) = ppTerm φ ψ z 1 := by
    unfold ppTerm
    refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
    simp only
    rw [SL_neg_smul, one_smul, deckRho_one]
    exact congrArg _ (hcentral z')
  rw [hneg, ← two_smul ℂ, smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]
  unfold ppTerm
  simp only [one_smul, deckRho_one]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_
  rw [image_eq_zero_of_notMem_tsupport (fun h => hw (hKfd (hK h))), smul_zero]

/-- **Pointwise approximation** at an interior point. -/
theorem norm_ppApply_seed_sub_le (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hmass : ppKernelMass φ = 1) (hφR : KernelSupport φ R) (hRε : 8 * R < ε₀ ^ 2)
    (hε₀ : 0 < ε₀) (hψc : Continuous ψ) (hK : tsupport ψ ⊆ K) (hKo : Metric.thickening ε₀ K ⊆ fdo)
    (hcentral : seedCentralFixed N ψ) {z : ℍ} (hz : z ∈ fdo) {η : ℝ}
    (hη : ∀ w, pairU z w ≤ R → ‖ψ w - ψ z‖ ≤ η) : ‖ppApply φ ψ z - ψ z‖ ≤ η := by
  rw [ppApply_eq_integral_of_seed hφR hRε hε₀ hK hKo hcentral hz]
  have hi1 := integrable_pairKernel_smul hφc hφR hψc z
  have hi2 := integrable_pairKernel_smul hφc hφR (continuous_const (y := ψ z)) z
  have hψz : ψ z = ∫ w, ((φ (pairU z w) : ℝ) : ℂ) • ψ z := by
    rw [integral_smul_const, integral_complex_ofReal, integral_pairKernel_eq_one hφc hφ0 hmass z,
      Complex.ofReal_one, one_smul]
  rw [hψz, ← integral_sub hi1 hi2]
  have hib : Integrable (fun w => φ (pairU z w) * η) :=
    (integrable_pairKernel_real hφc hφR z).mul_const η
  refine (norm_integral_le_of_norm_le hib (Eventually.of_forall fun w => ?_)).trans_eq ?_
  · rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hφ0 _)]
    by_cases hu : pairU z w ≤ R
    · exact mul_le_mul_of_nonneg_left (hη w hu) (hφ0 _)
    · rw [hφR _ (not_le.1 hu), zero_mul, zero_mul]
  · rw [integral_mul_const, integral_pairKernel_eq_one hφc hφ0 hmass z, one_mul]

/-- Away from the seed `L_φ ψ` vanishes. -/
theorem ppApply_seed_eq_zero_of_far (hφR : KernelSupport φ R) (hRε : 8 * R < ε₀ ^ 2)
    (hε₀ : 0 < ε₀) (hK : tsupport ψ ⊆ K) (hKo : Metric.thickening ε₀ K ⊆ fdo)
    (hcentral : seedCentralFixed N ψ) {z : ℍ} (hz : z ∈ fdo)
    (hfar : z ∉ Metric.thickening ε₀ K) : ppApply φ ψ z = 0 := by
  rw [ppApply_eq_integral_of_seed hφR hRε hε₀ hK hKo hcentral hz]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun w => ?_)
  by_cases hψ : ψ w = 0
  · simp [hψ]
  have hwK : w ∈ K := hK (subset_tsupport _ hψ)
  have hu : R < pairU z w := by
    by_contra h
    push Not at h
    exact hfar (Metric.mem_thickening_iff.2 ⟨w, hwK, dist_lt_of_pairU_le hRε hε₀ h⟩)
  simp [hφR _ hu]

/-- **`L²` approximation on an interior seed.** -/
theorem eLpNorm_ppApply_seed_sub_le (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hmass : ppKernelMass φ = 1) (hφR : KernelSupport φ R) (hRε : 8 * R < ε₀ ^ 2)
    (hε₀ : 0 < ε₀) (hψc : Continuous ψ) (hK : tsupport ψ ⊆ K) (hKo : Metric.thickening ε₀ K ⊆ fdo)
    (hcentral : seedCentralFixed N ψ) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ z w, pairU z w ≤ R → ‖ψ w - ψ z‖ ≤ η) :
    eLpNorm (ppApply φ ψ - ψ) 2 cellMeasure ≤
      ENNReal.ofReal η * cellMeasure (Metric.thickening ε₀ K) ^ (1 / (2 : ℝ)) := by
  have hS : MeasurableSet (Metric.thickening ε₀ K) := Metric.isOpen_thickening.measurableSet
  have hbound : ∀ᵐ z ∂cellMeasure,
      ‖(ppApply φ ψ - ψ) z‖ ≤ ‖(Metric.thickening ε₀ K).indicator (fun _ => η) z‖ := by
    filter_upwards [ae_mem_fdo] with z hz
    by_cases hzS : z ∈ Metric.thickening ε₀ K
    · rw [indicator_of_mem hzS, Real.norm_of_nonneg hη0, Pi.sub_apply]
      exact norm_ppApply_seed_sub_le hφc hφ0 hmass hφR hRε hε₀ hψc hK hKo hcentral hz
        fun w hw => hη z w hw
    · rw [indicator_of_notMem hzS, norm_zero, Pi.sub_apply,
        ppApply_seed_eq_zero_of_far hφR hRε hε₀ hK hKo hcentral hz hzS,
        image_eq_zero_of_notMem_tsupport (fun h => hzS (Metric.self_subset_thickening hε₀ K (hK h))),
        sub_zero, norm_zero]
  refine (eLpNorm_mono_ae hbound).trans ?_
  rw [eLpNorm_indicator_const hS (by norm_num) (by norm_num), Real.enorm_eq_ofReal hη0]
  norm_num

end Seed

/-! ## The approximate identity -/

/-- **Approximate identity.** For every central-fixed finite-deck `L²` vector `f` and `ε > 0`
there is a radius below which every nonnegative continuous profile of unit mass satisfies
`‖L_φ f - f‖ ≤ ε`. -/
theorem exists_radius_approxIdentity (f : deckCentralFixedL2 N) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M)
      (hR : 0 ≤ R) (hφR : KernelSupport φ R), (∀ u, 0 ≤ φ u) → ppKernelMass φ = 1 → R ≤ R₀ →
        ‖ppL2 hφc hφM hR hφR (f : DeckL2 N) - (f : DeckL2 N)‖ ≤ ε := by
  obtain ⟨ψ₀, hψ₀, hs₀, hK₀, hlt⟩ :=
    exists_interior_approx_vector N (f : DeckL2 N) (show 0 < ε / 3 by positivity)
  obtain ⟨ψ, hψdef⟩ : ∃ ψ, ψ = centralizeSeed N ψ₀ := ⟨_, rfl⟩
  have hψ : IsChartC1 ψ := hψdef ▸ isChartC1_centralizeSeed hψ₀
  have hs : HasCompactSupport ψ := hψdef ▸ hasCompactSupport_centralizeSeed hs₀
  have hK : tsupport ψ ⊆ fdo := hψdef ▸ (tsupport_centralizeSeed_subset ψ₀).trans hK₀
  have hcentral : seedCentralFixed N ψ := hψdef ▸ seedCentralFixed_centralizeSeed N ψ₀
  have hψL : MemLp ψ 2 cellMeasure := memLp_of_isChartC1_of_hasCompactSupport_vec hψ hs
  have hψc : Continuous ψ := continuous_of_isChartC1 hψ
  have happrox : ‖toDeckL2 ψ hψL - (f : DeckL2 N)‖ ≤ ε / 3 := by
    have h := norm_sub_centralizeL2_le
      (toDeckL2 ψ₀ (memLp_of_isChartC1_of_hasCompactSupport_vec hψ₀ hs₀)) f
    rw [centralizeL2_toDeckL2] at h
    subst hψdef
    exact h.trans (by rw [norm_sub_rev]; exact hlt.le)
  obtain ⟨ε₀, hε₀, hKo⟩ := hs.isCompact.exists_thickening_subset_open isOpen_fdo hK
  have hVfin : cellMeasure (Metric.thickening ε₀ (tsupport ψ)) < ∞ :=
    (Measure.restrict_apply_le _ _).trans_lt
      ((measure_mono (Metric.thickening_subset_cthickening _ _)).trans_lt
        (hs.isCompact.cthickening.measure_lt_top))
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = (cellMeasure (Metric.thickening ε₀ (tsupport ψ))).toReal ^
      (1 / (2 : ℝ)) := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := hVdef ▸ Real.rpow_nonneg ENNReal.toReal_nonneg _
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / 3 / (V + 1) := ⟨_, rfl⟩
  have hη : 0 < η := hηdef ▸ by positivity
  obtain ⟨r, hr, hunif⟩ :=
    Metric.uniformContinuous_iff.1 (hs.uniformContinuous_of_continuous hψc) η hη
  refine ⟨min (ε₀ ^ 2 / 16) (r ^ 2 / 16), by positivity,
    fun {φ} {M} {R} hφc hφM hR hφR hφ0 hmass hRle => ?_⟩
  have hRε : 8 * R < ε₀ ^ 2 := by
    have := hRle.trans (min_le_left _ _); nlinarith [sq_nonneg ε₀]
  have hRr : 8 * R < r ^ 2 := by
    have := hRle.trans (min_le_right _ _); nlinarith [sq_nonneg r]
  have hηb : ∀ z w, pairU z w ≤ R → ‖ψ w - ψ z‖ ≤ η := fun z w h => by
    have := hunif (dist_lt_of_pairU_le hRr hr (by rwa [pairU_comm]))
    rw [dist_eq_norm] at this
    exact this.le
  have hmass' : (ppKernelMass φ).toReal = 1 := by rw [hmass]; rfl
  have hnorm : ∀ g : DeckL2 N, ‖ppL2 hφc hφM hR hφR g‖ ≤ ‖g‖ := fun g => by
    have := norm_ppLinear_le hφc hφM hR hφR g
    rwa [hmass', one_mul] at this
  have hT : ‖ppL2 hφc hφM hR hφR (toDeckL2 ψ hψL) - toDeckL2 ψ hψL‖ ≤ ε / 3 := by
    have happ : ppL2 hφc hφM hR hφR (toDeckL2 ψ hψL) =
        toDeckL2 (ppApply φ ψ) (memLp_ppApply hφc hφM hR hφR hψL) := by
      rw [ppL2_apply]
      exact toDeckL2_congr _ _ (Eventually.of_forall fun z => by
        rw [ppApply_congr_ae φ (show ⇑(toDeckL2 ψ hψL) =ᵐ[cellMeasure] ψ from
          MemLp.coeFn_toLp hψL)])
    rw [happ, toDeckL2, toDeckL2, ← MemLp.toLp_sub, Lp.norm_toLp]
    have hb := eLpNorm_ppApply_seed_sub_le hφc hφ0 hmass hφR hRε hε₀ hψc subset_rfl hKo hcentral
      hη.le hηb
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVfin.ne)) hb).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.le, ← ENNReal.toReal_rpow, ← hVdef, hηdef]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc ‖ppL2 hφc hφM hR hφR (f : DeckL2 N) - (f : DeckL2 N)‖
      = ‖ppL2 hφc hφM hR hφR ((f : DeckL2 N) - toDeckL2 ψ hψL) +
          (ppL2 hφc hφM hR hφR (toDeckL2 ψ hψL) - toDeckL2 ψ hψL) +
          (toDeckL2 ψ hψL - (f : DeckL2 N))‖ := by rw [map_sub]; abel_nf
    _ ≤ ‖(f : DeckL2 N) - toDeckL2 ψ hψL‖ + ε / 3 + ε / 3 := by
        refine (norm_add₃_le).trans (add_le_add (add_le_add (hnorm _) hT) happrox)
    _ ≤ ε := by rw [norm_sub_rev]; linarith

/-! ## Smooth unit profiles -/

theorem ppKernelMass_smul {φ : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    ppKernelMass (fun u => c * φ u) = ENNReal.ofReal c * ppKernelMass φ := by
  unfold ppKernelMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun w => ?_
  rw [abs_mul, abs_of_nonneg hc, ENNReal.ofReal_mul hc]

/-- **Smooth unit profiles exist at every radius**: a nonnegative smooth profile vanishing for
`|u| > R` with `∫_ℍ φ(u(i, w)) dμ(w) = 1`. -/
theorem exists_unitProfile {R : ℝ} (hR : 0 < R) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ (∀ u, 0 ≤ φ u) ∧ (∀ u, R < |u| → φ u = 0) ∧
      ppKernelMass φ = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨R / 2, R, by positivity, by linarith⟩
  have hb0 : ∀ u, 0 ≤ b u := fun u => b.nonneg
  have hbR : ∀ u, R < |u| → b u = 0 := fun u hu => by
    have : u ∉ Function.support b := by
      rw [b.support_eq]
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
      exact hu.le
    simpa using this
  have hbc : Continuous b := b.contDiff (n := 0).continuous
  have hbM : ∀ u, |b u| ≤ 1 := fun u => by
    rw [abs_of_nonneg (hb0 u)]; exact b.le_one
  have hfin : ppKernelMass b < ∞ :=
    kernelMass_lt_top hR.le hbM fun u hu => hbR u (lt_of_lt_of_le hu (le_abs_self u))
  have hpos : ppKernelMass b ≠ 0 := by
    unfold ppKernelMass
    intro h0
    have hopen : IsOpen {w : ℍ | pairU UpperHalfPlane.I w < R / 2} :=
      isOpen_lt (continuous_pairU_right _) continuous_const
    have hne : ({w : ℍ | pairU UpperHalfPlane.I w < R / 2} : Set ℍ).Nonempty :=
      ⟨UpperHalfPlane.I, by simp [pairU]; positivity⟩
    have hvol := hopen.measure_pos (volume : Measure ℍ) hne
    have hle : (volume : Measure ℍ) {w : ℍ | pairU UpperHalfPlane.I w < R / 2} ≤
        ∫⁻ w, ENNReal.ofReal |b (pairU UpperHalfPlane.I w)| := by
      rw [← setLIntegral_one]
      refine (setLIntegral_mono (ENNReal.measurable_ofReal.comp
        (hbc.comp (continuous_pairU_right _)).abs.measurable) fun w hw => ?_).trans
          (setLIntegral_le_lintegral _ _)
      have hw' : pairU UpperHalfPlane.I w ∈ Metric.closedBall (0 : ℝ) (R / 2) := by
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
          abs_of_nonneg (pairU_nonneg _ _)]
        exact le_of_lt hw
      simp only [Function.comp_apply]
      rw [b.one_of_mem_closedBall hw', abs_one, ENNReal.ofReal_one]
    rw [h0] at hle
    exact (hvol.trans_le hle).ne' rfl
  refine ⟨fun u => (ppKernelMass b).toReal⁻¹ * b u, contDiff_const.mul (b.contDiff (n := ⊤)),
    fun u => mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (hb0 u),
    fun u hu => by simp [hbR u hu], ?_⟩
  rw [ppKernelMass_smul (inv_nonneg.2 ENNReal.toReal_nonneg), ENNReal.ofReal_inv_of_pos
    (ENNReal.toReal_pos hpos hfin.ne), ENNReal.ofReal_toReal hfin.ne,
    ENNReal.inv_mul_cancel hpos hfin.ne]

end

end GaloisForLFunctions.RHTower.DeckPointPair
