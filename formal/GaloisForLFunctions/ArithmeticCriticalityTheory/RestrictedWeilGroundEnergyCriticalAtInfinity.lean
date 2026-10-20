import GaloisForLFunctions.ArithmeticCriticalityTheory.ExplicitSmallApertureCCMGroundEnergyFloor

/-!
# Criticality at infinite aperture: the restricted Weil ground energy tends to zero

The restricted Weil operator of Connes–Consani–Moscovici at aperture `A` has ground energy `μ(A)`,
antitone in `A`. The theta span is the radical of the full zero form: for the smooth plateau
truncations `Φ u_L` of Riemann's kernel, `Ẑ(Φ u_L) → 0` while `∫ (Φ u_L)² ≥ 2Φ(1)²`
(`tendsto_fullZeroForm_thetaPlateau`). These are smooth sources supported in `[−L−1, L+1]`, so their
Rayleigh quotients bound `μ` from above at every aperture beyond `L + 1`:

* **Unconditional decay** (`exists_ccmRestrictedWeilGroundEnergy_lt`): for every `ε > 0`,
  `μ(A) < ε` for all large `A`.
* **Nonnegativity from the zero form** (`ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis'`):
  under RH, `Ẑ ≥ 0` on real tests (`riemannHypothesis_iff_forall_fullZeroForm_nonneg`), and the
  quadratic of a complex smooth source is `Ẑ(Re u) + Ẑ(Im u)`, so `μ(A) ≥ 0` at every aperture.
* **The criterion** (`riemannHypothesis_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero`):
  RH ⟺ `μ(A) → 0` as `A → ∞`. Without RH some `μ(B) < 0` and antitonicity keeps `μ ≤ μ(B)` beyond.

So RH is equivalent to the restricted Weil operators being asymptotically critical: their ground
energies decrease to the critical value `0` without crossing it, the CCM image of the absence of a
Hardy weight for the zero form.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

theorem fullZeroForm_zero : fullZeroForm (fun _ => 0) = 0 := by
  rw [GaloisForLFunctions.ArithmeticPositivityTheory.fullZeroForm_eq_re_weilFullFunctional
    (F := fun _ : ℝ => (0 : ℝ)) continuous_const HasCompactSupport.zero]
  simp [EF.weilTest, weilFullFunctional, paperFT, convolution]

/-- The interval embedding preserves the aperture norm. -/
theorem norm_suzukiWeilIntervalFormEmbedding {A : SuzukiPositiveAperture}
    (u : CCMArchimedeanFormDomain A) :
    ‖suzukiWeilIntervalFormEmbedding A u‖ = ‖ccmArchimedeanFormToAperture A u‖ := by
  change ‖suzukiPhysicalToApertureCLM A (ccmArchimedeanFormToAperture A u)‖ = _
  exact (suzukiApertureL2Equiv A).symm.norm_map _

/-! ### The plateau truncations of `Φ` -/

/-- The plateau truncation `Φ u_L` of Riemann's kernel. -/
def thetaPlateau (L x : ℝ) : ℝ := riemannKernelReal x * smoothPlateau L x

theorem contDiff_thetaPlateau (L : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (thetaPlateau L) := by
  unfold thetaPlateau smoothPlateau
  exact contDiff_riemannKernelReal.mul
    ((Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.add contDiff_id)))

theorem hasCompactSupport_thetaPlateau (L : ℝ) : HasCompactSupport (thetaPlateau L) :=
  (hasCompactSupport_smoothPlateau L).mul_left

theorem tsupport_thetaPlateau_subset (L : ℝ) :
    tsupport (thetaPlateau L) ⊆ Icc (-(L + 1)) (L + 1) :=
  closure_minimal (fun x hx => abs_le.mp (not_lt.mp fun h => hx (by
    show riemannKernelReal x * smoothPlateau L x = 0
    rw [smoothPlateau_eq_zero h.le, mul_zero]))) isClosed_Icc

/-- **The radical along `Φ`**: `Ẑ(Φ u_L) → 0`. -/
theorem tendsto_fullZeroForm_thetaPlateau :
    Tendsto (fun L => fullZeroForm (thetaPlateau L)) atTop (𝓝 0) := by
  have h := tendsto_fullZeroForm_add_translatePlateau (Finset.univ : Finset Unit) (fun _ => 1)
    (fun _ => 0) (v := fun _ => 0) contDiff_const HasCompactSupport.zero
  have h0 : phiDoobTest (fun _ => (0 : ℝ)) = fun _ => 0 := funext fun x => by simp [phiDoobTest]
  rw [h0, fullZeroForm_zero] at h
  refine h.congr fun L => congrArg fullZeroForm (funext fun x => ?_)
  simp [phiDoobTest, translateSpan, translateGroundState, thetaPlateau,
    (riemannKernelReal_pos x).ne']

theorem two_mul_sq_riemannKernelReal_one_le {L : ℝ} (hL : 1 ≤ L) :
    2 * riemannKernelReal 1 ^ 2 ≤ ∫ x, thetaPlateau L x ^ 2 := by
  have hint : Integrable fun x => thetaPlateau L x ^ 2 :=
    ((contDiff_thetaPlateau L).continuous.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_sq (hasCompactSupport_thetaPlateau L))
  have hlow : ∀ x ∈ Icc (-1 : ℝ) 1, riemannKernelReal 1 ^ 2 ≤ thetaPlateau L x ^ 2 := fun x hx => by
    have habs : |x| ≤ 1 := abs_le.mpr hx
    show riemannKernelReal 1 ^ 2 ≤ (riemannKernelReal x * smoothPlateau L x) ^ 2
    rw [smoothPlateau_eq_one (habs.trans hL), mul_one, ← riemannKernelReal_abs' x]
    exact pow_le_pow_left₀ (riemannKernelReal_pos 1).le
      (riemannKernelReal_antitone_of_nonneg (abs_nonneg x) habs) 2
  calc 2 * riemannKernelReal 1 ^ 2 = ∫ _ in Icc (-1 : ℝ) 1, riemannKernelReal 1 ^ 2 := by
        rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul]
        norm_num
    _ ≤ ∫ x in Icc (-1 : ℝ) 1, thetaPlateau L x ^ 2 :=
        setIntegral_mono_on continuous_const.integrableOn_Icc hint.integrableOn measurableSet_Icc hlow
    _ ≤ ∫ x, thetaPlateau L x ^ 2 :=
        setIntegral_le_integral hint (Eventually.of_forall fun _ => sq_nonneg _)

/-! ### The ground energy at large aperture -/

/-- **Unconditional decay**: `μ(A) < ε` for all large apertures. -/
theorem exists_ccmRestrictedWeilGroundEnergy_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ A₀ : ℝ, ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 → ccmRestrictedWeilGroundEnergy A < ε := by
  have hc : 0 < 2 * riemannKernelReal 1 ^ 2 := by have := riemannKernelReal_pos 1; positivity
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp
    (tendsto_fullZeroForm_thetaPlateau.eventually (gt_mem_nhds (mul_pos hε hc)))
  obtain ⟨L, hL⟩ : ∃ L, L = max L₁ 1 := ⟨_, rfl⟩
  have hZ : fullZeroForm (thetaPlateau L) < ε * (2 * riemannKernelReal 1 ^ 2) :=
    hL₁ L (hL ▸ le_max_left _ _)
  have hm := two_mul_sq_riemannKernelReal_one_le (hL ▸ le_max_right L₁ 1 : 1 ≤ L)
  refine ⟨L + 2, fun A hA => ?_⟩
  have hs : tsupport (thetaPlateau L) ⊆ Ioo (-A.1) A.1 :=
    (tsupport_thetaPlateau_subset L).trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hQ := ccmRestrictedWeilSourceQuadratic_realInteriorSource A (contDiff_thetaPlateau L)
    (hasCompactSupport_thetaPlateau L) hs
  have hN := norm_sq_realInteriorSource A (contDiff_thetaPlateau L)
    (hasCompactSupport_thetaPlateau L) hs
  obtain ⟨u, hu⟩ : ∃ u, u = realInteriorSource A (contDiff_thetaPlateau L)
    (hasCompactSupport_thetaPlateau L) hs := ⟨_, rfl⟩
  rw [← hu] at hQ hN
  have hmass : suzukiWeilIntervalFormMass A u.toCCMFormVector = ∫ x, thetaPlateau L x ^ 2 := by
    unfold suzukiWeilIntervalFormMass
    rw [norm_suzukiWeilIntervalFormEmbedding, hN]
  have hne : suzukiWeilIntervalFormEmbedding A u.toCCMFormVector ≠ 0 := fun h0 => by
    have : suzukiWeilIntervalFormMass A u.toCCMFormVector = 0 := by
      unfold suzukiWeilIntervalFormMass; rw [h0, norm_zero]; ring
    linarith
  have hglb := (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).1 ⟨u, hne, rfl⟩
  rw [suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy] at hglb
  unfold suzukiWeilIntervalFormRayleigh at hglb
  rw [hQ, hmass] at hglb
  refine lt_of_le_of_lt hglb ?_
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- Under RH every restricted Weil ground energy is nonnegative: the zero-form criterion applied to
the real and imaginary parts of each smooth source. -/
theorem ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' (hRH : RiemannHypothesis)
    (A : SuzukiPositiveAperture) : 0 ≤ ccmRestrictedWeilGroundEnergy A := by
  have hZ : ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → 0 ≤ fullZeroForm G :=
    fun G hG hGc => by
      have h := riemannHypothesis_iff_forall_fullZeroForm_nonneg.mp hRH
        (fun x => G x / riemannKernelReal x)
        (hG.div contDiff_riemannKernelReal fun x => (riemannKernelReal_pos x).ne')
        (hGc.mono' fun x hx => subset_tsupport G fun h0 => hx (by simp [h0]))
      have e : phiDoobTest (fun x => G x / riemannKernelReal x) = G := funext fun x => by
        unfold phiDoobTest
        field_simp [(riemannKernelReal_pos x).ne']
      rwa [e] at h
  rw [← suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  refine (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).2 ?_
  rintro r ⟨u, -, rfl⟩
  unfold suzukiWeilIntervalFormRayleigh suzukiWeilIntervalFormMass
  refine div_nonneg ?_ (sq_nonneg _)
  have hu2 : ContDiff ℝ 2 (u : ℝ → ℂ) := u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil,
    GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im hu2
      u.hasCompactSupport]
  exact add_nonneg (hZ _ (Complex.reCLM.contDiff.comp hu2)
      (u.hasCompactSupport.comp_left Complex.zero_re))
    (hZ _ (Complex.imCLM.contDiff.comp hu2) (u.hasCompactSupport.comp_left Complex.zero_im))

/-- **RH ⟺ the restricted Weil ground energy tends to zero at infinite aperture.** -/
theorem riemannHypothesis_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero :
    RiemannHypothesis ↔ ∀ ε > 0, ∃ A₀ : ℝ, ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      |ccmRestrictedWeilGroundEnergy A| < ε := by
  constructor
  · intro hRH ε hε
    obtain ⟨A₀, hA₀⟩ := exists_ccmRestrictedWeilGroundEnergy_lt hε
    refine ⟨A₀, fun A hA => abs_lt.mpr ⟨?_, hA₀ A hA⟩⟩
    linarith [ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH A]
  · intro h
    by_contra hRH
    obtain ⟨B, hB⟩ := exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis hRH
    obtain ⟨A₀, hA₀⟩ := h _ (neg_pos.mpr hB)
    let A : SuzukiPositiveAperture := ⟨max A₀ B.1, lt_of_lt_of_le B.2 (le_max_right _ _)⟩
    have h1 := abs_lt.mp (hA₀ A (le_max_left _ _))
    have h2 := ccmRestrictedWeilGroundEnergy_antitone (a := B) (b := A) (le_max_right A₀ B.1)
    linarith [h1.1]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
