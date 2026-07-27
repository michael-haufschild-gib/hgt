import GaloisForLFunctions.HTGeometry.DigammaGammaFactorialBlowUp

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

def rightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

theorem isOpen_rightHalfPlane : IsOpen rightHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_re

def gammaFactorialMicroscopeDomain : Set ℂ := {x : ℂ | x.re < 0}

theorem isOpen_gammaFactorialMicroscopeDomain : IsOpen gammaFactorialMicroscopeDomain := by
  exact isOpen_lt Complex.continuous_re continuous_const

theorem gammaFactorialMicroscopeDomain_ne_zero {x : ℂ}
    (hx : x ∈ gammaFactorialMicroscopeDomain) : x ≠ 0 := by
  intro hzero
  subst x
  simp [gammaFactorialMicroscopeDomain] at hx

theorem gammaFactorialMicroscopeDomain_inv_neg_re_pos {x : ℂ}
    (hx : x ∈ gammaFactorialMicroscopeDomain) : 0 < ((-x)⁻¹ : ℂ).re := by
  have hnegRe : 0 < (-x).re := by
    change x.re < 0 at hx
    simp only [Complex.neg_re]
    linarith
  rw [Complex.inv_re]
  exact div_pos hnegRe
    (Complex.normSq_pos.mpr
      (neg_ne_zero.mpr (gammaFactorialMicroscopeDomain_ne_zero hx)))

def outerReciprocalLimit (u : ℂ → ℂ) (x : ℂ) : ℂ :=
  u ((-x)⁻¹)

def LocallyPolynomialJetRigidAt (u : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∀ (r : ℕ) (G : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)), G ≠ 0 →
    ¬ ∀ᶠ z : ℂ in 𝓝 z₀,
      MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) u z) G = 0

theorem tendsto_outer_Gamma_factorialBlowUp_locallyUniformlyOn
    (u : ℂ → ℂ) (hu : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ u z) :
    TendstoLocallyUniformlyOn
      (fun (n : ℕ) (x : ℂ) => u
        (Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * x)))
      (outerReciprocalLimit u) atTop gammaFactorialMicroscopeDomain := by
  have hGamma := tendsto_Gamma_factorialBlowUp_locallyUniformlyOn_ne_zero.mono
    (fun x hx => gammaFactorialMicroscopeDomain_ne_zero hx)
  have hlimit : ContinuousOn (fun x : ℂ => (-x)⁻¹) gammaFactorialMicroscopeDomain :=
    continuous_neg.continuousOn.inv₀
      (fun x hx => neg_ne_zero.mpr (gammaFactorialMicroscopeDomain_ne_zero hx))
  apply continuousAt_comp_tendstoLocallyUniformlyOn _ hlimit hGamma
  intro x hx
  exact (hu ((-x)⁻¹) (gammaFactorialMicroscopeDomain_inv_neg_re_pos hx)).continuousAt

theorem exists_eventually_differentiable_outerGammaZoom_near
    (u : ℂ → ℂ) (hu : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ u z)
    {x : ℂ} (hx : x ∈ gammaFactorialMicroscopeDomain) :
    ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ V ⊆ gammaFactorialMicroscopeDomain ∧
      ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ
        (factorialBlowUpZoom (fun z => u (Complex.Gamma z)) n) V := by
  let limit : ℂ → ℂ := fun y => (-y)⁻¹
  have hx0 := gammaFactorialMicroscopeDomain_ne_zero hx
  have hlimitAt : ContinuousAt limit x :=
    continuousAt_neg.inv₀ (neg_ne_zero.mpr hx0)
  have hxpos : 0 < (limit x).re := gammaFactorialMicroscopeDomain_inv_neg_re_pos hx
  let ε : ℝ := (limit x).re / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  rw [Metric.continuousAt_iff] at hlimitAt
  obtain ⟨δ, hδ, hlimitMap⟩ := hlimitAt ε hε
  have hGammaOn : TendstoLocallyUniformlyOn
      (fun (n : ℕ) (y : ℂ) =>
        Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * y))
      limit atTop gammaFactorialMicroscopeDomain :=
    tendsto_Gamma_factorialBlowUp_locallyUniformlyOn_ne_zero.mono
      (fun y hy => gammaFactorialMicroscopeDomain_ne_zero hy)
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hGammaOn
  obtain ⟨t, ht, hGt⟩ := hGammaOn ε hε x hx
  rw [isOpen_gammaFactorialMicroscopeDomain.nhdsWithin_eq hx] at ht
  have hnbhd : t ∩ Metric.ball x δ ∩ gammaFactorialMicroscopeDomain ∈ 𝓝 x :=
    inter_mem (inter_mem ht (Metric.ball_mem_nhds x hδ))
      (isOpen_gammaFactorialMicroscopeDomain.mem_nhds hx)
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hnbhd
  refine ⟨V, hVopen, hxV, fun y hy => (hVsub hy).2, ?_⟩
  filter_upwards [hGt] with n hn
  intro y hy
  have hyall := hVsub hy
  have hyt : y ∈ t := hyall.1.1
  have hyball : y ∈ Metric.ball x δ := hyall.1.2
  let input : ℂ := -(n : ℂ) + reciprocalGammaFactorialScale n * y
  let gammaValue : ℂ := Complex.Gamma input
  have hcloseGamma : dist (limit y) gammaValue < ε := hn y hyt
  have hcloseLimit : dist (limit y) (limit x) < ε := hlimitMap hyball
  have hreGammaLimit :
      |gammaValue.re - (limit y).re| ≤ dist (limit y) gammaValue := by
    rw [Complex.dist_eq, norm_sub_rev]
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (gammaValue - limit y)
  have hreLimit : |(limit y).re - (limit x).re| ≤ dist (limit y) (limit x) := by
    rw [Complex.dist_eq]
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (limit y - limit x)
  have hgammaRe : 0 < gammaValue.re := by
    have h1 : (limit y).re - ε < gammaValue.re := by
      linarith [neg_le_of_abs_le hreGammaLimit]
    have h2 : (limit x).re - ε < (limit y).re := by
      linarith [neg_le_of_abs_le hreLimit]
    dsimp [ε] at h1 h2 ⊢
    linarith
  have hinputRegular : ∀ m : ℕ, input ≠ -(m : ℂ) := by
    intro m heq
    have hzero : gammaValue = 0 := by
      simp [gammaValue, input, heq, Complex.Gamma_neg_nat_eq_zero]
    rw [hzero] at hgammaRe
    simp at hgammaRe
  have hinputDiff : DifferentiableAt ℂ (fun z : ℂ =>
      -(n : ℂ) + reciprocalGammaFactorialScale n * z) y := by fun_prop
  have hGammaDiff : DifferentiableAt ℂ (fun z : ℂ =>
      Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * z)) y :=
    (Complex.differentiableAt_Gamma input hinputRegular).comp y hinputDiff
  have huDiff : DifferentiableAt ℂ u gammaValue :=
    (hu gammaValue hgammaRe).differentiableAt
  have hcomp := huDiff.comp y hGammaDiff
  simpa [factorialBlowUpZoom, input, gammaValue, Function.comp_def] using
    hcomp.differentiableWithinAt

theorem iteratedDeriv_outerGamma_factorialBlowUp_tendsto
    (u : ℂ → ℂ) (hu : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ u z)
    {x : ℂ} (hx : x ∈ gammaFactorialMicroscopeDomain) (j : ℕ) :
    Tendsto
      (fun n => iteratedDeriv j
        (factorialBlowUpZoom (fun z => u (Complex.Gamma z)) n) x)
      atTop (𝓝 (iteratedDeriv j (outerReciprocalLimit u) x)) := by
  obtain ⟨V, hVopen, hxV, hVU, hdiff⟩ :=
    exists_eventually_differentiable_outerGammaZoom_near u hu hx
  have hconv := (tendsto_outer_Gamma_factorialBlowUp_locallyUniformlyOn u hu).mono hVU
  exact iteratedDeriv_tendsto_of_locallyUniform hVopen hconv hdiff j hxV

theorem exists_local_autonomous_annihilator_outerReciprocalLimit
    (u : ℂ → ℂ) (hu : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ u z)
    (hDA : DifferentiallyAlgebraic (fun z => u (Complex.Gamma z))) :
    ∃ r : ℕ, ∃ Q : MvPolynomial (Fin (r + 1)) ℂ,
      Q ≠ 0 ∧ ∀ x ∈ gammaFactorialMicroscopeDomain,
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) (outerReciprocalLimit u) x) Q = 0 := by
  exact exists_nonzero_factorialInitialForm_of_differentiallyAlgebraic hDA
    (fun x hx j => iteratedDeriv_outerGamma_factorialBlowUp_tendsto u hu hx j)

theorem analyticAt_outerReciprocalLimit_neg_inv
    (u : ℂ → ℂ) {z : ℂ} (hu : AnalyticAt ℂ u z) (hz0 : z ≠ 0) :
    AnalyticAt ℂ (outerReciprocalLimit u) (-z⁻¹) := by
  have hx0 : -z⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz0)
  have hinner : AnalyticAt ℂ (fun x : ℂ => (-x)⁻¹) (-z⁻¹) :=
    analyticAt_id.neg.inv (neg_ne_zero.mpr hx0)
  have hu' : AnalyticAt ℂ u ((-(-z⁻¹))⁻¹) := by
    rw [neg_inv_neg_inv (z := z) hz0]
    exact hu
  have hcomp := AnalyticAt.comp (f := fun x : ℂ => (-x)⁻¹) (x := -z⁻¹) hu' hinner
  change AnalyticAt ℂ (fun x : ℂ => u ((-x)⁻¹)) (-z⁻¹)
  simpa only [Function.comp_def] using hcomp

/-- **Jets of the reciprocal outer limit are the Möbius jet expansion.**  On any open set of
analyticity, the `j`-th derivative of `outerReciprocalLimit u` at `-z⁻¹` is `mobiusJetExpansion u j`
at `z`.  Induction on `j`: the chain rule through `w ↦ -w⁻¹` turns the derivative of the left side
into the next jet times `z⁻²`, `hasDerivAt_mobiusJetExpansion` does the same on the right, and the
induction hypothesis makes the two functions agree near `z`, so their derivatives agree. -/
theorem iteratedDeriv_outerReciprocalLimit_neg_inv_eq_mobiusJetExpansion_local
    {u : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hu : ∀ z ∈ Ω, AnalyticAt ℂ u z) :
    ∀ (j : ℕ) (z : ℂ), z ∈ Ω → z ≠ 0 →
      iteratedDeriv j (outerReciprocalLimit u) (-z⁻¹) =
        mobiusJetExpansion u j z := by
  intro j
  induction j with
  | zero =>
      intro z hz hz0
      simp [mobiusJetExpansion, mobiusJetCoeff, iteratedDeriv_zero,
        outerReciprocalLimit]
  | succ j ih =>
      intro z hz hz0
      let x : ℂ := -z⁻¹
      have hFan : AnalyticAt ℂ (outerReciprocalLimit u) x := by
        simpa [x] using analyticAt_outerReciprocalLimit_neg_inv u (hu z hz) hz0
      have hFj : AnalyticAt ℂ (iteratedDeriv j (outerReciprocalLimit u)) x :=
        analyticAt_iteratedDeriv_of_analyticAt hFan j
      have hFderiv : HasDerivAt (iteratedDeriv j (outerReciprocalLimit u))
          (iteratedDeriv (j + 1) (outerReciprocalLimit u) x) x := by
        simpa [iteratedDeriv_succ] using hFj.differentiableAt.hasDerivAt
      have hphi : HasDerivAt (fun w : ℂ => -w⁻¹) (z⁻¹ ^ 2) z := by
        simpa [inv_pow] using (hasDerivAt_inv hz0).neg
      have hcomp : HasDerivAt
          (fun w : ℂ => iteratedDeriv j (outerReciprocalLimit u) (-w⁻¹))
          (iteratedDeriv (j + 1) (outerReciprocalLimit u) x * z⁻¹ ^ 2) z := by
        simpa [x, Function.comp_def] using hFderiv.comp z hphi
      have hexp : HasDerivAt (mobiusJetExpansion u j)
          (z⁻¹ ^ 2 * mobiusJetExpansion u (j + 1) z) z :=
        hasDerivAt_mobiusJetExpansion hu hz hz0 j
      have hzeroNhd : {w : ℂ | w ≠ 0} ∈ 𝓝 z :=
        isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hz0)
      have hev :
          (fun w : ℂ => iteratedDeriv j (outerReciprocalLimit u) (-w⁻¹)) =ᶠ[𝓝 z]
            mobiusJetExpansion u j := by
        filter_upwards [hΩ.mem_nhds hz, hzeroNhd] with w hwΩ hw0
        exact ih w hwΩ hw0
      have heqderiv :
          iteratedDeriv (j + 1) (outerReciprocalLimit u) x * z⁻¹ ^ 2 =
            z⁻¹ ^ 2 * mobiusJetExpansion u (j + 1) z := by
        calc
          _ = deriv
              (fun w : ℂ => iteratedDeriv j (outerReciprocalLimit u) (-w⁻¹)) z :=
                hcomp.deriv.symm
          _ = deriv (mobiusJetExpansion u j) z := hev.deriv_eq
          _ = _ := hexp.deriv
      have hzInv2 : z⁻¹ ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero hz0)
      have hcancel :
          z⁻¹ ^ 2 * iteratedDeriv (j + 1) (outerReciprocalLimit u) x =
            z⁻¹ ^ 2 * mobiusJetExpansion u (j + 1) z := by
        simpa [mul_comm] using heqderiv
      have hfinal := mul_left_cancel₀ hzInv2 hcancel
      simpa [x] using hfinal

theorem iteratedDeriv_outerReciprocalLimit_neg_inv_eq_mobiusJetExpansion
    (u : ℂ → ℂ) (hu : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ u z) :
    ∀ (j : ℕ) (z : ℂ), z ∈ rightHalfPlane →
      iteratedDeriv j (outerReciprocalLimit u) (-z⁻¹) = mobiusJetExpansion u j z := by
  intro j z hz
  refine iteratedDeriv_outerReciprocalLimit_neg_inv_eq_mobiusJetExpansion_local
    isOpen_rightHalfPlane hu j z hz ?_
  intro hzero
  subst hzero
  simp [rightHalfPlane] at hz

theorem mobiusJetValue_outer_eq_limitJet
    (u : ℂ → ℂ) (hu : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ u z)
    (r : ℕ) (z : ℂ) (hz : z ∈ rightHalfPlane) (j : Fin (r + 1)) :
    mobiusJetValue r u z j =
      iteratedDeriv (j : ℕ) (outerReciprocalLimit u) (-z⁻¹) := by
  rw [mobiusJetValue_eq_mobiusJetExpansion]
  exact (iteratedDeriv_outerReciprocalLimit_neg_inv_eq_mobiusJetExpansion
    u hu (j : ℕ) z hz).symm

theorem neg_inv_mem_gammaFactorialMicroscopeDomain_of_mem_rightHalfPlane
    {z : ℂ} (hz : z ∈ rightHalfPlane) :
    -z⁻¹ ∈ gammaFactorialMicroscopeDomain := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp [rightHalfPlane] at hz
  change 0 < z.re at hz
  change (-z⁻¹).re < 0
  rw [Complex.neg_re, Complex.inv_re]
  exact neg_lt_zero.mpr (div_pos hz (Complex.normSq_pos.mpr hz0))

theorem exists_polynomialJet_relation_on_rightHalfPlane_of_differentiallyAlgebraic_outer_comp_Gamma
    (u : ℂ → ℂ) (hu : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ u z)
    (hDA : DifferentiallyAlgebraic (fun z => u (Complex.Gamma z))) :
    ∃ r : ℕ, ∃ G : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
      G ≠ 0 ∧ ∀ z ∈ rightHalfPlane,
        MvPolynomial.eval₂ (Polynomial.evalRingHom z)
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) u z) G = 0 := by
  obtain ⟨r, Q, hQ, hQvan⟩ :=
    exists_local_autonomous_annihilator_outerReciprocalLimit u hu hDA
  let G : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := mobiusJetPullback r Q
  have hGne : G ≠ 0 := mobiusJetPullback_ne_zero hQ
  refine ⟨r, G, hGne, ?_⟩
  intro z hz
  have hx : -z⁻¹ ∈ gammaFactorialMicroscopeDomain :=
    neg_inv_mem_gammaFactorialMicroscopeDomain_of_mem_rightHalfPlane hz
  have hvalue := hQvan (-z⁻¹) hx
  have hmv : mobiusJetValue r u z =
      fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) (outerReciprocalLimit u) (-z⁻¹) := by
    funext j
    exact mobiusJetValue_outer_eq_limitJet u hu r z hz j
  rw [show G = mobiusJetPullback r Q from rfl, eval₂_mobiusJetPullback, hmv]
  exact hvalue

theorem hypertranscendental_outer_comp_Gamma
    (u : ℂ → ℂ) (hu : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ u z)
    (hrigid : LocallyPolynomialJetRigidAt u 1) :
    Hypertranscendental (fun z => u (Complex.Gamma z)) := by
  intro hDA
  obtain ⟨r, G, hG, hrel⟩ :=
    exists_polynomialJet_relation_on_rightHalfPlane_of_differentiallyAlgebraic_outer_comp_Gamma
      u hu hDA
  apply (hrigid r G hG)
  have honePos : (1 : ℂ) ∈ rightHalfPlane := by simp [rightHalfPlane]
  filter_upwards [isOpen_rightHalfPlane.mem_nhds honePos] with z hz
  exact hrel z hz

theorem analyticAt_digamma_on_rightHalfPlane
    (z : ℂ) (hz : z ∈ rightHalfPlane) : AnalyticAt ℂ Complex.digamma z := by
  apply analyticAt_digamma_of_offPoles
  intro p hp
  have hre := congrArg Complex.re hp
  change 0 < z.re at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hpnonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  linarith

theorem locallyPolynomialJetRigidAt_digamma :
    LocallyPolynomialJetRigidAt Complex.digamma 1 := by
  intro r G hG hlocal
  apply hG
  have honeOff : ∀ p : ℕ, (1 : ℂ) ≠ -(p : ℂ) := by
    intro p hp
    have hre := congrArg Complex.re hp
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have hpnonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    linarith
  apply polyJetEval_eq_zero_of_eventually G honeOff
  simpa [polyJetEval, digammaJet] using hlocal

theorem hypertranscendental_digamma_comp_Gamma_via_factorialComposition :
    Hypertranscendental (fun z => Complex.digamma (Complex.Gamma z)) := by
  exact hypertranscendental_outer_comp_Gamma Complex.digamma
    analyticAt_digamma_on_rightHalfPlane locallyPolynomialJetRigidAt_digamma

end

end GaloisForLFunctions
