import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedPtolemyTransport
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionSixthGlobal
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedFourPointOddParityCusp
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxSourceWeld

/-!
# Local cusp and stationary flux law for one reflected theta-source fibre

The global strict second--sixth curvature of the completed theta source opens the
reflection-odd four-point wall on every literal source fibre, not only after center mixing.
At the opposite end, superexponential source decay makes the same wall converge to the square
of its central fibre value.  Hence any negative fibre wall is forced into a strictly interior
stationary point.  Its derivative is an exact three-scale balance of the positive reflected
decay flux.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- Every reflected completed-source fibre is smooth to all orders. -/
theorem contDiff_thetaCuspReflectedSourceProduct (u : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (thetaCuspReflectedSourceProduct u) := by
  have hplus : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ => u + t) :=
    contDiff_const.add contDiff_id
  have hminus : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ => u - t) :=
    contDiff_const.sub contDiff_id
  unfold thetaCuspReflectedSourceProduct
  simpa only [Function.comp_apply] using
    (contDiff_thetaCuspFullSource.comp hplus).mul
      (contDiff_thetaCuspFullSource.comp hminus)

/-- Leibniz--reflection formula for every coalesced fibre jet. -/
theorem iteratedDeriv_thetaCuspReflectedSourceProduct_zero
    (n : ℕ) (u : ℝ) :
    iteratedDeriv n (thetaCuspReflectedSourceProduct u) 0 =
      ∑ i ∈ Finset.range (n + 1),
        n.choose i * iteratedDeriv i thetaCuspFullSource u *
          ((-1 : ℝ) ^ (n - i) *
            iteratedDeriv (n - i) thetaCuspFullSource u) := by
  let p : ℝ → ℝ := fun t => thetaCuspFullSource (u + t)
  let m : ℝ → ℝ := fun t => thetaCuspFullSource (u - t)
  have hplusSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) p := by
    change ContDiff ℝ (↑(⊤ : ℕ∞))
      (thetaCuspFullSource ∘ fun t : ℝ => u + t)
    exact contDiff_thetaCuspFullSource.comp (contDiff_const.add contDiff_id)
  have hminusSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) m := by
    change ContDiff ℝ (↑(⊤ : ℕ∞))
      (thetaCuspFullSource ∘ fun t : ℝ => u - t)
    exact contDiff_thetaCuspFullSource.comp (contDiff_const.sub contDiff_id)
  have hp : ContDiffAt ℝ n p 0 :=
    hplusSmooth.contDiffAt.of_le (by exact_mod_cast le_top)
  have hm : ContDiffAt ℝ n m 0 :=
    hminusSmooth.contDiffAt.of_le (by exact_mod_cast le_top)
  have hplus (i : ℕ) :
      iteratedDeriv i p 0 = iteratedDeriv i thetaCuspFullSource u := by
    dsimp only [p]
    rw [show (fun t : ℝ => thetaCuspFullSource (u + t)) =
        fun t : ℝ => thetaCuspFullSource (u + t) by rfl,
      iteratedDeriv_comp_const_add]
    simp
  have hminus (i : ℕ) :
      iteratedDeriv i m 0 =
        (-1 : ℝ) ^ i * iteratedDeriv i thetaCuspFullSource u := by
    dsimp only [m]
    rw [iteratedDeriv_comp_const_sub]
    simp [smul_eq_mul]
  change iteratedDeriv n (p * m) 0 = _
  rw [iteratedDeriv_mul hp hm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hplus, hminus]

/-- Reflected fibres are even in displacement. -/
theorem thetaCuspReflectedSourceProduct_even (u : ℝ) :
    Function.Even (thetaCuspReflectedSourceProduct u) := by
  intro t
  unfold thetaCuspReflectedSourceProduct
  rw [show u + -t = u - t by ring, show u - -t = u + t by ring]
  ring

private theorem iteratedDeriv_two_thetaCuspReflectedSourceProduct_zero (u : ℝ) :
    iteratedDeriv 2 (thetaCuspReflectedSourceProduct u) 0 =
      HilbertMetric.reflectedProductSecondJet
        (iteratedDeriv 0 thetaCuspFullSource u)
        (iteratedDeriv 1 thetaCuspFullSource u)
        (iteratedDeriv 2 thetaCuspFullSource u) := by
  rw [iteratedDeriv_thetaCuspReflectedSourceProduct_zero]
  simp [Finset.sum_range_succ, HilbertMetric.reflectedProductSecondJet]
  ring

private theorem iteratedDeriv_four_thetaCuspReflectedSourceProduct_zero (u : ℝ) :
    iteratedDeriv 4 (thetaCuspReflectedSourceProduct u) 0 =
      HilbertMetric.reflectedProductFourthJet
        (iteratedDeriv 0 thetaCuspFullSource u)
        (iteratedDeriv 1 thetaCuspFullSource u)
        (iteratedDeriv 2 thetaCuspFullSource u)
        (iteratedDeriv 3 thetaCuspFullSource u)
        (iteratedDeriv 4 thetaCuspFullSource u) := by
  rw [iteratedDeriv_thetaCuspReflectedSourceProduct_zero]
  simp [Finset.sum_range_succ, HilbertMetric.reflectedProductFourthJet]
  norm_num [Nat.choose]
  ring

private theorem iteratedDeriv_six_thetaCuspReflectedSourceProduct_zero (u : ℝ) :
    iteratedDeriv 6 (thetaCuspReflectedSourceProduct u) 0 =
      HilbertMetric.reflectedProductSixthJet
        (iteratedDeriv 0 thetaCuspFullSource u)
        (iteratedDeriv 1 thetaCuspFullSource u)
        (iteratedDeriv 2 thetaCuspFullSource u)
        (iteratedDeriv 3 thetaCuspFullSource u)
        (iteratedDeriv 4 thetaCuspFullSource u)
        (iteratedDeriv 5 thetaCuspFullSource u)
        (iteratedDeriv 6 thetaCuspFullSource u) := by
  rw [iteratedDeriv_thetaCuspReflectedSourceProduct_zero]
  simp [Finset.sum_range_succ, HilbertMetric.reflectedProductSixthJet]
  norm_num [Nat.choose]
  ring

/-- The coalesced second--sixth determinant of a literal reflected fibre is exactly the global
completed-source curvature at its center. -/
theorem thetaCuspReflectedSourceProduct_secondSixthHankel_zero (u : ℝ) :
    iteratedDeriv 2 (thetaCuspReflectedSourceProduct u) 0 *
          iteratedDeriv 6 (thetaCuspReflectedSourceProduct u) 0 -
        iteratedDeriv 4 (thetaCuspReflectedSourceProduct u) 0 ^ (2 : ℕ) =
      thetaCuspFullSourceReflectionSecondSixthCurvature u := by
  rw [iteratedDeriv_two_thetaCuspReflectedSourceProduct_zero,
    iteratedDeriv_four_thetaCuspReflectedSourceProduct_zero,
    iteratedDeriv_six_thetaCuspReflectedSourceProduct_zero]
  rfl

/-- **Unconditional source-fibre cusp.** Every literal reflected completed-source fibre has a
strictly positive odd four-point wall at all sufficiently small positive separations. -/
theorem exists_thetaCuspReflectedSourceOddParityWall_pos_right (u : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      0 < thetaCuspReflectedSourceOddParityWall u t := by
  let f : ℝ → ℝ := thetaCuspReflectedSourceProduct u
  have hf : ContDiff ℝ 8 f :=
    (contDiff_thetaCuspReflectedSourceProduct u).of_le
      (by
        exact WithTop.coe_le_coe.mpr le_top)
  have heven : Function.Even f := thetaCuspReflectedSourceProduct_even u
  have h1 : iteratedDeriv 1 f 0 = 0 :=
    iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h3 : iteratedDeriv 3 f 0 = 0 :=
    iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h5 : iteratedDeriv 5 f 0 = 0 :=
    iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h7 : iteratedDeriv 7 f 0 = 0 :=
    iteratedDeriv_zero_of_even_real_of_odd heven (by norm_num)
  have h6 : 0 < iteratedDeriv 2 f 0 * iteratedDeriv 6 f 0 -
      iteratedDeriv 4 f 0 ^ (2 : ℕ) := by
    rw [thetaCuspReflectedSourceProduct_secondSixthHankel_zero]
    exact thetaCuspFullSourceReflectionSecondSixthCurvature_pos u
  rcases HilbertMetric.exists_fourPointOddWall_pos_right hf h1 h3 h5 h7 h6 with
    ⟨delta, hdelta, hwall⟩
  refine ⟨delta, hdelta, fun t ht htdelta => ?_⟩
  simpa [thetaCuspReflectedSourceOddParityWall, toeplitzFourOddParityWall,
    HilbertMetric.fourPointOddWall, f] using hwall t ht htdelta

/-- Positive logarithmic decay flux of a reflected completed-source fibre. -/
def thetaCuspReflectedSourceDecayFlux (u t : ℝ) : ℝ :=
  thetaCuspReflectedSourceProduct u t * thetaCuspReflectedLogJetOne u t

/-- The intrinsic first reflected logarithmic jet is strictly positive off the center. -/
theorem thetaCuspReflectedLogJetOne_pos
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < thetaCuspReflectedLogJetOne u t := by
  have hanti : StrictAnti (deriv thetaCuspLogSource) :=
    strictAntiOn_univ.mp <|
      strictConcaveOn_thetaCuspLogSource.strictAntiOn_deriv fun x _ =>
        (hasDerivAt_thetaCuspLogSource x).differentiableAt
  have h := hanti (show u - t < u + t by linarith)
  unfold thetaCuspReflectedLogJetOne thetaCuspLogDecaySlope
  simp only [iteratedDeriv_one]
  linarith

theorem thetaCuspReflectedSourceDecayFlux_pos
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < thetaCuspReflectedSourceDecayFlux u t := by
  unfold thetaCuspReflectedSourceDecayFlux thetaCuspReflectedSourceProduct
  exact mul_pos
    (mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _))
    (thetaCuspReflectedLogJetOne_pos u ht)

private theorem deriv_thetaCuspLogSource_eq_div (x : ℝ) :
    deriv thetaCuspLogSource x =
      deriv thetaCuspFullSource x / thetaCuspFullSource x := by
  simpa only [iteratedDeriv_one] using
    (hasDerivAt_thetaCuspLogSource x).deriv

/-- Reflected source product differentiates to minus its positive decay flux. -/
theorem hasDerivAt_thetaCuspReflectedSourceProduct (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedSourceProduct u)
      (-thetaCuspReflectedSourceDecayFlux u t) t := by
  have hp : HasDerivAt (fun s : ℝ => thetaCuspFullSource (u + s))
      (deriv thetaCuspFullSource (u + t)) t := by
    have hp0 :=
      ((contDiff_thetaCuspFullSource.differentiable (by simp) (u + t)).hasDerivAt.comp t
        ((hasDerivAt_id t).const_add u))
    exact (hp0.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv (by ring)
  have hm : HasDerivAt (fun s : ℝ => thetaCuspFullSource (u - s))
      (-deriv thetaCuspFullSource (u - t)) t := by
    have hm0 := ((contDiff_thetaCuspFullSource.differentiable
        (by simp) (u - t)).hasDerivAt.comp t
          ((hasDerivAt_id t).const_sub u))
    exact (hm0.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv (by ring)
  have hraw := hp.mul hm
  unfold thetaCuspReflectedSourceProduct thetaCuspReflectedSourceDecayFlux
    thetaCuspReflectedLogJetOne thetaCuspLogDecaySlope
  simp only [iteratedDeriv_one]
  rw [deriv_thetaCuspLogSource_eq_div,
    deriv_thetaCuspLogSource_eq_div]
  have hplus := (thetaCuspFullSource_pos_all (u + t)).ne'
  have hminus := (thetaCuspFullSource_pos_all (u - t)).ne'
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  simp only [thetaCuspReflectedSourceProduct]
  field_simp [hplus, hminus]
  ring

/-- Exact first derivative of one source-fibre odd wall. -/
theorem hasDerivAt_thetaCuspReflectedSourceOddParityWall (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedSourceOddParityWall u)
      (thetaCuspReflectedSourceDecayFlux u (3 * t) * 3 *
          (thetaCuspReflectedSourceProduct u 0 -
            thetaCuspReflectedSourceProduct u t) +
        thetaCuspReflectedSourceDecayFlux u t *
          (thetaCuspReflectedSourceProduct u 0 -
            thetaCuspReflectedSourceProduct u (3 * t)) -
        2 * (thetaCuspReflectedSourceProduct u t -
            thetaCuspReflectedSourceProduct u (2 * t)) *
          (-thetaCuspReflectedSourceDecayFlux u t +
            2 * thetaCuspReflectedSourceDecayFlux u (2 * t))) t := by
  let f : ℝ → ℝ := thetaCuspReflectedSourceProduct u
  let d : ℝ → ℝ := thetaCuspReflectedSourceDecayFlux u
  have h0 : HasDerivAt (fun _ : ℝ => f 0) 0 t := hasDerivAt_const t (f 0)
  have h1 : HasDerivAt f (-d t) t := by
    simpa only [f, d] using hasDerivAt_thetaCuspReflectedSourceProduct u t
  have h2 : HasDerivAt (fun s : ℝ => f (2 * s)) (-2 * d (2 * t)) t := by
    have h := (hasDerivAt_thetaCuspReflectedSourceProduct u (2 * t)).comp t
      ((hasDerivAt_id t).const_mul 2)
    exact (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv (by
        dsimp only [d]
        ring)
  have h3 : HasDerivAt (fun s : ℝ => f (3 * s)) (-3 * d (3 * t)) t := by
    have h := (hasDerivAt_thetaCuspReflectedSourceProduct u (3 * t)).comp t
      ((hasDerivAt_id t).const_mul 3)
    exact (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv (by
        dsimp only [d]
        ring)
  change HasDerivAt
    (fun s : ℝ => (f 0 - f (3 * s)) * (f 0 - f s) -
      (f s - f (2 * s)) ^ (2 : ℕ)) _ t
  have hraw := ((h0.sub h3).mul (h0.sub h1)).sub ((h1.sub h2).pow 2)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  dsimp only [f, d]
  simp only [Pi.sub_apply, Nat.cast_ofNat, Nat.reduceSubDiff]
  ring

/-- The completed theta source tends to zero on the positive logarithmic ray. -/
theorem tendsto_thetaCuspFullSource_atTop_zero :
    Tendsto thetaCuspFullSource atTop (nhds 0) := by
  rcases thetaCuspFullSource_superexponential_envelope 1 with
    ⟨C, hC, hbound⟩
  have hupper : Tendsto (fun x : ℝ => C * Real.exp (-x)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot)))
  apply squeeze_zero' (Filter.Eventually.of_forall fun x =>
    (thetaCuspFullSource_pos_all x).le) ?_ hupper
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have habs : |x| = x := abs_of_nonneg hx
  simpa [habs] using hbound x

/-- Every fixed reflected source fibre vanishes at large displacement. -/
theorem tendsto_thetaCuspReflectedSourceProduct_atTop_zero (u : ℝ) :
    Tendsto (thetaCuspReflectedSourceProduct u) atTop (nhds 0) := by
  have hp0 := tendsto_thetaCuspFullSource_atTop_zero.comp
    (tendsto_atTop_add_const_left atTop u tendsto_id)
  have hp : Tendsto (fun t : ℝ => thetaCuspFullSource (u + t)) atTop (nhds 0) := by
    refine hp0.congr' (Filter.Eventually.of_forall fun t => ?_)
    rfl
  have hm0 := tendsto_thetaCuspFullSource_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (-u) tendsto_id)
  have hm : Tendsto (fun t : ℝ => thetaCuspFullSource (u - t)) atTop (nhds 0) := by
    refine hm0.congr' (Filter.Eventually.of_forall fun t => ?_)
    dsimp only [Function.comp_apply, id_eq]
    rw [← thetaCuspFullSource_neg]
    congr 1
    ring
  unfold thetaCuspReflectedSourceProduct
  simpa only [zero_mul] using hp.mul hm

/-- The source-fibre odd wall returns to the strictly positive square of its central value. -/
theorem tendsto_thetaCuspReflectedSourceOddParityWall_atTop (u : ℝ) :
    Tendsto (thetaCuspReflectedSourceOddParityWall u) atTop
      (nhds (thetaCuspReflectedSourceProduct u 0 ^ (2 : ℕ))) := by
  let f : ℝ → ℝ := thetaCuspReflectedSourceProduct u
  have hconst : Tendsto (fun _ : ℝ => f 0) atTop (nhds (f 0)) := tendsto_const_nhds
  have hf : Tendsto f atTop (nhds 0) :=
    tendsto_thetaCuspReflectedSourceProduct_atTop_zero u
  have hf2 : Tendsto (fun t : ℝ => f (2 * t)) atTop (nhds 0) :=
    hf.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hf3 : Tendsto (fun t : ℝ => f (3 * t)) atTop (nhds 0) :=
    hf.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3))
  change Tendsto
    (fun t : ℝ => (f 0 - f (3 * t)) * (f 0 - f t) -
      (f t - f (2 * t)) ^ (2 : ℕ)) atTop (nhds (f 0 ^ (2 : ℕ)))
  simpa [pow_two] using
    ((hconst.sub hf3).mul (hconst.sub hf)).sub ((hf.sub hf2).pow 2)

/-- **Stationary negative-fibre law.** Any negative reflected source wall forces a strictly
interior negative wall where the middle-scale decay flux obeys the exact three-scale balance. -/
theorem exists_thetaCuspReflectedSourceOddParityWall_stationary_neg_of_neg
    {u t₀ : ℝ} (ht₀ : 0 < t₀)
    (hneg : thetaCuspReflectedSourceOddParityWall u t₀ < 0) :
    ∃ t : ℝ, 0 < t ∧ thetaCuspReflectedSourceOddParityWall u t < 0 ∧
      4 * thetaCuspReflectedSourceMiddleDrop u t *
          thetaCuspReflectedSourceDecayFlux u (2 * t) =
        thetaCuspReflectedSourceDecayFlux u t *
            (thetaCuspReflectedSourceFullDrop u t +
              2 * thetaCuspReflectedSourceMiddleDrop u t) +
          3 * thetaCuspReflectedSourceFirstDrop u t *
            thetaCuspReflectedSourceDecayFlux u (3 * t) := by
  have hcenter : 0 < thetaCuspReflectedSourceProduct u 0 ^ (2 : ℕ) := by
    simp only [thetaCuspReflectedSourceProduct, add_zero, sub_zero]
    exact pow_pos (mul_pos (thetaCuspFullSource_pos_all u)
      (thetaCuspFullSource_pos_all u)) 2
  have hposEventually : ∀ᶠ t : ℝ in atTop,
      0 < thetaCuspReflectedSourceOddParityWall u t :=
    (tendsto_thetaCuspReflectedSourceOddParityWall_atTop u).eventually
      (Ioi_mem_nhds hcenter)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hposEventually
  let T : ℝ := max R (t₀ + 1)
  have hRT : R ≤ T := le_max_left _ _
  have ht₀T : t₀ < T := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hTpos : 0 < thetaCuspReflectedSourceOddParityWall u T := hR T hRT
  have hcont : Continuous (thetaCuspReflectedSourceOddParityWall u) := by
    let f : ℝ → ℝ := thetaCuspReflectedSourceProduct u
    have hf : Continuous f := (contDiff_thetaCuspReflectedSourceProduct u).continuous
    change Continuous (fun t : ℝ =>
      (f 0 - f (3 * t)) * (f 0 - f t) - (f t - f (2 * t)) ^ (2 : ℕ))
    fun_prop
  have ht₀mem : t₀ ∈ Icc (0 : ℝ) T := ⟨ht₀.le, ht₀T.le⟩
  obtain ⟨t, htmem, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨t₀, ht₀mem⟩ hcont.continuousOn
  have htneg : thetaCuspReflectedSourceOddParityWall u t < 0 :=
    lt_of_le_of_lt (hmin ht₀mem) hneg
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := le_antisymm (le_of_not_gt hnot) htmem.1
    subst t
    simp [thetaCuspReflectedSourceOddParityWall,
      toeplitzFourOddParityWall] at htneg
  have htT : t < T := by
    by_contra hnot
    have hteq : t = T := le_antisymm htmem.2 (le_of_not_gt hnot)
    subst t
    exact (not_lt_of_ge hTpos.le) htneg
  have hlocal : IsLocalMin (thetaCuspReflectedSourceOddParityWall u) t :=
    hmin.isLocalMin (Icc_mem_nhds htpos htT)
  have hstationary := hlocal.hasDerivAt_eq_zero
    (hasDerivAt_thetaCuspReflectedSourceOddParityWall u t)
  refine ⟨t, htpos, htneg, ?_⟩
  unfold thetaCuspReflectedSourceFirstDrop
    thetaCuspReflectedSourceMiddleDrop thetaCuspReflectedSourceFullDrop
  linarith

/-- **Compulsory dyadic flux retention.** A negative literal source wall cannot occur unless
some interior negative stationary wall retains more than three quarters of its first-scale decay
flux at twice the separation.  This is a new necessary shape law for any rank-four counterexample. -/
theorem exists_thetaCuspReflectedSourceOddParityWall_stationary_flux_amplification_of_neg
    {u t₀ : ℝ} (ht₀ : 0 < t₀)
    (hneg : thetaCuspReflectedSourceOddParityWall u t₀ < 0) :
    ∃ t : ℝ, 0 < t ∧ thetaCuspReflectedSourceOddParityWall u t < 0 ∧
      4 * thetaCuspReflectedSourceMiddleDrop u t *
          thetaCuspReflectedSourceDecayFlux u (2 * t) =
        thetaCuspReflectedSourceDecayFlux u t *
            (thetaCuspReflectedSourceFullDrop u t +
              2 * thetaCuspReflectedSourceMiddleDrop u t) +
          3 * thetaCuspReflectedSourceFirstDrop u t *
            thetaCuspReflectedSourceDecayFlux u (3 * t) ∧
      3 * thetaCuspReflectedSourceDecayFlux u t / 4 <
        thetaCuspReflectedSourceDecayFlux u (2 * t) := by
  rcases exists_thetaCuspReflectedSourceOddParityWall_stationary_neg_of_neg
      ht₀ hneg with ⟨t, ht, htneg, hbalance⟩
  let A : ℝ := thetaCuspReflectedSourceFirstDrop u t
  let B : ℝ := thetaCuspReflectedSourceMiddleDrop u t
  let T : ℝ := thetaCuspReflectedSourceFullDrop u t
  let D₁ : ℝ := thetaCuspReflectedSourceDecayFlux u t
  let D₂ : ℝ := thetaCuspReflectedSourceDecayFlux u (2 * t)
  let D₃ : ℝ := thetaCuspReflectedSourceDecayFlux u (3 * t)
  have hA : 0 < A := by
    exact thetaCuspReflectedSourceFirstDrop_pos u ht
  have hB : 0 < B := by
    dsimp only [B, thetaCuspReflectedSourceMiddleDrop,
      thetaCuspReflectedSourceProduct]
    exact sub_pos.mpr <| strictAntiOn_thetaCuspFullSource_mul_reflect u
      (show t ∈ Ici (0 : ℝ) from ht.le)
      (show 2 * t ∈ Ici (0 : ℝ) by
        simp only [mem_Ici]
        positivity)
      (by linarith)
  have hT : 0 < T := by
    simpa only [T, thetaCuspReflectedSourceFullDrop,
      thetaCuspReflectedSourceFirstDrop] using
      (thetaCuspReflectedSourceFirstDrop_pos u
        (show 0 < 3 * t by positivity))
  have hC : 0 < thetaCuspReflectedSourceProduct u (2 * t) -
      thetaCuspReflectedSourceProduct u (3 * t) := by
    unfold thetaCuspReflectedSourceProduct
    exact sub_pos.mpr <| strictAntiOn_thetaCuspFullSource_mul_reflect u
      (show 2 * t ∈ Ici (0 : ℝ) by
        simp only [mem_Ici]
        positivity)
      (show 3 * t ∈ Ici (0 : ℝ) by
        simp only [mem_Ici]
        positivity)
      (by linarith)
  have hTB : B < T := by
    dsimp only [B, T, thetaCuspReflectedSourceMiddleDrop,
      thetaCuspReflectedSourceFullDrop] at hC ⊢
    dsimp only [A, thetaCuspReflectedSourceFirstDrop] at hA
    linarith
  have hD₁ : 0 < D₁ := thetaCuspReflectedSourceDecayFlux_pos u ht
  have hD₂ : 0 < D₂ :=
    thetaCuspReflectedSourceDecayFlux_pos u (by positivity)
  have hD₃ : 0 < D₃ :=
    thetaCuspReflectedSourceDecayFlux_pos u (by positivity)
  have hright : B * (3 * D₁) <
      D₁ * (T + 2 * B) + 3 * A * D₃ := by
    nlinarith [mul_pos hD₁ (sub_pos.mpr hTB), mul_pos hA hD₃]
  have hbalanceLocal :
      4 * B * D₂ = D₁ * (T + 2 * B) + 3 * A * D₃ := by
    simpa only [A, B, T, D₁, D₂, D₃] using hbalance
  have hproduct : B * (3 * D₁) < B * (4 * D₂) := by
    calc
      B * (3 * D₁) < D₁ * (T + 2 * B) + 3 * A * D₃ := hright
      _ = 4 * B * D₂ := hbalanceLocal.symm
      _ = B * (4 * D₂) := by ring
  have hlinear : 3 * D₁ < 4 * D₂ := by
    by_contra hnot
    have hge : 4 * D₂ ≤ 3 * D₁ := le_of_not_gt hnot
    have hmul : B * (4 * D₂) ≤ B * (3 * D₁) :=
      mul_le_mul_of_nonneg_left hge hB.le
    exact (not_lt_of_ge hmul) hproduct
  refine ⟨t, ht, htneg, hbalance, ?_⟩
  dsimp only [D₁, D₂] at hlinear ⊢
  linarith

/-- **Unconditional source-fibre alternative.** At every center, either the complete positive
separation ray already satisfies the rank-four odd wall, or one interior negative stationary
witness obeys both the exact three-scale flux balance and strict dyadic flux retention. -/
theorem thetaCuspReflectedSourceOddParityWall_global_or_stationary_flux_obstruction
    (u : ℝ) :
    (∀ t : ℝ, 0 < t → 0 ≤ thetaCuspReflectedSourceOddParityWall u t) ∨
      ∃ t : ℝ, 0 < t ∧ thetaCuspReflectedSourceOddParityWall u t < 0 ∧
        4 * thetaCuspReflectedSourceMiddleDrop u t *
            thetaCuspReflectedSourceDecayFlux u (2 * t) =
          thetaCuspReflectedSourceDecayFlux u t *
              (thetaCuspReflectedSourceFullDrop u t +
                2 * thetaCuspReflectedSourceMiddleDrop u t) +
            3 * thetaCuspReflectedSourceFirstDrop u t *
              thetaCuspReflectedSourceDecayFlux u (3 * t) ∧
        3 * thetaCuspReflectedSourceDecayFlux u t / 4 <
          thetaCuspReflectedSourceDecayFlux u (2 * t) := by
  by_cases hglobal :
      ∀ t : ℝ, 0 < t → 0 ≤ thetaCuspReflectedSourceOddParityWall u t
  · exact Or.inl hglobal
  · right
    push Not at hglobal
    rcases hglobal with ⟨t, ht, hneg⟩
    exact
      exists_thetaCuspReflectedSourceOddParityWall_stationary_flux_amplification_of_neg
        ht hneg

end

end RHTower
