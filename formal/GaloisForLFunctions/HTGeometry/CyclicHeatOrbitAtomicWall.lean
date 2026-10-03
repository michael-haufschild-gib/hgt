import GaloisForLFunctions.HTGeometry.CyclicHeatOrbitFormationCapital

/-!
# The atomic-refinement capital wall

For `T > 0` the normalized source-window packet `x_T = T^{-1} ∫_0^T S_t v dt` (**(OG.22f)**) is
reached by the window control `T^{-1} 1_{(0,T]}`, whose energy is `1/T` (**(OG.35g)**).  Hence
`q_G(x_T) ≤ 1/T`.  As `T ↓ 0`, `x_T → v` in norm, while the injected atom itself is not reachable
(**(OG.35h)–(OG.35i)**): `W h = v` would give `|v_j| ≤ |v_j| ‖h‖/√(2λ_j)` for every `j`, impossible
for a spectrum tending to infinity.  Lower semicontinuity of the cost then forces
`q_G(x_T) → ∞` (**(OG.22g)**).
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {ι : Type*}

local notation "ℓ²ι" => lp (fun _ : ι => ℂ) 2

/-! ## Elementary window integrals -/

theorem integral_Ioc_exp_neg_mul {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    ∫ t in Ioc 0 T, Real.exp (-(a * t)) = (1 - Real.exp (-(a * T))) / a := by
  rw [← intervalIntegral.integral_of_le hT]
  have hderiv : ∀ x ∈ uIcc 0 T, HasDerivAt (fun t => -Real.exp (-(a * t)) / a)
      (Real.exp (-(a * x))) x := fun x _ => by
    have h := ((((hasDerivAt_id x).const_mul a).neg).exp.neg).div_const a
    refine h.congr_deriv ?_
    simp only [id, mul_one, Pi.neg_apply]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(a * t))).intervalIntegrable _ _)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  field_simp
  ring

/-- The window factor `g(a) = (1 - e^{-a})/a`. -/
def windowFactor (a : ℝ) : ℝ := (1 - Real.exp (-a)) / a

theorem windowFactor_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ windowFactor a := by
  unfold windowFactor
  have : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  exact div_nonneg (by linarith) ha.le

theorem windowFactor_le_one {a : ℝ} (ha : 0 < a) : windowFactor a ≤ 1 := by
  unfold windowFactor
  rw [div_le_one ha]
  have := Real.add_one_le_exp (-a)
  linarith

theorem tendsto_windowFactor : Tendsto windowFactor (𝓝[>] 0) (𝓝 1) := by
  have hd : HasDerivAt (fun a : ℝ => -Real.exp (-a)) 1 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).neg.exp).neg
    refine h.congr_deriv ?_
    simp
  have h := (hasDerivAt_iff_tendsto_slope_zero.1 hd).mono_left
    (nhdsWithin_mono _ fun a (ha : 0 < a) => ne_of_gt ha)
  refine h.congr fun a => ?_
  simp only [zero_add, neg_zero, Real.exp_zero, smul_eq_mul, windowFactor]
  ring

/-! ## The window control -/

theorem halfLine_Ioc_ne_top (T : ℝ) : (volume.restrict (Ioi (0 : ℝ))) (Ioc 0 T) ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (Measure.restrict_apply_le _ _)

theorem halfLine_Ioc_real {T : ℝ} (hT : 0 ≤ T) : (volume.restrict (Ioi (0 : ℝ))).real (Ioc 0 T) = T := by
  rw [measureReal_def, Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.2 Ioc_subset_Ioi_self, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hT]

/-- **(OG.35g)** The window control `T^{-1} 1_{(0,T]}`. -/
def windowControl (T : ℝ) : HalfLineL2 :=
  indicatorConstLp 2 measurableSet_Ioc (halfLine_Ioc_ne_top T) ((T⁻¹ : ℝ) : ℂ)

/-- **(OG.35g)** `‖T^{-1} 1_{(0,T]}‖² = 1/T`. -/
theorem norm_windowControl_sq {T : ℝ} (hT : 0 < T) : ‖windowControl T‖ ^ 2 = 1 / T := by
  rw [windowControl, norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, halfLine_Ioc_real hT.le,
    Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hT.le), mul_pow, ENNReal.toReal_ofNat,
    show T ^ (1 / 2 : ℝ) = Real.sqrt T from (Real.sqrt_eq_rpow T).symm, Real.sq_sqrt hT.le]
  field_simp

namespace HeatSource

variable (s : HeatSource ι) [DecidableEq ι]

theorem heatReachability_apply (u : HalfLineL2) (j : ι) :
    s.heatReachability u j = ⟪s.heatFrame j, u⟫_ℂ := by
  rw [← inner_single_one_left, heatReachability, ContinuousLinearMap.adjoint_inner_right,
    heatAnalysis_single]

omit [DecidableEq ι] in
theorem heatFrame_ae (j : ι) :
    (s.heatFrame j : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      fun t => starRingEnd ℂ (s.v j) * (Real.exp (-(s.lam j * t)) : ℂ) := by
  have hl := s.lam_pos j
  filter_upwards [Lp.coeFn_smul (starRingEnd ℂ (s.v j) * ((Real.sqrt (2 * s.lam j))⁻¹ : ℝ))
    (gammaCoherentVector 1 (s.lam_pos j)), gammaCoherentVector_ae 1 (s.lam_pos j)] with t h1 h2
  rw [heatFrame, h1, Pi.smul_apply, h2, smul_eq_mul, gammaCoherentProfile]
  have hs : Real.sqrt (2 * s.lam j) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.cast_one,
    sub_self, zero_div, Real.rpow_zero, mul_one]
  push_cast
  have hsC : (Real.sqrt (2 * s.lam j) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
  field_simp

theorem halfLineL2_coeFn_finset_sum_smul {κ : Type*} (F : Finset κ) (a : κ → ℂ) (w : κ → HalfLineL2) :
    ((∑ i ∈ F, a i • w i : HalfLineL2) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      fun t => ∑ i ∈ F, a i * (w i : ℝ → ℂ) t := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero _ _ _
  | insert i F hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (a i • w i) (∑ j ∈ F, a j • w j), Lp.coeFn_smul (a i) (w i), ih]
      with t h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]

/-- **(OG.29)** The analysis map is the heat observation: `(W^* x)(t) = ⟨S_t v, x⟩` for almost
every `t > 0`. -/
theorem heatAnalysis_ae [Countable ι] (x : ℓ²ι) :
    (s.heatAnalysis x : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] fun t => ⟪s.heatOrbit t, x⟫_ℂ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hx : x = 0 := lp.ext (funext fun j => (IsEmpty.false j).elim)
    subst hx
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ)))] with t ht
    rw [map_zero, ht, inner_zero_right]
    rfl
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  set F : ℕ → Finset ι := fun n => (Finset.range n).image e with hFdef
  have hFmono : Monotone F := fun a b hab => Finset.image_subset_image (Finset.range_subset_range.2 hab)
  have hFtend : Tendsto F atTop atTop := tendsto_atTop_finset_of_monotone hFmono fun j => by
    obtain ⟨n, rfl⟩ := he j
    exact ⟨n + 1, Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_self n), rfl⟩⟩
  have hsum : HasSum (fun j => x j • s.heatFrame j) (s.heatAnalysis x) := by
    have hs := summable_norm_smul_frame s.summable_norm_sq_heatFrame x
    rw [heatAnalysis, squareSummableSynthesis_apply]
    exact hs.of_norm.hasSum
  have hL2 : Tendsto (fun n => ∑ j ∈ F n, x j • s.heatFrame j) atTop (𝓝 (s.heatAnalysis x)) :=
    hsum.comp hFtend
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  have hfin : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ n,
      ((∑ j ∈ F n, x j • s.heatFrame j : HalfLineL2) : ℝ → ℂ) t =
        ∑ j ∈ F n, x j * (starRingEnd ℂ (s.v j) * (Real.exp (-(s.lam j * t)) : ℂ)) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [halfLineL2_coeFn_finset_sum_smul (F n) x s.heatFrame,
      ae_all_iff.2 fun j => s.heatFrame_ae j] with t h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun j _ => by rw [h2 j]
  filter_upwards [hae, hfin, ae_restrict_mem measurableSet_Ioi] with t h1 h2 ht
  have ht' : (0 : ℝ) ≤ t := le_of_lt ht
  have hg : HasSum (fun j => x j * (starRingEnd ℂ (s.v j) * (Real.exp (-(s.lam j * t)) : ℂ)))
      ⟪s.heatOrbit t, x⟫_ℂ := by
    have hfun : (fun j => x j * (starRingEnd ℂ (s.v j) * (Real.exp (-(s.lam j * t)) : ℂ))) =
        fun j => ⟪(s.heatOrbit t) j, x j⟫_ℂ := by
      funext j
      rw [RCLike.inner_apply, s.heatOrbit_apply, heatFactor_of_nonneg _ ht', map_mul,
        Complex.conj_ofReal, mul_comm (s.lam j) t]
      ring
    rw [hfun, lp.inner_eq_tsum]
    exact (lp.summable_inner (𝕜 := ℂ) (s.heatOrbit t) x).hasSum
  have hlim : Tendsto (fun i => ((∑ j ∈ F (ns i), x j • s.heatFrame j : HalfLineL2) : ℝ → ℂ) t) atTop
      (𝓝 ⟪s.heatOrbit t, x⟫_ℂ) := by
    simp_rw [h2]
    exact hg.comp (hFtend.comp hns.tendsto_atTop)
  exact tendsto_nhds_unique h1 hlim

/-- **(OG.22f)** The normalized source-window packet `x_T = T^{-1} ∫_0^T S_t v dt`. -/
def windowPacket (T : ℝ) : ℓ²ι := ((T⁻¹ : ℝ) : ℂ) • ∫ t in Ioc 0 T, s.heatOrbit t

theorem windowPacket_apply {T : ℝ} (hT : 0 < T) (j : ι) :
    s.windowPacket T j = s.v j * (windowFactor (s.lam j * T) : ℂ) := by
  have hint : IntegrableOn s.heatOrbit (Ioc 0 T) :=
    (s.continuous_heatOrbit.continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h := integral_inner (𝕜 := ℂ) hint (lp.single 2 j (1 : ℂ))
  rw [inner_single_one_left] at h
  rw [windowPacket, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ← h]
  have hpt : ∀ t ∈ Ioc (0 : ℝ) T, ⟪(lp.single 2 j (1 : ℂ) : ℓ²ι), s.heatOrbit t⟫_ℂ =
      s.v j * ((Real.exp (-(s.lam j * t)) : ℝ) : ℂ) := fun t ht => by
    rw [inner_single_one_left, s.heatOrbit_apply, heatFactor_of_nonneg _ (le_of_lt ht.1), mul_comm,
      mul_comm t]
  rw [setIntegral_congr_fun measurableSet_Ioc hpt, integral_const_mul, integral_complex_ofReal,
    integral_Ioc_exp_neg_mul (s.lam_pos j) hT.le, windowFactor]
  have hl := s.lam_pos j
  push_cast
  field_simp

/-- **(OG.35g)** `x_T = W(T^{-1} 1_{(0,T]})`. -/
theorem windowPacket_eq {T : ℝ} (hT : 0 < T) : s.windowPacket T = s.heatReachability (windowControl T) := by
  refine lp.ext (funext fun j => ?_)
  rw [s.windowPacket_apply hT, s.heatReachability_apply, ← inner_conj_symm, windowControl,
    MeasureTheory.L2.inner_indicatorConstLp_eq_setIntegral_inner ℂ]
  have hae : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))).restrict (Ioc 0 T),
      ⟪((T⁻¹ : ℝ) : ℂ), (s.heatFrame j : ℝ → ℂ) t⟫_ℂ =
        starRingEnd ℂ (s.v j) * (((T⁻¹ * Real.exp (-(s.lam j * t))) : ℝ) : ℂ) := by
    rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 Ioc_subset_Ioi_self]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self (s.heatFrame_ae j)]
      with t ht
    rw [RCLike.inner_apply, ht, Complex.conj_ofReal]
    push_cast
    ring
  rw [integral_congr_ae hae, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.2 Ioc_subset_Ioi_self, integral_const_mul, integral_complex_ofReal,
    integral_const_mul, integral_Ioc_exp_neg_mul (s.lam_pos j) hT.le, map_mul, Complex.conj_conj,
    Complex.conj_ofReal, windowFactor]
  have hl := s.lam_pos j
  push_cast
  field_simp

/-- **(OG.22g)** `x_T → v` as `T ↓ 0`. -/
theorem tendsto_windowPacket : Tendsto s.windowPacket (𝓝[>] 0) (𝓝 s.v) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun T => ‖s.windowPacket T - s.v‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hrw : ∀ᶠ T in 𝓝[>] (0 : ℝ), ‖s.windowPacket T - s.v‖ ^ 2 =
        ∑' j, ‖s.v j * ((windowFactor (s.lam j * T) : ℂ) - 1)‖ ^ 2 :=
      eventually_mem_nhdsWithin.mono fun T (hT : 0 < T) => by
        rw [lp_two_norm_sq_eq_tsum]
        refine tsum_congr fun j => ?_
        rw [lp.coeFn_sub, Pi.sub_apply, s.windowPacket_apply hT, mul_sub, mul_one]
    refine Tendsto.congr' (EventuallyEq.symm hrw) ?_
    have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
      (f := fun T j => ‖s.v j * ((windowFactor (s.lam j * T) : ℂ) - 1)‖ ^ 2) (g := fun _ => (0 : ℝ))
      (bound := fun j => ‖s.v j‖ ^ 2) s.summable_norm_sq (fun j => ?_)
      (eventually_mem_nhdsWithin.mono fun T (hT : 0 < T) j => ?_)
    · simpa using hlim
    · have h1 : Tendsto (fun T => s.lam j * T) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have := ((continuous_const_mul (s.lam j)).tendsto (0 : ℝ)).mono_left
            (nhdsWithin_le_nhds (s := Ioi 0))
          simpa using this
        · exact eventually_mem_nhdsWithin.mono fun T (hT : 0 < T) => mul_pos (s.lam_pos j) hT
      have h2 := (Complex.continuous_ofReal.tendsto 1).comp (tendsto_windowFactor.comp h1)
      have h3 := ((h2.sub_const 1).const_mul (s.v j)).norm.pow 2
      simpa using h3
    · have h0 := windowFactor_nonneg (mul_pos (s.lam_pos j) hT)
      have h1 := windowFactor_le_one (mul_pos (s.lam_pos j) hT)
      rw [norm_pow, norm_norm, norm_mul]
      have hle : ‖(windowFactor (s.lam j * T) : ℂ) - 1‖ ≤ 1 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_le]
        constructor <;> linarith
      calc (‖s.v j‖ * ‖(windowFactor (s.lam j * T) : ℂ) - 1‖) ^ 2 ≤ (‖s.v j‖ * 1) ^ 2 :=
            pow_le_pow_left₀ (by positivity)
              (mul_le_mul_of_nonneg_left hle (norm_nonneg _)) 2
        _ = ‖s.v j‖ ^ 2 := by ring
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at h
  refine h.congr fun T => ?_
  simp only [Function.comp_apply]
  rw [Real.sqrt_sq (norm_nonneg _)]

end HeatSource

namespace CyclicHeatSource

variable (c : CyclicHeatSource ι) [DecidableEq ι]

/-- **(OG.22g)** `q_G(x_T) ≤ 1/T`. -/
theorem orbitCostForm_windowPacket_le {T : ℝ} (hT : 0 < T) :
    c.orbitCostForm (c.windowPacket T) ≤ ENNReal.ofReal (1 / T) := by
  rw [c.windowPacket_eq hT, ← norm_windowControl_sq hT]
  exact c.orbitCostForm_heatReachability_le _

/-- **(OG.35h)–(OG.35i)** The injected atom `v` is not reachable. -/
theorem v_notMem_range_heatReachability [Infinite ι] : c.v ∉ Set.range c.heatReachability := by
  rintro ⟨h, hh⟩
  have hbound : ∀ j, 2 * c.lam j ≤ ‖h‖ ^ 2 := by
    intro j
    have hj := congrArg (fun x : ℓ²ι => x j) hh
    simp only at hj
    rw [c.heatReachability_apply] at hj
    have hle := norm_inner_le_norm (𝕜 := ℂ) (c.heatFrame j) h
    rw [hj] at hle
    have hnorm : ‖c.heatFrame j‖ = ‖c.v j‖ / Real.sqrt (2 * c.lam j) := by
      have h2 := c.norm_sq_heatFrame j
      have hl := c.lam_pos j
      rw [← Real.sqrt_sq (norm_nonneg (c.heatFrame j)), h2, Real.sqrt_div' _ (by positivity),
        Real.sqrt_sq (norm_nonneg _)]
    rw [hnorm] at hle
    have hv : 0 < ‖c.v j‖ := norm_pos_iff.2 (c.fullSupport j)
    have hs : 0 < Real.sqrt (2 * c.lam j) := Real.sqrt_pos.2 (by linarith [c.lam_pos j])
    have h1 : Real.sqrt (2 * c.lam j) ≤ ‖h‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hs] at hle
      nlinarith
    have h2 := pow_le_pow_left₀ hs.le h1 2
    rwa [Real.sq_sqrt (by linarith [c.lam_pos j])] at h2
  have hfin : {j | c.lam j ≤ ‖h‖ ^ 2 / 2}.Finite := by
    have := c.proper.eventually (eventually_gt_atTop (‖h‖ ^ 2 / 2))
    rw [Filter.eventually_cofinite] at this
    simpa using this
  refine Set.infinite_univ (α := ι) (hfin.subset fun j _ => ?_)
  simp only [Set.mem_setOf_eq]
  linarith [hbound j]

/-- **(OG.22g)** `q_G(v) = ∞`. -/
theorem orbitCostForm_v [Infinite ι] : c.orbitCostForm c.v = ⊤ := by
  by_contra h
  have hlt : c.orbitCostForm c.v < ⊤ := lt_top_iff_ne_top.2 h
  rw [← Set.mem_setOf_eq (p := fun x => c.orbitCostForm x < ⊤), ← (c.range_heatReachability).2] at hlt
  exact c.v_notMem_range_heatReachability hlt

/-- **(OG.22g) The atomic-refinement wall.**  `q_G(x_T) → ∞` as `T ↓ 0`. -/
theorem tendsto_orbitCostForm_windowPacket [Infinite ι] :
    Tendsto (fun T => c.orbitCostForm (c.windowPacket T)) (𝓝[>] 0) (𝓝 ⊤) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => absurd ha not_top_lt⟩
  have hlsc := c.lowerSemicontinuous_orbitCostForm c.v a (lt_of_lt_of_eq ha c.orbitCostForm_v.symm)
  exact c.tendsto_windowPacket.eventually hlsc

end CyclicHeatSource

end GaloisForLFunctions.HTGeometry
