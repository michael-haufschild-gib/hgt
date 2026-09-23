import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# No continuous scalar comparison at a critical-line zero

With `q s = exp(-2πi s)` the completed-density defect is `M s = q(1-s) - q(conj s)`.  At a point of
the critical line `1 - ρ = conj ρ`, so `M(ρ + w) = q(conj ρ)(exp(2πi w) - exp(-2πi conj w))`.

Along the critical line `w = i t` the two exponents coincide and `M` vanishes identically; along the
real direction `w = t` the difference is `2i sin(2πt)`, whose slope at the origin is the nonzero
number `4πi q(conj ρ)`.

So a factorization `M = h · A` with `h` continuous and `A` a nonzero holomorphic germ vanishing at
`ρ` is impossible: the vertical direction forces `h ρ = 0`, and then the horizontal slope of `h · A`
is `0 · A'(ρ) = 0`, contradicting `4πi q(conj ρ) ≠ 0`.
-/

noncomputable section

namespace RHTower

open Complex Filter Topology

/-- The exponential clock of the Hurwitz comparison. -/
def hurwitzQ (s : ℂ) : ℂ := Complex.exp (-2 * (Real.pi : ℂ) * I * s)

/-- The completed-density analytic defect `q(1-s) - q(conj s)`. -/
def hurwitzM (s : ℂ) : ℂ := hurwitzQ (1 - s) - hurwitzQ ((starRingEnd ℂ) s)

theorem hurwitzQ_ne_zero (s : ℂ) : hurwitzQ s ≠ 0 := Complex.exp_ne_zero _

theorem one_sub_eq_conj {ρ : ℂ} (hρ : ρ.re = 1 / 2) : 1 - ρ = (starRingEnd ℂ) ρ := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, hρ]
    norm_num
  · simp

theorem hurwitzM_shift {ρ : ℂ} (hρ : ρ.re = 1 / 2) (w : ℂ) :
    hurwitzM (ρ + w) =
      hurwitzQ ((starRingEnd ℂ) ρ) *
        (Complex.exp (2 * (Real.pi : ℂ) * I * w) -
          Complex.exp (-2 * (Real.pi : ℂ) * I * (starRingEnd ℂ) w)) := by
  have harg : (1 : ℂ) - (ρ + w) = (starRingEnd ℂ) ρ - w := by
    rw [← one_sub_eq_conj hρ]; ring
  have h1 : hurwitzQ (1 - (ρ + w)) =
      hurwitzQ ((starRingEnd ℂ) ρ) * Complex.exp (2 * (Real.pi : ℂ) * I * w) := by
    rw [harg, hurwitzQ, hurwitzQ, ← Complex.exp_add]
    congr 1
    ring
  have h2 : hurwitzQ ((starRingEnd ℂ) (ρ + w)) =
      hurwitzQ ((starRingEnd ℂ) ρ) *
        Complex.exp (-2 * (Real.pi : ℂ) * I * (starRingEnd ℂ) w) := by
    rw [map_add, hurwitzQ, hurwitzQ, ← Complex.exp_add]
    congr 1
    ring
  rw [hurwitzM, h1, h2, mul_sub]

/-- **The defect vanishes along the critical line.** -/
theorem hurwitzM_vertical {ρ : ℂ} (hρ : ρ.re = 1 / 2) (t : ℝ) :
    hurwitzM (ρ + (t : ℂ) * I) = 0 := by
  rw [hurwitzM_shift hρ]
  have hconj : (starRingEnd ℂ) ((t : ℂ) * I) = -(t : ℂ) * I := by simp
  rw [hconj]
  have hsame : Complex.exp (2 * (Real.pi : ℂ) * I * ((t : ℂ) * I)) =
      Complex.exp (-2 * (Real.pi : ℂ) * I * (-(t : ℂ) * I)) := by
    congr 1
    ring
  rw [hsame, sub_self, mul_zero]

theorem hurwitzM_center {ρ : ℂ} (hρ : ρ.re = 1 / 2) : hurwitzM ρ = 0 := by
  have := hurwitzM_vertical hρ 0
  simpa using this

/-- **The defect is a nonzero sine along the real direction.** -/
theorem hurwitzM_horizontal {ρ : ℂ} (hρ : ρ.re = 1 / 2) (t : ℝ) :
    hurwitzM (ρ + (t : ℂ)) =
      hurwitzQ ((starRingEnd ℂ) ρ) *
        (Complex.exp (2 * (Real.pi : ℂ) * I * (t : ℂ)) -
          Complex.exp (-2 * (Real.pi : ℂ) * I * (t : ℂ))) := by
  rw [hurwitzM_shift hρ, Complex.conj_ofReal]

theorem hasDerivAt_hurwitzM_horizontal {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    HasDerivAt (fun t : ℝ => hurwitzM (ρ + (t : ℂ)))
      (hurwitzQ ((starRingEnd ℂ) ρ) * (4 * (Real.pi : ℂ) * I)) 0 := by
  have hEq : (fun t : ℝ => hurwitzM (ρ + (t : ℂ))) =
      fun t : ℝ => hurwitzQ ((starRingEnd ℂ) ρ) *
        (Complex.exp (2 * (Real.pi : ℂ) * I * (t : ℂ)) -
          Complex.exp (-2 * (Real.pi : ℂ) * I * (t : ℂ))) :=
    funext fun t => hurwitzM_horizontal hρ t
  rw [hEq]
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * w))
      (2 * (Real.pi : ℂ) * I) 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).const_mul (2 * (Real.pi : ℂ) * I)).cexp)
  have h2 : HasDerivAt (fun w : ℂ => Complex.exp (-2 * (Real.pi : ℂ) * I * w))
      (-2 * (Real.pi : ℂ) * I) 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).const_mul (-2 * (Real.pi : ℂ) * I)).cexp)
  have hF : HasDerivAt (fun w : ℂ => hurwitzQ ((starRingEnd ℂ) ρ) *
      (Complex.exp (2 * (Real.pi : ℂ) * I * w) -
        Complex.exp (-2 * (Real.pi : ℂ) * I * w)))
      (hurwitzQ ((starRingEnd ℂ) ρ) * (4 * (Real.pi : ℂ) * I)) 0 := by
    have hsub := (h1.sub h2).const_mul (hurwitzQ ((starRingEnd ℂ) ρ))
    have heq : hurwitzQ ((starRingEnd ℂ) ρ) *
        (2 * (Real.pi : ℂ) * I - -2 * (Real.pi : ℂ) * I) =
        hurwitzQ ((starRingEnd ℂ) ρ) * (4 * (Real.pi : ℂ) * I) := by ring
    rw [heq] at hsub
    exact hsub
  exact hF.comp_ofReal

/-- **No continuous scalar comparison.**  At a critical-line point, the completed-density defect is
not a continuous scalar multiple of any nonzero holomorphic germ vanishing there. -/
theorem no_continuous_scalar_comparison {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    {A : ℂ → ℂ} (hA : AnalyticAt ℂ A ρ) (hA0 : A ρ = 0)
    (hAne : ¬ (∀ᶠ z in 𝓝 ρ, A z = 0))
    {h : ℂ → ℂ} (hh : ContinuousAt h ρ)
    (hfac : ∀ᶠ s in 𝓝 ρ, hurwitzM s = h s * A s) : False := by
  have hAnz : ∀ᶠ z in 𝓝[≠] ρ, A z ≠ 0 :=
    (hA.eventually_eq_zero_or_eventually_ne_zero).resolve_left hAne
  -- the vertical direction forces `h ρ = 0`
  have hvert : Tendsto (fun t : ℝ => ρ + (t : ℂ) * I) (𝓝[≠] (0 : ℝ)) (𝓝[≠] ρ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun t : ℝ => ρ + (t : ℂ) * I := by fun_prop
      have hlim := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({(0 : ℝ)}ᶜ)))
      simpa using hlim
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hc
      have : (t : ℂ) * I = 0 := by linear_combination hc
      rcases mul_eq_zero.mp this with h1 | h1
      · exact ht (by exact_mod_cast h1)
      · exact Complex.I_ne_zero h1
  have hzero : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), h (ρ + (t : ℂ) * I) = 0 := by
    filter_upwards [hvert.eventually hAnz,
      (hvert.mono_right nhdsWithin_le_nhds).eventually hfac] with t hA1 hf1
    rw [hurwitzM_vertical hρ t] at hf1
    exact (mul_eq_zero.mp hf1.symm).resolve_right hA1
  have hhρ : h ρ = 0 := by
    have hcont : Tendsto (fun t : ℝ => h (ρ + (t : ℂ) * I)) (𝓝[≠] (0 : ℝ)) (𝓝 (h ρ)) := by
      refine hh.tendsto.comp ?_
      refine tendsto_nhdsWithin_iff.mp hvert |>.1.mono_left le_rfl
    have hconst : Tendsto (fun t : ℝ => h (ρ + (t : ℂ) * I)) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      Tendsto.congr' (hzero.mono fun t ht => ht.symm) tendsto_const_nhds
    exact tendsto_nhds_unique hcont hconst
  -- the horizontal direction gives the contradiction
  obtain ⟨d, hd⟩ : ∃ d, HasDerivAt A d ρ := ⟨_, hA.differentiableAt.hasDerivAt⟩
  have hhoriz : Tendsto (fun t : ℝ => ρ + (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 ρ) := by
    have hc : Continuous fun t : ℝ => ρ + (t : ℂ) := by fun_prop
    have hlim := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({(0 : ℝ)}ᶜ)))
    simpa using hlim
  have hhorizP : Tendsto (fun t : ℝ => ρ + (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] ρ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hhoriz ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hc
    exact ht (by exact_mod_cast (by linear_combination hc : (t : ℂ) = 0))
  have hMzero : hurwitzM (ρ + ((0 : ℝ) : ℂ)) = 0 := by
    simpa using hurwitzM_center hρ
  have hMdiv : Tendsto (fun t : ℝ => hurwitzM (ρ + (t : ℂ)) / (t : ℂ)) (𝓝[≠] (0 : ℝ))
      (𝓝 (hurwitzQ ((starRingEnd ℂ) ρ) * (4 * (Real.pi : ℂ) * I))) := by
    refine ((hasDerivAt_hurwitzM_horizontal hρ).tendsto_slope).congr (fun t => ?_)
    rw [slope_def_module, hMzero, sub_zero, sub_zero, Complex.real_smul]
    push_cast
    ring
  have hAdiv : Tendsto (fun t : ℝ => A (ρ + (t : ℂ)) / (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝 d) := by
    refine (hd.tendsto_slope.comp hhorizP).congr (fun t => ?_)
    show slope A ρ (ρ + (t : ℂ)) = A (ρ + (t : ℂ)) / (t : ℂ)
    rw [slope_def_module, hA0, sub_zero, add_sub_cancel_left, smul_eq_mul]
    ring
  have hprod : Tendsto (fun t : ℝ => hurwitzM (ρ + (t : ℂ)) / (t : ℂ)) (𝓝[≠] (0 : ℝ))
      (𝓝 (0 * d)) := by
    have heq : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
        hurwitzM (ρ + (t : ℂ)) / (t : ℂ) =
          h (ρ + (t : ℂ)) * (A (ρ + (t : ℂ)) / (t : ℂ)) := by
      filter_upwards [hhoriz.eventually hfac] with t ht
      rw [ht]
      ring
    refine Tendsto.congr' (heq.mono fun t ht => ht.symm) (Tendsto.mul ?_ hAdiv)
    rw [← hhρ]
    exact hh.tendsto.comp hhoriz
  have huniq := tendsto_nhds_unique hMdiv hprod
  rw [zero_mul] at huniq
  have hc : hurwitzQ ((starRingEnd ℂ) ρ) ≠ 0 := hurwitzQ_ne_zero _
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rcases mul_eq_zero.mp huniq with h1 | h1
  · exact hc h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · norm_num at h3
      · exact hpi h3
    · exact Complex.I_ne_zero h2

/-! ### The completed-density specialization -/

/-- The completed-density analytic defect germ `4 z_s² ΞC(z_s)` with `z_s = (s - ½)(-i)`. -/
def xiHurwitzGerm (s : ℂ) : ℂ :=
  4 * ((s - 1 / 2) * (-I)) ^ (2 : ℕ) * XiC ((s - 1 / 2) * (-I))

theorem xiHurwitzGerm_differentiable : Differentiable ℂ xiHurwitzGerm := by
  have haff : Differentiable ℂ fun s : ℂ => (s - 1 / 2) * (-I) := by fun_prop
  exact (((differentiable_const 4).mul (haff.pow 2)).mul (XiC_differentiable.comp haff))

theorem xiHurwitzGerm_not_eventually_zero (ρ : ℂ) :
    ¬ (∀ᶠ z in 𝓝 ρ, xiHurwitzGerm z = 0) := by
  intro hev
  -- a small nonzero point where `ΞC` does not vanish
  have hcont : ContinuousAt XiC 0 := XiC_differentiable.continuous.continuousAt
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), XiC z ≠ 0 := hcont.eventually_ne XiC_zero_ne
  obtain ⟨z₀, hz₀ne, hz₀⟩ : ∃ z₀ : ℂ, XiC z₀ ≠ 0 ∧ z₀ ≠ 0 := by
    have hpunct : ∀ᶠ z in 𝓝[≠] (0 : ℂ), XiC z ≠ 0 ∧ z ≠ 0 := by
      filter_upwards [nhdsWithin_le_nhds hne, self_mem_nhdsWithin] with z h1 h2
      exact ⟨h1, h2⟩
    obtain ⟨z₀, hz₀, hz₀'⟩ := hpunct.exists
    exact ⟨z₀, hz₀, hz₀'⟩
  -- the identity theorem propagates the vanishing to the whole plane
  have hana : AnalyticOnNhd ℂ xiHurwitzGerm Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr xiHurwitzGerm_differentiable
  have hzero : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_const 0)
  have hall : ∀ z : ℂ, xiHurwitzGerm z = 0 := fun z =>
    hana.eqOn_of_preconnected_of_eventuallyEq hzero isPreconnected_univ (Set.mem_univ ρ)
      hev (Set.mem_univ z)
  have hs₀ : xiHurwitzGerm (1 / 2 + z₀ * I) = 4 * z₀ ^ (2 : ℕ) * XiC z₀ := by
    have harg : ((1 / 2 + z₀ * I) - 1 / 2) * (-I) = z₀ := by
      have hI : I * -I = 1 := by
        rw [mul_neg, Complex.I_mul_I]
        ring
      calc ((1 / 2 + z₀ * I) - 1 / 2) * (-I) = z₀ * (I * -I) := by ring
        _ = z₀ := by rw [hI, mul_one]
    rw [xiHurwitzGerm, harg]
  have := hall (1 / 2 + z₀ * I)
  rw [hs₀] at this
  rcases mul_eq_zero.mp this with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · norm_num at h2
    · exact hz₀ (pow_eq_zero_iff two_ne_zero |>.mp h2)
  · exact hz₀ne h1

/-- **No continuous scalar comparison for the completed density.**  At a critical-line zero of the
completed function, the analytic defect is not a continuous scalar multiple of the completed-density
germ. -/
theorem no_continuous_scalar_comparison_xi {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hzero : XiC ((ρ - 1 / 2) * (-I)) = 0)
    {h : ℂ → ℂ} (hh : ContinuousAt h ρ)
    (hfac : ∀ᶠ s in 𝓝 ρ, hurwitzM s = h s * xiHurwitzGerm s) : False := by
  refine no_continuous_scalar_comparison hρ
    (xiHurwitzGerm_differentiable.analyticAt ρ) ?_ (xiHurwitzGerm_not_eventually_zero ρ) hh hfac
  rw [xiHurwitzGerm, hzero, mul_zero]

end RHTower
