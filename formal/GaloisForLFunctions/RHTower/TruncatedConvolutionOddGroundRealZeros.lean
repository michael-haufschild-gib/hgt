import GaloisForLFunctions.RHTower.TruncatedConvolutionGroundSelection

/-!
# The compressed minima converge to the bottom of the truncated-convolution form

The Fourier coefficients of the ground give a trial vector in every compression, so the compressed
minimum is squeezed between the bottom of the form and the Rayleigh quotient of the projected
ground.  Parseval makes the projection converge in mean square and the Lipschitz bound transports
that to the Rayleigh quotients.
-/

open MeasureTheory Filter Topology Matrix

open scoped Matrix ComplexOrder

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem l2NormSq_sub_comm (f g : ℝ → ℂ) :
    l2NormSq (fun x => f x - g x) = l2NormSq (fun x => g x - f x) := by
  rw [l2NormSq, l2NormSq]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← norm_neg (f x - g x), neg_sub]

/-- The compressed Fourier coefficients of a function. -/
def xiCoeffVec (xi : ℝ → ℂ) (N : ℕ) : CCMCenteredParityIndex N → ℂ :=
  fun i => l2Pair (fourierChar (ccmParityCenteredMode N i)) xi

theorem truncConvModePoly_xiCoeffVec (xi : ℝ → ℂ) (N : ℕ) :
    truncConvModePoly (xiCoeffVec xi N) = fourierPartialSum xi N := by
  funext x
  simp only [truncConvModePoly, indexTrigPoly, xiCoeffVec, fourierPartialSum]
  exact sum_ccmParityCenteredMode N (fun j => l2Pair (fourierChar j) xi * fourierChar j x)

theorem l2NormSq_truncConvModePoly_xiCoeffVec (xi : ℝ → ℂ) (N : ℕ) :
    l2NormSq (truncConvModePoly (xiCoeffVec xi N))
      = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖l2Pair (fourierChar n) xi‖ ^ 2 := by
  rw [l2NormSq_truncConvModePoly]
  exact sum_ccmParityCenteredMode N (fun j => ‖l2Pair (fourierChar j) xi‖ ^ 2)

/-- **The projected ground converges in mean square.** -/
theorem tendsto_l2NormSq_sub_xiCoeffVec {xi : ℝ → ℂ} (hxi : Continuous xi) :
    Tendsto (fun N : ℕ =>
        l2NormSq fun x => truncConvModePoly (xiCoeffVec xi N) x - xi x) atTop (𝓝 0) := by
  have h := tendsto_l2NormSq_sub_fourierPartialSum hxi
  refine h.congr fun N => ?_
  rw [truncConvModePoly_xiCoeffVec]
  exact l2NormSq_sub_comm _ _

/-- **The projected ground has norm tending to one.** -/
theorem tendsto_l2NormSq_xiCoeffVec {k : ℝ → ℝ} {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi) :
    Tendsto (fun N : ℕ => l2NormSq (truncConvModePoly (xiCoeffVec xi N))) atTop (𝓝 1) := by
  have hsub := tendsto_l2NormSq_sub_fourierPartialSum H.contXi
  have hid : ∀ N : ℕ, l2NormSq (truncConvModePoly (xiCoeffVec xi N))
      = l2NormSq xi - l2NormSq (fun x => xi x - fourierPartialSum xi N x) := by
    intro N
    rw [l2NormSq_truncConvModePoly_xiCoeffVec,
      l2NormSq_sub_fourierPartialSum H.contXi N]
    ring
  have hlim : Tendsto (fun N : ℕ =>
      l2NormSq xi - l2NormSq (fun x => xi x - fourierPartialSum xi N x)) atTop
      (𝓝 (l2NormSq xi - 0)) := tendsto_const_nhds.sub hsub
  have hval : l2NormSq xi - 0 = 1 := by rw [sub_zero, H.normXi]
  rw [hval] at hlim
  exact hlim.congr fun N => (hid N).symm

theorem l2Pair_xi_form {k : ℝ → ℝ} {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi) :
    l2Pair xi (truncConv k xi) = (lam : ℂ) := by
  rw [l2Pair_congr_right H.eig, l2Pair_smul_right (lam : ℂ) xi xi, l2Pair_xi_xi H, mul_one]

/-- **The Rayleigh quotients of the projected ground converge to the bottom.** -/
theorem tendsto_form_xiCoeffVec {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (_heven : ∀ u, k (-u) = k u) {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi) :
    Tendsto (fun N : ℕ => (l2Pair (truncConvModePoly (xiCoeffVec xi N))
        (truncConv k (truncConvModePoly (xiCoeffVec xi N)))).re) atTop (𝓝 lam) := by
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun u => (hk u).continuousAt
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hkc.continuousOn
  set P : ℕ → ℝ → ℂ := fun N => truncConvModePoly (xiCoeffVec xi N) with hP
  have hPc : ∀ N, Continuous (P N) := fun N => continuous_truncConvModePoly _
  have hd : Tendsto (fun N : ℕ => Real.sqrt (l2NormSq fun x => P N x - xi x)) atTop (𝓝 0) := by
    have h := (tendsto_l2NormSq_sub_xiCoeffVec H.contXi)
    have := (Real.continuous_sqrt.tendsto 0).comp h
    simpa [Function.comp_def] using this
  have hn : Tendsto (fun N : ℕ => Real.sqrt (l2NormSq (P N))) atTop (𝓝 1) := by
    have h := tendsto_l2NormSq_xiCoeffVec H
    have := (Real.continuous_sqrt.tendsto 1).comp h
    simpa [Function.comp_def] using this
  have hbound : Tendsto (fun N : ℕ =>
      M * Real.sqrt (l2NormSq fun x => P N x - xi x) * Real.sqrt (l2NormSq (P N))
        + M * Real.sqrt (l2NormSq xi) * Real.sqrt (l2NormSq fun x => P N x - xi x))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ =>
        M * Real.sqrt (l2NormSq fun x => P N x - xi x) * Real.sqrt (l2NormSq (P N))) atTop
        (𝓝 (M * 0 * 1)) := ((tendsto_const_nhds.mul hd).mul hn)
    have h2 : Tendsto (fun N : ℕ =>
        M * Real.sqrt (l2NormSq xi) * Real.sqrt (l2NormSq fun x => P N x - xi x)) atTop
        (𝓝 (M * Real.sqrt (l2NormSq xi) * 0)) := tendsto_const_nhds.mul hd
    have := h1.add h2
    simpa using this
  have hsq : Tendsto (fun N : ℕ =>
      ‖l2Pair (P N) (truncConv k (P N)) - l2Pair xi (truncConv k xi)‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hbound
    exact norm_form_sub_le hkc hM H.contXi (hPc N)
  have hlim : Tendsto (fun N : ℕ => l2Pair (P N) (truncConv k (P N))) atTop
      (𝓝 (l2Pair xi (truncConv k xi))) := by
    rw [← tendsto_sub_nhds_zero_iff]
    exact tendsto_zero_iff_norm_tendsto_zero.2 hsq
  rw [l2Pair_xi_form H] at hlim
  have := (Complex.continuous_re.tendsto ((lam : ℝ) : ℂ)).comp hlim
  simpa [Function.comp_def] using this

/-! ## The compressed minima converge to the bottom -/

/-- **The compressed minima converge to the bottom of the form.** -/
theorem tendsto_truncConvMin {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (_hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi)
    (w : ∀ N : ℕ, CCMCenteredParityIndex N → ℂ)
    (hw : ∀ N, w N ∈ truncConvSphere N)
    (hmin : ∀ N, ∀ v ∈ truncConvSphere N,
      truncConvRayleigh k N (w N) ≤ truncConvRayleigh k N v) :
    Tendsto (fun N : ℕ => truncConvRayleigh k N (w N)) atTop (𝓝 lam) := by
  have hlower : ∀ N : ℕ, lam ≤ truncConvRayleigh k N (w N) := by
    intro N
    have hnorm : l2NormSq (truncConvModePoly (w N)) = 1 := by
      rw [l2NormSq_truncConvModePoly]
      exact hw N
    have h := truncConv_form_lower hk heven H (continuous_truncConvModePoly (w N))
    rw [hnorm, mul_one] at h
    exact h
  set L : ℕ → ℝ := fun N => l2NormSq (truncConvModePoly (xiCoeffVec xi N)) with hL
  set F : ℕ → ℝ := fun N => truncConvRayleigh k N (xiCoeffVec xi N) with hF
  have hLlim : Tendsto L atTop (𝓝 1) := tendsto_l2NormSq_xiCoeffVec H
  have hFlim : Tendsto F atTop (𝓝 lam) := tendsto_form_xiCoeffVec hk heven H
  have hquot : Tendsto (fun N : ℕ => F N / L N) atTop (𝓝 lam) := by
    have h : Tendsto (fun N : ℕ => F N / L N) atTop (𝓝 (lam / 1)) := hFlim.div hLlim one_ne_zero
    rwa [div_one] at h
  have hupper : ∀ᶠ N : ℕ in atTop, truncConvRayleigh k N (w N) ≤ F N / L N := by
    have hev : ∀ᶠ N : ℕ in atTop, 0 < L N :=
      hLlim.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hev] with N hLN
    have hfloor := truncConvRayleigh_min_le (hmin N) (xiCoeffVec xi N)
    rw [← l2NormSq_truncConvModePoly] at hfloor
    rw [le_div_iff₀ hLN]
    exact hfloor
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hquot
    (Filter.Eventually.of_forall hlower) hupper

/-! ## Phase normalization -/

/-- The phase-normalized compressed ground. -/
def phaseGround (xi : ℝ → ℂ) {N : ℕ} (w : CCMCenteredParityIndex N → ℂ) :
    CCMCenteredParityIndex N → ℂ :=
  fun i => (starRingEnd ℂ) (l2Pair xi (truncConvModePoly w)) /
    ((‖l2Pair xi (truncConvModePoly w)‖ : ℝ) : ℂ) * w i

theorem phaseGround_eq (xi : ℝ → ℂ) {N : ℕ} (w : CCMCenteredParityIndex N → ℂ) :
    phaseGround xi w = fun i => (starRingEnd ℂ) (l2Pair xi (truncConvModePoly w)) /
      ((‖l2Pair xi (truncConvModePoly w)‖ : ℝ) : ℂ) * w i := rfl

theorem truncConvModePoly_phaseGround (xi : ℝ → ℂ) {N : ℕ}
    (w : CCMCenteredParityIndex N → ℂ) (x : ℝ) :
    truncConvModePoly (phaseGround xi w) x
      = ((starRingEnd ℂ) (l2Pair xi (truncConvModePoly w)) /
          ((‖l2Pair xi (truncConvModePoly w)‖ : ℝ) : ℂ)) * truncConvModePoly w x := by
  simp only [truncConvModePoly]
  exact indexTrigPoly_const_mul _ _ _ _

theorem norm_phaseFactor {xi : ℝ → ℂ} {N : ℕ} {w : CCMCenteredParityIndex N → ℂ}
    (hc : l2Pair xi (truncConvModePoly w) ≠ 0) :
    ‖(starRingEnd ℂ) (l2Pair xi (truncConvModePoly w)) /
      ((‖l2Pair xi (truncConvModePoly w)‖ : ℝ) : ℂ)‖ = 1 := by
  set c : ℂ := l2Pair xi (truncConvModePoly w) with hcdef
  have hn : (0 : ℝ) < ‖c‖ := norm_pos_iff.2 hc
  rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn,
    div_self (ne_of_gt hn)]

theorem phaseGround_mem_sphere {xi : ℝ → ℂ} {N : ℕ} {w : CCMCenteredParityIndex N → ℂ}
    (hw : w ∈ truncConvSphere N) (hc : l2Pair xi (truncConvModePoly w) ≠ 0) :
    phaseGround xi w ∈ truncConvSphere N := by
  have hn := norm_phaseFactor (xi := xi) (w := w) hc
  show ∑ i, ‖phaseGround xi w i‖ ^ 2 = 1
  have hval : ∀ i, ‖phaseGround xi w i‖ ^ 2 = ‖w i‖ ^ 2 := by
    intro i
    rw [phaseGround, norm_mul, hn, one_mul]
  rw [Finset.sum_congr rfl fun i _ => hval i]
  exact hw

theorem truncConvRayleigh_phaseGround {k : ℝ → ℝ} {xi : ℝ → ℂ} {N : ℕ}
    {w : CCMCenteredParityIndex N → ℂ} (hc : l2Pair xi (truncConvModePoly w) ≠ 0) :
    truncConvRayleigh k N (phaseGround xi w) = truncConvRayleigh k N w := by
  have hn := norm_phaseFactor (xi := xi) (w := w) hc
  have h := truncConvRayleigh_complex_mul k
    ((starRingEnd ℂ) (l2Pair xi (truncConvModePoly w)) /
      ((‖l2Pair xi (truncConvModePoly w)‖ : ℝ) : ℂ)) w
  rw [hn] at h
  rw [phaseGround_eq]
  simpa using h

theorem l2Pair_xi_phaseGround {xi : ℝ → ℂ} {N : ℕ} {w : CCMCenteredParityIndex N → ℂ}
    (hc : l2Pair xi (truncConvModePoly w) ≠ 0) :
    l2Pair xi (truncConvModePoly (phaseGround xi w))
      = ((‖l2Pair xi (truncConvModePoly w)‖ : ℝ) : ℂ) := by
  set c : ℂ := l2Pair xi (truncConvModePoly w) with hcdef
  have hn : (0 : ℝ) < ‖c‖ := norm_pos_iff.2 hc
  have hP : truncConvModePoly (phaseGround xi w)
      = fun x => ((starRingEnd ℂ) c / ((‖c‖ : ℝ) : ℂ)) * truncConvModePoly w x :=
    funext fun x => truncConvModePoly_phaseGround xi w x
  rw [hP, l2Pair_smul_right _ xi (truncConvModePoly w), ← hcdef]
  have hcc : (starRingEnd ℂ) c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  have hne : ((‖c‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hn
  field_simp
  rw [hcc]
  push_cast
  ring

/-! ## Mean-square convergence of the compressed grounds -/

/-- **The phase-normalized compressed grounds converge to the ground in mean square.** -/
theorem tendsto_l2NormSq_phaseGround_sub {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) {lam gap : ℝ} {xi : ℝ → ℂ}
    (H : TruncConvOddGround k lam gap xi)
    (w : ∀ N : ℕ, CCMCenteredParityIndex N → ℂ)
    (hw : ∀ N, w N ∈ truncConvSphere N)
    (hmin : ∀ N, ∀ v ∈ truncConvSphere N,
      truncConvRayleigh k N (w N) ≤ truncConvRayleigh k N v)
    (hc : ∀ N, l2Pair xi (truncConvModePoly (w N)) ≠ 0) :
    Tendsto (fun N : ℕ =>
        l2NormSq fun x => truncConvModePoly (phaseGround xi (w N)) x - xi x) atTop (𝓝 0) := by
  set P : ℕ → ℝ → ℂ := fun N => truncConvModePoly (phaseGround xi (w N)) with hP
  have hPc : ∀ N, Continuous (P N) := fun N => continuous_truncConvModePoly _
  set cn : ℕ → ℝ := fun N => ‖l2Pair xi (truncConvModePoly (w N))‖ with hcn
  have hpair : ∀ N, l2Pair xi (P N) = ((cn N : ℝ) : ℂ) := fun N => l2Pair_xi_phaseGround (hc N)
  have hnorm : ∀ N, l2NormSq (P N) = 1 := by
    intro N
    rw [hP, l2NormSq_truncConvModePoly]
    exact phaseGround_mem_sphere (hw N) (hc N)
  have hray : ∀ N, (l2Pair (P N) (truncConv k (P N))).re = truncConvRayleigh k N (w N) := by
    intro N
    rw [← truncConvRayleigh_phaseGround (k := k) (hc N)]
    rfl
  set r : ℕ → ℝ → ℂ := fun N => truncConvResidual xi (P N) with hr
  have hres : ∀ N, gap * l2NormSq (r N) ≤ truncConvRayleigh k N (w N) - lam := by
    intro N
    have h := truncConv_gap_estimate hk heven H (hPc N)
    rw [hnorm N, mul_one, hray N] at h
    exact h
  have hmu := tendsto_truncConvMin hk hk'c heven H w hw hmin
  have hmusub : Tendsto (fun N : ℕ => truncConvRayleigh k N (w N) - lam) atTop (𝓝 0) := by
    have := hmu.sub (tendsto_const_nhds (x := lam) (f := (atTop : Filter ℕ)))
    simpa using this
  have hrlim : Tendsto (fun N : ℕ => l2NormSq (r N)) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => l2NormSq_nonneg _) (fun N => ?_)
      (by simpa using hmusub.div_const gap)
    rw [le_div_iff₀ H.gapPos]
    have := hres N
    linarith [this]
  have hcsq : ∀ N, cn N ^ 2 = 1 - l2NormSq (r N) := by
    intro N
    have h := l2NormSq_truncConvResidual H (hPc N)
    rw [hnorm N, hpair N] at h
    rw [hr]
    simp only
    rw [h, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hclim : Tendsto cn atTop (𝓝 1) := by
    have hsq : Tendsto (fun N : ℕ => cn N ^ 2) atTop (𝓝 1) := by
      have : Tendsto (fun N : ℕ => 1 - l2NormSq (r N)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub hrlim
      rw [sub_zero] at this
      exact this.congr fun N => (hcsq N).symm
    have hroot : Tendsto (fun N : ℕ => Real.sqrt (cn N ^ 2)) atTop (𝓝 (Real.sqrt 1)) :=
      (Real.continuous_sqrt.tendsto 1).comp hsq
    rw [Real.sqrt_one] at hroot
    exact hroot.congr fun N => Real.sqrt_sq (norm_nonneg _)
  have hsplit : ∀ N, l2NormSq (fun x => P N x - xi x)
      ≤ 2 * l2NormSq (r N) + 2 * ((cn N - 1) ^ 2 * l2NormSq xi) := by
    intro N
    have hid : ∀ x, P N x - xi x = r N x + ((cn N : ℝ) - 1 : ℂ) * xi x := by
      intro x
      rw [hr]
      simp only [truncConvResidual_eq, hpair N]
      push_cast
      ring
    have hfun : (fun x => P N x - xi x)
        = fun x => r N x + (((cn N : ℝ) - 1 : ℂ)) * xi x := funext hid
    rw [hfun]
    have hb : l2NormSq (fun x => (((cn N : ℝ) - 1 : ℂ)) * xi x)
        = (cn N - 1) ^ 2 * l2NormSq xi := by
      rw [l2NormSq_const_mul]
      congr 1
      rw [show (((cn N : ℝ) - 1 : ℂ)) = (((cn N - 1 : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hadd := l2NormSq_add_le (f := r N) (g := fun x => (((cn N : ℝ) - 1 : ℂ)) * xi x)
      (continuous_truncConvResidual H.contXi (hPc N)) (continuous_const.mul H.contXi)
    rw [hb] at hadd
    exact hadd
  refine squeeze_zero (fun N => l2NormSq_nonneg _) hsplit ?_
  have hlim2 : Tendsto (fun N : ℕ => 2 * l2NormSq (r N)
      + 2 * ((cn N - 1) ^ 2 * l2NormSq xi)) atTop (𝓝 (2 * 0 + 2 * ((1 - 1) ^ 2 * l2NormSq xi))) := by
    refine (tendsto_const_nhds.mul hrlim).add (tendsto_const_nhds.mul ?_)
    exact ((hclim.sub tendsto_const_nhds).pow 2).mul tendsto_const_nhds
  simpa using hlim2

end

end RHTower
