import GaloisForLFunctions.RHTower.BurnolAllPrimeCompletionWall

/-!
# The prime-dilation Cartier wall trace

The two orientations of the all-prime Burnol--Xi completion,

`C_p(s) = s²(s-1)/(2(p^s-1))`,   `C_p^∨(s) = C_p(1-s)`,

are singular exactly on the prime-dilation lattice `λ_{p,k} = 2πik/log p`.  At the common
zero-frequency point the completion evaluates the coefficient to zero, but the transverse Cartier
derivative recovers it with exact unit gain:

`-2 log p · ∂_s [C_p(s) u]_{s=0} = u`,   `2 log p · ∂_s [C_p^∨(s) u]_{s=1} = u`.

At every nonzero sideband the completion has a simple pole whose normalized residue recovers the
same coefficient.  Both statements are limits of explicit difference quotients; no divisor, zero,
or critical-line datum enters.
-/

open Complex Real Filter Topology

noncomputable section

namespace RHTower

/-- The reflected orientation of the all-prime completion. -/
def burnolAllPrimeCompletionMultiplierReflected (p : ℕ) (s : ℂ) : ℂ :=
  burnolAllPrimeCompletionMultiplier p (1 - s)

/-- The prime-dilation frequency lattice `λ_{p,k} = 2πik/log p`. -/
def burnolPrimeSideband (p : ℕ) (k : ℤ) : ℂ :=
  2 * π * Complex.I * (k : ℂ) / ((Real.log (p : ℝ) : ℝ) : ℂ)

/-! ## The prime dilation as an exponential -/

theorem burnolPrimeLog_pos {p : ℕ} (hp : 2 ≤ p) : 0 < Real.log (p : ℝ) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
  exact Real.log_pos hp1

theorem burnolPrimeLogC_ne_zero {p : ℕ} (hp : 2 ≤ p) :
    ((Real.log (p : ℝ) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (burnolPrimeLog_pos hp))

theorem burnolNatCpow_eq_exp {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    (p : ℂ) ^ s = Complex.exp (((Real.log (p : ℝ) : ℝ) : ℂ) * s) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hpne : ((p : ℕ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hlog : Complex.log ((p : ℕ) : ℂ) = ((Real.log (p : ℝ) : ℝ) : ℂ) := by
    rw [show ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_log hppos.le]
  rw [Complex.cpow_def_of_ne_zero hpne, hlog]

theorem nat_cpow_sideband {p : ℕ} (hp : 2 ≤ p) (k : ℤ) :
    (p : ℂ) ^ (burnolPrimeSideband p k) = 1 := by
  have hLne := burnolPrimeLogC_ne_zero hp
  rw [burnolNatCpow_eq_exp hp, burnolPrimeSideband,
    show ((Real.log (p : ℝ) : ℝ) : ℂ) *
        (2 * (π : ℂ) * Complex.I * (k : ℂ) / ((Real.log (p : ℝ) : ℝ) : ℂ)) =
      (k : ℂ) * (2 * (π : ℂ) * Complex.I) by field_simp]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem hasDerivAt_burnolNatCpow {p : ℕ} (hp : 2 ≤ p) (w : ℂ) :
    HasDerivAt (fun s : ℂ => (p : ℂ) ^ s)
      ((p : ℂ) ^ w * ((Real.log (p : ℝ) : ℝ) : ℂ)) w := by
  rw [funext (burnolNatCpow_eq_exp hp)]
  have hlin : HasDerivAt (fun s : ℂ => ((Real.log (p : ℝ) : ℝ) : ℂ) * s)
      (((Real.log (p : ℝ) : ℝ) : ℂ)) w := by
    simpa using (hasDerivAt_id w).const_mul (((Real.log (p : ℝ) : ℝ) : ℂ))
  exact hlin.cexp

/-! ## The zero-frequency Cartier derivative -/

theorem tendsto_burnolNatCpow_slope_zero {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun s : ℂ => ((p : ℂ) ^ s - 1) / s) (𝓝[≠] (0 : ℂ))
      (𝓝 (((Real.log (p : ℝ) : ℝ) : ℂ))) := by
  have hd := hasDerivAt_burnolNatCpow hp (0 : ℂ)
  rw [Complex.cpow_zero, one_mul] at hd
  have h := hasDerivAt_iff_tendsto_slope.mp hd
  refine h.congr (fun s => ?_)
  rw [slope_def_field, Complex.cpow_zero, sub_zero]

/-- **The transverse Cartier derivative at the nilpotent wall.** -/
theorem tendsto_burnolAllPrimeCompletion_div_zero {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun s : ℂ => burnolAllPrimeCompletionMultiplier p s / s) (𝓝[≠] (0 : ℂ))
      (𝓝 (-1 / (2 * ((Real.log (p : ℝ) : ℝ) : ℂ)))) := by
  have hLne := burnolPrimeLogC_ne_zero hp
  have hquot : Tendsto (fun s : ℂ => (s - 1) / 2 * (((p : ℂ) ^ s - 1) / s)⁻¹)
      (𝓝[≠] (0 : ℂ)) (𝓝 (((0 : ℂ) - 1) / 2 * (((Real.log (p : ℝ) : ℝ) : ℂ))⁻¹)) := by
    refine Filter.Tendsto.mul ?_ ((tendsto_burnolNatCpow_slope_zero hp).inv₀ hLne)
    exact ((continuous_id.sub continuous_const).div_const 2).continuousWithinAt.tendsto
  have hval : ((0 : ℂ) - 1) / 2 * (((Real.log (p : ℝ) : ℝ) : ℂ))⁻¹ =
      -1 / (2 * ((Real.log (p : ℝ) : ℝ) : ℂ)) := by
    field_simp
    ring
  rw [hval] at hquot
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsne : s ≠ 0 := hs
  by_cases hd : (p : ℂ) ^ s - 1 = 0
  · rw [burnolAllPrimeCompletionMultiplier, hd]
    simp
  · rw [burnolAllPrimeCompletionMultiplier]
    field_simp

/-- **Unit-gain recovery of the coefficient at the nilpotent wall.** -/
theorem tendsto_burnolCartierZeroWallTrace {p : ℕ} (hp : 2 ≤ p) (u : ℂ) :
    Tendsto (fun s : ℂ => -2 * ((Real.log (p : ℝ) : ℝ) : ℂ) *
        (burnolAllPrimeCompletionMultiplier p s * u / s)) (𝓝[≠] (0 : ℂ)) (𝓝 u) := by
  have hLne := burnolPrimeLogC_ne_zero hp
  have h := ((tendsto_burnolAllPrimeCompletion_div_zero hp).mul_const u).const_mul
    (-2 * ((Real.log (p : ℝ) : ℝ) : ℂ))
  have hval : -2 * ((Real.log (p : ℝ) : ℝ) : ℂ) *
      (-1 / (2 * ((Real.log (p : ℝ) : ℝ) : ℂ)) * u) = u := by
    field_simp
  rw [hval] at h
  refine h.congr (fun s => ?_)
  ring

/-! ## The sideband residues -/

/-- **Simple pole at every sideband.** -/
theorem tendsto_burnolAllPrimeCompletion_sidebandResidue {p : ℕ} (hp : 2 ≤ p) (k : ℤ) :
    Tendsto (fun s : ℂ => (s - burnolPrimeSideband p k) *
        burnolAllPrimeCompletionMultiplier p s) (𝓝[≠] (burnolPrimeSideband p k))
      (𝓝 ((burnolPrimeSideband p k) ^ (2 : ℕ) * (burnolPrimeSideband p k - 1) /
        (2 * ((Real.log (p : ℝ) : ℝ) : ℂ)))) := by
  set lam : ℂ := burnolPrimeSideband p k with hlam
  have hLne := burnolPrimeLogC_ne_zero hp
  have hone : (p : ℂ) ^ lam = 1 := nat_cpow_sideband hp k
  have hslope : Tendsto (fun s : ℂ => ((p : ℂ) ^ s - 1) / (s - lam)) (𝓝[≠] lam)
      (𝓝 (((Real.log (p : ℝ) : ℝ) : ℂ))) := by
    have hd := hasDerivAt_burnolNatCpow hp lam
    rw [hone, one_mul] at hd
    have h := hasDerivAt_iff_tendsto_slope.mp hd
    refine h.congr (fun s => ?_)
    rw [slope_def_field, hone]
  have hquot : Tendsto (fun s : ℂ => s ^ (2 : ℕ) * (s - 1) / 2 * (((p : ℂ) ^ s - 1) / (s - lam))⁻¹)
      (𝓝[≠] lam) (𝓝 (lam ^ (2 : ℕ) * (lam - 1) / 2 * (((Real.log (p : ℝ) : ℝ) : ℂ))⁻¹)) := by
    refine Filter.Tendsto.mul ?_ (hslope.inv₀ hLne)
    exact (((continuous_pow 2).mul (continuous_id.sub continuous_const)).div_const
      2).continuousWithinAt.tendsto
  have hval : lam ^ (2 : ℕ) * (lam - 1) / 2 * (((Real.log (p : ℝ) : ℝ) : ℂ))⁻¹ =
      lam ^ (2 : ℕ) * (lam - 1) / (2 * ((Real.log (p : ℝ) : ℝ) : ℂ)) := by
    field_simp
  rw [hval] at hquot
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsne : s - lam ≠ 0 := sub_ne_zero.mpr hs
  by_cases hd : (p : ℂ) ^ s - 1 = 0
  · rw [burnolAllPrimeCompletionMultiplier, hd]
    simp
  · rw [burnolAllPrimeCompletionMultiplier]
    field_simp

theorem burnolPrimeSideband_sub_one_ne_zero (p : ℕ) (k : ℤ) :
    burnolPrimeSideband p k - 1 ≠ 0 := by
  intro hc
  have h1 : burnolPrimeSideband p k = 1 := by linear_combination hc
  have h2 : (burnolPrimeSideband p k).re = 0 := by
    rw [burnolPrimeSideband, Complex.div_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.normSq_apply]
    ring
  rw [h1] at h2
  norm_num at h2

/-- **Unit-gain recovery of the coefficient at every nonzero sideband.** -/
theorem tendsto_burnolCartierSidebandTrace {p : ℕ} (hp : 2 ≤ p) {k : ℤ}
    (hk : burnolPrimeSideband p k ≠ 0) (u : ℂ) :
    Tendsto (fun s : ℂ => 2 * ((Real.log (p : ℝ) : ℝ) : ℂ) /
        ((burnolPrimeSideband p k) ^ (2 : ℕ) * (burnolPrimeSideband p k - 1)) *
        ((s - burnolPrimeSideband p k) * (burnolAllPrimeCompletionMultiplier p s * u)))
      (𝓝[≠] (burnolPrimeSideband p k)) (𝓝 u) := by
  set lam : ℂ := burnolPrimeSideband p k with hlam
  have hLne := burnolPrimeLogC_ne_zero hp
  have hlamOne : lam - 1 ≠ 0 := burnolPrimeSideband_sub_one_ne_zero p k
  have h := ((tendsto_burnolAllPrimeCompletion_sidebandResidue hp k).mul_const u).const_mul
    (2 * ((Real.log (p : ℝ) : ℝ) : ℂ) / (lam ^ (2 : ℕ) * (lam - 1)))
  have hval : 2 * ((Real.log (p : ℝ) : ℝ) : ℂ) / (lam ^ (2 : ℕ) * (lam - 1)) *
      (lam ^ (2 : ℕ) * (lam - 1) / (2 * ((Real.log (p : ℝ) : ℝ) : ℂ)) * u) = u := by
    field_simp
  rw [hval] at h
  refine h.congr (fun s => ?_)
  ring

/-! ## Reflected orientation -/

/-- **The transverse Cartier derivative of the reflected orientation at `s = 1`.** -/
theorem tendsto_burnolAllPrimeCompletionReflected_div_one {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun s : ℂ => burnolAllPrimeCompletionMultiplierReflected p s / (s - 1))
      (𝓝[≠] (1 : ℂ)) (𝓝 (1 / (2 * ((Real.log (p : ℝ) : ℝ) : ℂ)))) := by
  have hmap : Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] (1 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Tendsto (fun s : ℂ => 1 - s) (𝓝 (1 : ℂ)) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : s ≠ 1 := hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcon
      exact hs' (sub_eq_zero.mp hcon).symm
  have h := ((tendsto_burnolAllPrimeCompletion_div_zero hp).comp hmap).neg
  have hval : -(-1 / (2 * ((Real.log (p : ℝ) : ℝ) : ℂ))) =
      1 / (2 * ((Real.log (p : ℝ) : ℝ) : ℂ)) := by ring
  rw [hval] at h
  refine h.congr (fun s => ?_)
  simp only [Function.comp_apply]
  rw [burnolAllPrimeCompletionMultiplierReflected,
    show s - 1 = -(1 - s) by ring, div_neg]

/-! ## The signed horizon gap and the head-energy transgression -/

/-- The signed separation of the two cofinite prime-dilation walls. -/
def burnolHorizonGap (rho : ℂ) : ℝ := rho.re - (1 - rho.re)

theorem burnolHorizonGap_eq (rho : ℂ) : burnolHorizonGap rho = 2 * rho.re - 1 := by
  rw [burnolHorizonGap]
  ring

theorem burnolHorizonGap_pos_iff (rho : ℂ) : 0 < burnolHorizonGap rho ↔ 1 / 2 < rho.re := by
  rw [burnolHorizonGap]
  constructor <;> intro h <;> linarith

/-- **The two-horizon form of the head-energy transgression.**  Both factors of the physical energy
defect are boundary quantities: the signed horizon gap and the oriented Burnol current. -/
theorem xiDivisor_burnolCartier_headEnergyDefect_eq_horizonGap_mul_headFlux
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolSoninGammaHeadEnergy (1 / 2)
          (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) -
        burnolSoninGammaHeadEnergy (1 / 2) burnolFixedSubWindowSourceAtom =
      burnolHorizonGap (rho : ℂ) *
        burnolSoninOrientedGammaHeadFlux (1 / 2)
          (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) := by
  rw [xiDivisor_burnolCartier_gammaHeadEnergyDefect_eq_horizontal_mul_headFlux rho h,
    burnolHorizonGap_eq]
  ring

end RHTower
