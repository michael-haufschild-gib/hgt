import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryCompactProfileIsPositiveBeyondLogLogOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SubpolynomialCutoffsRetainGrowingHighConductorGaps
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SubpolynomialConductorRatiosSetExplicitOverlapClocks

/-!
# Super-log-log positivity on every subpolynomial conductor span

The spectral clock supplies the low-conductor floor. A cutoff-dependent cap
preserves the high-conductor gap; the raw residual pays their mixed pairing.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

private theorem profile_energy_smul (φ : ℝ → ℝ) (c : ℝ) {N : ℕ} (s : ℝ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N (s • u) = s ^ 2 * completeWeilEnergy φ c N u := by
  simp only [completeWeilEnergy, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

private theorem profile_energy_add (φ : ℝ → ℝ) (c : ℝ) {N : ℕ}
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N (x + y) = completeWeilEnergy φ c N x +
      2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, y⟫ +
        completeWeilEnergy φ c N y := by
  have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (completeWeilMatrix_isHermitian φ c N)) y x
  simp only [completeWeilEnergy, map_add, inner_add_left, inner_add_right]
  rw [hsym, real_inner_comm y (Matrix.toEuclideanLin (completeWeilMatrix φ c N) x)]
  ring

/-- Every subpolynomial conductor cutoff admits an explicit super-log-log overlap
clock retaining each logarithmic margin of exponent below one half. -/
theorem eventually_subpolynomial_span_coercivity {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ x : ℝ, x ∉ Set.Icc 0 1 → φ x = 0)
    (hM : 0 < ∫ x, φ x ^ 2) (cutoff : ℕ → ℕ)
    (hcutoff : Tendsto (fun N : ℕ => Real.log (max 1 (cutoff N) : ℕ) / Real.log N)
      atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) (hηlt : η < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      c ≤ subpolynomialProfileClock φ cutoff N →
      ∀ x ∈ conductorSubspace (cutoff N) N,
        Real.log (N : ℝ) ^ (-η) / 4 * ‖x‖ ^ 2 ≤ completeWeilEnergy φ c N x := by
  let q := (1 - 2 * η) / 4
  have hq : 0 < q := by dsimp only [q]; linarith only [hηlt]
  have hq1 : q ≤ 1 := by dsimp only [q]; linarith only [hη]
  have hqgap : 2 * q + 2 * η < 1 := by dsimp only [q]; linarith only [hηlt]
  obtain ⟨D, C, _hD, hC, hhigh⟩ :=
    exists_profile_highConductor_gap_of_terminal_and_overlap_rates hφ hsupp hM
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htlim := Real.tendsto_log_atTop.comp hLlim
  filter_upwards [eventually_raw_residual_below_logarithmic_floor hφ hsupp hM hq.le hqgap,
    eventually_subpolynomial_high_band_horizon (subpolynomialConductorHull cutoff)
      (fun N => le_max_right _ _) (tendsto_subpolynomialConductorRatio hcutoff)
      (D := D) hq hq1 hC,
    htlim.eventually (eventually_exp_le_completedConductorEnergy_up_to_explicit_clock hφ hsupp hM hη)]
    with N hrawN hhorN hfloorN
  let L := Real.log (N : ℝ)
  let t := Real.log L
  let Q := ⌊L ^ q⌋₊
  let R := subpolynomialConductorHull cutoff N
  obtain ⟨hQ2, hQR, hR6, hlogR, hhor⟩ := hhorN
  change 2 ≤ Q at hQ2
  change Q ≤ R at hQR
  change R ^ 6 ≤ N at hR6
  change 1080 * (1 + Real.log R) ≤ L at hlogR
  have hL1 : 1 ≤ L := by linarith only [hlogR, Real.log_natCast_nonneg R]
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQpow : (Q : ℝ) ≤ L ^ q := Nat.floor_le (Real.rpow_nonneg hL.le _)
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have hQQ : Q * Q ≤ N := (Nat.mul_le_mul hQR hQR).trans hRR
  have hlogQ : 18 * (1 + Real.log Q) ≤ Real.log N := by
    have hQRreal : (Q : ℝ) ≤ R := by exact_mod_cast hQR
    have hh := Real.log_le_log hQ0 hQRreal
    linarith only [hh, hlogR, Real.log_natCast_nonneg R]
  intro c hc hclock x hx
  have hxR : x ∈ conductorSubspace R N :=
    conductorSubspace_mono (le_max_left _ _) N hx
  have hcProfile : c ≤ compactProfileTailClock φ t := hclock.trans (min_le_left _ _)
  have hcT : c ≤ t ^ 2 := hcProfile.trans (compactProfileTailClock_le_sq φ t)
  have hcCap : c ≤ t / Real.sqrt ((1 + Real.log R) / L) := hclock.trans (min_le_right _ _)
  obtain ⟨_hcL, hw, hrad, hsize, hresWidth, hterminal, hgap⟩ := hhor c hc hcT hcCap
  let e := L ^ (-η)
  have he : 0 < e := Real.rpow_pos_of_pos hL _
  have he1 : e ≤ 1 := by
    exact (Real.rpow_le_rpow_of_exponent_le hL1 (neg_nonpos.mpr hη.le)).trans_eq
      (Real.rpow_zero L)
  have hres := hrawN c hc hcT hresWidth Q (by omega) hQpow
  have hfloor : ∀ m ∈ Icc 1 Q, e ≤ completedConductorEnergy φ c m := by
    intro m hm
    have hh := hfloorN c (zero_lt_one.trans_le hc) hcProfile m (mem_Icc.mp hm).1
    have heq : e = Real.exp (-η * t) := by
      dsimp only [e, t]
      rw [Real.rpow_def_of_pos hL]
      congr 1
      ring
    rw [heq]
    exact hh
  have hlowEnergy : ∀ p ∈ conductorSubspace Q N,
      e / 2 * ‖p‖ ^ 2 ≤ completeWeilEnergy φ c N p :=
    conductor_span_coercive_of_raw_budget hQ2 hQQ hlogQ
      (completeWeilMatrix_isHermitian φ c N) (completedConductorEnergy φ c) he hfloor hres
  have hhighEnergy : ∀ z ∈ conductorSubspace R N, z ∈ (conductorSubspace Q N)ᗮ →
      ‖z‖ ^ 2 ≤ completeWeilEnergy φ c N z := by
    intro z hzR hzQ
    by_cases hz0 : z = 0
    · simp only [hz0, norm_zero, zero_pow (by decide : 2 ≠ 0), completeWeilEnergy,
        map_zero, inner_zero_left, le_refl]
    have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    let y := ‖z‖⁻¹ • z
    have hyR : y ∈ conductorSubspace R N := Submodule.smul_mem _ _ hzR
    have hyQ : y ∈ (conductorSubspace Q N)ᗮ := Submodule.smul_mem _ _ hzQ
    have hyNorm : ‖y‖ = 1 := by
      dsimp only [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hzNorm), inv_mul_cancel₀ hzNorm.ne']
    obtain ⟨b, -, hby⟩ := (mem_conductorSubspace_iff (M := R) (N := N) (x := y)).mp hyR
    rw [hby] at hyQ hyNorm
    have hh := hhigh hQ2 hQR hR6 hlogR hc hw hrad hsize hterminal b hyQ hyNorm
    rw [← hby] at hh
    have hWy : 1 ≤ completeWeilEnergy φ c N y := by
      linarith only [hh, hgap, primeAdjunctionMass_nonneg R b]
    change 1 ≤ completeWeilEnergy φ c N (‖z‖⁻¹ • z) at hWy
    rw [profile_energy_smul] at hWy
    have hprod := mul_le_mul_of_nonneg_left hWy (sq_nonneg ‖z‖)
    have hscale : ‖z‖ ^ 2 * (‖z‖⁻¹ ^ 2 * completeWeilEnergy φ c N z) =
        completeWeilEnergy φ c N z := by field_simp
    rwa [mul_one, hscale] at hprod
  let p := (conductorSubspace Q N).starProjection x
  let z := x - p
  have hp : p ∈ conductorSubspace Q N := (conductorSubspace Q N).starProjection_apply_mem x
  have hzQ : z ∈ (conductorSubspace Q N)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [real_inner_comm]
    exact (conductorSubspace Q N).starProjection_inner_eq_zero x v hv
  have hzR : z ∈ conductorSubspace R N :=
    (conductorSubspace R N).sub_mem hxR (conductorSubspace_mono hQR N hp)
  have hpyth : ‖p‖ ^ 2 + ‖z‖ ^ 2 = ‖x‖ ^ 2 :=
    norm_starProjection_sq_add_sub_sq (conductorSubspace Q N) x
  have hpEnergy := hlowEnergy p hp
  have hzEnergy := hhighEnergy z hzR hzQ
  have hcross := low_packet_cross_le hQ2 hQQ hlogQ (completeWeilMatrix φ c N)
    (completedConductorEnergy φ c) he hres hp hzQ
  have hcrossCost : 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p, z⟫| ≤
      e / 8 * (‖p‖ ^ 2 + ‖z‖ ^ 2) := by
    have hh := mul_nonneg (show 0 ≤ e / 8 by positivity) (sq_nonneg (‖p‖ - ‖z‖))
    nlinarith only [hcross, hh]
  have hxSplit : x = p + z := by dsimp only [z]; abel
  have henergy := profile_energy_add φ c p z
  rw [← hxSplit] at henergy
  have hcrossLower := neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p, z⟫
  have hzReserve := mul_le_mul_of_nonneg_right he1 (sq_nonneg ‖z‖)
  have hnonneg := mul_nonneg he.le (add_nonneg (sq_nonneg ‖p‖) (sq_nonneg ‖z‖))
  have hzNonneg := mul_nonneg he.le (sq_nonneg ‖z‖)
  change e / 4 * ‖x‖ ^ 2 ≤ _
  rw [← hpyth]
  nlinarith only [hpEnergy, hzEnergy, hcrossCost, henergy, hcrossLower, hzReserve, hnonneg, hzNonneg]

#print axioms eventually_subpolynomial_span_coercivity

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
