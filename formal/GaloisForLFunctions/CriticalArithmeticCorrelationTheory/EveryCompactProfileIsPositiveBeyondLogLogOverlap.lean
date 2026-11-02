import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryCompactProfileHasAnExplicitTailClock
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LogarithmicFloorsControlQuadraticOverlapResiduals
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AlmostPolynomialConductorSpansRetainHighEnergyGaps

/-!
# Every compact profile is positive beyond log-log overlap

An explicit clock from the weighted logarithmic Fourier tail grows faster than
`log log N`. It preserves logarithmic energy floors on almost-polynomial conductor
spans. A small polylogarithmic block pays the residual; the complementary block
retains a growing prime-adjunction gap.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

private theorem conductor_analysis_frame_lower {Q N : ℕ} (hQ : 2 ≤ Q)
    (hQN : Q * Q ≤ N) (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) (hx : x ∈ conductorSubspace Q N) :
    (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤
      ∑ m ∈ Icc 1 Q, ⟪normalizedRamanujanHorizonVector m N, x⟫ ^ 2 := by
  by_cases hx0 : x = 0
  · simp only [hx0, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      inner_zero_right, sum_const_zero, le_refl]
  have hxpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  obtain ⟨a, -, hax⟩ := (mem_conductorSubspace_iff (M := Q) (N := N) (x := x)).mp hx
  have hcoef := (half_and_three_halves_riesz_of_log_le hQ hQN hlog a).1
  rw [← hax] at hcoef
  have hnorm : ‖x‖ ^ 2 = ∑ m ∈ Icc 1 Q,
      a m * ⟪normalizedRamanujanHorizonVector m N, x⟫ := by
    calc
      _ = ⟪x, x⟫ := (real_inner_self_eq_norm_sq x).symm
      _ = ⟪∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N, x⟫ :=
        congrArg (fun y => ⟪y, x⟫) hax
      _ = _ := by rw [sum_inner]; simp only [real_inner_smul_left]
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 Q) a
    (fun m => ⟪normalizedRamanujanHorizonVector m N, x⟫)
  rw [← hnorm] at hcs
  have hmul := mul_le_mul_of_nonneg_right
    (show (∑ m ∈ Icc 1 Q, a m ^ 2) ≤ 2 * ‖x‖ ^ 2 by linarith only [hcoef])
    (sum_nonneg (s := Icc 1 Q) fun m _ => sq_nonneg ⟪normalizedRamanujanHorizonVector m N, x⟫)
  have hprod : ‖x‖ ^ 2 * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 *
      (2 * ∑ m ∈ Icc 1 Q, ⟪normalizedRamanujanHorizonVector m N, x⟫ ^ 2) := by
    calc
      _ = (‖x‖ ^ 2) ^ 2 := (sq _).symm
      _ ≤ _ := hcs.trans hmul
      _ = _ := by ring
  have hh := (mul_le_mul_iff_right₀ hxpos).mp hprod
  linarith only [hh]

private theorem conductor_span_coercive_of_relative_budget {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N) (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    {A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} (hA : A.IsHermitian)
    (E : ℕ → ℝ) {e : ℝ} (he : 0 < e) (hfloor : ∀ m ∈ Icc 1 Q, e ≤ E m)
    (hbudget : (∑ m ∈ Icc 1 Q,
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ^ 2 / E m ^ 2) ≤ 1 / 16) :
    ∀ x ∈ conductorSubspace Q N, e / 2 * ‖x‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin A x, x⟫ := by
  classical
  let I := ↥(Icc 1 Q)
  let V := conductorSubspace Q N
  let v : I → V := fun m => ⟨conductorBasisFamily Q N m, Submodule.subset_span ⟨m, rfl⟩⟩
  have hframe (x : V) : (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ ∑ m : I, ⟪v m, x⟫ ^ 2 := by
    change (1 / 2 : ℝ) * ‖(x : EuclideanSpace ℝ (PrimeHorizonIndex N))‖ ^ 2 ≤
      ∑ m : ↥(Icc 1 Q), ⟪normalizedRamanujanHorizonVector m.1 N,
        (x : EuclideanSpace ℝ (PrimeHorizonIndex N))⟫ ^ 2
    rw [sum_coe_sort (Icc 1 Q) (fun m : ℕ =>
      ⟪normalizedRamanujanHorizonVector m N, (x : EuclideanSpace ℝ (PrimeHorizonIndex N))⟫ ^ 2)]
    exact conductor_analysis_frame_lower hQ hQN hlog x x.property
  have hsmall : (∑ m : I,
      ‖Matrix.toEuclideanLin A (v m : EuclideanSpace ℝ (PrimeHorizonIndex N)) -
        E m.1 • (v m : EuclideanSpace ℝ (PrimeHorizonIndex N))‖ ^ 2 / E m.1 ^ 2) ≤
        (1 / 2 : ℝ) / 8 := by
    change (∑ m : ↥(Icc 1 Q),
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m.1 N) -
        E m.1 • normalizedRamanujanHorizonVector m.1 N‖ ^ 2 / E m.1 ^ 2) ≤ (1 / 2 : ℝ) / 8
    rw [sum_coe_sort (Icc 1 Q) (fun m : ℕ =>
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ^ 2 / E m ^ 2)]
    convert hbudget using 1; norm_num
  have hbound := inner_ge_half_floor_on_subspace_of_relative_frame_budget
    (Matrix.toEuclideanLin A) (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    V v (fun m : I => E m.1) (by norm_num : (0 : ℝ) < 1 / 2) he hframe
    (fun m => hfloor m.1 m.property) hsmall
  intro x hx
  exact hbound ⟨x, hx⟩

/-- A common positive conductor floor and a summed raw residual budget give
coercivity on the whole finite conductor span. -/
theorem conductor_span_coercive_of_raw_budget {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N) (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    {A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} (hA : A.IsHermitian)
    (E : ℕ → ℝ) {e : ℝ} (he : 0 < e) (hfloor : ∀ m ∈ Icc 1 Q, e ≤ E m)
    (hraw : (∑ m ∈ Icc 1 Q,
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
        E m • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤ e ^ 2 / 128) :
    ∀ x ∈ conductorSubspace Q N, e / 2 * ‖x‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin A x, x⟫ := by
  apply conductor_span_coercive_of_relative_budget hQ hQN hlog hA E he hfloor
  calc
    _ ≤ ∑ m ∈ Icc 1 Q,
        ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
          E m • normalizedRamanujanHorizonVector m N‖ ^ 2 / e ^ 2 := by
      refine sum_le_sum fun m hm => ?_
      exact div_le_div₀ (sq_nonneg _) le_rfl (sq_pos_of_pos he)
        (pow_le_pow_left₀ he.le (hfloor m hm) 2)
    _ = (∑ m ∈ Icc 1 Q,
        ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N) -
          E m • normalizedRamanujanHorizonVector m N‖ ^ 2) / e ^ 2 := (sum_div _ _ _).symm
    _ ≤ 1 / 16 := (div_le_iff₀ (sq_pos_of_pos he)).mpr
      (by nlinarith only [hraw, sq_nonneg e])

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

/-- Every nonzero compact `C²` profile is uniformly coercive beyond every fixed log-log
multiple on an almost-polynomial conductor span. The explicit overlap clock is independent
of both the margin exponent and the conductor-cutoff exponent. -/
theorem eventually_explicit_clock_almost_polynomial_span_coercivity {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ x : ℝ, x ∉ Set.Icc 0 1 → φ x = 0)
    (hM : 0 < ∫ x, φ x ^ 2) {η κ : ℝ} (hη : 0 < η) (hηlt : η < 1 / 2)
    (hκ : 2 < κ) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      c ≤ compactProfileTailClock φ (Real.log (Real.log (N : ℝ))) →
      ∀ x ∈ conductorSubspace (almostPolynomialConductorCutoff κ N) N,
        Real.log (N : ℝ) ^ (-η) / 4 * ‖x‖ ^ 2 ≤ completeWeilEnergy φ c N x := by
  let q := (1 - 2 * η) / 4
  have hq : 0 < q := by dsimp only [q]; linarith only [hηlt]
  have hqgap : 2 * q + 2 * η < 1 := by dsimp only [q]; linarith only [hηlt]
  obtain ⟨H, C, hH, hC, hhigh⟩ := exists_profile_completeWeilEnergy_ge_adjunction_and_log hφ hsupp hM
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htlim := Real.tendsto_log_atTop.comp hLlim
  filter_upwards [eventually_raw_residual_below_logarithmic_floor hφ hsupp hM hq.le hqgap,
    eventually_almost_polynomial_high_band_horizon (H := H) hq hκ hC,
    htlim.eventually (eventually_exp_le_completedConductorEnergy_up_to_explicit_clock hφ hsupp hM hη)]
    with N hrawN hhorN hfloorN
  let L := Real.log (N : ℝ)
  let t := Real.log L
  let Q := ⌊L ^ q⌋₊
  let R := almostPolynomialConductorCutoff κ N
  obtain ⟨hQ2, hQR, hR6, hlogR, hhor⟩ := hhorN
  change 2 ≤ Q at hQ2
  change Q ≤ R at hQR
  change R ^ 6 ≤ N at hR6
  change 36 * (1 + Real.log R) ≤ L at hlogR
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
  intro c hc hclock x hxR
  have hcT : c ≤ t ^ 2 := hclock.trans (compactProfileTailClock_le_sq φ t)
  have hcLog : c ≤ t * Real.log t := hclock.trans (compactProfileTailClock_le_mul_log φ t)
  obtain ⟨hcL, hw, hrad, hsize, hresWidth, hsmall, hgap⟩ := hhor c hc hcT hcLog
  let e := L ^ (-η)
  have he : 0 < e := Real.rpow_pos_of_pos hL _
  have he1 : e ≤ 1 := by
    exact (Real.rpow_le_rpow_of_exponent_le hL1 (neg_nonpos.mpr hη.le)).trans_eq
      (Real.rpow_zero L)
  have hres := hrawN c hc hcT hresWidth Q (by omega) hQpow
  have hfloor : ∀ m ∈ Icc 1 Q, e ≤ completedConductorEnergy φ c m := by
    intro m hm
    have hh := hfloorN c (zero_lt_one.trans_le hc) hclock m (mem_Icc.mp hm).1
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
    have hh := hhigh hQ2 hQR hR6 hlogR hc hcL hw hrad hsize hsmall b hyQ
      (by rw [hyNorm]; norm_num) hyNorm.le
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

/-- The actual overlap range exceeds every fixed multiple of `log log N`. -/
theorem tendsto_explicit_profile_overlap_div_loglog_atTop (φ : ℝ → ℝ) :
    Tendsto (fun N : ℕ => compactProfileTailClock φ (Real.log (Real.log (N : ℝ))) /
      Real.log (Real.log (N : ℝ))) atTop atTop := by
  have htlim : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact (tendsto_compactProfileTailClock_div_atTop φ).comp htlim

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
