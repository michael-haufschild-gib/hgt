import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalComplementRetainsWeightedReserves
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalSchurPairingRetainsTheCollarWeight
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot

/-!
# Full-space Weil positivity at a small critical multiple

The low conductor packet, deep-row pairing, and weighted collar reserves fit
one common critical overlap interval. The two intermediate bands absorb the
remaining couplings; the subcritical theorem covers the lower overlap range.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open BezoutValuationIncidence CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics CriticalScaleArithmeticRigidity

/-- Weighted Schur synthesis: prefix and collar coercivity are kept separate
until the residual pairing is paid. -/
theorem completeWeil_posDef_of_weighted_blocks {Q R₀ R₁ M N : ℕ} {c μ p s : ℝ}
    (hc1 : 1 ≤ c) (hp : 0 < p) (hs : 0 < s) (hMN : M ≤ N)
    (hQR₀ : Q ≤ R₀) (hR₀R₁ : R₀ ≤ R₁)
    (hlow : ∀ a : ℕ → ℝ,
      (1 / 4 : ℝ) * (∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2) ≤
        ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
          (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N),
          ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N⟫)
    (hcomp : ∀ {u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      u₀ ∈ conductorSubspace R₀ N → u₀ ∈ (conductorSubspace Q N)ᗮ →
      u₁ ∈ conductorSubspace R₁ N → u₁ ∈ (conductorSubspace R₀ N)ᗮ →
      w ∈ (conductorSubspace R₁ N)ᗮ →
      4 * ‖u₀‖ ^ 2 + (3 + μ) * ‖u₁‖ ^ 2 +
        2 * p * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
        3 * s * topCollarSeventhMass M N (primeHorizonExtension w) ≤
      completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w))
    (hpair : ∀ {u₀ : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u₀ ∈ conductorSubspace R₀ N →
      ∀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
      8 * (∑ m ∈ Icc 1 Q,
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N,
          u₀ + u₁ + w⟫ ^ 2 / completedConductorEnergy tiltedUnitSpline c m) ≤
        ‖u₀‖ ^ 2 + μ * ‖u₁‖ ^ 2 +
        p * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
        s * topCollarSeventhMass M N (primeHorizonExtension w)) :
    (completeWeilMatrix tiltedUnitSpline c N).PosDef := by
  refine posDef_of_inner_pos_on_ne_zero (completeWeilMatrix_isHermitian tiltedUnitSpline c N)
    fun x hx => ?_
  let y := (conductorSubspace Q N).starProjection x
  have hy : y ∈ conductorSubspace Q N := (conductorSubspace Q N).starProjection_apply_mem x
  have hz : x - y ∈ (conductorSubspace Q N)ᗮ := sub_starProjection_mem_orthogonal_telescoped _ x
  obtain ⟨a, -, ha⟩ := (mem_conductorSubspace_iff (M := Q) (N := N) (x := y)).mp hy
  obtain ⟨u₀, u₁, w, hz_eq, hu₀, hu₀Q, hu₁, hu₁R, hw, hnorm⟩ :=
    telescoped_three_band_orthogonal_split hQR₀ hR₀R₁ hz
  have hx_eq : x = y + (u₀ + u₁ + w) := by rw [← hz_eq]; abel
  rw [hz_eq] at hz hnorm
  have hyz : ⟪y, u₀ + u₁ + w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hy hz
  have hxnorm : ‖x‖ ^ 2 = ‖y‖ ^ 2 + ‖u₀‖ ^ 2 + ‖u₁‖ ^ 2 + ‖w‖ ^ 2 := by
    rw [hx_eq, norm_add_sq_real, hyz, mul_zero, add_zero, hnorm]
    ring
  let E := fun m => completedConductorEnergy tiltedUnitSpline c m
  let r := fun m => Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
    (normalizedRamanujanHorizonVector m N) - E m • normalizedRamanujanHorizonVector m N
  let λ := tiltedSplineSpectralFloorConstant / (2 * c ^ 7)
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hλ : 0 < λ := div_pos tiltedSplineSpectralFloorConstant_pos (by positivity)
  have hE : ∀ m ∈ Icc 1 Q, 0 < E m := by
    intro m hm
    have h := spectralFloor_conductor_energy_ge hc1 (mem_Icc.mp hm).1
    change λ ≤ E m - λ at h
    linarith only [h, hλ]
  have hsum : 0 ≤ ∑ m ∈ Icc 1 Q, E m * a m ^ 2 :=
    sum_nonneg fun m hm => mul_nonneg (hE m hm).le (sq_nonneg _)
  have hlow' := hlow a
  rw [← ha, spectralFloorWeilMatrix_inner] at hlow'
  have hvz : ∀ m ∈ Icc 1 Q, ⟪normalizedRamanujanHorizonVector m N, u₀ + u₁ + w⟫ = 0 := by
    intro m hm
    exact Submodule.inner_right_of_mem_orthogonal
      (mem_conductorSubspace_normalizedRamanujanHorizonVector hm) hz
  have hcross : ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) y,
      u₀ + u₁ + w⟫ = ∑ m ∈ Icc 1 Q, a m * ⟪r m, u₀ + u₁ + w⟫ := by
    rw [ha, map_sum, sum_inner]
    refine sum_congr rfl fun m hm => ?_
    rw [map_smul, real_inner_smul_left]
    congr 1
    dsimp only [r]
    rw [inner_sub_left, real_inner_smul_left, hvz m hm, mul_zero, sub_zero]
  have hcrossabs := two_abs_weighted_sum_le (a := a)
    (t := fun m => ⟪r m, u₀ + u₁ + w⟫) hE
  rw [← hcross] at hcrossabs
  have hcomp' := hcomp hu₀ hu₀Q hu₁ hu₁R hw
  have hpair' := hpair hu₀ u₁ w
  have hsplit := hermitian_inner_add_eq_telescoped
    (completeWeilMatrix_isHermitian tiltedUnitSpline c N) y (u₀ + u₁ + w)
  have hneg := neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) y,
    u₀ + u₁ + w⟫
  let P := ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2
  let S7 := topCollarSeventhMass M N (primeHorizonExtension w)
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS7 : 0 ≤ S7 := topCollarSeventhMass_nonneg _ _ _
  have hfull : λ * ‖y‖ ^ 2 + 3 * ‖u₀‖ ^ 2 + 3 * ‖u₁‖ ^ 2 + p * P + 2 * s * S7 ≤
      completeWeilEnergy tiltedUnitSpline c N x := by
    rw [← hx_eq] at hsplit
    change completeWeilEnergy tiltedUnitSpline c N x = completeWeilEnergy tiltedUnitSpline c N y +
      completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w) + _ at hsplit
    change (1 / 4 : ℝ) * (∑ m ∈ Icc 1 Q, E m * a m ^ 2) ≤
      completeWeilEnergy tiltedUnitSpline c N y - λ * ‖y‖ ^ 2 at hlow'
    change 8 * (∑ m ∈ Icc 1 Q, ⟪r m, u₀ + u₁ + w⟫ ^ 2 / E m) ≤
      ‖u₀‖ ^ 2 + μ * ‖u₁‖ ^ 2 + p * P + s * S7 at hpair'
    change 4 * ‖u₀‖ ^ 2 + (3 + μ) * ‖u₁‖ ^ 2 + 2 * p * P + 3 * s * S7 ≤ _ at hcomp'
    linarith only [hlow', hcomp', hpair', hcrossabs, hsplit, hneg, hsum]
  have hw_mass : ‖w‖ ^ 2 ≤ P + S7 := by
    have hS := sum_sq_Ioc_le_topCollarSeventhMass M N (primeHorizonExtension w)
    have hsplitw : ‖w‖ ^ 2 = P + ∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2 := by
      rw [← sum_primeHorizonExtension_sq w, Ioc_eq_Icc_sdiff_Icc_telescoped M N, add_comm]
      exact (sum_sdiff (Icc_subset_Icc le_rfl hMN)).symm
    linarith only [hsplitw, hS]
  let δ := min λ (min 3 (min p (2 * s)))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδλ : δ ≤ λ := min_le_left _ _
  have hδ3 : δ ≤ 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hδp : δ ≤ p := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδs : δ ≤ 2 * s := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hwy : δ * ‖w‖ ^ 2 ≤ p * P + 2 * s * S7 := by
    have h₁ := mul_le_mul_of_nonneg_left hw_mass hδ.le
    have h₂ := mul_le_mul_of_nonneg_right hδp hP
    have h₃ := mul_le_mul_of_nonneg_right hδs hS7
    linarith only [h₁, h₂, h₃]
  have hfloor : δ * ‖x‖ ^ 2 ≤ completeWeilEnergy tiltedUnitSpline c N x := by
    rw [hxnorm]
    have h₁ := mul_le_mul_of_nonneg_right hδλ (sq_nonneg ‖y‖)
    have h₂ := mul_le_mul_of_nonneg_right hδ3 (sq_nonneg ‖u₀‖)
    have h₃ := mul_le_mul_of_nonneg_right hδ3 (sq_nonneg ‖u₁‖)
    linarith only [hfull, hwy, h₁, h₂, h₃]
  exact (mul_pos hδ (sq_pos_of_pos (norm_pos_iff.mpr hx))).trans_le hfloor


/-- The complete tilted-spline Weil matrix is eventually positive definite on
the whole horizon space at one fixed positive critical multiple. -/
theorem exists_critical_multiple_completeWeilMatrix_posDef :
    ∃ K : ℝ, 0 < K ∧ 2 * K ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
        c ≤ 2 * K * Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
        (completeWeilMatrix tiltedUnitSpline c N).PosDef := by
  let D := explicitConductorCutoffConstant
  let g := dyadicTopMassConstant
  let H := 256 * Real.exp 2 + 4
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  have hg : 0 < g := dyadicTopMassConstant_pos
  have hH : 0 < H := by dsimp only [H]; positivity
  obtain ⟨Kcomp, hKcomp, hKcomp1, hcomp⟩ := exists_critical_multiple_weighted_complement
  obtain ⟨Kpair, hKpair, hKpairHalf, hpair⟩ := exists_critical_multiple_schur_payment
    (show 0 < 1 / (32 * D) by positivity) (show 0 < g / 64 by positivity)
  obtain ⟨Klow, hKlow, hKlowHalf, hlow⟩ :=
    exists_critical_multiple_low_packet_and_collar_budget (show (0 : ℝ) < 1 by norm_num)
  let K := min Kcomp (min Kpair Klow)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKc : K ≤ Kcomp := min_le_left _ _
  have hKp : K ≤ Kpair := (min_le_right _ _).trans (min_le_left _ _)
  have hKl : K ≤ Klow := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨K, hK, by linarith only [hKc, hKcomp1], ?_⟩
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hcomp, hpair, hlow,
    eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_eighth
      (by norm_num : (0 : ℝ) < 1 / 16)
      (by change (1 / 16 : ℝ) < 1 / 8; norm_num : (1 / 16 : ℝ) < oneEighthPowerLogExponent),
    eventually_three_cutoff_bounds_one_ninth
      (by norm_num : (0 : ℝ) < 13 / 32) (by norm_num : (13 / 32 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 4096) (le_refl (1 / 4096 : ℝ)),
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually_ge_atTop (2 + 8 * H),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 1 / 2) 1)]
    with N hcompN hpairN hlowN hsubN hcut hLX hlarge hhalf
  intro c hc1 hc
  let L := Real.log (N : ℝ)
  let t := 1 + Real.log L
  let θ := 1 / t ^ 5
  let Q := ⌊L ^ (13 / 32 : ℝ)⌋₊
  let R₀ := ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊
  let R₁ := ⌊(N : ℝ) ^ θ⌋₊
  let T := linearDefectCutoff c
  let M := N / T
  change 2 + 8 * H ≤ L at hlarge
  have hL1 : 1 ≤ L := by linarith only [hlarge, hH]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcrange {K' : ℝ} (hKK' : K ≤ K') : c ≤ 2 * K' * L ^ (1 / 8 : ℝ) := hc.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKK' zero_le_two)
      (Real.rpow_nonneg hL0.le (1 / 8 : ℝ)))
  have hcc := hcrange hKc
  have hcp := hcrange hKp
  have hcl := hcrange hKl
  by_cases hsub : c ≤ L ^ (1 / 16 : ℝ)
  · exact hsubN c hc1 hsub
  have hclo : L ^ (1 / 16 : ℝ) ≤ c := le_of_not_ge hsub
  have hcroot : c ≤ L ^ (1 / 8 : ℝ) := hcc.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hKcomp1
      (Real.rpow_nonneg hL0.le (1 / 8 : ℝ)))
  have hcL : c ≤ L := hcroot.trans ((Real.rpow_le_rpow_of_exponent_le hL1
    (by norm_num : (1 / 8 : ℝ) ≤ 1)).trans_eq (Real.rpow_one L))
  have ht0 : 0 < t := by
    have := Real.log_nonneg hL1
    dsimp only [t]; positivity
  have hN1 : 1 ≤ N := by
    by_contra hn
    have : N = 0 := by omega
    subst this
    simp [L] at hL0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hQ2, hQR₀, -, -, -, -, -, -, -, -, -, -⟩ := hcut
  have hhalf' : t ^ 5 ≤ L ^ (1 / 2 : ℝ) := by simpa only [one_mul] using hhalf
  have hLhalf : L ^ (1 / 2 : ℝ) ≤ θ * L := by
    have h := mul_le_mul_of_nonneg_right hhalf' (Real.rpow_nonneg hL0.le (1 / 2 : ℝ))
    have he : L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [he] at h
    have h' := (le_div_iff₀ (show 0 < t ^ 5 by positivity)).mpr (by linarith only [h] :
      L ^ (1 / 2 : ℝ) * t ^ 5 ≤ L)
    change L ^ (1 / 2 : ℝ) ≤ 1 / t ^ 5 * L
    exact h'.trans_eq (by ring)
  have hR₀R₁ : R₀ ≤ R₁ := by
    apply Nat.floor_mono
    rw [Real.rpow_def_of_pos hN0]
    exact Real.exp_le_exp.mpr (hLhalf.trans_eq (by dsimp only [L]; ring))
  have hL18 : L ^ 18 ≤ (N : ℝ) := by
    calc
      _ ≤ ((N : ℝ) ^ (1 / 36 : ℝ)) ^ 18 := pow_le_pow_left₀ hL0.le hLX 18
      _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 36 : ℝ)),
          ← Real.rpow_mul hN0.le]; norm_num
      _ ≤ N := (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
  have hstrip : 2 * linearPrimeStrip c ≤ M := by
    obtain ⟨hT3, -, -, hTup⟩ := linearDefectCutoff_bounds hc1
    change 3 ≤ T at hT3
    have hT : (T : ℝ) ≤ H * L := hTup.trans (mul_le_mul_of_nonneg_left hcL hH.le)
    have hs := linearPrimeStrip_le_four_mul hc1 hcL
    have hprod : ((2 * linearPrimeStrip c * T : ℕ) : ℝ) ≤ N := by
      push_cast
      calc
        _ ≤ (2 * (4 * L)) * (H * L) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs zero_le_two) hT (Nat.cast_nonneg T) (by positivity)
        _ = (8 * H) * L ^ 2 := by ring
        _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_right (by linarith only [hlarge]) (sq_nonneg _)
        _ = L ^ 3 := by ring
        _ ≤ L ^ 18 := pow_le_pow_right₀ hL1 (by norm_num)
        _ ≤ N := hL18
    apply (Nat.le_div_iff_mul_le (show 0 < T by omega)).mpr
    exact_mod_cast hprod
  let p := (1 / (32 * D)) * L / t ^ 5
  let s := (g / 64) * L / c ^ 7
  have hp : 0 < p := by dsimp only [p]; positivity
  have hs : 0 < s := by dsimp only [s]; positivity
  refine completeWeil_posDef_of_weighted_blocks (μ := L ^ (1 / 2 : ℝ) / 32)
    (p := p) (s := s) hc1 hp hs (Nat.div_le_self N T) hQR₀ hR₀R₁
    (hlowN c hc1 hcl).1 ?_ ?_
  · intro u₀ u₁ w hu₀ hu₀Q hu₁ hu₁R hw
    have h := hcompN c hclo hcc u₀ hu₀ hu₀Q u₁ hu₁ hu₁R w hw
    convert h using 1 <;> dsimp only [p, s, θ, D, g, L, t] <;> ring
  · intro u₀ hu₀ u₁ w
    exact hpairN c hc1 hcp M (Nat.div_le_self N T) hstrip u₀ hu₀ u₁ w

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_critical_multiple_completeWeilMatrix_posDef

