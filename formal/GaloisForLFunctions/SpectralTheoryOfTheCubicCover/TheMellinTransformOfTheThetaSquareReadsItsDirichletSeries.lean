import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheThetaCoefficientsHaveTheHeckeBound

/-!
# The Mellin transform of the theta square reads its Dirichlet series

The constant term of `θ_s²` at height `v` is `b(v, 0)² + R(v)` (`tsum_amplitude_mul_neg`), with
`b(v, 0) = c v^{2/3}` and the nonconstant part

`R(v) = Σ_{h ≠ 0} b(v, h) b(v, −h) = Σ_{h ≠ 0} T_s(h)² v² K_{1/3}(4π|ξ_h| v)²`.

Its Mellin transform is the Dirichlet series of the squared coefficients
(`integral_thetaSqRemainder`): for `Re s > 4`,

`∫_0^∞ v^s R(v) v^{−3} dv = M(s) Σ_{h ≠ 0} T_s(h)² (4π|ξ_h|)^{−s}`,   `M(s) = ∫_0^∞ t^{s−1} K_{1/3}(t)² dt`.

* `norm_besselK_le`: `|K_{1/3}(x)| ≤ C x^{−1/3} e^{−x/2}` for `x > 0` (Schläfli integral,
  `t + x²/(4t) ≥ t/2 + x/2`).
* `besselSqMellin` (`M`): convergent and holomorphic on `Re s > 2/3`
  (`besselSqMellin_differentiableAt`), and `M(4/3) ≠ 0` (`besselSqMellin_four_thirds_ne_zero`:
  `K_{1/3}` is real and positive).
* `summable_cuspFrequency_rpow`: `Σ_{h ≠ 0} |ξ_h|^{−t}` converges for `t > 2` (`3ℤ[ω]` is a lattice
  of rank two in `ℂ`).
* The interchange of sum and integral is absolute by the Hecke bound `|T_s(h)|² ≪ (1 + |ξ_h|)²`.
-/

noncomputable section

open MeasureTheory Filter Asymptotics
open scoped BigOperators Classical Topology

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein

/-! ### The cubic Bessel kernel -/

/-- `|K_{1/3}(x)| ≤ C x^{−1/3} e^{−x/2}` for `x > 0`. -/
theorem norm_besselK_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
    ‖schlafliBesselK (1 / 3) x‖ ≤ C * x ^ (-(1 : ℝ) / 3) * Real.exp (-x / 2) := by
  let g : ℝ → ℝ := fun t => t ^ (-(2 : ℝ) / 3) * Real.exp (-t / 2)
  have hg : IntegrableOn g (Set.Ioi 0) := by
    have hh := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := -(2 : ℝ) / 3) (p := (1 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    simpa only [g, Real.rpow_one, show ∀ t : ℝ, -(1 / 2) * t = -t / 2 by intro t; ring] using hh
  have hg0 : 0 ≤ ∫ t in Set.Ioi 0, g t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  refine ⟨(1 / 2) * (2 : ℝ) ^ ((1 : ℝ) / 3) * ∫ t in Set.Ioi 0, g t, by positivity, fun x hx => ?_⟩
  have hpoint (t : ℝ) (ht : 0 < t) : cubicSchlafliDensity x t ≤ Real.exp (-x / 2) * g t := by
    have hfrac : x / 2 - t / 2 ≤ x ^ 2 / (4 * t) :=
      (le_div_iff₀ (by positivity : 0 < 4 * t)).mpr
        (by nlinarith only [sq_nonneg (x - t), sq_nonneg t])
    calc
      _ ≤ t ^ (-(2 : ℝ) / 3) * Real.exp (-x / 2 + -t / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hfrac]))
          (Real.rpow_nonneg ht.le _)
      _ = _ := by rw [Real.exp_add]; dsimp [g]; ring
  have hb := setIntegral_mono_on (cubicSchlafliDensity_integrable x)
    (hg.const_mul (Real.exp (-x / 2))) measurableSet_Ioi hpoint
  rw [integral_const_mul] at hb
  have hsplit : (x / 2) ^ (-(1 : ℝ) / 3) = x ^ (-(1 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [Real.div_rpow hx.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
    norm_num
  rw [schlafliBesselK_one_third_norm x hx, hsplit]
  calc _ ≤ (1 / 2 : ℝ) * (x ^ (-(1 : ℝ) / 3) * (2 : ℝ) ^ ((1 : ℝ) / 3)) *
        (Real.exp (-x / 2) * ∫ t in Set.Ioi 0, g t) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem besselK_continuousOn : ContinuousOn (fun x : ℝ => schlafliBesselK (1 / 3) x) (Set.Ioi 0) :=
  fun x hx => (schlafliBesselK_cubic_hasDerivAt x hx).continuousAt.continuousWithinAt

/-- `K_{1/3}(t)²`. -/
def besselSq (t : ℝ) : ℂ := schlafliBesselK (1 / 3) t ^ 2

/-- `M(s) = ∫_0^∞ t^{s−1} K_{1/3}(t)² dt`. -/
def besselSqMellin (s : ℂ) : ℂ := mellin besselSq s

theorem besselSq_locallyIntegrableOn : LocallyIntegrableOn besselSq (Set.Ioi 0) :=
  (besselK_continuousOn.pow 2).locallyIntegrableOn measurableSet_Ioi

theorem besselSq_isBigO_top : besselSq =O[atTop] fun t => Real.exp (-1 * t) := by
  obtain ⟨C, hC, hK⟩ := norm_besselK_le
  refine IsBigO.of_bound (C ^ 2) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, besselSq, norm_pow]
  have hr : t ^ (-(1 : ℝ) / 3) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num)
  have hr0 : 0 ≤ t ^ (-(1 : ℝ) / 3) := Real.rpow_nonneg ht0.le _
  have he : Real.exp (-t / 2) ^ 2 = Real.exp (-1 * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc ‖schlafliBesselK (1 / 3) t‖ ^ 2
      ≤ (C * t ^ (-(1 : ℝ) / 3) * Real.exp (-t / 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hK t ht0) 2
    _ ≤ (C * 1 * Real.exp (-t / 2)) ^ 2 := by gcongr
    _ = C ^ 2 * Real.exp (-1 * t) := by rw [mul_one, mul_pow, he]

theorem besselSq_isBigO_bot : besselSq =O[𝓝[>] 0] (· ^ (-(2 / 3 : ℝ))) := by
  obtain ⟨C, hC, hK⟩ := norm_besselK_le
  refine IsBigO.of_bound (C ^ 2) ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), besselSq, norm_pow]
  have hr0 : 0 ≤ t ^ (-(1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
  have he : (t ^ (-(1 : ℝ) / 3)) ^ 2 = t ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have hexp : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  calc ‖schlafliBesselK (1 / 3) t‖ ^ 2
      ≤ (C * t ^ (-(1 : ℝ) / 3) * Real.exp (-t / 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hK t ht) 2
    _ ≤ (C * t ^ (-(1 : ℝ) / 3) * 1) ^ 2 := by gcongr
    _ = C ^ 2 * t ^ (-(2 / 3 : ℝ)) := by rw [mul_one, mul_pow, he]

theorem besselSqMellin_convergent (s : ℂ) (hs : 2 / 3 < s.re) : MellinConvergent besselSq s :=
  mellinConvergent_of_isBigO_rpow_exp one_pos besselSq_locallyIntegrableOn besselSq_isBigO_top
    besselSq_isBigO_bot hs

/-- `M` is holomorphic on `Re s > 2/3`. -/
theorem besselSqMellin_differentiableAt (s : ℂ) (hs : 2 / 3 < s.re) :
    DifferentiableAt ℂ besselSqMellin s :=
  mellin_differentiableAt_of_isBigO_rpow_exp one_pos besselSq_locallyIntegrableOn
    besselSq_isBigO_top besselSq_isBigO_bot hs

/-- `M(4/3) ≠ 0`: its real part is the integral of the positive function `t^{1/3} K_{1/3}(t)²`. -/
theorem besselSqMellin_four_thirds_ne_zero : besselSqMellin (4 / 3) ≠ 0 := by
  obtain ⟨c, hc, hK⟩ := schlafliBesselK_one_third_exp_lower
  have hconv := besselSqMellin_convergent (4 / 3) (by norm_num)
  have hpt : ∀ t : ℝ, 0 < t → ((t : ℂ) ^ ((4 / 3 : ℂ) - 1) • besselSq t).re =
      t ^ ((1 : ℝ) / 3) * (schlafliBesselK (1 / 3) t).re ^ 2 := by
    intro t ht
    have hK : schlafliBesselK (1 / 3) t = ((schlafliBesselK (1 / 3) t).re : ℂ) := by
      rw [schlafliBesselK_one_third_ofReal t ht, Complex.ofReal_re]
    have hc : (t : ℂ) ^ ((4 / 3 : ℂ) - 1) = ((t ^ ((1 : ℝ) / 3) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow ht.le]
      norm_num
    rw [besselSq, hK, hc, smul_eq_mul, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.ofReal_re]
  have hpos : ∀ t : ℝ, 0 < t → 0 < t ^ ((1 : ℝ) / 3) * (schlafliBesselK (1 / 3) t).re ^ 2 := by
    intro t ht
    have h1 := hK t ht
    have h2 : 0 < c * Real.exp (-9 * t / 4) := by positivity
    exact mul_pos (Real.rpow_pos_of_pos ht _) (pow_pos (h2.trans_le h1) 2)
  intro h0
  have hre : (∫ t in Set.Ioi (0 : ℝ), (((t : ℂ) ^ ((4 / 3 : ℂ) - 1) • besselSq t).re)) = 0 := by
    have h1 := integral_re hconv
    simp only [RCLike.re_to_complex] at h1
    rw [h1]
    change (besselSqMellin (4 / 3)).re = 0
    rw [h0, Complex.zero_re]
  have hI : IntegrableOn (fun t : ℝ => (((t : ℂ) ^ ((4 / 3 : ℂ) - 1) • besselSq t).re))
      (Set.Ioi 0) := hconv.re
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun t : ℝ => (((t : ℂ) ^ ((4 / 3 : ℂ) - 1) • besselSq t).re) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      simp only [Pi.zero_apply]
      rw [hpt t ht]
      exact (hpos t ht).le
  have hsupp : Function.support (fun t : ℝ => (((t : ℂ) ^ ((4 / 3 : ℂ) - 1) • besselSq t).re)) ∩
      Set.Ioi 0 = Set.Ioi 0 := by
    refine Set.inter_eq_right.mpr fun t ht => ?_
    rw [Function.mem_support, hpt t ht]
    exact (hpos t ht).ne'
  have hlt := (setIntegral_pos_iff_support_of_nonneg_ae hnn hI).mpr (by
    rw [hsupp, Real.volume_Ioi]
    exact ENNReal.zero_lt_top)
  rw [hre] at hlt
  exact lt_irrefl _ hlt

/-! ### A lattice sum -/

instance periodLattice_discrete : DiscreteTopology periodLattice := by
  unfold periodLattice
  infer_instance

instance periodLattice_isZLattice : IsZLattice ℝ periodLattice := by
  unfold periodLattice
  infer_instance

/-- `|ξ_h| = |3h| / (3 |3λ|)`. -/
theorem norm_cuspFrequency_eq (h : O) :
    ‖cuspFrequency h‖ = ‖(periodPoint h : ℂ)‖ / (3 * ‖(3 : ℂ) * ringComplex traceLambda‖) := by
  rw [periodPoint_val, cuspFrequency, norm_div, norm_mul, norm_mul (3 : ℂ) (ringComplex h)]
  have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
  rw [h3]
  field_simp

/-- `Σ_{h ≠ 0} |ξ_h|^{−t}` converges for `t > 2`. -/
theorem summable_cuspFrequency_rpow {t : ℝ} (ht : 2 < t) :
    Summable (fun h : O => ‖cuspFrequency h‖ ^ (-t)) := by
  have hrank : Module.finrank ℤ periodLattice = 2 := by
    rw [ZLattice.rank ℝ periodLattice, Complex.finrank_real_complex]
  have hL := ZLattice.summable_norm_rpow (L := periodLattice) (-t) (by rw [hrank]; push_cast; linarith)
  have hc := hL.comp_injective periodPoint_bijective.injective
  set D := 3 * ‖(3 : ℂ) * ringComplex traceLambda‖ with hD
  have hD0 : 0 < D := by
    have : (3 : ℂ) * ringComplex traceLambda ≠ 0 :=
      mul_ne_zero (by norm_num) (ringComplex_ne_zero traceLambda_ne_zero)
    positivity
  refine (hc.div_const (D ^ (-t))).congr fun h => ?_
  simp only [Function.comp_apply]
  rw [norm_cuspFrequency_eq, Real.div_rpow (norm_nonneg _) hD0.le]
  rfl

/-- `Σ_{h ≠ 0} |T_s(h)|² |ξ_h|^{−σ}` converges for `σ > 4` (Hecke bound). -/
theorem summable_sourceCoefficient_sq_rpow {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else
      ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 * ‖cuspFrequency h‖ ^ (-σ)) := by
  obtain ⟨C, hC, hb⟩ := sourceCoefficient_sq_le
  set m := ‖(3 : ℂ) * ringComplex traceLambda‖ with hm
  have hs := (summable_cuspFrequency_rpow (t := σ - 2) (by linarith)).mul_left (C * (m + 1) ^ 2)
  refine Summable.of_nonneg_of_le (fun h => ?_) (fun h => ?_) hs
  · split_ifs
    · exact le_rfl
    · positivity
  · split_ifs with hh
    · positivity
    have hξ : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    have hlow := cuspFrequency_norm_lower h hh
    have hm0 : 0 < m :=
      norm_pos_iff.mpr (mul_ne_zero (by norm_num) (ringComplex_ne_zero traceLambda_ne_zero))
    have h1 : 1 + ‖cuspFrequency h‖ ≤ (m + 1) * ‖cuspFrequency h‖ := by
      have h2 := mul_le_mul_of_nonneg_left hlow hm0.le
      rw [← hm, mul_inv_cancel₀ hm0.ne'] at h2
      nlinarith
    have hpow : ‖cuspFrequency h‖ ^ 2 * ‖cuspFrequency h‖ ^ (-σ) = ‖cuspFrequency h‖ ^ (-(σ - 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hξ]
      congr 1
      push_cast
      ring
    calc ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 * ‖cuspFrequency h‖ ^ (-σ)
        ≤ C * (1 + ‖cuspFrequency h‖) ^ 2 * ‖cuspFrequency h‖ ^ (-σ) := by
          gcongr
          exact hb h hh
      _ ≤ C * ((m + 1) * ‖cuspFrequency h‖) ^ 2 * ‖cuspFrequency h‖ ^ (-σ) := by gcongr
      _ = C * (m + 1) ^ 2 * (‖cuspFrequency h‖ ^ 2 * ‖cuspFrequency h‖ ^ (-σ)) := by ring
      _ = _ := by rw [hpow]

/-! ### The Mellin link -/

/-- The nonconstant part `R(v) = Σ_{h ≠ 0} b(v, h) b(v, −h)` of the constant term of `θ_s²`. -/
def thetaSqRemainder (v : ℝ) : ℂ :=
  ∑' h : O, if h = 0 then 0 else rationalSourceModeAmplitude v h * rationalSourceModeAmplitude v (-h)

/-- The Dirichlet series `Σ_{h ≠ 0} T_s(h)² (4π|ξ_h|)^{−s}`. -/
def thetaSqDirichlet (s : ℂ) : ℂ :=
  ∑' h : O, if h = 0 then 0 else
    rationalSourceResidualFourierCoefficient h ^ 2 * ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)

/-- The constant term of `θ_s²` at height `v` is `b(v, 0)² + R(v)`. -/
theorem tsum_amplitude_mul_neg (v : ℝ) (hv : 0 < v) :
    ∑' h : O, rationalSourceModeAmplitude v h * rationalSourceModeAmplitude v (-h) =
      rationalSourceModeAmplitude v 0 ^ 2 + thetaSqRemainder v := by
  have hs := rationalSourceModeAmplitude_summable v hv
  have hsum : Summable (fun h : O => rationalSourceModeAmplitude v h * rationalSourceModeAmplitude v (-h)) := by
    refine Summable.of_norm_bounded (hs.mul_right (∑' k : O, ‖rationalSourceModeAmplitude v k‖)) fun h => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hs.le_tsum (-h) fun k _ => norm_nonneg _) (norm_nonneg _)
  rw [hsum.tsum_eq_add_tsum_ite 0, neg_zero, sq, thetaSqRemainder]

/-- **The Mellin link.** For `Re s > 4`:
`∫_0^∞ v^s R(v) v^{−3} dv = M(s) Σ_{h ≠ 0} T_s(h)² (4π|ξ_h|)^{−s}`. -/
theorem integral_thetaSqRemainder (s : ℂ) (hs : 4 < s.re) :
    ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * thetaSqRemainder v / (v : ℂ) ^ 3 =
      besselSqMellin s * thetaSqDirichlet s := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  set a : O → ℝ := fun h => 4 * Real.pi * ‖cuspFrequency h‖ with ha_def
  have ha : ∀ h : O, h ≠ 0 → 0 < a h := fun h hh =>
    by have := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh); positivity
  set F : O → ℝ → ℂ := fun h v => if h = 0 then 0 else
    rationalSourceResidualFourierCoefficient h ^ 2 * ((v : ℂ) ^ (s - 1) • besselSq (a h * v)) with hF
  have hconv := besselSqMellin_convergent s (by linarith)
  -- the integrand is the sum of the `F h`
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ), (v : ℂ) ^ s * thetaSqRemainder v / (v : ℂ) ^ 3 = ∑' h, F h v := by
    intro v (hv : 0 < v)
    have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
    have hcp : (v : ℂ) ^ (s - 1) = (v : ℂ) ^ s / v := by
      rw [Complex.cpow_sub _ _ hv0, Complex.cpow_one]
    rw [thetaSqRemainder, ← tsum_mul_left, ← tsum_div_const]
    refine tsum_congr fun h => ?_
    by_cases hh : h = 0
    · simp [hF, hh]
    · simp only [hF, hh, if_false, sourceAmplitude_mul_neg v hv h hh, besselSq, smul_eq_mul, hcp,
        ha_def]
      field_simp
  -- each `F h` is integrable, with integral `T_s(h)² a_h^{−s} M(s)`
  have hint : ∀ h, Integrable (F h) (volume.restrict (Set.Ioi 0)) := by
    intro h
    by_cases hh : h = 0
    · simp only [hF, hh, if_true]
      exact integrable_zero _ _ _
    · simp only [hF, hh, if_false]
      exact ((MellinConvergent.comp_mul_left (ha h hh)).mpr hconv).const_mul _
  have hval : ∀ h, ∫ v in Set.Ioi (0 : ℝ), F h v = besselSqMellin s *
      (if h = 0 then 0 else rationalSourceResidualFourierCoefficient h ^ 2 * ((a h : ℝ) : ℂ) ^ (-s)) := by
    intro h
    by_cases hh : h = 0
    · simp [hF, hh]
    · simp only [hF, hh, if_false]
      rw [integral_const_mul]
      have hm := mellin_comp_mul_left besselSq s (ha h hh)
      simp only [mellin] at hm
      rw [hm, besselSqMellin, mellin, smul_eq_mul]
      ring
  -- absolute convergence
  set N : ℝ := ∫ t in Set.Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • besselSq t‖ with hN
  have hnorm : ∀ h, ∫ v in Set.Ioi (0 : ℝ), ‖F h v‖ = N * (4 * Real.pi) ^ (-s.re) *
      (if h = 0 then 0 else
        ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 * ‖cuspFrequency h‖ ^ (-s.re)) := by
    intro h
    by_cases hh : h = 0
    · simp [hF, hh]
    simp only [hF, hh, if_false]
    have hah := ha h hh
    have hcpow : ∀ v : ℝ, 0 < v → ‖(v : ℂ) ^ (s - 1)‖ = a h ^ (1 - s.re) * ‖((a h * v : ℝ) : ℂ) ^ (s - 1)‖ := by
      intro v hv
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        Complex.sub_re, Complex.one_re, Real.mul_rpow hah.le hv.le, ← mul_assoc,
        ← Real.rpow_add hah]
      norm_num
    calc ∫ v in Set.Ioi (0 : ℝ), ‖rationalSourceResidualFourierCoefficient h ^ 2 *
          ((v : ℂ) ^ (s - 1) • besselSq (a h * v))‖
        = ∫ v in Set.Ioi (0 : ℝ), ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 * a h ^ (1 - s.re) *
            ‖((a h * v : ℝ) : ℂ) ^ (s - 1) • besselSq (a h * v)‖ := by
          refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
          rw [norm_mul, norm_pow, norm_smul, norm_smul, hcpow v hv]
          ring
      _ = ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 * a h ^ (1 - s.re) *
            ((a h)⁻¹ * N) := by
          rw [integral_const_mul]
          congr 1
          have hc := integral_comp_mul_left_Ioi
            (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) • besselSq t‖) 0 hah
          rw [mul_zero] at hc
          rw [hc, smul_eq_mul]
      _ = _ := by
          have hsplit : a h ^ (1 - s.re) * (a h)⁻¹ = (4 * Real.pi) ^ (-s.re) * ‖cuspFrequency h‖ ^ (-s.re) := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hah, ha_def, Real.mul_rpow (by positivity)
              (norm_nonneg _)]
            ring_nf
          calc _ = N * ‖rationalSourceResidualFourierCoefficient h‖ ^ 2 *
                (a h ^ (1 - s.re) * (a h)⁻¹) := by ring
            _ = _ := by rw [hsplit]; ring
  have hsum : Summable (fun h => ∫ v in Set.Ioi (0 : ℝ), ‖F h v‖) := by
    simp_rw [hnorm]
    exact (summable_sourceCoefficient_sq_rpow hs).mul_left _
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, ← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hval]
  rw [tsum_mul_left, thetaSqDirichlet]

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
