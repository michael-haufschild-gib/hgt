import GaloisForLFunctions.ArithmeticCompensationTheory.ThePrimePolarResidualHasTheDeLaValleePoussinSaving
import GaloisForLFunctions.HTGeometry.SmoothTransitionDerivBound

/-!
# Uniform frequency bounds for the literal prime–polar cutoff

Lag Abel summation compares every von Mangoldt atom with both polar densities
before taking absolute values. A fixed smooth edge gives a bound linear in
frequency with a vanishing normalized coefficient. Positivity of the two
separate measures gives a second bound independent of frequency.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticCompensationTheory
open ArithmeticIncidencePositivity HTGeometry

/-- A unit-width edge equal to one below `S - 1` and zero above `S`. -/
def primePolarCutoff (S s : ℝ) : ℝ := Real.smoothTransition (S - s)

theorem primePolarCutoff_nonneg (S s : ℝ) : 0 ≤ primePolarCutoff S s :=
  Real.smoothTransition.nonneg _

theorem primePolarCutoff_le_one (S s : ℝ) : primePolarCutoff S s ≤ 1 :=
  Real.smoothTransition.le_one _

theorem primePolarCutoff_eq_zero {S s : ℝ} (hs : S ≤ s) :
    primePolarCutoff S s = 0 := Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hs)

theorem primePolarCutoff_eq_one {S s : ℝ} (hs : s ≤ S - 1) :
    primePolarCutoff S s = 1 := Real.smoothTransition.one_of_one_le (by linarith only [hs])

theorem contDiff_primePolarCutoff (S : ℝ) : ContDiff ℝ 1 (primePolarCutoff S) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

/-- Half-density and cosine in the same lag weight as the actual prime source. -/
def primePolarLagWeight (S t s : ℝ) : ℝ :=
  Real.exp (-s / 2) * primePolarCutoff S s * Real.cos (t * s)

theorem contDiff_primePolarLagWeight (S t : ℝ) :
    ContDiff ℝ 1 (primePolarLagWeight S t) :=
  (((contDiff_id.neg.div_const 2).exp).mul (contDiff_primePolarCutoff S)).mul
    ((contDiff_const.mul contDiff_id).cos)

theorem primePolarLagWeight_eq_zero {S s : ℝ} (t : ℝ) (hs : S ≤ s) :
    primePolarLagWeight S t s = 0 := by
  rw [primePolarLagWeight, primePolarCutoff_eq_zero hs, mul_zero, zero_mul]

theorem abs_primePolarLagWeight_le (S t s : ℝ) :
    |primePolarLagWeight S t s| ≤ Real.exp (-s / 2) * primePolarCutoff S s := by
  rw [primePolarLagWeight, abs_mul,
    abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (primePolarCutoff_nonneg S s))]
  exact mul_le_of_le_one_right
    (mul_nonneg (Real.exp_pos _).le (primePolarCutoff_nonneg S s)) (Real.abs_cos_le_one _)

theorem abs_deriv_primePolarLagWeight_le {D : ℝ}
    (hD : ∀ s : ℝ, |deriv Real.smoothTransition s| ≤ D) (S t s : ℝ) :
    |deriv (primePolarLagWeight S t) s| ≤
      Real.exp (-s / 2) * (1 / 2 + D + |t|) := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s / 2))
      (Real.exp (-s / 2) * (-(1 : ℝ) / 2)) s :=
    ((hasDerivAt_id s).neg.div_const 2).exp
  have hc : HasDerivAt (primePolarCutoff S)
      (deriv Real.smoothTransition (S - s) * (-1)) s :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
      (S - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub S)
  have ht : HasDerivAt (fun s : ℝ => Real.cos (t * s))
      (-Real.sin (t * s) * t) s := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id s).const_mul t).cos
  change |deriv (((fun s : ℝ => Real.exp (-s / 2)) * primePolarCutoff S) *
    (fun s : ℝ => Real.cos (t * s))) s| ≤ _
  rw [(he.mul hc |>.mul ht).deriv]
  simp only [Pi.mul_apply]
  have h1 : |Real.exp (-s / 2) * (-(1 : ℝ) / 2) * primePolarCutoff S s| ≤
      Real.exp (-s / 2) * (1 / 2) := by
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (primePolarCutoff_nonneg S s)]
    norm_num
    exact mul_le_of_le_one_right (by positivity) (primePolarCutoff_le_one S s)
  have h2 : |Real.exp (-s / 2) * (deriv Real.smoothTransition (S - s) * (-1))| ≤
      Real.exp (-s / 2) * D := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
    norm_num
    exact mul_le_mul_of_nonneg_left (hD _) (Real.exp_pos _).le
  have h3 : |Real.exp (-s / 2) * primePolarCutoff S s * (-Real.sin (t * s) * t)| ≤
      Real.exp (-s / 2) * |t| := by
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (primePolarCutoff_nonneg S s), abs_mul, abs_neg]
    have hcut := mul_le_of_le_one_right (Real.exp_pos (-s / 2)).le
      (primePolarCutoff_le_one S s)
    have hsin := mul_le_of_le_one_left (abs_nonneg t) (Real.abs_sin_le_one (t * s))
    exact mul_le_mul hcut hsin (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Real.exp_pos _).le
  have hcos := mul_le_of_le_one_right
    (abs_nonneg (Real.exp (-s / 2) * (-(1 : ℝ) / 2) * primePolarCutoff S s +
      Real.exp (-s / 2) * (deriv Real.smoothTransition (S - s) * (-1))))
    (Real.abs_cos_le_one (t * s))
  have htri := abs_add_le
    ((Real.exp (-s / 2) * (-(1 : ℝ) / 2) * primePolarCutoff S s +
      Real.exp (-s / 2) * (deriv Real.smoothTransition (S - s) * (-1))) * Real.cos (t * s))
    (Real.exp (-s / 2) * primePolarCutoff S s * (-Real.sin (t * s) * t))
  rw [abs_mul] at htri
  have hab := abs_add_le
    (Real.exp (-s / 2) * (-(1 : ℝ) / 2) * primePolarCutoff S s)
    (Real.exp (-s / 2) * (deriv Real.smoothTransition (S - s) * (-1)))
  linarith only [h1, h2, h3, hcos, htri, hab]

/-- The prime and the two polar measures retain their literal coefficients. -/
def primePolarCutoffSymbol (S t : ℝ) : ℝ :=
  2 * ((∑ n ∈ Finset.range (⌈Real.exp S⌉₊ + 1),
    ArithmeticFunction.vonMangoldt n * primePolarLagWeight S t (Real.log n)) -
      ∫ s in Ioi (0 : ℝ), (Real.exp s + 1) * primePolarLagWeight S t s)

/-- One universal arithmetic error bounds every frequency, with only linear frequency loss. -/
theorem exists_primePolarCutoffSymbol_low_frequency_bound :
    ∃ c > 0, ∃ K : ℝ, 0 ≤ K ∧ ∃ D : ℝ, 0 ≤ D ∧ ∃ S₀ : ℝ, 0 < S₀ ∧
      ∀ S, S₀ ≤ S → ∀ t : ℝ,
        |primePolarCutoffSymbol S t| ≤
          2 * K * S * Real.exp (S / 2) * Real.exp (-c * Real.sqrt S) *
            (1 / 2 + D + |t|) := by
  obtain ⟨c, hc, K, hK, S₀, hS₀, hE⟩ := exists_abs_chebyshevTwoPoleDefect_mul_exp_le
  obtain ⟨D, hD, hd⟩ := exists_bound_deriv_smoothTransition
  refine ⟨c, hc, K, hK, D, hD, S₀, hS₀, ?_⟩
  intro S hS t
  have hSpos : 0 < S := hS₀.trans_le hS
  have hN : Real.exp S ≤ (⌈Real.exp S⌉₊ : ℝ) := Nat.le_ceil _
  have hh := contDiff_primePolarLagWeight S t
  have hv : ∀ s : ℝ, S ≤ s → primePolarLagWeight S t s = 0 :=
    fun s hs => primePolarLagWeight_eq_zero t hs
  have hM (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) S) :
      |chebyshevTwoPoleDefect s| * Real.exp (-s / 2) ≤
        K * Real.exp (S / 2) * Real.exp (-c * Real.sqrt S) := by
    have h := hE S hS (1 / 2) (by norm_num) le_rfl s ⟨hs.1.le, hs.2⟩
    rw [show -(1 / 2 : ℝ) * s = -s / 2 by ring,
      show ((1 : ℝ) - 1 / 2) * S = S / 2 by ring] at h
    exact h
  have hi := (integrableOn_Ioi_chebyshevTwoPoleDefect_mul_deriv hh hSpos hv hN).mono_set
    (show Ioc (0 : ℝ) S ⊆ Ioi 0 from fun s hs => hs.1)
  have hp (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) S) :
      |chebyshevTwoPoleDefect s * deriv (primePolarLagWeight S t) s| ≤
        (K * Real.exp (S / 2) * Real.exp (-c * Real.sqrt S)) * (1 / 2 + D + |t|) := by
    rw [abs_mul]
    calc _ ≤ |chebyshevTwoPoleDefect s| *
          (Real.exp (-s / 2) * (1 / 2 + D + |t|)) :=
        mul_le_mul_of_nonneg_left (abs_deriv_primePolarLagWeight_le hd S t s) (abs_nonneg _)
      _ = (|chebyshevTwoPoleDefect s| * Real.exp (-s / 2)) * (1 / 2 + D + |t|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hM s hs) (by positivity)
  have hb := (abs_integral_le_integral_abs (f := fun s =>
    chebyshevTwoPoleDefect s * deriv (primePolarLagWeight S t) s)
      (μ := volume.restrict (Ioc (0 : ℝ) S))).trans
    (setIntegral_mono_on hi.abs
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      measurableSet_Ioc hp)
  rw [primePolarCutoffSymbol, sum_vonMangoldt_sub_polar_eq_chebyshev hh hSpos hv hN,
    integral_chebyshev_mul_deriv_eq_Ioc hh hSpos hv hN, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hvol : (volume (Ioc (0 : ℝ) S)).toReal = S := by
    rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hSpos.le]
  simp only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ] at hb
  rw [hvol] at hb
  calc _ ≤ 2 * (S * ((K * Real.exp (S / 2) * Real.exp (-c * Real.sqrt S)) *
      (1 / 2 + D + |t|))) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

/-- The positive polar density on the same cutoff as the prime atoms. -/
def primePolarDensity (S s : ℝ) : ℝ :=
  (Real.exp s + 1) * Real.exp (-s / 2) * primePolarCutoff S s

theorem primePolarDensity_nonneg (S s : ℝ) : 0 ≤ primePolarDensity S s :=
  mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
    (primePolarCutoff_nonneg S s)

theorem continuous_primePolarDensity (S : ℝ) : Continuous (primePolarDensity S) :=
  ((Real.continuous_exp.add continuous_const).mul
    (Real.continuous_exp.comp (continuous_id.neg.div_const 2))).mul
      (contDiff_primePolarCutoff S).continuous

theorem primePolarDensity_eq_zero {S s : ℝ} (hs : S ≤ s) :
    primePolarDensity S s = 0 := by
  rw [primePolarDensity, primePolarCutoff_eq_zero hs, mul_zero]

theorem integrableOn_primePolarDensity {S : ℝ} (hS : 0 < S) :
    IntegrableOn (primePolarDensity S) (Ioi (0 : ℝ)) := by
  have hi : IntegrableOn (primePolarDensity S) (Ioc (0 : ℝ) S) :=
    (continuous_primePolarDensity S).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hz : IntegrableOn (primePolarDensity S) (Ioi S) :=
    (integrableOn_zero (μ := volume) (s := Ioi S)).congr_fun
      (fun s hs => (primePolarDensity_eq_zero hs.le).symm) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi hS.le]
  exact hi.union hz

theorem primePolarDensity_le_exp {S s : ℝ} (hs : 0 ≤ s) :
    primePolarDensity S s ≤ 2 * Real.exp (s / 2) := by
  have he : (Real.exp s + 1) * Real.exp (-s / 2) =
      Real.exp (s / 2) + Real.exp (-s / 2) := by
    rw [add_mul, one_mul, ← Real.exp_add, show s + -s / 2 = s / 2 by ring]
  have hcut := mul_le_of_le_one_right
    (show 0 ≤ (Real.exp s + 1) * Real.exp (-s / 2) by positivity)
    (primePolarCutoff_le_one S s)
  rw [he] at hcut
  have hexp := Real.exp_le_exp.mpr (show -s / 2 ≤ s / 2 by linarith only [hs])
  change ((Real.exp s + 1) * Real.exp (-s / 2)) * primePolarCutoff S s ≤ _
  rw [he]
  exact hcut.trans (show Real.exp (s / 2) + Real.exp (-s / 2) ≤
    2 * Real.exp (s / 2) by linarith only [hexp])

/-- The polar measure has its natural half-exponential mass, without a horizon-length loss. -/
theorem integral_primePolarDensity_le {S : ℝ} (hS : 0 < S) :
    (∫ s in Ioi (0 : ℝ), primePolarDensity S s) ≤ 4 * Real.exp (S / 2) := by
  rw [integral_Ioi_eq_intervalIntegral (continuous_primePolarDensity S) hS
    (fun s hs => primePolarDensity_eq_zero hs.le)]
  have hi := intervalIntegral.integral_mono_on (μ := volume) hS.le
    ((continuous_primePolarDensity S).intervalIntegrable (μ := volume) 0 S)
    ((by fun_prop : Continuous (fun s : ℝ => 2 * Real.exp (s / 2))).intervalIntegrable
      (μ := volume) 0 S)
    (fun s hs => primePolarDensity_le_exp hs.1)
  have he : (∫ s in (0 : ℝ)..S, 2 * Real.exp (s / 2)) =
      4 * (Real.exp (S / 2) - 1) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_div _ (by norm_num : (2 : ℝ) ≠ 0),
      integral_exp]
    norm_num
    ring
  rw [he] at hi
  linarith only [hi]

theorem integrableOn_primePolarDensity_cos {S : ℝ} (hS : 0 < S) (t : ℝ) :
    IntegrableOn (fun s => primePolarDensity S s * Real.cos (t * s)) (Ioi (0 : ℝ)) := by
  apply (integrableOn_primePolarDensity hS).mono'
    (((continuous_primePolarDensity S).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
  filter_upwards [] with s
  change ‖primePolarDensity S s * Real.cos (t * s)‖ ≤ primePolarDensity S s
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (primePolarDensity_nonneg S s)]
  exact mul_le_of_le_one_right (primePolarDensity_nonneg S s) (Real.abs_cos_le_one _)

theorem abs_integral_primePolarDensity_cos_le {S : ℝ} (hS : 0 < S) (t : ℝ) :
    |∫ s in Ioi (0 : ℝ), primePolarDensity S s * Real.cos (t * s)| ≤
      ∫ s in Ioi (0 : ℝ), primePolarDensity S s := by
  apply (abs_integral_le_integral_abs).trans
    (integral_mono (integrableOn_primePolarDensity_cos hS t).abs
      (integrableOn_primePolarDensity hS) ?_)
  intro s
  change |primePolarDensity S s * Real.cos (t * s)| ≤ primePolarDensity S s
  rw [abs_mul, abs_of_nonneg (primePolarDensity_nonneg S s)]
  exact mul_le_of_le_one_right (primePolarDensity_nonneg S s) (Real.abs_cos_le_one _)

private theorem abs_primePolar_prime_sum_le (S t : ℝ) :
    |∑ n ∈ Finset.range (⌈Real.exp S⌉₊ + 1), ArithmeticFunction.vonMangoldt n *
      primePolarLagWeight S t (Real.log n)| ≤
    ∑ n ∈ Finset.range (⌈Real.exp S⌉₊ + 1), ArithmeticFunction.vonMangoldt n *
      primePolarLagWeight S 0 (Real.log n) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have he : primePolarLagWeight S 0 (Real.log n) =
      Real.exp (-Real.log n / 2) * primePolarCutoff S (Real.log n) := by
    simp only [primePolarLagWeight, zero_mul, Real.cos_zero, mul_one]
  rw [he]
  exact mul_le_mul_of_nonneg_left (abs_primePolarLagWeight_le S t (Real.log n))
    ArithmeticFunction.vonMangoldt_nonneg

/-- Positivity of each measure bounds every frequency by its zero-frequency discrepancy
and four copies of the polar mass. -/
theorem abs_primePolarCutoffSymbol_le_zero_add_exp {S : ℝ} (hS : 0 < S) (t : ℝ) :
    |primePolarCutoffSymbol S t| ≤ |primePolarCutoffSymbol S 0| + 16 * Real.exp (S / 2) := by
  have he (t s : ℝ) : (Real.exp s + 1) * primePolarLagWeight S t s =
      primePolarDensity S s * Real.cos (t * s) := by
    dsimp only [primePolarLagWeight, primePolarDensity]
    ring
  have hzero : primePolarCutoffSymbol S 0 =
      2 * ((∑ n ∈ Finset.range (⌈Real.exp S⌉₊ + 1), ArithmeticFunction.vonMangoldt n *
        primePolarLagWeight S 0 (Real.log n)) -
          ∫ s in Ioi (0 : ℝ), primePolarDensity S s) := by
    simp only [primePolarCutoffSymbol, he, zero_mul, Real.cos_zero, mul_one]
  have hp := abs_primePolar_prime_sum_le S t
  have hd := abs_integral_primePolarDensity_cos_le hS t
  have htri := abs_add_le
    (∑ n ∈ Finset.range (⌈Real.exp S⌉₊ + 1), ArithmeticFunction.vonMangoldt n *
      primePolarLagWeight S t (Real.log n))
    (-(∫ s in Ioi (0 : ℝ), primePolarDensity S s * Real.cos (t * s)))
  simp only [← sub_eq_add_neg, abs_neg] at htri
  have hz := le_abs_self (primePolarCutoffSymbol S 0)
  rw [hzero] at hz
  rw [primePolarCutoffSymbol, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [he]
  rw [hzero]
  have hb := integral_primePolarDensity_le hS
  linarith only [hp, hd, htri, hz, hb]

private theorem tendsto_mul_exp_neg_sqrt {c : ℝ} (hc : 0 < c) :
    Tendsto (fun S : ℝ => S * Real.exp (-c * Real.sqrt S)) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
    (Real.tendsto_sqrt_atTop.const_mul_atTop hc)).const_mul (c ^ 2)⁻¹
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with S hS
  change (c ^ 2)⁻¹ * ((c * Real.sqrt S) ^ 2 * Real.exp (-(c * Real.sqrt S))) = _
  rw [mul_pow, Real.sq_sqrt hS, neg_mul]
  field_simp [hc.ne']

/-- After normalization by the natural aperture mass, cancellation is uniform on each
bounded frequency interval. -/
theorem eventually_primePolarCutoffSymbol_small_on_frequency_interval
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : ℝ in atTop, 0 < S ∧ ∀ t : ℝ, |t| ≤ T →
      |primePolarCutoffSymbol S t| ≤ ε * Real.exp (S / 2) := by
  obtain ⟨c, hc, K, hK, D, hD, S₀, hS₀, hb⟩ :=
    exists_primePolarCutoffSymbol_low_frequency_bound
  have hl := (tendsto_mul_exp_neg_sqrt hc).const_mul (2 * K * (1 / 2 + D + |T|))
  rw [mul_zero] at hl
  have he := hl.eventually (gt_mem_nhds hε)
  filter_upwards [eventually_ge_atTop S₀, he] with S hS hs
  refine ⟨hS₀.trans_le hS, fun t ht => ?_⟩
  have hsf : 0 ≤ 2 * K * S * Real.exp (S / 2) * Real.exp (-c * Real.sqrt S) :=
    by have hSpos := hS₀.trans_le hS; positivity
  calc _ ≤ 2 * K * S * Real.exp (S / 2) * Real.exp (-c * Real.sqrt S) *
        (1 / 2 + D + |t|) := hb S hS t
    _ ≤ 2 * K * S * Real.exp (S / 2) * Real.exp (-c * Real.sqrt S) *
        (1 / 2 + D + |T|) := mul_le_mul_of_nonneg_left
          (by linarith only [ht, le_abs_self T]) hsf
    _ = (2 * K * (1 / 2 + D + |T|) * (S * Real.exp (-c * Real.sqrt S))) *
        Real.exp (S / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs.le (Real.exp_pos _).le

/-- The same cutoff multipliers have a common frequency-independent normalized bound. -/
theorem eventually_primePolarCutoffSymbol_bounded_all_frequencies :
    ∀ᶠ S : ℝ in atTop, 0 < S ∧ ∀ t : ℝ,
      |primePolarCutoffSymbol S t| ≤ 17 * Real.exp (S / 2) := by
  filter_upwards [eventually_primePolarCutoffSymbol_small_on_frequency_interval 0
    (by norm_num : (0 : ℝ) < 1)] with S hS
  refine ⟨hS.1, fun t => ?_⟩
  have h0 := hS.2 0 (by simp)
  have ht := abs_primePolarCutoffSymbol_le_zero_add_exp hS.1 t
  linarith only [h0, ht]

end GaloisForLFunctions.ArithmeticCompensationTheory
