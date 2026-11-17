import GaloisForLFunctions.HilbertMetric.Bergman.DiskArea
import GaloisForLFunctions.HTGeometry.HardyDiskMultiplier
import GaloisForLFunctions.HTGeometry.ProductOccupancyDichotomy

/-!
# Every square-integrable holomorphic disk function has Bergman coordinates

Nonnegative polar integration gives the area Parseval formula even when
its value is infinite. Finite area therefore forces square summability
of the normalized Taylor coefficients. Taylor reconstruction proves
that the coefficient model contains every holomorphic L² disk function.
-/

open MeasureTheory Set Filter Metric Complex Real
open scoped ENNReal BigOperators
namespace GaloisForLFunctions.HilbertMetric.Bergman
open HTGeometry
noncomputable section

private def taylorRadial (f : ℂ → ℂ) (n : ℕ) (r : ℝ) : ℝ :=
  (2 * π * ‖diskCoeff f n‖ ^ 2) * r ^ (2 * n + 1)

private theorem taylorRadial_integrable (f : ℂ → ℂ) (n : ℕ) :
    IntegrableOn (taylorRadial f n) (Ioo 0 1) :=
  (show Continuous (taylorRadial f n) by unfold taylorRadial; fun_prop).integrableOn_Icc.mono_set
    Ioo_subset_Icc_self

private theorem integral_taylorRadial (f : ℂ → ℂ) (n : ℕ) :
    ∫ r in Ioo (0 : ℝ) 1, taylorRadial f n r = π * ‖diskCoeff f n‖ ^ 2 / ((n : ℝ) + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  unfold taylorRadial
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  field_simp (disch := positivity)
  ring

private theorem hasSum_taylorRadial {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n => taylorRadial f n r)
      (r * ∫ θ in (0 : ℝ)..(2 * π), ‖f (circleMap 0 r θ)‖ ^ 2) := by
  have h := (hasSum_circleAverage_normSq_diskCoeff hf hr0 hr1).mul_left (2 * π * r)
  have he (I : ℝ) : (2 * π * r) * ((2 * π)⁻¹ * I) = r * I := by
    field_simp [Real.pi_ne_zero]
  rw [he] at h
  exact h.congr_fun fun n => by rw [taylorRadial, pow_succ]; ring

/-- Area Parseval holds in extended nonnegative reals, before any integrability assumption. -/
theorem holomorphic_area_parseval {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) :
    (∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖f z‖ ^ 2)) =
      ∑' n : ℕ, ENNReal.ofReal (π * ‖diskCoeff f n‖ ^ 2 / ((n : ℝ) + 1)) := by
  rw [holomorphic_lintegral_polar f hf]
  calc
    _ = ∫⁻ r in Ioo (0 : ℝ) 1, ∑' n, ENNReal.ofReal (taylorRadial f n r) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      change ENNReal.ofReal (r * ∫ θ in (0 : ℝ)..(2 * π),
        ‖f (circleMap 0 r θ)‖ ^ 2) = ∑' n, ENNReal.ofReal (taylorRadial f n r)
      rw [← (hasSum_taylorRadial hf hr.1.le hr.2).tsum_eq,
        ENNReal.ofReal_tsum_of_nonneg (fun n => ?_)
          (hasSum_taylorRadial hf hr.1.le hr.2).summable]
      unfold taylorRadial
      have hr0 : 0 ≤ r := hr.1.le
      positivity
    _ = _ := by
      rw [lintegral_tsum (fun n =>
        (show Measurable (taylorRadial f n) by unfold taylorRadial; fun_prop).ennreal_ofReal.aemeasurable)]
      apply tsum_congr
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (taylorRadial_integrable f n) ?_,
        integral_taylorRadial]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      unfold taylorRadial
      have hr0 : 0 ≤ r := hr.1.le
      positivity

/-- Normalized Taylor coordinates in the orthonormal Bergman monomial basis. -/
def normalizedTaylor (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  diskCoeff f n / (Real.sqrt ((n : ℝ) + 1) : ℂ)

private theorem normalizedTaylor_norm_sq (f : ℂ → ℂ) (n : ℕ) :
    ‖normalizedTaylor f n‖ ^ 2 = ‖diskCoeff f n‖ ^ 2 / ((n : ℝ) + 1) := by
  rw [normalizedTaylor, norm_div, div_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]

/-- Finite area forces the actual normalized Taylor sequence to lie in ℓ². -/
theorem memlp_normalizedTaylor {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hi : IntegrableOn (fun z => ‖f z‖ ^ 2) (ball (0 : ℂ) 1)) :
    Memℓp (normalizedTaylor f) 2 := by
  have hfin : (∑' n : ℕ, ENNReal.ofReal
      (π * ‖diskCoeff f n‖ ^ 2 / ((n : ℝ) + 1))) ≠ ∞ := by
    rw [← holomorphic_area_parseval hf]
    exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => sq_nonneg ‖f z‖)).mpr hi
  have hs := (tsum_ofReal_ne_top_iff_summable
    (fun n : ℕ => π * ‖diskCoeff f n‖ ^ 2 / ((n : ℝ) + 1))
    (fun _ => by positivity)).mp hfin
  have hw : Summable (fun n : ℕ => ‖diskCoeff f n‖ ^ 2 / ((n : ℝ) + 1)) := by
    refine (hs.mul_left π⁻¹).congr fun n => ?_
    field_simp [Real.pi_ne_zero]
  rw [memℓp_gen_iff (by norm_num)]
  refine hw.congr fun n => ?_
  rw [show (2 : ENNReal).toReal = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, normalizedTaylor_norm_sq]

/-- Taylor reconstruction is surjective onto all holomorphic square-integrable disk functions. -/
theorem exists_disk_coordinates {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hi : IntegrableOn (fun z => ‖f z‖ ^ 2) (ball (0 : ℂ) 1)) :
    ∃ a : Disk, (∀ z : ℂ, ‖z‖ < 1 → diskFun a z = f z) ∧
      (∀ n : ℕ, a n = normalizedTaylor f n) ∧
      π * ‖a‖ ^ 2 = ∫ z in ball (0 : ℂ) 1, ‖f z‖ ^ 2 := by
  let a : Disk := ⟨normalizedTaylor f, memlp_normalizedTaylor hf hi⟩
  have he (n : ℕ) : coefficient a n = diskCoeff f n := by
    have hn : (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
    change (Real.sqrt ((n : ℝ) + 1) : ℂ) *
      (diskCoeff f n / (Real.sqrt ((n : ℝ) + 1) : ℂ)) = _
    field_simp
  have hfun (z : ℂ) (hz : ‖z‖ < 1) : diskFun a z = f z := by
    rw [diskFun]
    simp only [he]
    exact (hasSum_diskCoeff hf hz).tsum_eq
  refine ⟨a, hfun, fun _ => rfl, ?_⟩
  rw [← integral_diskFun_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  rw [hfun z (by simpa only [mem_ball, dist_zero_right] using hz)]

/-- Agreement on the geometric disk determines every normalized Hilbert coordinate. -/
theorem diskFun_eqOn_iff (a b : Disk) :
    (∀ z : ℂ, ‖z‖ < 1 → diskFun a z = diskFun b z) ↔ a = b := by
  constructor
  · intro h
    ext n
    have he := diskCoeff_congr (fun z hz => h z
      (by simpa only [mem_ball, dist_zero_right] using hz)) n
    rw [diskCoeff_diskFun, diskCoeff_diskFun, coefficient, coefficient] at he
    have hn : (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
    exact mul_left_cancel₀ hn he
  · rintro rfl z _
    rfl

/-- The coefficient model represents each holomorphic L² disk function uniquely. -/
theorem existsUnique_disk_coordinates {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hi : IntegrableOn (fun z => ‖f z‖ ^ 2) (ball (0 : ℂ) 1)) :
    ∃! a : Disk, ∀ z : ℂ, ‖z‖ < 1 → diskFun a z = f z := by
  obtain ⟨a, ha, _, _⟩ := exists_disk_coordinates hf hi
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply (diskFun_eqOn_iff b a).mp
  intro z hz
  exact (hb z hz).trans (ha z hz).symm

#print axioms holomorphic_area_parseval
#print axioms memlp_normalizedTaylor
#print axioms exists_disk_coordinates
#print axioms existsUnique_disk_coordinates
end
end GaloisForLFunctions.HilbertMetric.Bergman
