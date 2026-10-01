import GaloisForLFunctions.RHTower.PMPowerDampedMobiusSource
import GaloisForLFunctions.RHTower.PMDilationMellin
import GaloisForLFunctions.RHTower.MellinHeadChart
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Mellin transforms of the literal power-damped Möbius source

The arithmetic coefficients shift the Möbius Dirichlet series exactly. Absolute
dilation interchange identifies the literal source transform on its initial
strip as `(1 - 2^(1-s)) ζ(s) / (s ζ(s+ε))`.

For a canonically square-integrable member, the existing logarithmic head chart
gives analyticity on `Re s > 1/2`; Cauchy--Schwarz also proves absolute Mellin
convergence there. Canonical admission at small positive damping remains open.
-/

open MeasureTheory Set Filter Topology ArithmeticFunction
noncomputable section
namespace RHTower

def pmPowerDampedMobiusCoeff (ε : ℝ) (n : ℕ) : ℂ :=
  ((((moebius n : ℤ) : ℝ) * (n : ℝ) ^ (-ε) : ℝ) : ℂ)

theorem pmPowerDampedMobiusCoeff_zero (ε : ℝ) : pmPowerDampedMobiusCoeff ε 0 = 0 := by
  simp [pmPowerDampedMobiusCoeff]

theorem pmPowerDampedMobiusCoeff_term (ε : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (pmPowerDampedMobiusCoeff ε) s n =
      LSeries.term (fun n => (moebius n : ℂ)) (s + (ε : ℂ)) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, pmPowerDampedMobiusCoeff,
    Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_cpow (Nat.cast_nonneg n),
    Complex.ofReal_neg, Complex.ofReal_natCast, Complex.cpow_neg,
    Complex.cpow_add _ _ (by exact_mod_cast hn : (n : ℂ) ≠ 0)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem pmPowerDampedMobiusCoeff_lSeriesSummable (ε : ℝ) {s : ℂ}
    (hs : 1 < s.re + ε) : LSeriesSummable (pmPowerDampedMobiusCoeff ε) s := by
  change Summable (LSeries.term (pmPowerDampedMobiusCoeff ε) s)
  have heq := funext (pmPowerDampedMobiusCoeff_term ε s)
  rw [heq]
  exact ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by simpa using hs)

theorem pmPowerDampedMobiusCoeff_lSeries (ε : ℝ) {s : ℂ}
    (hs : 1 < s.re + ε) :
    LSeries (pmPowerDampedMobiusCoeff ε) s = 1 / riemannZeta (s + (ε : ℂ)) := by
  have hs' : 1 < (s + (ε : ℂ)).re := by simpa using hs
  have heq : LSeries (pmPowerDampedMobiusCoeff ε) s =
      LSeries (fun n => (moebius n : ℂ)) (s + (ε : ℂ)) :=
    tsum_congr (pmPowerDampedMobiusCoeff_term ε s)
  rw [heq]
  apply (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs')).mpr
  have h := LSeries_one_mul_Lseries_moebius hs'
  rw [LSeries_one_eq_riemannZeta hs'] at h
  simpa only [mul_comm] using h

theorem pm_fermiNymanGen_dilate (a t : ℝ) :
    fermiNymanGen a t = fermiNymanGen 1 (a * t) := by
  simp only [fermiNymanGen, GaloisForLFunctions.NymanMellin.nymanGen, one_mul, mul_one,
    mul_assoc]

theorem pmPowerDampedFermiSource_eq_dilation (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    pmPowerDampedFermiSource ε t =
      -pmWeightedDilationSource (pmPowerDampedMobiusCoeff ε) (fermiNymanGen 1) t := by
  have hcut : (1 : ℝ) < ((⌊1 / t⌋₊ : ℝ) + 1) * t :=
    (div_lt_iff₀ ht).mp (Nat.lt_floor_add_one (1 / t))
  rw [pmWeightedDilationSource_eq_sum _ _ ⌊1 / t⌋₊ (θ := 1) ht (fun x hx =>
    fermiNymanGen_eq_zero_of_inv_lt (by norm_num) (by simpa using hx)) hcut]
  unfold pmPowerDampedFermiSource
  congr 1
  simp_rw [← pm_fermiNymanGen_dilate]
  change (∑ d ∈ Finset.Icc 1 ⌊1 / t⌋₊,
    pmPowerDampedMobiusCoeff ε d * fermiNymanGen (d : ℝ) t) = _
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
    omega
  · intro n hn hnot
    have hn0 : n = 0 := by
      simp only [Finset.mem_Icc, Finset.mem_range] at hn hnot
      omega
    subst n
    rw [pmPowerDampedMobiusCoeff_zero, zero_mul]

private theorem pm_mellinConvergent_fermiNymanGen {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) {a : ℝ} (ha : 0 < a) :
    MellinConvergent (fermiNymanGen a) s := by
  have h1 := GaloisForLFunctions.NymanMellin.mellinConvergent_nymanGen hs0 hs1 ha
  have h2 := GaloisForLFunctions.NymanMellin.mellinConvergent_nymanGen hs0 hs1
    (by positivity : (0 : ℝ) < 2 * a)
  change MellinConvergent (fun t => GaloisForLFunctions.NymanMellin.nymanGen a t -
    2 * GaloisForLFunctions.NymanMellin.nymanGen (2 * a) t) s
  simpa only [smul_eq_mul] using
    (hasMellin_sub h1 (h2.const_smul (2 : ℂ))).1

theorem hasMellin_pmPowerDampedFermiSource (ε : ℝ) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsε : 1 < s.re + ε) :
    HasMellin (pmPowerDampedFermiSource ε) s
      ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s / (s * riemannZeta (s + (ε : ℂ)))) := by
  have h := pmWeightedDilationSource_hasMellin (pmPowerDampedMobiusCoeff ε)
    (fermiNymanGen 1) (pmPowerDampedMobiusCoeff_zero ε)
    (pmPowerDampedMobiusCoeff_lSeriesSummable ε hsε)
    (pm_mellinConvergent_fermiNymanGen hs0 hs1 (by norm_num))
  have hneg : mellin (pmPowerDampedFermiSource ε) s =
      -mellin (pmWeightedDilationSource (pmPowerDampedMobiusCoeff ε) (fermiNymanGen 1)) s := by
    unfold mellin
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (t : ℂ) ^ (s - 1) • pmPowerDampedFermiSource ε t =
      -((t : ℂ) ^ (s - 1) •
        pmWeightedDilationSource (pmPowerDampedMobiusCoeff ε) (fermiNymanGen 1) t)
    rw [pmPowerDampedFermiSource_eq_dilation ε ht, smul_neg]
  constructor
  · apply h.1.neg.congr_fun _ measurableSet_Ioi
    intro t ht
    change -((t : ℂ) ^ (s - 1) •
      pmWeightedDilationSource (pmPowerDampedMobiusCoeff ε) (fermiNymanGen 1) t) =
        (t : ℂ) ^ (s - 1) • pmPowerDampedFermiSource ε t
    rw [pmPowerDampedFermiSource_eq_dilation ε ht, smul_neg]
  · rw [hneg, h.2, pmPowerDampedMobiusCoeff_lSeries ε hsε,
      mellin_fermiNymanGen hs0 hs1 (by norm_num : (0 : ℝ) < 1)]
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul, div_eq_mul_inv, mul_inv_rev]
    ring

theorem pm_mellin_eq_head_laplace {f : ℝ → ℂ}
    (hf : ∀ t : ℝ, 1 < t → f t = 0) (s : ℂ) :
    mellin f s = GaloisForLFunctions.HTGeometry.laplaceRay (logChartHead 1 f) (s - 1 / 2) := by
  have hhead : mellin f s = ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) * f t := by
    unfold mellin
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self)]
    · simp only [smul_eq_mul]
    · intro t ht
      have ht1 : 1 < t := by
        rcases ht with ⟨ht0, htn⟩
        simp only [mem_Ioc, not_and, not_le] at htn
        exact htn ht0
      rw [hf t ht1, smul_zero]
  rw [hhead, integral_Ioc_eq_integral_Ioo]
  have h := mellinHead_eq_laplaceRay (by norm_num : (0 : ℝ) < 1) f (1 - s)
  have he : -(1 - s) = s - 1 := by ring
  have hz : (1 : ℂ) / 2 - (1 - s) = s - 1 / 2 := by ring
  simpa only [he, hz, Complex.ofReal_one, Complex.one_cpow, one_mul] using h

theorem pm_mellinConvergent_of_memLp {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi 0))) (hsupp : ∀ t : ℝ, 1 < t → f t = 0)
    {s : ℂ} (hs : 1 / 2 < s.re) : MellinConvergent f s := by
  have hk : MemLp (powerWitness s) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm
      ((continuousOn_powerWitness s).aestronglyMeasurable measurableSet_Ioc)).mpr
        (integrableOn_normSq_powerWitness hs)
  have hhead : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hf.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)
  have hp : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * f t) (Ioc (0 : ℝ) 1) :=
    hk.integrable_mul hhead
  have ht : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * f t) (Ioi (1 : ℝ)) := by
    refine integrableOn_zero.congr_fun (fun t ht => ?_) measurableSet_Ioi
    change (0 : ℂ) = (t : ℂ) ^ (s - 1) * f t
    rw [hsupp t ht, mul_zero]
  change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * f t) (Ioi (0 : ℝ))
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one)]
  exact hp.union ht

theorem pm_analyticOnNhd_mellin_of_memLp {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi 0))) (hsupp : ∀ t : ℝ, 1 < t → f t = 0) :
    AnalyticOnNhd ℂ (mellin f) {s : ℂ | 1 / 2 < s.re} := by
  have hhead : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    hf.mono_measure (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl)
  have hlp := memLp_two_logChartHead (by norm_num : (0 : ℝ) < 1) hhead
  have ha : AnalyticOnNhd ℂ
      (GaloisForLFunctions.HTGeometry.laplaceRay (logChartHead 1 f)) {w : ℂ | 0 < w.re} :=
    (GaloisForLFunctions.HTGeometry.differentiableOn_laplaceRay hlp).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)
  have heq : mellin f = fun s =>
      GaloisForLFunctions.HTGeometry.laplaceRay (logChartHead 1 f) (s - 1 / 2) :=
    funext (pm_mellin_eq_head_laplace hsupp)
  rw [heq]
  intro s hs
  change 1 / 2 < s.re at hs
  have hs' : 0 < (s - (1 : ℂ) / 2).re := by simpa using sub_pos.mpr hs
  exact (ha (s - 1 / 2) hs').comp (f := fun z : ℂ => z - 1 / 2)
    (analyticAt_id.sub analyticAt_const)

theorem analyticOnNhd_mellin_pmPowerDampedFermiSource (ε : ℝ)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi 0))) :
    AnalyticOnNhd ℂ (mellin (pmPowerDampedFermiSource ε)) {s : ℂ | 1 / 2 < s.re} :=
  pm_analyticOnNhd_mellin_of_memLp hf (fun _ ht =>
    pmPowerDampedFermiSource_eq_zero_of_one_lt ε ht)

theorem mellinConvergent_pmPowerDampedFermiSource (ε : ℝ)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi 0)))
    {s : ℂ} (hs : 1 / 2 < s.re) : MellinConvergent (pmPowerDampedFermiSource ε) s :=
  pm_mellinConvergent_of_memLp hf (fun _ ht =>
    pmPowerDampedFermiSource_eq_zero_of_one_lt ε ht) hs

end RHTower
