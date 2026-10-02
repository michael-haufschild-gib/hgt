import GaloisForLFunctions.RHTower.PMMertensLogTent
import GaloisForLFunctions.RHTower.FermiNymanFiniteCoefficientError

/-!
# A last-scale harmonic correction does not repair raw Möbius approximation

Subtracting `N*h_N` from the last Möbius coefficient gives the literal
Fermi approximant `rawMobiusFermiApprox N + N*h_N*fermiNymanGen N`.
Its reciprocal auxiliary error on `N <= x < 2*N` equals
`M(floor(x))-M(N)+N*h_N`. The centering-invariant Mertens window floor
therefore survives in its canonical Fermi norm, by reciprocal substitution
and the existing finite-coefficient coercivity theorem.

The resulting unconditional non-convergence theorem rules out this
specific correction. It supplies neither a proof nor a disproof of RH.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.NymanMellin
namespace RHTower

def pmTailCorrectedMobiusCoeff (N d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) -
    if d = N then (N : ℝ) * deningerHarmonicPartial N else 0

def pmTailCorrectedMobiusNymanError (N : ℕ) : ℝ → ℂ :=
  finiteNymanError N (pmTailCorrectedMobiusCoeff N)

def pmTailCorrectedMobiusFermiApprox (N : ℕ) (t : ℝ) : ℂ :=
  rawMobiusFermiApprox N t +
    (((N : ℝ) * deningerHarmonicPartial N : ℝ) : ℂ) * fermiNymanGen (N : ℝ) t

def pmTailCorrectedMobiusFermiErrorEnergy (N : ℕ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - pmTailCorrectedMobiusFermiApprox N t‖ ^ 2

theorem sum_pmTailCorrectedMobiusCoeff {N : ℕ} (hN : 1 ≤ N) (F : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 N, (pmTailCorrectedMobiusCoeff N d : ℂ) * F d) =
      (∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℂ) * F d) -
        (((N : ℝ) * deningerHarmonicPartial N : ℝ) : ℂ) * F N := by
  have he : (∑ d ∈ Finset.Icc 1 N, (pmTailCorrectedMobiusCoeff N d : ℂ) * F d) =
      ∑ d ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius d : ℤ) : ℂ) * F d -
          if d = N then (((N : ℝ) * deningerHarmonicPartial N : ℝ) : ℂ) * F N else 0) := by
    apply Finset.sum_congr rfl
    intro d _hd
    by_cases hd : d = N
    · subst d
      simp only [pmTailCorrectedMobiusCoeff]
      push_cast
      ring
    · simp only [pmTailCorrectedMobiusCoeff, if_neg hd, sub_zero]
      push_cast
      rfl
  rw [he, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_Icc, le_refl, and_true, if_pos hN]

theorem pmTailCorrectedMobiusNymanError_eq_raw {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    pmTailCorrectedMobiusNymanError N t = rawMobiusNymanError N t -
      (((N : ℝ) * deningerHarmonicPartial N : ℝ) : ℂ) * nymanGen (N : ℝ) t := by
  rw [pmTailCorrectedMobiusNymanError, finiteNymanError,
    sum_pmTailCorrectedMobiusCoeff hN (fun d => nymanGen (d : ℝ) t), rawMobiusNymanError]
  ring

theorem integral_normSq_pmTailCorrectedMobiusNymanError_le_six {N : ℕ} (hN : 1 ≤ N) :
    (∫ t in Ioi (0 : ℝ), ‖pmTailCorrectedMobiusNymanError N t‖ ^ 2) ≤
      6 * pmTailCorrectedMobiusFermiErrorEnergy N := by
  have he : pmTailCorrectedMobiusFermiErrorEnergy N =
      ∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t +
        ∑ d ∈ Finset.Icc 1 N, (pmTailCorrectedMobiusCoeff N d : ℂ) *
          fermiNymanGen (d : ℝ) t‖ ^ 2 := by
    unfold pmTailCorrectedMobiusFermiErrorEnergy
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _ht
    dsimp only
    rw [sum_pmTailCorrectedMobiusCoeff hN (fun d => fermiNymanGen (d : ℝ) t),
      pmTailCorrectedMobiusFermiApprox, rawMobiusFermiApprox]
    congr 2
    ring
  rw [he]
  exact integral_normSq_finiteNymanError_le_six N (pmTailCorrectedMobiusCoeff N)

private theorem pmSum_Icc_moebius_eq_mertensM (k : ℕ) :
    (∑ d ∈ Finset.Icc 1 k, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) =
      Sieve.mertensM k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  rw [Sieve.mertensM, Finset.sum_range_succ']
  simp only [ArithmeticFunction.map_zero, Int.cast_zero, add_zero]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Nat.add_comm 1 d]

theorem sum_moebius_floor_first_omitted {N : ℕ} (hN : 1 ≤ N) {x : ℝ}
    (hNx : (N : ℝ) ≤ x) (hxN : x < 2 * N) :
    (∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      (⌊x / (d : ℝ)⌋ : ℝ)) = 1 - (Sieve.mertensM ⌊x⌋₊ - Sieve.mertensM N) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 1 ≤ x := hN1.trans hNx
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hNfloor : N ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr hNx
  have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 ⌊x⌋₊ := Finset.Icc_subset_Icc_right hNfloor
  have hdiff : (∑ d ∈ Finset.Icc 1 ⌊x⌋₊ \ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (⌊x / (d : ℝ)⌋ : ℝ)) =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊ \ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hdmem, hdnot⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨hd1, hdfloor⟩ := Finset.mem_Icc.mp hdmem
    have hNd : N < d := by
      by_contra h
      exact hdnot (Finset.mem_Icc.mpr ⟨hd1, by omega⟩)
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hdx : (d : ℝ) ≤ x := (by exact_mod_cast hdfloor : (d : ℝ) ≤ ⌊x⌋₊).trans
      (Nat.floor_le hx0)
    have hNdR : (N : ℝ) < d := by exact_mod_cast hNd
    have hfloor : (⌊x / (d : ℝ)⌋ : ℤ) = 1 := by
      apply Int.floor_eq_iff.mpr
      constructor
      · norm_num only [Int.cast_one]
        exact (le_div_iff₀ hd0).mpr (by simpa using hdx)
      · norm_num only [Int.cast_one]
        apply (div_lt_iff₀ hd0).mpr
        linarith
    rw [hfloor]
    norm_num
  have hfull := sum_moebius_floor_truncated ⌊x⌋₊ hx0 le_rfl
  rw [if_pos hx1, ← Finset.sum_sdiff hsub, hdiff] at hfull
  have hm := Finset.sum_sdiff (f := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) hsub
  rw [pmSum_Icc_moebius_eq_mertensM, pmSum_Icc_moebius_eq_mertensM] at hm
  linarith

theorem pmTailCorrectedMobiusNymanError_inv_first_window {N : ℕ} (hN : 1 ≤ N)
    {x : ℝ} (hNx : (N : ℝ) ≤ x) (hxN : x < 2 * N) :
    pmTailCorrectedMobiusNymanError N x⁻¹ =
      ((Sieve.mertensM ⌊x⌋₊ - Sieve.mertensM N + (N : ℝ) *
        deningerHarmonicPartial N : ℝ) : ℂ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hx1 : 1 ≤ x := hN1.trans hNx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have ht1 : x⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hx1 (inv_pos.mpr hx0).le
    simpa only [one_mul, mul_inv_cancel₀ hx0.ne'] using h
  have hfloor : (⌊x / (N : ℝ)⌋ : ℤ) = 1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · norm_num only [Int.cast_one]
      exact (le_div_iff₀ hN0).mpr (by simpa using hNx)
    · norm_num only [Int.cast_one]
      exact (div_lt_iff₀ hN0).mpr (by linarith)
  rw [pmTailCorrectedMobiusNymanError_eq_raw hN, rawMobiusNymanError,
    indicator_of_mem (show x⁻¹ ∈ Ioc (0 : ℝ) 1 from ⟨inv_pos.mpr hx0, ht1⟩),
    sum_moebius_nymanGen, show 1 / x⁻¹ = x by simp,
    sum_moebius_floor_first_omitted hN hNx hxN, nymanGen,
    show 1 / ((N : ℝ) * x⁻¹) = x / N by field_simp,
    Int.fract, hfloor]
  push_cast
  field_simp [hNc]
  ring

private theorem pmInverseNormSqDensity_eq (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • ‖f (x ^ (-1 : ℝ))‖ ^ 2 =
      ‖f x⁻¹‖ ^ 2 / x ^ 2 := by
  rw [show (-1 : ℝ) - 1 = -(2 : ℝ) by norm_num,
    Real.rpow_neg hx.le, Real.rpow_two, Real.rpow_neg_one]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem integral_pmInverseNormSq (f : ℝ → ℂ) :
    (∫ x in Ioi (0 : ℝ), ‖f x⁻¹‖ ^ 2 / x ^ 2) =
      ∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2 := by
  have h := integral_comp_rpow_Ioi (fun t => ‖f t‖ ^ 2) (p := -1) (by norm_num)
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => pmInverseNormSqDensity_eq f hx)] at h
  exact h

private theorem integrableOn_pmInverseNormSq {f : ℝ → ℂ}
    (hi : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioi (0 : ℝ))) :
    IntegrableOn (fun x => ‖f x⁻¹‖ ^ 2 / x ^ 2) (Ioi (0 : ℝ)) := by
  have h := (integrableOn_Ioi_comp_rpow_iff (fun t => ‖f t‖ ^ 2)
    (p := -1) (by norm_num)).mpr hi
  exact h.congr_fun (fun x hx => pmInverseNormSqDensity_eq f hx) measurableSet_Ioi

theorem pmTailCorrectedMobius_first_window_energy_le {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in Ioc (N : ℝ) (2 * N),
      ((Sieve.mertensM ⌊x⌋₊ - (Sieve.mertensM N - (N : ℝ) * deningerHarmonicPartial N)) / x) ^ 2) ≤
      ∫ t in Ioi (0 : ℝ), ‖pmTailCorrectedMobiusNymanError N t‖ ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hi := integrableOn_pmInverseNormSq
    (integrableOn_normSq_finiteNymanError N (pmTailCorrectedMobiusCoeff N))
  calc
    _ = ∫ x in Ioo (N : ℝ) (2 * N),
        ((Sieve.mertensM ⌊x⌋₊ - (Sieve.mertensM N - (N : ℝ) * deningerHarmonicPartial N)) / x) ^ 2 :=
      integral_Ioc_eq_integral_Ioo
    _ = ∫ x in Ioo (N : ℝ) (2 * N),
        ‖pmTailCorrectedMobiusNymanError N x⁻¹‖ ^ 2 / x ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      dsimp only
      rw [pmTailCorrectedMobiusNymanError_inv_first_window hN hx.1.le hx.2,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
      ring
    _ ≤ ∫ x in Ioi (0 : ℝ), ‖pmTailCorrectedMobiusNymanError N x⁻¹‖ ^ 2 / x ^ 2 := by
      apply setIntegral_mono_set hi
        (Eventually.of_forall (fun x => div_nonneg (sq_nonneg _) (sq_nonneg x)))
      exact Eventually.of_forall (fun _ hx => hN0.trans hx.1)
    _ = _ := integral_pmInverseNormSq _

theorem frequent_pmTailCorrectedMobiusFermiErrorEnergy_floor :
    ∃ C : ℝ, 0 < C ∧ ∀ N₀ : ℕ, ∃ N : ℕ,
      N₀ ≤ N ∧ C ≤ pmTailCorrectedMobiusFermiErrorEnergy N := by
  obtain ⟨C, hC, hf⟩ := pmMertens_centered_dyadic_window_energy_cofinal_floor
  refine ⟨C / 6, by positivity, ?_⟩
  intro N₀
  obtain ⟨N, hN1, hN₀N, hfloor⟩ := hf N₀
  refine ⟨N, hN₀N, ?_⟩
  have hM := hfloor (Sieve.mertensM N - (N : ℝ) * deningerHarmonicPartial N)
  have hwindow := pmTailCorrectedMobius_first_window_energy_le hN1
  have herror := integral_normSq_pmTailCorrectedMobiusNymanError_le_six hN1
  linarith

theorem not_tendsto_pmTailCorrectedMobiusFermiErrorEnergy_zero :
    ¬ Tendsto pmTailCorrectedMobiusFermiErrorEnergy atTop (𝓝 0) := by
  intro h
  obtain ⟨C, hC, hf⟩ := frequent_pmTailCorrectedMobiusFermiErrorEnergy_floor
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp h C hC
  obtain ⟨N, hN, hfloor⟩ := hf N₀
  have hdist := hN₀ N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hC.le.trans hfloor)] at hdist
  exact (not_lt_of_ge hfloor) hdist

end RHTower
