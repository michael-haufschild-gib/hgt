import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSplineOrbitDecidesTheCriticalLine
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits
import GaloisForLFunctions.HeckeKreinToeplitz.KernelsOnGroupsAndTheirNegativeIndex
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.UnboundedOverlapIsTheRiemannHypothesis
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheShortWindowsInheritThePolarization
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BoundedWeilEnergyUpgradesL1LimitsToStrongLimits
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhatTheFailureOfTheHodgeIndexMeasures
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineStateHasNoPositiveLaplaceZero
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineGroundEnergyCurvature

/-!
# The confined form counts the zeros right of the line

ECS confines Weil's form on the half-line `u < 0` by the weight `e^{−8u}`:
`Q_R = W + a(R) W₈`, `W₈(H) = ∫ H² e^{−8u}`, with `a(R) = a(1)/R`. On a finite family of `C²` tests in a
window `[−A, 0]` its Gram matrix is `confinedGram R H`, whose form on real coefficients is the full
critical energy of the combination (`hermQuad_confinedGram_ofReal`).

* **Monotone in the ratio** (`hermNegIndex_confinedGram_mono`): `a(R)` decreases, `W₈ ≥ 0`, so the
  negative index grows with `R`.
* **Bounded by the right zeros** (`hermNegIndex_confinedGram_le`): `Q_R ≥ W` and Weil's Gram matrix
  has at most as many negative squares as `ζ` has zeros right of the line.
* **Attained at large ratios** (`exists_halfLineTests_eventually_le_hermNegIndex`): translates of the
  cubic spline, moved into `u < 0`, carry every negative square of Weil's form (orientation law);
  as `R → ∞` the confinement vanishes and the index is lower semicontinuous.
* **The index law** (`confinedIndex_law`): some confined Gram matrix of half-line tests has at least
  `n` negative squares iff `ζ` has at least `n` zeros right of the line. Off RH some ratio carries two
  negative squares (`exists_two_le_hermNegIndex_confinedGram_of_not_RH`); the index is bounded over
  all ratios and families iff the right zeros are finite (`bddAbove_confinedIndex_iff_finite`).
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23 Matrix
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory
  HTGeometry HeckeKreinToeplitz ArithmeticOrientationGeometry SpacingScaleHarmonicAnalysis

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-! ### Half-line tests and the confined Gram matrix -/

/-- A `C²` test supported in a window `[−A, 0]` of the half-line. -/
def IsHalfLineTest (H : ℝ → ℝ) : Prop := ContDiff ℝ 2 H ∧ ∃ A : ℝ, ∀ u, u ∉ Icc (-A) 0 → H u = 0

theorem IsHalfLineTest.hasCompactSupport {H : ℝ → ℝ} (hH : IsHalfLineTest H) : HasCompactSupport H := by
  obtain ⟨A, hA⟩ := hH.2
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc fun u hu => by
    by_contra h; exact hu (hA u h)

/-- A finite family of half-line tests lives in one common window. -/
theorem exists_common_window {ι : Type*} [Fintype ι] {H : ι → ℝ → ℝ} (hH : ∀ i, IsHalfLineTest (H i)) :
    ∃ A : ℝ, ∀ i u, u ∉ Icc (-A) 0 → H i u = 0 := by
  choose A hA using fun i => (hH i).2
  refine ⟨∑ i, |A i|, fun i u hu => hA i u fun h => hu ⟨?_, h.2⟩⟩
  have : A i ≤ ∑ j, |A j| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (A j)) (Finset.mem_univ i))
  linarith [h.1]

variable {ι : Type*} [Fintype ι]

/-- The Gram matrix `∫ H_i H_j e^{−8u}` of the confinement mass. -/
def confinementGram (H : ι → ℝ → ℝ) : Matrix ι ι ℂ :=
  fun i j => ((∫ u, H i u * H j u * Real.exp (-(8 * u)) : ℝ) : ℂ)

/-- The Gram matrix of the confined form `Q_R = W + a(R) W₈` on a finite family of tests. -/
def confinedGram (R : ℝ) (H : ι → ℝ → ℝ) : Matrix ι ι ℂ :=
  weilGram Λw (fun i => cx (H i)) + (criticalAliasCoefficient R : ℂ) • confinementGram H

/-- The Hermitian form is additive in the matrix and real-homogeneous. -/
theorem hermQuad_add_smul (A B : Matrix ι ι ℂ) (t : ℝ) (x : ι → ℂ) :
    hermQuad (A + (t : ℂ) • B) x = hermQuad A x + t * hermQuad B x := by
  simp only [hermQuad, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]

/-- On real coefficients the confinement form is `∫ (Σ y_i H_i)² e^{−8u}`. -/
theorem hermQuad_confinementGram_ofReal {H : ι → ℝ → ℝ} (hc : ∀ i, Continuous (H i))
    (hs : ∀ i, HasCompactSupport (H i)) (y : ι → ℝ) :
    hermQuad (confinementGram H) (fun i => (y i : ℂ)) =
      ∫ u, (∑ i, y i * H i u) ^ 2 * Real.exp (-(8 * u)) := by
  have hint : ∀ i j, Integrable fun u => H i u * H j u * Real.exp (-(8 * u)) := fun i j =>
    (((hc i).mul (hc j)).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hs i).mul_right.mul_right : HasCompactSupport (H i * H j * fun u => Real.exp (-(8 * u))))
  have hexp : (fun u => (∑ i, y i * H i u) ^ 2 * Real.exp (-(8 * u))) =
      fun u => ∑ i, ∑ j, y i * y j * (H i u * H j u * Real.exp (-(8 * u))) := by
    funext u
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexp, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
  simp only [hermQuad, dotProduct, mulVec, confinementGram, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- The confinement form is nonnegative. -/
theorem hermQuad_confinementGram_nonneg {H : ι → ℝ → ℝ} (hc : ∀ i, Continuous (H i))
    (hs : ∀ i, HasCompactSupport (H i)) (x : ι → ℂ) : 0 ≤ hermQuad (confinementGram H) x := by
  rw [hermQuad_eq_re_add_im (G := confinementGram H) (fun i j => Complex.ofReal_im _),
    hermQuad_confinementGram_ofReal hc hs, hermQuad_confinementGram_ofReal hc hs]
  exact add_nonneg (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)

/-- **The confined Gram matrix is the Gram matrix of the critical energy.** On real coefficients its
form is the full critical energy at ratio `R` of the combination of the tests. -/
theorem hermQuad_confinedGram_ofReal (R : ℝ) {H : ι → ℝ → ℝ} (hH : ∀ i, IsHalfLineTest (H i))
    (y : ι → ℝ) :
    hermQuad (confinedGram R H) (fun i => (y i : ℂ)) =
      criticalHalfLineFullEnergy R (fun u => ∑ i, y i * H i u) := by
  obtain ⟨A, hA⟩ := exists_common_window hH
  have hs : ∀ i, HasCompactSupport (H i) := fun i => (hH i).hasCompactSupport
  have hc : ∀ i, Continuous (H i) := fun i => (hH i).1.continuous
  set G : ℝ → ℝ := fun u => ∑ i, y i * H i u
  have hG : ContDiff ℝ 2 G := ContDiff.sum fun i _ => contDiff_const.mul (hH i).1
  have hGv : ∀ u, u ∉ Icc (-A) 0 → G u = 0 := fun u hu => by simp [G, hA _ u hu]
  have hGc : HasCompactSupport G := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    fun u hu => by by_contra h; exact hu (hGv u h)
  rw [confinedGram, hermQuad_add_smul, hermQuad_weilGram_ofReal (fun i => (hH i).1) hA,
    hermQuad_confinementGram_ofReal hc hs, weilQuad_eq_arch_sub_prime_add_pole hG hGc]
  have hG0 : G 0 = 0 := by
    have h1 : Tendsto G (𝓝[>] 0) (𝓝 (G 0)) :=
      hG.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto G (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds.congr'
      (eventually_nhdsWithin_of_forall fun u (hu : 0 < u) =>
        (hGv u fun h => absurd h.2 (not_le.mpr hu)).symm)
    exact tendsto_nhds_unique h1 h2
  have hI : (∫ u in Iio 0, G u ^ 2 * Real.exp (-(8 * u))) = ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_
    rcases (not_lt.mp (show ¬ u < 0 from hu)).lt_or_eq with h | h
    · rw [hGv u fun hm => absurd hm.2 (not_le.mpr h)]; ring
    · rw [← h, hG0]; ring
  rw [criticalHalfLineFullEnergy, hI]

/-! ### The confinement coefficient -/

theorem criticalAliasCoefficient_antitone {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    criticalAliasCoefficient S ≤ criticalAliasCoefficient R := by
  rw [criticalAliasCoefficient_eq_div S, criticalAliasCoefficient_eq_div R]
  exact div_le_div_of_nonneg_left (criticalAliasCoefficient_positive one_pos).le hR hRS

theorem tendsto_criticalAliasCoefficient_atTop :
    Tendsto criticalAliasCoefficient atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.const_mul (criticalAliasCoefficient 1)
  rw [mul_zero] at h
  exact h.congr fun R => by rw [criticalAliasCoefficient_eq_div R, div_eq_mul_inv]

/-! ### Monotonicity and the upper bound -/

/-- **The index grows with the ratio**: the confinement `a(R) W₈ ≥ 0` decreases. -/
theorem hermNegIndex_confinedGram_mono {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) {H : ι → ℝ → ℝ}
    (hc : ∀ i, Continuous (H i)) (hs : ∀ i, HasCompactSupport (H i)) :
    hermNegIndex (confinedGram R H) ≤ hermNegIndex (confinedGram S H) := by
  refine hermNegIndex_le_of_hermQuad_le _ _ fun x => ?_
  simp only [confinedGram, hermQuad_add_smul]
  have h0 := hermQuad_confinementGram_nonneg hc hs x
  have ha := criticalAliasCoefficient_antitone hR hRS
  nlinarith

/-- **The index is bounded by the right zeros.** The confined form dominates Weil's form, whose Gram
matrix has at most as many negative squares as `ζ` has zeros right of the line. -/
theorem hermNegIndex_confinedGram_le {R : ℝ} (hR : 0 < R) {H : ι → ℝ → ℝ}
    (hH : ∀ i, ContDiff ℝ 2 (H i)) (hs : ∀ i, HasCompactSupport (H i)) :
    (hermNegIndex (confinedGram R H) : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
  have hle : hermNegIndex (confinedGram R H) ≤ hermNegIndex (weilGram Λw fun i => cx (H i)) := by
    refine hermNegIndex_le_of_hermQuad_le _ _ fun x => ?_
    rw [confinedGram, hermQuad_add_smul]
    have h0 := hermQuad_confinementGram_nonneg (fun i => (hH i).continuous) hs x
    have ha := (criticalAliasCoefficient_positive hR).le
    nlinarith
  exact (by exact_mod_cast hle : (hermNegIndex (confinedGram R H) : ℕ∞) ≤ _).trans
    (negIndex_weilGram_le_offLineCount (fun i => cx (H i)) (fun i => cx_contDiff (hH i))
      fun i => (hs i).comp_left Complex.ofReal_zero)

/-! ### The lower bound at large ratios -/

/-- The cubic spline shifted to `u − t`. -/
theorem isHalfLineTest_shiftedSpline {t : ℝ} (ht : t ≤ -4) :
    IsHalfLineTest (scaleShift t BiScaleUncertainty.ChebyshevGauge.cubicSpline) := by
  refine ⟨BiScaleUncertainty.ChebyshevGauge.contDiff_cubicSpline.comp (contDiff_id.sub contDiff_const),
    -(t - 4), fun u hu => ?_⟩
  refine BiScaleUncertainty.ChebyshevGauge.cubicSpline_eq_zero ?_
  rcases not_and_or.mp hu with h | h
  · rw [not_le] at h; rw [abs_of_neg (by linarith)]; linarith
  · rw [not_le] at h; rw [abs_of_pos (by linarith)]; linarith

/-- **Translates of the cubic spline carry every negative square at large ratios.** If `ζ` has at
least `n` zeros right of the line, some finite family of half-line tests has a confined Gram matrix
with at least `n` negative squares at every large ratio. -/
theorem exists_halfLineTests_eventually_le_hermNegIndex {n : ℕ}
    (hn : (n : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard) :
    ∃ (S : Finset ℝ) (H : S → ℝ → ℝ), (∀ s, IsHalfLineTest (H s)) ∧
      ∀ᶠ R in atTop, n ≤ hermNegIndex (confinedGram R H) := by
  have hsp : BiScaleUncertainty.ChebyshevGauge.cubicSpline ∈ realTests :=
    ⟨BiScaleUncertainty.ChebyshevGauge.contDiff_cubicSpline,
      BiScaleUncertainty.ChebyshevGauge.hasCompactSupport_cubicSpline⟩
  obtain ⟨S, -, hS⟩ := (zeta_orientationIndex_law hsp denseShifts_ratHecke n).2
    (by rwa [seenRightZeros_cubicSpline])
  set c : ℝ := -(∑ s ∈ S, |s|) - 4
  let H : S → ℝ → ℝ := fun s => scaleShift ((s : ℝ) + c) BiScaleUncertainty.ChebyshevGauge.cubicSpline
  have hH : ∀ s, IsHalfLineTest (H s) := fun s => isHalfLineTest_shiftedSpline (by
    have : (s : ℝ) ≤ ∑ s ∈ S, |s| :=
      (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg j) s.2)
    simp only [c]; linarith)
  have hfun : (fun s : S => cx (H s)) = fun s : S => ArithmeticCastelnuovoSeveri.translate
      ((s : ℝ) + c) (cx BiScaleUncertainty.ChebyshevGauge.cubicSpline) :=
    funext fun s => cx_scaleShift_eq_translate _ _
  have hW : weilGram Λw (fun s => cx (H s)) =
      weilGram Λw (fun s : S => ArithmeticCastelnuovoSeveri.translate (s : ℝ)
        (cx BiScaleUncertainty.ChebyshevGauge.cubicSpline)) := by
    rw [hfun, weilGram_translate_add]
  refine ⟨S, H, hH, ?_⟩
  have hlim : ∀ a b, Tendsto (fun R => confinedGram R H a b) atTop
      (𝓝 (weilGram Λw (fun s => cx (H s)) a b)) := fun a b => by
    have h := ((Complex.continuous_ofReal.tendsto 0).comp tendsto_criticalAliasCoefficient_atTop).mul_const
      (confinementGram H a b)
    simp only [Function.comp_def, Complex.ofReal_zero, zero_mul] at h
    have h2 : Tendsto (fun R => weilGram Λw (fun s => cx (H s)) a b +
        (criticalAliasCoefficient R : ℂ) * confinementGram H a b) atTop
        (𝓝 (weilGram Λw (fun s => cx (H s)) a b)) := by
      simpa only [add_zero] using tendsto_const_nhds.add h
    exact h2.congr fun R => by simp only [confinedGram, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  filter_upwards [eventually_le_hermNegIndex (weilGram_isHermitian _ _) hlim] with R hR
  rw [hW] at hR
  exact hS.trans hR

/-! ### The index law -/

/-- **The index law of the confined form.** Some confined Gram matrix of half-line tests has at least
`n` negative squares iff `ζ` has at least `n` zeros right of the critical line. -/
theorem confinedIndex_law (n : ℕ) :
    (∃ (R : ℝ) (_ : 0 < R) (S : Finset ℝ) (H : S → ℝ → ℝ), (∀ s, IsHalfLineTest (H s)) ∧
        n ≤ hermNegIndex (confinedGram R H)) ↔
      (n : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
  constructor
  · rintro ⟨R, hR, S, H, hH, hn⟩
    exact (by exact_mod_cast hn : (n : ℕ∞) ≤ hermNegIndex (confinedGram R H)).trans
      (hermNegIndex_confinedGram_le hR (fun s => (hH s).1) fun s => (hH s).hasCompactSupport)
  · intro hn
    obtain ⟨S, H, hH, hev⟩ := exists_halfLineTests_eventually_le_hermNegIndex hn
    obtain ⟨R, hR, hpos⟩ := (hev.and (eventually_gt_atTop 0)).exists
    exact ⟨R, hpos, S, H, hH, hR⟩

/-- **Off RH some ratio carries two negative squares**: right zeros come in conjugate pairs. -/
theorem exists_two_le_hermNegIndex_confinedGram_of_not_RH (h : ¬ RiemannHypothesis) :
    ∃ (R : ℝ) (_ : 0 < R) (S : Finset ℝ) (H : S → ℝ → ℝ), (∀ s, IsHalfLineTest (H s)) ∧
      2 ≤ hermNegIndex (confinedGram R H) := by
  refine (confinedIndex_law 2).2 ?_
  have hne : {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re} ≠ ∅ := fun he =>
    h (riemannHypothesis_iff_no_rightZero.2 he)
  have hsec : (sectorZeros zetaZeroConfig 1).encard ≠ 0 := by
    intro h0
    apply hne
    have h2 := zeta_rightZeros_encard_eq_two_mul_sectorZeros 1
    rw [h0, mul_zero] at h2
    exact Set.encard_eq_zero.mp h2
  have h2 := zeta_rightZeros_encard_eq_two_mul_sectorZeros 1
  change (2 : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard
  rw [h2]
  calc (2 : ℕ∞) = 2 * 1 := by norm_num
    _ ≤ 2 * (sectorZeros zetaZeroConfig 1).encard := by
      gcongr; exact Order.one_le_iff_ne_zero.mpr hsec

/-- **Bounded index ⇔ finitely many right zeros.** The negative index of the confined form is bounded
over all ratios and all finite families of half-line tests iff `ζ` has finitely many zeros right of
the line. -/
theorem bddAbove_confinedIndex_iff_finite :
    (∃ N : ℕ, ∀ (R : ℝ) (_ : 0 < R) (S : Finset ℝ) (H : S → ℝ → ℝ), (∀ s, IsHalfLineTest (H s)) →
        hermNegIndex (confinedGram R H) ≤ N) ↔
      {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.Finite := by
  constructor
  · rintro ⟨N, hN⟩
    by_contra hinf
    have hle : ((N + 1 : ℕ) : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
      rw [Set.Infinite.encard_eq hinf]; exact le_top
    obtain ⟨R, hR, S, H, hH, hn⟩ := (confinedIndex_law (N + 1)).2 hle
    have := hN R hR S H hH
    omega
  · intro hfin
    refine ⟨hfin.toFinset.card, fun R hR S H hH => ?_⟩
    have h := hermNegIndex_confinedGram_le hR (fun s => (hH s).1) fun s => (hH s).hasCompactSupport
    rw [Set.Finite.encard_eq_coe_toFinset_card hfin] at h
    exact_mod_cast h

end GaloisForLFunctions.ExclusionOfTheCriticalState
