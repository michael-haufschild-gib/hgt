import GaloisForLFunctions.HTGeometry.LogPrimeExponentialCarrier
import GaloisForLFunctions.HTGeometry.EntireSeriesJointHolomorphy
import GaloisForLFunctions.HTGeometry.CompExpDescent
import GaloisForLFunctions.HTGeometry.ExponentialForwardSubstitution
import GaloisForLFunctions.HTGeometry.FamilyPowerGauge
import GaloisForLFunctions.HTGeometry.ExponentialFullIndependence
import GaloisForLFunctions.HTGeometry.DAGaugeCurvatureNecessity
import GaloisForLFunctions.HTGeometry.EntireExponentialCompositionDA
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicInvariance
import GaloisForLFunctions.HTGeometry.EntireFamilyDifferentialAlgebraicLocus

/-!
# Realising a prescribed countable differential-algebraic fibre locus

The fibre locus of a jointly entire family is countable unless it is everything.  This file proves
the sharp converse: every countable subset of the parameter plane is the exact locus, and can be
realised by a family which is zero free and `1`-periodic in the fibre variable.

The family is `exp` of a log-prime exponential carrier evaluated at `e^{2πiz}`, with amplitudes
damped by a Gaussian factor and multiplied by the product of the first `j` prescribed vanishing
factors.  At a prescribed parameter the amplitudes vanish from some index on, so the fibre is a
finite exponential sum, hence satisfies an algebraic differential equation.  Elsewhere every
amplitude is nonzero and the rationally independent prime frequencies forbid every algebraic
differential equation; the exponential and the `e^{2πiz}` substitution both preserve this.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter

noncomputable section

/-- The product of the first `j` factors of a family of entire factors. -/
def zeroProduct (h : ℕ → ℂ → ℂ) (j : ℕ) (t : ℂ) : ℂ := ∏ i ∈ Finset.range j, h i t

theorem norm_zeroProduct_le {h : ℕ → ℂ → ℂ} (hbd : ∀ i t, ‖h i t‖ ≤ ‖t‖ + 1) (j : ℕ) (t : ℂ) :
    ‖zeroProduct h j t‖ ≤ (‖t‖ + 1) ^ j := by
  rw [zeroProduct, norm_prod]
  refine le_trans (Finset.prod_le_prod (fun i _ => norm_nonneg _)
    (fun i _ => hbd i t)) ?_
  simp [Finset.prod_const]

theorem zeroProduct_eq_zero (h : ℕ → ℂ → ℂ) {j i : ℕ} (hij : i < j) {t : ℂ} (hz : h i t = 0) :
    zeroProduct h j t = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.2 hij) hz

theorem zeroProduct_ne_zero (h : ℕ → ℂ → ℂ) (j : ℕ) {t : ℂ} (ht : ∀ i, h i t ≠ 0) :
    zeroProduct h j t ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => ht i

theorem differentiable_zeroProduct {h : ℕ → ℂ → ℂ} (hd : ∀ i, Differentiable ℂ (h i)) (j : ℕ) :
    Differentiable ℂ (zeroProduct h j) := by
  have hp : Differentiable ℂ (∏ i ∈ Finset.range j, fun t : ℂ => h i t) :=
    Differentiable.finsetProd fun i _ => hd i
  have heq : zeroProduct h j = ∏ i ∈ Finset.range j, fun t : ℂ => h i t := by
    funext t
    simp [zeroProduct, Finset.prod_apply]
  rw [heq]
  exact hp

/-- The damped amplitude of the realisation: the prime-power damping of the log-prime carrier,
squared off by a further Gaussian factor which absorbs every polynomial growth in the parameter. -/
def dampedAmplitude (j : ℕ) : ℂ := logPrimeAmplitude j * ((2 : ℂ) ^ (j * j))⁻¹

theorem dampedAmplitude_ne_zero (j : ℕ) : dampedAmplitude j ≠ 0 := by
  refine mul_ne_zero (logPrimeAmplitude_ne_zero j) (inv_ne_zero (pow_ne_zero _ ?_))
  norm_num

theorem norm_dampedAmplitude (j : ℕ) :
    ‖dampedAmplitude j‖ = ‖logPrimeAmplitude j‖ * ((2 : ℝ) ^ (j * j))⁻¹ := by
  rw [dampedAmplitude, norm_mul, norm_inv, norm_pow]
  norm_num

/-- The Gaussian damping beats every geometric growth in the index. -/
theorem summable_geomTimesDamping (B R : ℝ) :
    Summable fun j : ℕ => B ^ j * ‖dampedAmplitude j‖ * Real.exp (R * |logPrimeFrequency j|) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |B| ≤ 2 ^ N := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (R := ℝ) |B| (by norm_num : (1:ℝ) < 2)
    exact ⟨N, hN.le⟩
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun j => ‖logPrimeAmplitude j‖ * Real.exp (R * |logPrimeFrequency j|))
    (expSeriesNormallySummable_logPrime R) ?_
  filter_upwards [eventually_ge_atTop N] with j hj
  have hu : 0 ≤ ‖logPrimeAmplitude j‖ * Real.exp (R * |logPrimeFrequency j|) :=
    mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
  have hBj : |B| ^ j ≤ (2 : ℝ) ^ (j * j) := by
    calc |B| ^ j ≤ ((2:ℝ) ^ N) ^ j := pow_le_pow_left₀ (abs_nonneg B) hN j
      _ = (2:ℝ) ^ (N * j) := by rw [← pow_mul]
      _ ≤ (2:ℝ) ^ (j * j) := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right j hj)
  have hfac : |B ^ j * ‖dampedAmplitude j‖ * Real.exp (R * |logPrimeFrequency j|)|
      = (|B| ^ j * ((2:ℝ) ^ (j * j))⁻¹) *
        (‖logPrimeAmplitude j‖ * Real.exp (R * |logPrimeFrequency j|)) := by
    rw [norm_dampedAmplitude]
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (Real.exp_nonneg _),
      abs_of_nonneg (mul_nonneg (norm_nonneg _) (by positivity))]
    ring
  rw [Real.norm_eq_abs, hfac]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hu) (le_of_eq (one_mul _))
  rw [mul_inv_le_iff₀ (by positivity), one_mul]
  exact hBj

/-- The amplitude of the realising family: the vanishing product damped into summability. -/
def realizationAmplitude (h : ℕ → ℂ → ℂ) (j : ℕ) (t : ℂ) : ℂ :=
  zeroProduct h j t * dampedAmplitude j

theorem norm_realizationAmplitude_le {h : ℕ → ℂ → ℂ} (hbd : ∀ i t, ‖h i t‖ ≤ ‖t‖ + 1)
    (j : ℕ) (t : ℂ) :
    ‖realizationAmplitude h j t‖ ≤ (‖t‖ + 1) ^ j * ‖dampedAmplitude j‖ := by
  rw [realizationAmplitude, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_zeroProduct_le hbd j t) (norm_nonneg _)

theorem expSeriesNormallySummable_realizationAmplitude {h : ℕ → ℂ → ℂ}
    (hbd : ∀ i t, ‖h i t‖ ≤ ‖t‖ + 1) (t : ℂ) :
    ExpSeriesNormallySummable (fun j => realizationAmplitude h j t) logPrimeFrequency := by
  intro R
  refine Summable.of_norm_bounded (summable_geomTimesDamping (‖t‖ + 1) R) fun j => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))]
  exact mul_le_mul_of_nonneg_right (norm_realizationAmplitude_le hbd j t) (Real.exp_nonneg _)

/-- The realising two-variable carrier. -/
def realizationCarrier (h : ℕ → ℂ → ℂ) (t w : ℂ) : ℂ :=
  cexpSeriesCarrier (fun j => realizationAmplitude h j t) logPrimeFrequency w

theorem norm_cexpChar_le (omega : ℝ) (w : ℂ) :
    ‖cexpChar omega w‖ ≤ Real.exp (‖w‖ * |omega|) := by
  rw [norm_cexpChar]
  refine Real.exp_le_exp.2 ?_
  calc -(omega * w.im) ≤ |omega * w.im| := neg_le_abs _
    _ = |omega| * |w.im| := abs_mul _ _
    _ ≤ |omega| * ‖w‖ := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm w) (abs_nonneg _)
    _ = ‖w‖ * |omega| := by ring

theorem differentiable_realizationCarrier {h : ℕ → ℂ → ℂ} (hbd : ∀ i t, ‖h i t‖ ≤ ‖t‖ + 1)
    (hd : ∀ i, Differentiable ℂ (h i)) :
    Differentiable ℂ fun p : ℂ × ℂ => realizationCarrier h p.1 p.2 := by
  have hterm : ∀ j : ℕ, Differentiable ℂ fun p : ℂ × ℂ =>
      realizationAmplitude h j p.1 * cexpChar (logPrimeFrequency j) p.2 := by
    intro j
    refine Differentiable.mul ?_ ?_
    · unfold realizationAmplitude
      exact ((differentiable_zeroProduct hd j).comp differentiable_fst).mul_const _
    · exact (differentiable_cexpChar _).comp differentiable_snd
  have hbd : ∀ (R : ℝ) (j : ℕ) (p : ℂ × ℂ), ‖p‖ ≤ R + 1 →
      ‖realizationAmplitude h j p.1 * cexpChar (logPrimeFrequency j) p.2‖
        ≤ (|R| + 2) ^ j * ‖dampedAmplitude j‖ *
          Real.exp ((|R| + 1) * |logPrimeFrequency j|) := by
    intro R j p hp
    have h1 : ‖p.1‖ ≤ |R| + 1 := le_trans (norm_fst_le p) (le_trans hp (by
      have := le_abs_self R; linarith))
    have h2 : ‖p.2‖ ≤ |R| + 1 := le_trans (norm_snd_le p) (le_trans hp (by
      have := le_abs_self R; linarith))
    rw [norm_mul]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
    · refine le_trans (norm_realizationAmplitude_le hbd j p.1) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact pow_le_pow_left₀ (by positivity) (by linarith) j
    · refine le_trans (norm_cexpChar_le _ _) ?_
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
  have := differentiable_tsum_of_ball_bounds (f := fun (j : ℕ) (p : ℂ × ℂ) =>
      realizationAmplitude h j p.1 * cexpChar (logPrimeFrequency j) p.2) hterm
    (M := fun R j => (|R| + 2) ^ j * ‖dampedAmplitude j‖ *
      Real.exp ((|R| + 1) * |logPrimeFrequency j|))
    (fun R => summable_geomTimesDamping (|R| + 2) (|R| + 1)) hbd
  exact this

theorem differentiable_realizationCarrier_fibre {h : ℕ → ℂ → ℂ}
    (hbd : ∀ i t, ‖h i t‖ ≤ ‖t‖ + 1) (t : ℂ) :
    Differentiable ℂ (realizationCarrier h t) :=
  differentiable_cexpSeriesCarrier (expSeriesNormallySummable_realizationAmplitude hbd t)

theorem analyticOnNhd_realizationCarrier {h : ℕ → ℂ → ℂ} (hbd : ∀ i t, ‖h i t‖ ≤ ‖t‖ + 1)
    (t : ℂ) :
    AnalyticOnNhd ℂ (realizationCarrier h t) Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.2 (differentiable_realizationCarrier_fibre hbd t)

/-- The exponentiated carrier: entire and zero free. -/
def realizationExpCarrier (h : ℕ → ℂ → ℂ) (t w : ℂ) : ℂ := Complex.exp (realizationCarrier h t w)

theorem differentiable_realizationExpCarrier {h : ℕ → ℂ → ℂ} (hbd : ∀ i t, ‖h i t‖ ≤ ‖t‖ + 1)
    (t : ℂ) :
    Differentiable ℂ (realizationExpCarrier h t) :=
  Complex.differentiable_exp.comp (differentiable_realizationCarrier_fibre hbd t)

/-- The realising family: the exponential of the log-prime carrier evaluated at `e^{2πiz}`. -/
def daLocusRealization (h : ℕ → ℂ → ℂ) (t z : ℂ) : ℂ :=
  realizationExpCarrier h t (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))

theorem daLocusTwoPiI_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- The realising family is jointly entire. -/
theorem differentiable_realization {h : ℕ → ℂ → ℂ} (hbd : ∀ i t, ‖h i t‖ ≤ ‖t‖ + 1)
    (hd : ∀ i, Differentiable ℂ (h i)) :
    Differentiable ℂ fun p : ℂ × ℂ => daLocusRealization h p.1 p.2 := by
  have h2 : Differentiable ℂ fun p : ℂ × ℂ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * p.2) :=
    Complex.differentiable_exp.comp (by fun_prop)
  have h3 : Differentiable ℂ fun p : ℂ × ℂ =>
      ((p.1, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * p.2)) : ℂ × ℂ) :=
    Differentiable.prodMk differentiable_fst h2
  have h1 : Differentiable ℂ fun p : ℂ × ℂ =>
      realizationCarrier h p.1 (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * p.2)) :=
    (differentiable_realizationCarrier hbd hd).comp h3
  exact Complex.differentiable_exp.comp h1

/-- The realising family never vanishes. -/
theorem realization_ne_zero (h : ℕ → ℂ → ℂ) (t z : ℂ) : daLocusRealization h t z ≠ 0 :=
  Complex.exp_ne_zero _

/-- The realising family is `1`-periodic in its second variable. -/
theorem realization_periodic (h : ℕ → ℂ → ℂ) (t z : ℂ) :
    daLocusRealization h t (z + 1) = daLocusRealization h t z := by
  unfold daLocusRealization
  have h : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (z + 1))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) := by
    rw [mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [h]

/-! ### The fibres off the prescribed set -/

theorem realizationAmplitude_ne_zero (h : ℕ → ℂ → ℂ) {t : ℂ} (ht : ∀ i, h i t ≠ 0) (j : ℕ) :
    realizationAmplitude h j t ≠ 0 :=
  mul_ne_zero (zeroProduct_ne_zero h j ht) (dampedAmplitude_ne_zero j)

theorem infinite_support_realizationAmplitude (h : ℕ → ℂ → ℂ) {t : ℂ} (ht : ∀ i, h i t ≠ 0) :
    {j : ℕ | realizationAmplitude h j t ≠ 0}.Infinite := by
  have hall : {j : ℕ | realizationAmplitude h j t ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall fun j => realizationAmplitude_ne_zero h ht j
  rw [hall]
  exact Set.infinite_univ

theorem differentiallyAlgebraicOn_univ_of_differentiallyAlgebraic {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiallyAlgebraic f) : DifferentiallyAlgebraicOn f U := by
  obtain ⟨n, P, hP, hrel⟩ := hf
  exact ⟨n, P, hP, fun z _ => hrel z⟩

/-- **A fibre at which no factor vanishes is hypertranscendental.** -/
theorem not_differentiallyAlgebraic_realization {h : ℕ → ℂ → ℂ}
    (hbd : ∀ i t, ‖h i t‖ ≤ ‖t‖ + 1) {t : ℂ} (ht : ∀ i, h i t ≠ 0) :
    ¬ DifferentiallyAlgebraic (daLocusRealization h t) := by
  intro hDA
  have hexp : DifferentiallyAlgebraic (realizationExpCarrier h t) :=
    differentiallyAlgebraic_of_comp_exp
      (differentiable_realizationExpCarrier hbd t).contDiff daLocusTwoPiI_ne_zero hDA
  have hcar : ¬ DifferentiallyAlgebraicOn (realizationCarrier h t) Set.univ :=
    not_differentiallyAlgebraicOn_cexpSeriesCarrier
      rationallyIndependentSequence_logPrimeFrequency
      (expSeriesNormallySummable_realizationAmplitude hbd t)
      (infinite_support_realizationAmplitude h ht) isOpen_univ Set.univ_nonempty
  have hfam : ¬ FamilyDifferentiallyAlgebraicOn (fun _ : Fin 1 => realizationCarrier h t)
      Set.univ := fun hf => hcar ((familyDifferentiallyAlgebraicOn_one_iff _ _).1 hf)
  have hexpfam := not_familyDifferentiallyAlgebraicOn_exp isOpen_univ isPreconnected_univ
    Set.univ_nonempty (fun _ => analyticOnNhd_realizationCarrier hbd t) hfam
  exact hexpfam ((familyDifferentiallyAlgebraicOn_one_iff _ _).2
    (differentiallyAlgebraicOn_univ_of_differentiallyAlgebraic hexp))

/-! ### The fibres on the prescribed set -/

theorem realizationAmplitude_eq_zero (h : ℕ → ℂ → ℂ) {i j : ℕ} (hij : i < j) {t : ℂ}
    (hz : h i t = 0) : realizationAmplitude h j t = 0 := by
  rw [realizationAmplitude, zeroProduct_eq_zero h hij hz, zero_mul]

theorem realizationCarrier_eq_finset_sum {h : ℕ → ℂ → ℂ} {i : ℕ} {t : ℂ} (hz : h i t = 0)
    (w : ℂ) :
    realizationCarrier h t w
      = ∑ j ∈ Finset.range (i + 1),
          realizationAmplitude h j t * cexpChar (logPrimeFrequency j) w := by
  rw [realizationCarrier, cexpSeriesCarrier]
  refine tsum_eq_sum fun j hj => ?_
  have hij : i < j := by
    rw [Finset.mem_range] at hj
    omega
  rw [realizationAmplitude_eq_zero h hij hz, zero_mul]

theorem differentiallyAlgebraic_realizationCarrier {h : ℕ → ℂ → ℂ} {i : ℕ} {t : ℂ}
    (hz : h i t = 0) : DifferentiallyAlgebraic (realizationCarrier h t) := by
  have heq : realizationCarrier h t
      = fun w => ∑ j ∈ Finset.range (i + 1),
          realizationAmplitude h j t * cexpChar (logPrimeFrequency j) w := by
    funext w
    exact realizationCarrier_eq_finset_sum hz w
  rw [heq]
  refine differentiallyAlgebraic_finsetSum _ _ (fun j _ => ?_) (fun j _ => ?_)
  · exact (differentiable_cexpChar _).const_mul _
  · by_cases hc : realizationAmplitude h j t = 0
    · simpa [hc] using differentiallyAlgebraic_const 0
    · refine (differentiallyAlgebraic_const_mul_iff hc).2 ?_
      exact differentiallyAlgebraic_cexp_linear (Complex.I * (logPrimeFrequency j : ℂ))

/-- **A fibre at which some factor vanishes satisfies an algebraic differential equation.** -/
theorem differentiallyAlgebraic_realization {h : ℕ → ℂ → ℂ}
    (hbd : ∀ i t, ‖h i t‖ ≤ ‖t‖ + 1) {i : ℕ} {t : ℂ} (hz : h i t = 0) :
    DifferentiallyAlgebraic (daLocusRealization h t) := by
  have h1 : DifferentiallyAlgebraic (realizationExpCarrier h t) :=
    differentiallyAlgebraic_cexp_comp (analyticOnNhd_realizationCarrier hbd t)
      (differentiallyAlgebraic_realizationCarrier hz)
  exact differentiallyAlgebraic_comp_exp
    (differentiable_realizationExpCarrier hbd t).contDiff daLocusTwoPiI_ne_zero h1

/-! ### Realising a prescribed countable locus -/

/-- The factor family with a single prescribed zero at `α i`, normalised to keep the growth
linear. -/
def prescribedFactor (α : ℕ → ℂ) (i : ℕ) (t : ℂ) : ℂ := (t - α i) * (((1 + ‖α i‖)⁻¹ : ℝ) : ℂ)

theorem norm_prescribedFactor_le (α : ℕ → ℂ) (i : ℕ) (t : ℂ) :
    ‖prescribedFactor α i t‖ ≤ ‖t‖ + 1 := by
  have hpos : (0 : ℝ) < 1 + ‖α i‖ := by positivity
  rw [prescribedFactor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < (1 + ‖α i‖)⁻¹)]
  rw [mul_inv_le_iff₀ hpos]
  refine le_trans (norm_sub_le t (α i)) ?_
  nlinarith [norm_nonneg t, norm_nonneg (α i)]

theorem differentiable_prescribedFactor (α : ℕ → ℂ) (i : ℕ) :
    Differentiable ℂ (prescribedFactor α i) := by
  unfold prescribedFactor
  fun_prop

theorem prescribedFactor_eq_zero_iff (α : ℕ → ℂ) (i : ℕ) (t : ℂ) :
    prescribedFactor α i t = 0 ↔ t = α i := by
  have hne : (((1 + ‖α i‖)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    positivity
  rw [prescribedFactor, mul_eq_zero, or_iff_left hne, sub_eq_zero]

/-- The factor family with no zeros at all. -/
def unitFactor (_i : ℕ) (_t : ℂ) : ℂ := 1

theorem norm_unitFactor_le (i : ℕ) (t : ℂ) : ‖unitFactor i t‖ ≤ ‖t‖ + 1 := by
  simp only [unitFactor, norm_one]
  have := norm_nonneg t
  linarith

theorem differentiable_unitFactor (i : ℕ) : Differentiable ℂ (unitFactor i) :=
  differentiable_const 1

/-- **Every countable subset of the plane is exactly the differential-algebraic fibre locus of a
jointly entire, zero-free, `1`-periodic family.**  The family is `exp` of a log-prime exponential
carrier evaluated at `e^{2πiz}`; a fibre truncates to a finite exponential sum exactly at the
prescribed parameters, and elsewhere its amplitudes are all nonzero, so the rationally independent
prime frequencies forbid every algebraic differential equation. -/
theorem exists_entire_zeroFree_periodic_family_daLocus (A : Set ℂ) (hA : A.Countable) :
    ∃ G : ℂ × ℂ → ℂ, Differentiable ℂ G ∧ (∀ p, G p ≠ 0) ∧
      (∀ t z : ℂ, G (t, z + 1) = G (t, z)) ∧
      {t : ℂ | DifferentiallyAlgebraic fun z => G (t, z)} = A := by
  rcases Set.eq_empty_or_nonempty A with rfl | hne
  · refine ⟨fun p => daLocusRealization unitFactor p.1 p.2,
      differentiable_realization norm_unitFactor_le differentiable_unitFactor,
      fun p => realization_ne_zero _ _ _, fun t z => realization_periodic _ _ _, ?_⟩
    refine Set.eq_empty_of_forall_notMem fun t ht => ?_
    exact not_differentiallyAlgebraic_realization norm_unitFactor_le
      (fun i => by simp [unitFactor]) ht
  · obtain ⟨α, rfl⟩ := hA.exists_eq_range hne
    refine ⟨fun p => daLocusRealization (prescribedFactor α) p.1 p.2,
      differentiable_realization (norm_prescribedFactor_le α) (differentiable_prescribedFactor α),
      fun p => realization_ne_zero _ _ _, fun t z => realization_periodic _ _ _, ?_⟩
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · intro hDA
      by_contra hnot
      push Not at hnot
      exact not_differentiallyAlgebraic_realization (norm_prescribedFactor_le α)
        (fun i => fun hz => hnot i ((prescribedFactor_eq_zero_iff α i t).1 hz).symm) hDA
    · rintro ⟨i, rfl⟩
      exact differentiallyAlgebraic_realization (norm_prescribedFactor_le α)
        ((prescribedFactor_eq_zero_iff α i (α i)).2 rfl)

/-- **The complete dichotomy.**  The differential-algebraic fibre locus of a jointly entire
one-parameter family is either the whole parameter plane or countable, and every countable subset of
the plane is realised exactly, by a zero-free family which is `1`-periodic in the fibre variable. -/
theorem daLocus_classification :
    (∀ Φ : ℂ × ℂ → ℂ, Differentiable ℂ Φ →
        {t : ℂ | DifferentiallyAlgebraic fun z => Φ (t, z)} = Set.univ ∨
          {t : ℂ | DifferentiallyAlgebraic fun z => Φ (t, z)}.Countable) ∧
      (∀ A : Set ℂ, A.Countable → ∃ G : ℂ × ℂ → ℂ, Differentiable ℂ G ∧ (∀ p, G p ≠ 0) ∧
        (∀ t z : ℂ, G (t, z + 1) = G (t, z)) ∧
        {t : ℂ | DifferentiallyAlgebraic fun z => G (t, z)} = A) :=
  ⟨fun _ hΦ => entireFamily_daLocus_eq_univ_or_countable hΦ,
    fun A hA => exists_entire_zeroFree_periodic_family_daLocus A hA⟩

end

end GaloisForLFunctions.HTGeometry
