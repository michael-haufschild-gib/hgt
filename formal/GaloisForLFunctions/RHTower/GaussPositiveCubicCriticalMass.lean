import Mathlib.Analysis.PSeries
import GaloisForLFunctions.HTGeometry.PositiveOperatorCubicMoment
import GaloisForLFunctions.RHTower.GaussComponentSampledEnergyBounds
import GaloisForLFunctions.RHTower.GaussFourierDiagonal
import GaloisForLFunctions.RHTower.GaussRelativeDiagonal

/-!
# Positive cubic critical mass of the actual Gauss operator

The literal folded Gauss quasi-inner block is positive.  Its source-relative first Fourier
diagonal therefore controls its cubic diagonal by positive moment log-convexity.  At three
components, both reflected orientations eventually dominate one quarter of the coefficient-faithful
critical sampled energy.  Consequently the actual two-sided cubic diagonal partial sums diverge.
-/

open RCLike
open scoped InnerProductSpace ComplexConjugate ComplexOrder

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

/-- The inverse-square prime multiplier is a positive quadratic form. -/
theorem re_inner_gaussPrimeScaleInvSqBlock_nonneg {p : ℝ} (hp : 1 < p)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    0 ≤ re (inner ℂ u (gaussPrimeScaleInvSqBlock hp u)) := by
  rw [MeasureTheory.L2.inner_def]
  rw [← integral_re (MeasureTheory.L2.integrable_inner u (gaussPrimeScaleInvSqBlock hp u))]
  refine integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.lpBoundedMulCLM_coeFn
    (measurable_gaussPrimeScaleInvSqCircle p) zero_le_one
    (norm_gaussPrimeScaleInvSqCircle_le hp) u] with z hz
  change (0 : ℝ) ≤ re (inner ℂ (u z)
    (((MeasureTheory.lpBoundedMulCLM
      (measurable_gaussPrimeScaleInvSqCircle p) zero_le_one
      (norm_gaussPrimeScaleInvSqCircle_le hp)) u :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) z))
  rw [hz, RCLike.inner_apply']
  have hval : gaussPrimeScaleInvSqCircle p z =
      ((gaussPrimeScaleInvSq p
        ((AddCircle.equivIoc (1 : ℝ) 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) : ℝ) : ℂ) := rfl
  rw [hval]
  have hphi : 0 ≤ gaussPrimeScaleInvSq p
      ((AddCircle.equivIoc (1 : ℝ) 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) :=
    (gaussPrimeScaleInvSq_pos _ _).le
  rw [show (starRingEnd ℂ) (u z) *
      (((gaussPrimeScaleInvSq p
          ((AddCircle.equivIoc (1 : ℝ) 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) : ℝ) : ℂ) * u z)
      = ((gaussPrimeScaleInvSq p
          ((AddCircle.equivIoc (1 : ℝ) 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) : ℝ) : ℂ) *
          ((starRingEnd ℂ) (u z) * u z) by ring]
  rw [Complex.conj_mul']
  exact_mod_cast mul_nonneg hphi (sq_nonneg ‖u z‖)

/-- The unscaled folded Gauss quasi-inner block is symmetric. -/
theorem gaussQuasiInnerG_inner {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ))
    (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (gaussQuasiInnerG hm k p u) v : ℂ) =
      inner ℂ u (gaussQuasiInnerG hm k p v) := by
  rw [gaussQuasiInnerG_apply hm k p hp, gaussQuasiInnerG_apply hm k p hp,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  congr 1
  rw [gaussPrimeScaleBlock_inner hp,
    gaussDiagonalBlock_inner hm k p,
    gaussPrimeScaleInvSqBlock_inner hp,
    ← gaussDiagonalBlockStar_inner hm k p,
    gaussPrimeScaleBlock_inner hp]

/-- The unscaled folded Gauss quasi-inner block is positive. -/
theorem gaussQuasiInnerG_isPositive {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) : (gaussQuasiInnerG hm k p).IsPositive := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  refine ⟨gaussQuasiInnerG_inner hm k p hp, fun u => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, gaussQuasiInnerG_inner hm k p hp,
    inner_fourierLp_gaussQuasiInnerG hm k p hp]
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hP := re_inner_gaussPrimeScaleInvSqBlock_nonneg hp
    (gaussDiagonalBlockStar hm k p (gaussPrimeScaleBlock hp u))
  simpa [Complex.mul_re] using mul_nonneg hp0 hP

/-- The full Gauss quasi-inner block remains positive after archimedean scaling. -/
theorem gaussQuasiInnerGFull_isPositive {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) : (gaussQuasiInnerGFull hm k p).IsPositive := by
  rw [gaussQuasiInnerGFull_eq]
  apply (gaussQuasiInnerG_isPositive hm k p).smul_of_nonneg
  change 0 ≤ ((gaussArchScale m ^ 2 : ℝ) : ℂ)
  rw [Complex.nonneg_iff]
  exact ⟨sq_nonneg _, rfl⟩

/-- The one-step moving amplitude is bounded below uniformly by the inverse prime. -/
theorem one_div_prime_le_gaussAmplitudeSegment_one {p s : ℝ}
    (hp : 1 < p) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    1 / p ≤ gaussAmplitudeSegment p 1 s := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hlog : 0 < Real.log p := Real.log_pos hp
  have he1 : 1 ≤ Real.exp (Real.log p * s) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg hlog.le hs0
  have he2 : 1 / p ≤ Real.exp (Real.log p * (s - 1)) := by
    have harg : -Real.log p ≤ Real.log p * (s - 1) := by nlinarith
    have h := Real.exp_le_exp.mpr harg
    rw [Real.exp_neg, Real.exp_log hp0] at h
    simpa [one_div] using h
  rw [gaussAmplitudeSegment]
  norm_num
  have hleft := mul_le_mul_of_nonneg_left he1 (by linarith : 0 ≤ 1 - s)
  have hright := mul_le_mul_of_nonneg_left he2 hs0
  have hpinv : 1 / p ≤ 1 := (div_le_one hp0).mpr hp.le
  have hbase : 1 / p ≤ (1 - s) * 1 + s * (1 / p) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - s) (sub_nonneg.mpr hpinv)]
  simpa [one_div] using hbase.trans (add_le_add hleft hright)

/-- Once the source-relative cofactor is at most `1/(2p)`, the unscaled first Fourier diagonal
retains at least half the squared source coefficient. -/
theorem half_norm_gaussSampleValue_sq_le_re_inner_gaussQuasiInnerG
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {i : ℤ} (hi : i ≠ 0)
    (hF : gaussFoldDefect hm k p hp i *
        (gaussFoldDefect hm k p hp i +
          2 * ‖gaussPrimeScaleBlock hp
            (fourierLp 2 (0 : ℤ) :
              Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))‖)
      ≤ 1 / (2 * (p : ℝ))) :
    ‖gaussSampleValue k p i‖ ^ 2 / 2 ≤
      re (inner ℂ (fourierLp 2 i)
        (gaussQuasiInnerG hm k p (fourierLp 2 i))) := by
  let d2 : ℝ := ‖gaussSampleValue k p i‖ ^ 2
  let A : ℝ := gaussAmplitudeSegment (p : ℝ) 1
    (Int.fract (gaussSamplePhase m p i))
  let F : ℝ := gaussFoldDefect hm k p hp i *
    (gaussFoldDefect hm k p hp i +
      2 * ‖gaussPrimeScaleBlock hp
        (fourierLp 2 (0 : ℤ) :
          Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))‖)
  let z : ℂ := inner ℂ (fourierLp 2 i)
    (gaussQuasiInnerG hm k p (fourierLp 2 i))
  let target : ℂ := (((p : ℝ) : ℂ) *
      (gaussSampleValue k p i * starRingEnd ℂ (gaussSampleValue k p i))) *
    ((A : ℝ) : ℂ)
  have hscalar : ((p : ℝ) : ℂ) *
      (gaussSampleValue k p i * starRingEnd ℂ (gaussSampleValue k p i)) =
      (((p : ℝ) * d2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    dsimp [d2]
    push_cast
    ring
  have htarget_complex : target = ((((p : ℝ) * d2 * A : ℝ)) : ℂ) := by
    change ((((p : ℝ) : ℂ) *
      (gaussSampleValue k p i * starRingEnd ℂ (gaussSampleValue k p i))) *
        ((A : ℝ) : ℂ)) = _
    rw [hscalar]
    exact (Complex.ofReal_mul ((p : ℝ) * d2) A).symm
  have htarget : target.re = (p : ℝ) * d2 * A := by
    rw [htarget_complex]
    rfl
  have hA : 1 / (p : ℝ) ≤ A := by
    apply one_div_prime_le_gaussAmplitudeSegment_one hp
    · exact Int.fract_nonneg _
    · exact Int.fract_lt_one _
  have hrel := norm_inner_gaussQuasiInnerG_sub_amplitude_le hm k p hp hi
  change ‖z - target‖ ≤ ‖(((p : ℝ) : ℂ) *
      (gaussSampleValue k p i * starRingEnd ℂ (gaussSampleValue k p i)))‖ * F at hrel
  have hnormscalar : ‖(((p : ℝ) : ℂ) *
      (gaussSampleValue k p i * starRingEnd ℂ (gaussSampleValue k p i)))‖ =
      (p : ℝ) * d2 := by
    rw [hscalar, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (by positivity) (sq_nonneg _)
  have herror : ‖z - target‖ ≤ d2 / 2 := by
    rw [hnormscalar] at hrel
    calc
      ‖z - target‖ ≤ (p : ℝ) * d2 * F := hrel
      _ ≤ (p : ℝ) * d2 * (1 / (2 * (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hF (mul_nonneg (by positivity) (sq_nonneg _))
      _ = d2 / 2 := by
        have hp0 : (p : ℝ) ≠ 0 := by positivity
        field_simp
  have htarget_lower : d2 ≤ target.re := by
    rw [htarget]
    have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp
    have hpa : 1 ≤ (p : ℝ) * A := by
      calc
        1 = (p : ℝ) * (1 / (p : ℝ)) := by field_simp
        _ ≤ (p : ℝ) * A := mul_le_mul_of_nonneg_left hA hp0.le
    have hd2 : 0 ≤ d2 := by
      dsimp [d2]
      positivity
    calc
      d2 = d2 * 1 := by ring
      _ ≤ d2 * ((p : ℝ) * A) := mul_le_mul_of_nonneg_left hpa hd2
      _ = (p : ℝ) * d2 * A := by ring
  have hre := Complex.abs_re_le_norm (z - target)
  have hreal : target.re - z.re ≤ ‖z - target‖ := by
    have hneg : target.re - z.re ≤ |(z - target).re| := by
      rw [Complex.sub_re]
      nlinarith [neg_le_abs (z.re - target.re)]
    exact hneg.trans hre
  dsimp [z, d2]
  nlinarith

/-- Positivity amplifies the retained source coefficient into the actual cubic Fourier diagonal. -/
theorem eighth_scaled_norm_gaussSampleValue_pow_six_le_re_inner_gaussQuasiInnerGFull_cube
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {i : ℤ} (hi : i ≠ 0)
    (hF : gaussFoldDefect hm k p hp i *
        (gaussFoldDefect hm k p hp i +
          2 * ‖gaussPrimeScaleBlock hp
            (fourierLp 2 (0 : ℤ) :
              Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))‖)
      ≤ 1 / (2 * (p : ℝ))) :
    gaussArchScale m ^ 6 * ‖gaussSampleValue k p i‖ ^ 6 / 8 ≤
      re (inner ℂ (fourierLp 2 i)
        ((gaussQuasiInnerGFull hm k p ^ 3) (fourierLp 2 i))) := by
  let q : ℝ := re (inner ℂ (fourierLp 2 i)
    (gaussQuasiInnerGFull hm k p (fourierLp 2 i)))
  let lower : ℝ := gaussArchScale m ^ 2 * ‖gaussSampleValue k p i‖ ^ 2 / 2
  have hbase := half_norm_gaussSampleValue_sq_le_re_inner_gaussQuasiInnerG
    hm k p hp hi hF
  have hscale : 0 ≤ gaussArchScale m ^ 2 := sq_nonneg _
  have hfirst : lower ≤ q := by
    have hmul := mul_le_mul_of_nonneg_left hbase hscale
    dsimp [lower, q]
    rw [gaussQuasiInnerGFull_eq, smul_apply, inner_smul_right]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    simpa [mul_div_assoc] using hmul
  have hlower : 0 ≤ lower := by
    dsimp [lower]
    positivity
  have hcub : lower ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ hlower hfirst 3
  have hmom := (gaussQuasiInnerGFull_isPositive hm k p).re_inner_pow_three_ge
    (fourierLp 2 i) (norm_fourierLp_eq_one i)
  calc
    gaussArchScale m ^ 6 * ‖gaussSampleValue k p i‖ ^ 6 / 8 = lower ^ 3 := by
      dsimp [lower]
      ring
    _ ≤ q ^ 3 := hcub
    _ ≤ re (inner ℂ (fourierLp 2 i)
        ((gaussQuasiInnerGFull hm k p ^ 3) (fourierLp 2 i))) := by
      simpa [q] using hmom

/-- Real two-orientation cubic diagonal of the actual three-component Gauss block. -/
def gaussCubeTwoSidedDiagonalReal (k : Fin 3) (p : Nat.Primes) (n : ℕ) : ℝ :=
  re (inner ℂ (fourierLp 2 ((n : ℤ) + 1))
      ((gaussQuasiInnerGFull (by omega : 1 ≤ 3) k p ^ 3)
        (fourierLp 2 ((n : ℤ) + 1)))) +
    re (inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
      ((gaussQuasiInnerGFull (by omega : 1 ≤ 3) k p ^ 3)
        (fourierLp 2 (-((n : ℤ) + 1)))))

/-- Both reflected orientations eventually retain one quarter of the sampled critical energy. -/
theorem eventually_quarter_energy_le_gaussCubeTwoSidedDiagonalReal
    (k : Fin 3) (p : Nat.Primes) :
    ∀ᶠ n : ℕ in atTop,
      gaussComponentPrimeMagnitudeEnergy k p n / 4 ≤
        gaussCubeTwoSidedDiagonalReal k p n := by
  have hm : (1 : ℕ) ≤ 3 := by omega
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  let F : ℤ → ℝ := fun i =>
    gaussFoldDefect hm k p hp i *
      (gaussFoldDefect hm k p hp i +
        2 * ‖gaussPrimeScaleBlock hp
          (fourierLp 2 (0 : ℤ) :
            Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))‖)
  have hιp : Tendsto (fun n : ℕ => (((n : ℤ) + 1)).natAbs) atTop atTop := by
    refine (tendsto_add_atTop_nat 1).congr fun n => ?_
    omega
  have hιm : Tendsto (fun n : ℕ => ((-((n : ℤ) + 1))).natAbs) atTop atTop := by
    refine (tendsto_add_atTop_nat 1).congr fun n => ?_
    omega
  have hFp : Tendsto (fun n : ℕ => F ((n : ℤ) + 1)) atTop (nhds 0) :=
    tendsto_gaussRelativeDiagonalFactor hm k p hp hιp
  have hFm : Tendsto (fun n : ℕ => F (-((n : ℤ) + 1))) atTop (nhds 0) :=
    tendsto_gaussRelativeDiagonalFactor hm k p hp hιm
  have hthreshold : (0 : ℝ) < 1 / (2 * (p : ℝ)) := by positivity
  have hFpe : ∀ᶠ n : ℕ in atTop, F ((n : ℤ) + 1) ≤ 1 / (2 * (p : ℝ)) :=
    hFp.eventually (eventually_le_nhds hthreshold)
  have hFme : ∀ᶠ n : ℕ in atTop, F (-((n : ℤ) + 1)) ≤ 1 / (2 * (p : ℝ)) :=
    hFm.eventually (eventually_le_nhds hthreshold)
  filter_upwards [hFpe, hFme] with n hpos hneg
  have hip : ((n : ℤ) + 1) ≠ 0 := by omega
  have him : (-((n : ℤ) + 1)) ≠ 0 := by omega
  have hcubep :=
    eighth_scaled_norm_gaussSampleValue_pow_six_le_re_inner_gaussQuasiInnerGFull_cube
      hm k p hp hip hpos
  have hcubem :=
    eighth_scaled_norm_gaussSampleValue_pow_six_le_re_inner_gaussQuasiInnerGFull_cube
      hm k p hp him hneg
  have henergyp : gaussArchScale 3 ^ 6 *
      ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ 6 =
        gaussComponentPrimeMagnitudeEnergy k p n := by
    have h := norm_gaussSampleValueFull_pow hm k p hip
    rw [show (((n : ℤ) + 1).natAbs - 1) = n by omega] at h
    simpa using h
  have henergym : gaussArchScale 3 ^ 6 *
      ‖gaussSampleValue k p (-((n : ℤ) + 1))‖ ^ 6 =
        gaussComponentPrimeMagnitudeEnergy k p n := by
    have h := norm_gaussSampleValueFull_pow hm k p him
    rw [show ((-((n : ℤ) + 1)).natAbs - 1) = n by omega] at h
    simpa using h
  rw [gaussCubeTwoSidedDiagonalReal]
  rw [henergyp] at hcubep
  rw [henergym] at hcubem
  nlinarith

/-- Every two-orientation cubic diagonal term is nonnegative, including the finite prefix. -/
theorem gaussCubeTwoSidedDiagonalReal_nonneg (k : Fin 3) (p : Nat.Primes) (n : ℕ) :
    0 ≤ gaussCubeTwoSidedDiagonalReal k p n := by
  have hm : (1 : ℕ) ≤ 3 := by omega
  have hT := gaussQuasiInnerGFull_isPositive hm k p
  let ip : ℤ := (n : ℤ) + 1
  let im : ℤ := -((n : ℤ) + 1)
  have hqp : 0 ≤ re (inner ℂ (fourierLp 2 ip)
      (gaussQuasiInnerGFull hm k p (fourierLp 2 ip))) :=
    hT.re_inner_nonneg_right _
  have hqm : 0 ≤ re (inner ℂ (fourierLp 2 im)
      (gaussQuasiInnerGFull hm k p (fourierLp 2 im))) :=
    hT.re_inner_nonneg_right _
  have hmp := hT.re_inner_pow_three_ge
    (fourierLp 2 ip) (norm_fourierLp_eq_one ip)
  have hmm := hT.re_inner_pow_three_ge
    (fourierLp 2 im) (norm_fourierLp_eq_one im)
  have hcp : 0 ≤ re (inner ℂ (fourierLp 2 ip)
      ((gaussQuasiInnerGFull hm k p ^ 3) (fourierLp 2 ip))) :=
    (pow_nonneg hqp 3).trans hmp
  have hcm : 0 ≤ re (inner ℂ (fourierLp 2 im)
      ((gaussQuasiInnerGFull hm k p ^ 3) (fourierLp 2 im))) :=
    (pow_nonneg hqm 3).trans hmm
  simpa [gaussCubeTwoSidedDiagonalReal, ip, im] using add_nonneg hcp hcm

/-- The actual two-orientation cubic Gauss diagonal has divergent positive partial sums. -/
theorem tendsto_gaussCubeTwoSidedDiagonal_sum_atTop (k : Fin 3) (p : Nat.Primes) :
    Tendsto
      (fun M : ℕ => ∑ n ∈ Finset.range M, gaussCubeTwoSidedDiagonalReal k p n)
      atTop atTop := by
  have hm : (1 : ℕ) ≤ 3 := by omega
  obtain ⟨c, C, hc, hC, henergy⟩ :=
    exists_gaussComponentPrimeMagnitudeEnergy_bounds hm k p
  have hevent := eventually_quarter_energy_le_gaussCubeTwoSidedDiagonalReal k p
  have hpoint : ∀ᶠ n : ℕ in atTop,
      c / (4 * ((n : ℝ) + 1)) ≤ gaussCubeTwoSidedDiagonalReal k p n := by
    filter_upwards [hevent] with n hn
    have hlow := (henergy n).1
    calc
      c / (4 * ((n : ℝ) + 1)) = (c / ((n : ℝ) + 1)) / 4 := by
        have hn0 : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp
      _ ≤ gaussComponentPrimeMagnitudeEnergy k p n / 4 := by
        exact div_le_div_of_nonneg_right hlow (by norm_num)
      _ ≤ gaussCubeTwoSidedDiagonalReal k p n := hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpoint
  let r : ℝ := c / (4 * ((N : ℝ) + 1))
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hshift_point : ∀ j : ℕ,
      r * (1 / ((j : ℝ) + 1)) ≤ gaussCubeTwoSidedDiagonalReal k p (N + j) := by
    intro j
    have hNj := hN (N + j) (Nat.le_add_right N j)
    have hden : 4 * ((N : ℝ) + (j : ℝ) + 1) ≤
        4 * ((N : ℝ) + 1) * ((j : ℝ) + 1) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)
        (show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j)]
    have hsmall : 0 < 4 * ((N : ℝ) + (j : ℝ) + 1) := by positivity
    have hfrac : c / (4 * ((N : ℝ) + 1) * ((j : ℝ) + 1)) ≤
        c / (4 * ((N : ℝ) + (j : ℝ) + 1)) :=
      div_le_div_of_nonneg_left hc.le hsmall hden
    calc
      r * (1 / ((j : ℝ) + 1)) =
          c / (4 * ((N : ℝ) + 1) * ((j : ℝ) + 1)) := by
        dsimp [r]
        field_simp
      _ ≤ c / (4 * ((N : ℝ) + (j : ℝ) + 1)) := hfrac
      _ = c / (4 * (((N + j : ℕ) : ℝ) + 1)) := by push_cast; ring
      _ ≤ gaussCubeTwoSidedDiagonalReal k p (N + j) := hNj
  have hsum_shift : ∀ M : ℕ,
      r * (∑ j ∈ Finset.range M, (1 / ((j : ℝ) + 1))) ≤
        ∑ j ∈ Finset.range M, gaussCubeTwoSidedDiagonalReal k p (N + j) := by
    intro M
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hshift_point j
  have hsum_total : ∀ M : ℕ,
      r * (∑ j ∈ Finset.range M, (1 / ((j : ℝ) + 1))) ≤
        ∑ j ∈ Finset.range (N + M), gaussCubeTwoSidedDiagonalReal k p j := by
    intro M
    rw [Finset.sum_range_add]
    exact (hsum_shift M).trans (le_add_of_nonneg_left
      (Finset.sum_nonneg fun j _ => gaussCubeTwoSidedDiagonalReal_nonneg k p j))
  have hharm : Tendsto
      (fun M : ℕ => r * (∑ j ∈ Finset.range M, (1 / ((j : ℝ) + 1))))
      atTop atTop :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop hr
  have hshift : Tendsto
      (fun M : ℕ => ∑ j ∈ Finset.range (N + M), gaussCubeTwoSidedDiagonalReal k p j)
      atTop atTop :=
    tendsto_atTop_mono hsum_total hharm
  have hshift' : Tendsto
      (fun M : ℕ => ∑ j ∈ Finset.range (M + N), gaussCubeTwoSidedDiagonalReal k p j)
      atTop atTop := by
    simpa [Nat.add_comm] using hshift
  exact (tendsto_add_atTop_iff_nat N).mp hshift'

end

end RHTower
