import GaloisForLFunctions.RHTower.PutnamJumpBlowUp
import GaloisForLFunctions.RHTower.StripHorizontalShift

/-!
# Near-arithmetic ladders of zeta zeros

Putnam's periodisation has a jump at the origin, and the conjugate Cauchy kernel picks that jump out
with unbounded mass.  Its Fourier coefficients along a vertical progression are the normalised zeta
values, so the pairing stays bounded as soon as those of nonnegative index are absolutely summable.
This upgrades Putnam's theorem to a divergence:

`∑_{n ≥ 0} |ζ(½+i(a+dn))| / |½+i(a+dn)| = ∞`.

Divergence survives perturbation.  If `ζ(½+i(a+dn)+η_n) = 0` along a tail with `η ∈ ℓ²`, a second-order
Taylor expansion of the Laplace representation bounds the normalised zeta value at the unperturbed
point by `|η_n| |b_n| + K |η_n|²`, where `b_n` samples the Fourier transform of `x C_a(x)`.  A Bessel
inequality on the lattice dual to `d` gives `b ∈ ℓ²`, so the coefficients would be summable.

Consequently no sequence of zeros lies within an `ℓ²` perturbation of an arithmetic progression. The
perturbation may be complex, so the zeros need not lie on the critical line.
-/

open Complex MeasureTheory Set Filter Topology HTGeometry

noncomputable section

namespace RHTower

/-! ### Divergence along a progression -/

/-- The power pairing of the periodisation is the Fourier coefficient scaled by `r^m`. -/
theorem integral_periodization_conjPow_eq {a d : ℝ} (r : ℝ) (m : ℕ) :
    (∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        putnamPeriodization a d y * ((r : ℂ) * Complex.exp (-(d : ℂ) * (y : ℂ) * I)) ^ m)
      = (r : ℂ) ^ m * ∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (m : ℤ) x := by
  have hpt : ∀ y : ℝ,
      putnamPeriodization a d y * ((r : ℂ) * Complex.exp (-(d : ℂ) * (y : ℂ) * I)) ^ m
        = (r : ℂ) ^ m * putnamPeriodTwist a d (m : ℤ) y := by
    intro y
    rw [putnamPeriodTwist, mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpt y), integral_const_mul]

/-- The conjugate Cauchy pairing expands in Fourier coefficients of nonnegative index, so it is
bounded by their total mass. -/
theorem norm_integral_periodization_conjCauchy_le {a d r A : ℝ} (hd : 0 < d)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hA : ∀ N : ℕ, ∑ m ∈ Finset.range N,
      ‖∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (m : ℤ) x‖ ≤ A) :
    ‖∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        putnamPeriodization a d y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)‖ ≤ A := by
  classical
  set P := putnamPeriod d with hPdef
  set D := putnamPeriodization a d with hDdef
  set w : ℝ → ℂ := fun y => (r : ℂ) * Complex.exp (-(d : ℂ) * (y : ℂ) * I) with hwdef
  set M := periodizationBound d with hMdef
  have hPpos : 0 < P := putnamPeriod_pos hd
  have hrle : (0 : ℝ) < 1 - r := by linarith
  have hkey : ∀ y : ℝ, (starRingEnd ℂ) ((circleFactor r d y)⁻¹) = (1 - w y)⁻¹ := by
    intro y
    rw [map_inv₀, conj_circleFactor]
  have hcontK : Continuous (fun y : ℝ => (1 - w y)⁻¹) :=
    (continuous_const.sub (continuous_conjArg r d)).inv₀
      (fun y => one_sub_conjArg_ne_zero hr0 hr1 d y)
  have hboundK : ∀ y : ℝ, ‖(1 - w y)⁻¹‖ ≤ (1 - r)⁻¹ := by
    intro y
    rw [norm_inv]
    gcongr
    exact norm_one_sub_conjArg_ge hr0 d y
  have hpow : ∀ n : ℕ, IntegrableOn (fun y => D y * (w y ^ n * (1 - w y)⁻¹)) (Ioc (0 : ℝ) P) := by
    intro n
    refine integrableOn_periodization_mul hd
      (((continuous_conjArg r d).pow n).mul hcontK) (C := r ^ n * (1 - r)⁻¹) (fun y => ?_)
    rw [norm_mul, norm_pow, norm_conjArg r d y hr0]
    exact mul_le_mul_of_nonneg_left (hboundK y) (by positivity)
  have hsum : ∀ n : ℕ, IntegrableOn (fun y => D y * ∑ m ∈ Finset.range n, w y ^ m)
      (Ioc (0 : ℝ) P) := by
    intro n
    refine integrableOn_periodization_mul hd
      (continuous_finsetSum _ fun m _ => (continuous_conjArg r d).pow m)
      (C := ∑ m ∈ Finset.range n, r ^ m) (fun y => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_pow, norm_conjArg r d y hr0]
  have hpartial : ∀ n : ℕ, ‖∫ y in Ioc (0 : ℝ) P, D y * ∑ m ∈ Finset.range n, w y ^ m‖ ≤ A := by
    intro n
    have hpt : ∀ y : ℝ, D y * ∑ m ∈ Finset.range n, w y ^ m
        = ∑ m ∈ Finset.range n, D y * w y ^ m := fun y => by rw [Finset.mul_sum]
    rw [setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpt y)]
    rw [MeasureTheory.integral_finsetSum (s := Finset.range n)
      (f := fun (m : ℕ) (y : ℝ) => D y * w y ^ m)
      (fun m _ => integrableOn_periodization_mul hd ((continuous_conjArg r d).pow m)
        (C := r ^ m) (fun y => by rw [norm_pow, norm_conjArg r d y hr0]))]
    refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum fun m _ => ?_) (hA n))
    rw [integral_periodization_conjPow_eq, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hr0 hr1.le)
  have hstep : ∀ n : ℕ, (∫ y in Ioc (0 : ℝ) P, D y * (1 - w y)⁻¹)
      = (∫ y in Ioc (0 : ℝ) P, D y * ∑ m ∈ Finset.range n, w y ^ m)
        + ∫ y in Ioc (0 : ℝ) P, D y * (w y ^ n * (1 - w y)⁻¹) := by
    intro n
    have hpt : ∀ y : ℝ, D y * (1 - w y)⁻¹
        = D y * ∑ m ∈ Finset.range n, w y ^ m + D y * (w y ^ n * (1 - w y)⁻¹) := by
      intro y
      have hne : (1 : ℂ) - w y ≠ 0 := one_sub_conjArg_ne_zero hr0 hr1 d y
      have hg := geom_sum_mul (w y) n
      field_simp
      linear_combination (D y) * hg
    rw [setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpt y),
      integral_add (hsum n) (hpow n)]
  have htail : ∀ n : ℕ, ‖∫ y in Ioc (0 : ℝ) P, D y * (w y ^ n * (1 - w y)⁻¹)‖
      ≤ M * (1 - r)⁻¹ * P * r ^ n := by
    intro n
    refine le_trans (norm_integral_le_of_norm_le_const (C := M * (1 - r)⁻¹ * r ^ n) ?_) ?_
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun y hy => ?_)
      rw [norm_mul, norm_mul, norm_pow, norm_conjArg r d y hr0]
      have h1 : ‖D y‖ ≤ M := norm_putnamPeriodization_le_bound hd hy
      have h2 : ‖(1 - w y)⁻¹‖ ≤ (1 - r)⁻¹ := hboundK y
      have hMnn : (0 : ℝ) ≤ M := periodizationBound_nonneg d
      have hrnn : (0 : ℝ) ≤ r ^ n := by positivity
      have hinn : (0 : ℝ) ≤ (1 - r)⁻¹ := by positivity
      calc ‖D y‖ * (r ^ n * ‖(1 - w y)⁻¹‖)
          ≤ M * (r ^ n * (1 - r)⁻¹) := by
            refine mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hrnn) (by positivity) hMnn
        _ = M * (1 - r)⁻¹ * r ^ n := by ring
    · have hmeas : (volume.restrict (Ioc (0 : ℝ) P)).real univ = P := by
        simp [MeasureTheory.Measure.real, Real.volume_Ioc]
        linarith
      rw [hmeas]
      have hnn : (0 : ℝ) ≤ M * (1 - r)⁻¹ * r ^ n := by
        have := periodizationBound_nonneg d
        positivity
      nlinarith [hnn, hPpos]
  have hlim : Tendsto (fun n : ℕ => A + M * (1 - r)⁻¹ * P * r ^ n) atTop (𝓝 A) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    simpa using (this.const_mul (M * (1 - r)⁻¹ * P)).const_add A
  rw [setIntegral_congr_fun measurableSet_Ioc (fun y _ => by rw [hkey y])]
  refine ge_of_tendsto' hlim fun n => ?_
  rw [hstep n]
  exact le_trans (norm_add_le _ _) (add_le_add (hpartial n) (htail n))

/-- The pairing against the imaginary part of the Cauchy kernel is controlled by the sup norm of the
periodisation and the total mass of its Fourier coefficients of nonnegative index. -/
theorem norm_integral_periodization_kernelIm_le_of_coeff {a d r A : ℝ} (hd : 0 < d)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hA : ∀ N : ℕ, ∑ m ∈ Finset.range N,
      ‖∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (m : ℤ) x‖ ≤ A) :
    ‖∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        putnamPeriodization a d y * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ)‖
      ≤ (periodizationBound d * putnamPeriod d + 3 * A) / 2 := by
  set P := putnamPeriod d with hPdef
  set D := putnamPeriodization a d with hDdef
  set M := periodizationBound d with hMdef
  have hMnn : (0 : ℝ) ≤ M := periodizationBound_nonneg d
  have hP : 0 < P := putnamPeriod_pos hd
  have hint1 : IntegrableOn (fun y => D y * (circleFactor r d y)⁻¹) (Ioc (0 : ℝ) P) :=
    integrableOn_periodization_mul hd (continuous_circleKernel hr0 hr1 d)
      (norm_circleKernel_le hr0 hr1 d)
  have hint2 : IntegrableOn (fun y => D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹))
      (Ioc (0 : ℝ) P) := by
    refine integrableOn_periodization_mul hd
      (Complex.continuous_conj.comp (continuous_circleKernel hr0 hr1 d))
      (C := (1 - r)⁻¹) (fun y => ?_)
    rw [RCLike.norm_conj]
    exact norm_circleKernel_le hr0 hr1 d y
  have hint3 : IntegrableOn D (Ioc (0 : ℝ) P) := integrableOn_putnamPeriodization hd
  have hconjBound : ‖∫ y in Ioc (0 : ℝ) P, D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)‖ ≤ A :=
    norm_integral_periodization_conjCauchy_le hd hr0 hr1 hA
  have hmean : ‖∫ y in Ioc (0 : ℝ) P, D y‖ ≤ A := by
    have h := hA 1
    rw [Finset.sum_range_one] at h
    refine le_of_eq_of_le ?_ h
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc (fun y _ => ?_)
    rw [putnamPeriodTwist]
    norm_num
    rfl
  -- the Poisson pairing
  have hpt : ∀ y : ℝ, D y * ((poissonFactor r d y : ℝ) : ℂ)
      = D y * (circleFactor r d y)⁻¹ + D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹) - D y := by
    intro y
    have hconj : (circleFactor r d y)⁻¹ + (starRingEnd ℂ) ((circleFactor r d y)⁻¹)
        = 2 * ((((circleFactor r d y)⁻¹).re : ℝ) : ℂ) := by
      rw [Complex.add_conj]
      push_cast
      ring
    rw [poissonFactor]
    push_cast
    rw [show (2 : ℂ) * ((((circleFactor r d y)⁻¹).re : ℝ) : ℂ)
        = (circleFactor r d y)⁻¹ + (starRingEnd ℂ) ((circleFactor r d y)⁻¹) from hconj.symm]
    ring
  have hpoisson : (∫ y in Ioc (0 : ℝ) P, D y * ((poissonFactor r d y : ℝ) : ℂ))
      = (∫ y in Ioc (0 : ℝ) P, D y * (circleFactor r d y)⁻¹)
        + (∫ y in Ioc (0 : ℝ) P, D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹))
        - ∫ y in Ioc (0 : ℝ) P, D y := by
    have hsplit : (∫ y in Ioc (0 : ℝ) P,
          (D y * (circleFactor r d y)⁻¹ + D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹) - D y))
        = (∫ y in Ioc (0 : ℝ) P,
            (D y * (circleFactor r d y)⁻¹ + D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)))
          - ∫ y in Ioc (0 : ℝ) P, D y :=
      integral_sub (hint1.add hint2) hint3
    have hadd : (∫ y in Ioc (0 : ℝ) P,
          (D y * (circleFactor r d y)⁻¹ + D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)))
        = (∫ y in Ioc (0 : ℝ) P, D y * (circleFactor r d y)⁻¹)
          + ∫ y in Ioc (0 : ℝ) P, D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹) :=
      integral_add hint1 hint2
    rw [setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpt y), hsplit, hadd]
  have hpoint : ∀ y : ℝ, ‖D y * ((poissonFactor r d y : ℝ) : ℂ)‖
      = poissonFactor r d y * ‖D y‖ := by
    intro y
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (poissonFactor_nonneg hr0 hr1 d y)]
    ring
  have hPint : IntegrableOn (poissonFactor r d) (Ioc (0 : ℝ) P) :=
    integrableOn_poissonFactor hr0 hr1
  have hintNorm : IntegrableOn (fun y => poissonFactor r d y * ‖D y‖) (Ioc (0 : ℝ) P) := by
    refine ((integrableOn_putnamPeriodization (a := a) hd).norm).bdd_mul
      (c := 2 * (1 - r)⁻¹ + 1)
      ((continuous_poissonFactor hr0 hr1 d).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact abs_poissonFactor_le hr0 hr1 d y
  have hmono : (∫ y in Ioc (0 : ℝ) P, poissonFactor r d y * ‖D y‖)
      ≤ ∫ y in Ioc (0 : ℝ) P, poissonFactor r d y * M := by
    refine setIntegral_mono_on hintNorm (hPint.mul_const M) measurableSet_Ioc (fun y hy => ?_)
    exact mul_le_mul_of_nonneg_left (norm_putnamPeriodization_le_bound hd hy)
      (poissonFactor_nonneg hr0 hr1 d y)
  have hval : (∫ y in Ioc (0 : ℝ) P, poissonFactor r d y * M) = P * M := by
    rw [integral_mul_const, integral_poissonFactor hd hr0 hr1]
  have hpoissonBound : ‖∫ y in Ioc (0 : ℝ) P, D y * ((poissonFactor r d y : ℝ) : ℂ)‖ ≤ P * M := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    rw [setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpoint y)]
    rw [hval] at hmono
    exact hmono
  -- the Cauchy pairing
  have hcauchyBound : ‖∫ y in Ioc (0 : ℝ) P, D y * (circleFactor r d y)⁻¹‖ ≤ P * M + 2 * A := by
    have heq : (∫ y in Ioc (0 : ℝ) P, D y * (circleFactor r d y)⁻¹)
        = (∫ y in Ioc (0 : ℝ) P, D y * ((poissonFactor r d y : ℝ) : ℂ))
          - (∫ y in Ioc (0 : ℝ) P, D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹))
          + ∫ y in Ioc (0 : ℝ) P, D y := by
      rw [hpoisson]
      ring
    rw [heq]
    refine le_trans (norm_add_le _ _) ?_
    have := norm_sub_le (∫ y in Ioc (0 : ℝ) P, D y * ((poissonFactor r d y : ℝ) : ℂ))
      (∫ y in Ioc (0 : ℝ) P, D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹))
    linarith
  -- the imaginary part is half the difference
  have hsub : (∫ y in Ioc (0 : ℝ) P,
        (D y * (circleFactor r d y)⁻¹ - D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)))
      = (∫ y in Ioc (0 : ℝ) P, D y * (circleFactor r d y)⁻¹)
        - ∫ y in Ioc (0 : ℝ) P, D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹) :=
    integral_sub hint1 hint2
  have hptIm : ∀ y : ℝ,
      D y * (circleFactor r d y)⁻¹ - D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)
        = (2 * I) * (D y * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ)) := by
    intro y
    have h := Complex.sub_conj ((circleFactor r d y)⁻¹)
    rw [show D y * (circleFactor r d y)⁻¹ - D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)
        = D y * ((circleFactor r d y)⁻¹ - (starRingEnd ℂ) ((circleFactor r d y)⁻¹)) by ring, h]
    push_cast
    ring
  have hkey : (2 * I) * (∫ y in Ioc (0 : ℝ) P, D y * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ))
      = (∫ y in Ioc (0 : ℝ) P, D y * (circleFactor r d y)⁻¹)
        - ∫ y in Ioc (0 : ℝ) P, D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹) := by
    rw [← integral_const_mul, ← hsub]
    exact (setIntegral_congr_fun measurableSet_Ioc (fun y _ => hptIm y)).symm
  have h2 : ‖(2 : ℂ) * I‖ = 2 := by
    rw [norm_mul, Complex.norm_I, mul_one]
    norm_num
  have hdiff := norm_sub_le (∫ y in Ioc (0 : ℝ) P, D y * (circleFactor r d y)⁻¹)
    (∫ y in Ioc (0 : ℝ) P, D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹))
  have hnorm := congrArg norm hkey
  rw [norm_mul, h2] at hnorm
  have hcomm : M * P = P * M := mul_comm _ _
  rw [hcomm]
  linarith

/-- A uniform bound on the pairing is contradicted by the jump at a single radius: the jump forces
the folded pairing to grow like the mass of the conjugate kernel. -/
theorem jump_estimate_of_pairing_bound {a d B₀ : ℝ} (hd : 0 < d)
    {δ : ℝ} (hδ0 : 0 < δ) (hδH : δ < putnamPeriod d / 2)
    (hδ : ∀ y ∈ Ioc (0 : ℝ) δ,
      ‖(putnamPeriodization a d y - putnamPeriodization a d (putnamPeriod d - y))
        - (putnamPeriodization a d 0 - putnamLeftValue a d)‖
        ≤ ‖putnamPeriodization a d 0 - putnamLeftValue a d‖ / 2)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hB : ‖∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        putnamPeriodization a d y * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ)‖ ≤ B₀) :
    ‖putnamPeriodization a d 0 - putnamLeftValue a d‖ / 2
        * ((Real.log (1 + r) - Real.log (1 - r)) / d)
      ≤ B₀
        + (2 * periodizationBound d
            + ‖putnamPeriodization a d 0 - putnamLeftValue a d‖) * (putnamPeriod d / 2)
          * (1 / (1 - Real.cos (d * δ) ^ 2)) := by
  classical
  set P := putnamPeriod d with hPdef
  set D := putnamPeriodization a d with hDdef
  set M := periodizationBound d with hMdef
  set J : ℂ := D 0 - putnamLeftValue a d with hJdef
  set K : ℝ → ℝ := fun y => ((circleFactor r d y)⁻¹).im with hKdef
  set Λ : ℝ := (Real.log (1 + r) - Real.log (1 - r)) / d with hΛdef
  set Ψ : ℝ → ℂ := fun y => D y - D (P - y) with hΨdef
  set Cδ : ℝ := 1 / (1 - Real.cos (d * δ) ^ 2) with hCδdef
  have hP : 0 < P := putnamPeriod_pos hd
  have hH : 0 < P / 2 := by linarith
  have hMnn : (0 : ℝ) ≤ M := periodizationBound_nonneg d
  have hfinH : (volume (Ioc (0 : ℝ) (P / 2))) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hKnn : ∀ y ∈ Ioc (0 : ℝ) (P / 2), 0 ≤ K y := fun y hy =>
    circleKernelIm_nonneg_of_mem hd hr0 hr1 hy
  have hKbdd : ∀ y : ℝ, ‖((K y : ℝ) : ℂ)‖ ≤ (1 - r)⁻¹ := norm_ofReal_circleKernelIm_le hr0 hr1 d
  have hΛeq : (∫ y in Ioc (0 : ℝ) (P / 2), K y) = Λ := integral_circleKernel_im_half hd hr0 hr1
  have hKintR : IntegrableOn K (Ioc (0 : ℝ) (P / 2)) := by
    refine Integrable.mono' (g := fun _ : ℝ => (1 - r)⁻¹) (integrableOn_const hfinH)
      ((Complex.continuous_im.comp
        (continuous_circleKernel hr0 hr1 d)).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun y => ?_)
    have := hKbdd y
    rwa [Complex.norm_real] at this
  have hΨint : IntegrableOn Ψ (Ioc (0 : ℝ) (P / 2)) := integrableOn_foldBase hd
  have hconstint : IntegrableOn (fun _ : ℝ => J) (Ioc (0 : ℝ) (P / 2)) := integrableOn_const hfinH
  have hJKint : IntegrableOn (fun y => J * ((K y : ℝ) : ℂ)) (Ioc (0 : ℝ) (P / 2)) :=
    integrableOn_mul_bdd hconstint (continuous_circleKernel_im hr0 hr1 d) hKbdd
  have hdiffKint : IntegrableOn (fun y => (Ψ y - J) * ((K y : ℝ) : ℂ)) (Ioc (0 : ℝ) (P / 2)) :=
    integrableOn_mul_bdd (hΨint.sub hconstint) (continuous_circleKernel_im hr0 hr1 d) hKbdd
  have hbound : ‖∫ y in Ioc (0 : ℝ) (P / 2), Ψ y * ((K y : ℝ) : ℂ)‖ ≤ B₀ := by
    rwa [fold_kernelIm_pairing (a := a) hd hr0 hr1] at hB
  have hJval : (∫ y in Ioc (0 : ℝ) (P / 2), J * ((K y : ℝ) : ℂ)) = J * ((Λ : ℝ) : ℂ) := by
    rw [integral_const_mul]
    congr 1
    have hco : (∫ y in Ioc (0 : ℝ) (P / 2), ((K y : ℝ) : ℂ))
        = (((∫ y in Ioc (0 : ℝ) (P / 2), K y) : ℝ) : ℂ) := integral_ofReal
    rw [hco, hΛeq]
  have hsplit : (∫ y in Ioc (0 : ℝ) (P / 2), Ψ y * ((K y : ℝ) : ℂ))
      = J * ((Λ : ℝ) : ℂ) + ∫ y in Ioc (0 : ℝ) (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ) := by
    rw [← hJval, ← integral_add hJKint hdiffKint]
    exact setIntegral_congr_fun measurableSet_Ioc (fun y _ => by ring)
  have hδle : δ ≤ P / 2 := hδH.le
  have hIoc : Ioc (0 : ℝ) δ ∪ Ioc δ (P / 2) = Ioc (0 : ℝ) (P / 2) :=
    Set.Ioc_union_Ioc_eq_Ioc hδ0.le hδle
  have hdisj : Disjoint (Ioc (0 : ℝ) δ) (Ioc δ (P / 2)) :=
    Set.disjoint_left.mpr (fun x hx hx' => absurd hx'.1 (not_lt.mpr hx.2))
  have hsub1 : Ioc (0 : ℝ) δ ⊆ Ioc (0 : ℝ) (P / 2) := Ioc_subset_Ioc_right hδle
  have hsub2 : Ioc δ (P / 2) ⊆ Ioc (0 : ℝ) (P / 2) := Ioc_subset_Ioc_left hδ0.le
  have herr : (∫ y in Ioc (0 : ℝ) (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ))
      = (∫ y in Ioc (0 : ℝ) δ, (Ψ y - J) * ((K y : ℝ) : ℂ))
        + ∫ y in Ioc δ (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ) := by
    rw [← hIoc, setIntegral_union hdisj measurableSet_Ioc
      (hdiffKint.mono_set hsub1) (hdiffKint.mono_set hsub2)]
  have hΛnn : 0 ≤ Λ := by
    rw [← hΛeq]
    exact setIntegral_nonneg measurableSet_Ioc (fun y hy => hKnn y hy)
  have hKmass : (∫ y in Ioc (0 : ℝ) δ, K y) ≤ Λ := by
    have hsplitK : (∫ y in Ioc (0 : ℝ) (P / 2), K y)
        = (∫ y in Ioc (0 : ℝ) δ, K y) + ∫ y in Ioc δ (P / 2), K y := by
      rw [← hIoc, setIntegral_union hdisj measurableSet_Ioc
        (hKintR.mono_set hsub1) (hKintR.mono_set hsub2)]
    have hfarnn : 0 ≤ ∫ y in Ioc δ (P / 2), K y :=
      setIntegral_nonneg measurableSet_Ioc (fun y hy => hKnn y (hsub2 hy))
    rw [hΛeq] at hsplitK
    linarith
  have hnear : ‖∫ y in Ioc (0 : ℝ) δ, (Ψ y - J) * ((K y : ℝ) : ℂ)‖ ≤ ‖J‖ / 2 * Λ := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    have hmono : (∫ y in Ioc (0 : ℝ) δ, ‖(Ψ y - J) * ((K y : ℝ) : ℂ)‖)
        ≤ ∫ y in Ioc (0 : ℝ) δ, ‖J‖ / 2 * K y := by
      refine setIntegral_mono_on ((hdiffKint.mono_set hsub1).norm)
        ((hKintR.mono_set hsub1).const_mul _) measurableSet_Ioc (fun y hy => ?_)
      have hKy : 0 ≤ K y := hKnn y (hsub1 hy)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hKy]
      exact mul_le_mul_of_nonneg_right (hδ y hy) hKy
    have hval : (∫ y in Ioc (0 : ℝ) δ, ‖J‖ / 2 * K y) = ‖J‖ / 2 * ∫ y in Ioc (0 : ℝ) δ, K y :=
      integral_const_mul _ _
    rw [hval] at hmono
    refine le_trans hmono ?_
    exact mul_le_mul_of_nonneg_left hKmass (by positivity)
  have hfar : ‖∫ y in Ioc δ (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ)‖
      ≤ (2 * M + ‖J‖) * (P / 2) * Cδ := by
    have hCδnn : 0 ≤ Cδ := by
      rw [hCδdef]
      have h := abs_circleKernelIm_le_of_far (d := d) (r := r) hd hr0 hr1 hδ0 hδH
        (y := P / 2) ⟨hδH, le_refl _⟩
      exact le_trans (abs_nonneg _) h
    have hCnn : 0 ≤ (2 * M + ‖J‖) * Cδ := by
      have : (0 : ℝ) ≤ 2 * M + ‖J‖ := by positivity
      exact mul_nonneg this hCδnn
    have hptbound : ∀ y ∈ Ioc δ (P / 2), ‖(Ψ y - J) * ((K y : ℝ) : ℂ)‖
        ≤ (2 * M + ‖J‖) * Cδ := by
      intro y hy
      have hyH : y ∈ Ioc (0 : ℝ) (P / 2) := hsub2 hy
      have h1 : ‖Ψ y‖ ≤ 2 * M := by
        refine le_trans (norm_sub_le _ _) ?_
        have hA := norm_putnamPeriodization_le_bound (a := a) hd
          (show y ∈ Ioc (0 : ℝ) P from ⟨hyH.1, by linarith [hyH.2]⟩)
        have hB' := norm_periodization_reflect_le (a := a) hd hyH
        linarith
      have h2 : ‖Ψ y - J‖ ≤ 2 * M + ‖J‖ := le_trans (norm_sub_le _ _) (by linarith)
      have h3 : ‖((K y : ℝ) : ℂ)‖ ≤ Cδ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_circleKernelIm_le_of_far hd hr0 hr1 hδ0 hδH hy
      rw [norm_mul]
      exact mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
    refine le_trans (norm_integral_le_of_norm_le_const (C := (2 * M + ‖J‖) * Cδ) ?_) ?_
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall hptbound)
    · have hmeas : (volume.restrict (Ioc δ (P / 2))).real univ = P / 2 - δ := by
        simp [MeasureTheory.Measure.real, Real.volume_Ioc]
        linarith
      rw [hmeas]
      have : P / 2 - δ ≤ P / 2 := by linarith
      calc (2 * M + ‖J‖) * Cδ * (P / 2 - δ)
          ≤ (2 * M + ‖J‖) * Cδ * (P / 2) := mul_le_mul_of_nonneg_left this hCnn
        _ = (2 * M + ‖J‖) * (P / 2) * Cδ := by ring
  have hJnorm : ‖J * ((Λ : ℝ) : ℂ)‖ = ‖J‖ * Λ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛnn]
  have hfinal : ‖J‖ * Λ
      ≤ ‖∫ y in Ioc (0 : ℝ) (P / 2), Ψ y * ((K y : ℝ) : ℂ)‖
        + ‖∫ y in Ioc (0 : ℝ) (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ)‖ := by
    have heq : J * ((Λ : ℝ) : ℂ)
        = (∫ y in Ioc (0 : ℝ) (P / 2), Ψ y * ((K y : ℝ) : ℂ))
          - ∫ y in Ioc (0 : ℝ) (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ) := by
      rw [hsplit]
      ring
    rw [← hJnorm, heq]
    exact norm_sub_le _ _
  have herrnorm : ‖∫ y in Ioc (0 : ℝ) (P / 2), (Ψ y - J) * ((K y : ℝ) : ℂ)‖
      ≤ ‖J‖ / 2 * Λ + (2 * M + ‖J‖) * (P / 2) * Cδ := by
    rw [herr]
    exact le_trans (norm_add_le _ _) (add_le_add hnear hfar)
  linarith [hfinal, hbound, herrnorm]

/-- **The Fourier coefficients of nonnegative index are not absolutely summable.**  Absolute
summability bounds the conjugate pairing uniformly in the radius, while the jump makes it unbounded. -/
theorem not_summable_norm_putnamFourierCoeff {a d : ℝ} (hd : 0 < d) :
    ¬ Summable fun n : ℕ =>
      ‖∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (n : ℤ) x‖ := by
  intro hsum
  set A : ℝ := ∑' n : ℕ, ‖∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (n : ℤ) x‖
    with hAdef
  have hAnn : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  have hA : ∀ N : ℕ, ∑ m ∈ Finset.range N,
      ‖∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (m : ℤ) x‖ ≤ A := fun N =>
    hsum.sum_le_tsum (Finset.range N) (fun _ _ => norm_nonneg _)
  set P := putnamPeriod d with hPdef
  set D := putnamPeriodization a d with hDdef
  set M := periodizationBound d with hMdef
  set J : ℂ := D 0 - putnamLeftValue a d with hJdef
  have hP : 0 < P := putnamPeriod_pos hd
  have hMnn : (0 : ℝ) ≤ M := periodizationBound_nonneg d
  have hJne : J ≠ 0 := by
    intro h
    refine putnamLeftValue_sub_ne_zero (a := a) hd ?_
    have hneg : putnamLeftValue a d - D 0 = -J := by rw [hJdef]; ring
    rw [hneg, h, neg_zero]
  have hJpos : 0 < ‖J‖ := norm_pos_iff.mpr hJne
  obtain ⟨δ, hδ0, hδH, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < P / 2 ∧
      ∀ y ∈ Ioc (0 : ℝ) δ, ‖(D y - D (P - y)) - J‖ ≤ ‖J‖ / 2 := by
    have hlim := tendsto_foldedDifference (a := a) hd
    rw [Metric.tendsto_nhdsWithin_nhds] at hlim
    obtain ⟨δ₀, hδ₀, hδ₀'⟩ := hlim (‖J‖ / 2) (by positivity)
    refine ⟨min (δ₀ / 2) (P / 4), by positivity, ?_, ?_⟩
    · calc min (δ₀ / 2) (P / 4) ≤ P / 4 := min_le_right _ _
        _ < P / 2 := by linarith
    · intro y hy
      have hy0 : 0 < y := hy.1
      have hylt : y < δ₀ := by
        have h2 := hy.2
        have h1 : min (δ₀ / 2) (P / 4) ≤ δ₀ / 2 := min_le_left _ _
        linarith
      have hres := hδ₀' (mem_Ioi.mpr hy0)
        (by rw [Real.dist_eq, sub_zero, abs_of_pos hy0]; exact hylt)
      rw [dist_eq_norm] at hres
      exact hres.le
  have hdδ0 : 0 < d * δ := by positivity
  have hdδπ : d * δ < Real.pi := by
    rw [← putnamPeriod_half_mul hd]
    exact mul_lt_mul_of_pos_left hδH hd
  have hcos1 : Real.cos (d * δ) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hdδπ.le hdδ0
    simpa using this
  have hcos0 : -1 < Real.cos (d * δ) := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hdδ0.le (le_refl Real.pi) hdδπ
    simpa using this
  have hCpos : 0 < 1 - Real.cos (d * δ) ^ 2 := by nlinarith
  set Cδ : ℝ := 1 / (1 - Real.cos (d * δ) ^ 2) with hCδdef
  have hCδnn : 0 ≤ Cδ := by
    rw [hCδdef]
    positivity
  set B₀ : ℝ := (M * P + 3 * A) / 2 with hB₀def
  set B : ℝ := B₀ + (2 * M + ‖J‖) * (P / 2) * Cδ with hBdef
  have hBnn : 0 ≤ B := by
    have h1 : (0 : ℝ) ≤ B₀ := by positivity
    have h2 : (0 : ℝ) ≤ (2 * M + ‖J‖) * (P / 2) * Cδ := by positivity
    linarith
  set L : ℝ := B / (‖J‖ / 2) + 1 with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    have : (0 : ℝ) ≤ B / (‖J‖ / 2) := by positivity
    linarith
  set r : ℝ := 1 - Real.exp (-(d * L)) with hrdef
  have hexp1 : Real.exp (-(d * L)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 < d * L := by positivity
    linarith
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    linarith
  have hr1 : r < 1 := by
    rw [hrdef]
    have := Real.exp_pos (-(d * L))
    linarith
  have hone_sub : 1 - r = Real.exp (-(d * L)) := by
    rw [hrdef]
    ring
  have hΛge : L ≤ (Real.log (1 + r) - Real.log (1 - r)) / d := by
    rw [hone_sub, Real.log_exp]
    have hlog : 0 ≤ Real.log (1 + r) := Real.log_nonneg (by linarith)
    rw [le_div_iff₀ hd]
    linarith
  have hest := jump_estimate_of_pairing_bound (a := a) hd hδ0 hδH hδ hr0 hr1
    (norm_integral_periodization_kernelIm_le_of_coeff hd hr0 hr1 hA)
  have h1 : ‖J‖ / 2 * L ≤ ‖J‖ / 2 * ((Real.log (1 + r) - Real.log (1 - r)) / d) :=
    mul_le_mul_of_nonneg_left hΛge (by positivity)
  have h2 : ‖J‖ / 2 * L = B + ‖J‖ / 2 := by
    rw [hLdef]
    field_simp
  linarith [hest, h1, h2]

/-- **Divergence along a vertical progression.**  The normalised zeta values on any arithmetic
progression of the critical line are not absolutely summable. -/
theorem not_summable_norm_riemannZeta_div {a d : ℝ} (hd : 0 < d) :
    ¬ Summable fun n : ℕ =>
      ‖riemannZeta (1 / 2 + ((a + d * n : ℝ) : ℂ) * I) / (1 / 2 + ((a + d * n : ℝ) : ℂ) * I)‖ := by
  intro hsum
  refine not_summable_norm_putnamFourierCoeff (a := a) hd (hsum.congr fun n => ?_)
  have h := integral_putnamPeriodization_fourier (a := a) hd (n : ℤ)
  have h2 : (∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d (n : ℤ) x)
      = -riemannZeta (1 / 2 + ((a + d * ((n : ℤ) : ℝ) : ℝ) : ℂ) * I)
          / (1 / 2 + ((a + d * ((n : ℤ) : ℝ) : ℝ) : ℂ) * I) := by
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Ioc (fun x _ => rfl)
  rw [h2, show ((n : ℤ) : ℝ) = (n : ℝ) by push_cast; rfl, neg_div, norm_neg]

/-! ### The Laplace representation on the open strip -/

theorem integrableOn_putnamTwist_mul_cexp_Iio (a ξ : ℝ) {η : ℂ}
    (h1 : (1 / 2 + ((a + ξ : ℝ) : ℂ) * I + η).re < 1) :
    IntegrableOn (fun x : ℝ => putnamTwist a ξ x * Complex.exp (-η * (x : ℂ))) (Iio (0 : ℝ)) := by
  set z : ℂ := 1 / 2 + ((a + ξ : ℝ) : ℂ) * I + η with hz
  have hbase : IntegrableOn (fun x : ℝ => Complex.exp ((1 - z) * (x : ℂ))) (Iic (0 : ℝ)) := by
    refine integrableOn_exp_mul_complex_Iic ?_ 0
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  refine (hbase.mono_set Iio_subset_Iic_self).congr_fun ?_ measurableSet_Iio
  intro x hx
  simp only
  rw [putnamTwist_of_neg hx, ← Complex.exp_add]
  congr 1
  rw [hz]
  ring

theorem integrableOn_putnamTwist_mul_cexp_Ici (a ξ : ℝ) {η : ℂ}
    (h0 : 0 < (1 / 2 + ((a + ξ : ℝ) : ℂ) * I + η).re) :
    IntegrableOn (fun x : ℝ => putnamTwist a ξ x * Complex.exp (-η * (x : ℂ))) (Ici (0 : ℝ)) := by
  set z : ℂ := 1 / 2 + ((a + ξ : ℝ) : ℂ) * I + η with hz
  have hmaj : IntegrableOn (fun x : ℝ => Real.exp (-z.re * x)) (Ici (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi (-1) h0).mono_set
      (fun x hx => by simp only [mem_Ioi]; exact lt_of_lt_of_le (by norm_num) hx)
  refine Integrable.mono' hmaj
    (((measurable_putnamTwist a ξ).mul
      (Complex.measurable_exp.comp (by fun_prop))).aestronglyMeasurable.restrict) ?_
  refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  have hx0 : (0 : ℝ) ≤ x := hx
  rw [putnamTwist_of_nonneg hx0, mul_assoc, ← Complex.exp_add, norm_mul, Complex.norm_exp]
  have hre : (-(1 / 2 + ((a + ξ : ℝ) : ℂ) * I) * (x : ℂ) + -η * (x : ℂ)).re = -z.re * x := by
    have : -(1 / 2 + ((a + ξ : ℝ) : ℂ) * I) * (x : ℂ) + -η * (x : ℂ) = -z * (x : ℂ) := by
      rw [hz]
      ring
    rw [this]
    simp [Complex.mul_re]
  rw [hre]
  have hfract : ‖((Int.fract (Real.exp x) : ℝ) : ℂ)‖ ≤ 1 := norm_fract_le _
  nlinarith [hfract, (Real.exp_pos (-z.re * x)).le,
    norm_nonneg ((Int.fract (Real.exp x) : ℝ) : ℂ)]

theorem integrable_putnamTwist_mul_cexp (a ξ : ℝ) {η : ℂ}
    (h0 : 0 < (1 / 2 + ((a + ξ : ℝ) : ℂ) * I + η).re)
    (h1 : (1 / 2 + ((a + ξ : ℝ) : ℂ) * I + η).re < 1) :
    Integrable (fun x : ℝ => putnamTwist a ξ x * Complex.exp (-η * (x : ℂ))) := by
  have hunion : Iio (0 : ℝ) ∪ Ici (0 : ℝ) = univ := by
    ext x
    simp only [mem_union, mem_Iio, mem_Ici, mem_univ, iff_true]
    exact lt_or_ge x 0
  have := (integrableOn_putnamTwist_mul_cexp_Iio a ξ h1).union
    (integrableOn_putnamTwist_mul_cexp_Ici a ξ h0)
  rw [hunion, integrableOn_univ] at this
  exact this

/-- **The Laplace representation on the open strip.**  Putnam's kernel, twisted by a complex
exponential, integrates to the normalised zeta value at any point of the open critical strip. -/
theorem integral_putnamTwist_mul_cexp (a ξ : ℝ) {η : ℂ}
    (h0 : 0 < (1 / 2 + ((a + ξ : ℝ) : ℂ) * I + η).re)
    (h1 : (1 / 2 + ((a + ξ : ℝ) : ℂ) * I + η).re < 1) :
    (∫ x : ℝ, putnamTwist a ξ x * Complex.exp (-η * (x : ℂ)))
      = -riemannZeta (1 / 2 + ((a + ξ : ℝ) : ℂ) * I + η) / (1 / 2 + ((a + ξ : ℝ) : ℂ) * I + η) := by
  set z : ℂ := 1 / 2 + ((a + ξ : ℝ) : ℂ) * I + η with hz
  have hzne : z ≠ 1 := by
    intro h
    rw [h] at h1
    norm_num at h1
  have hzne0 : z ≠ 0 := by
    intro h
    rw [h] at h0
    norm_num at h0
  have hc1 : (0 : ℝ) < (1 - z).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hsplit := MeasureTheory.integral_add_compl (μ := (volume : Measure ℝ))
    (f := fun x : ℝ => putnamTwist a ξ x * Complex.exp (-η * (x : ℂ))) (s := Iio (0 : ℝ))
    measurableSet_Iio (integrable_putnamTwist_mul_cexp a ξ h0 h1)
  have hcompl : (Iio (0 : ℝ))ᶜ = Ici (0 : ℝ) := by
    ext x
    simp
  rw [hcompl] at hsplit
  have hleft : (∫ x in Iio (0 : ℝ), putnamTwist a ξ x * Complex.exp (-η * (x : ℂ)))
      = 1 / (1 - z) := by
    have hcongr : (∫ x in Iio (0 : ℝ), putnamTwist a ξ x * Complex.exp (-η * (x : ℂ)))
        = ∫ x in Iio (0 : ℝ), Complex.exp ((1 - z) * (x : ℂ)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Iio fun x hx => ?_
      rw [putnamTwist_of_neg hx, ← Complex.exp_add]
      congr 1
      rw [hz]
      ring
    have hIio : (∫ x in Iio (0 : ℝ), Complex.exp ((1 - z) * (x : ℂ)))
        = ∫ x in Iic (0 : ℝ), Complex.exp ((1 - z) * (x : ℂ)) :=
      MeasureTheory.integral_Iic_eq_integral_Iio.symm
    rw [hcongr, hIio, integral_exp_mul_complex_Iic hc1 0]
    simp
  have hright : (∫ x in Ici (0 : ℝ), putnamTwist a ξ x * Complex.exp (-η * (x : ℂ)))
      = 1 / (z - 1) - riemannZeta z / z := by
    have hIci : (∫ x in Ici (0 : ℝ), putnamTwist a ξ x * Complex.exp (-η * (x : ℂ)))
        = ∫ x in Ioi (0 : ℝ), putnamTwist a ξ x * Complex.exp (-η * (x : ℂ)) :=
      MeasureTheory.integral_Ici_eq_integral_Ioi
    rw [hIci]
    have hcongr : (∫ x in Ioi (0 : ℝ), putnamTwist a ξ x * Complex.exp (-η * (x : ℂ)))
        = ∫ x in Ioi (0 : ℝ), ((Int.fract (Real.exp x) : ℝ) : ℂ) * Complex.exp (-z * (x : ℂ)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      rw [putnamTwist_of_nonneg (le_of_lt hx), mul_assoc, ← Complex.exp_add]
      congr 2
      rw [hz]
      ring
    rw [hcongr]
    exact integral_Ioi_zero_fract_exp h0 hzne
  rw [← hsplit, hleft, hright]
  have hne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzne)
  have hne' : z - 1 ≠ 0 := sub_ne_zero.mpr hzne
  field_simp
  ring

/-! ### The first moment and the Taylor remainder -/

theorem norm_putnamTwist_le (a ξ x : ℝ) : ‖putnamTwist a ξ x‖ ≤ Real.exp (-(|x| / 2)) := by
  rw [norm_putnamTwist]
  exact norm_putnamKernel_le a x

/-- `|x| e^{-|x|/2} ≤ 4 e^{-|x|/4}`. -/
theorem abs_mul_exp_neg_half_le (x : ℝ) :
    |x| * Real.exp (-(|x| / 2)) ≤ 4 * Real.exp (-(1 / 4 * |x|)) := by
  have h : |x| / 4 ≤ Real.exp (|x| / 4) := by
    linarith [Real.add_one_le_exp (|x| / 4)]
  have hsplit : Real.exp (-(|x| / 2)) = Real.exp (-(|x| / 4)) * Real.exp (-(1 / 4 * |x|)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hone : Real.exp (|x| / 4) * Real.exp (-(|x| / 4)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hpos := Real.exp_pos (-(1 / 4 * |x|))
  have hpos2 := Real.exp_pos (-(|x| / 4))
  rw [hsplit]
  have hmain : |x| * Real.exp (-(|x| / 4)) ≤ 4 := by
    have := mul_le_mul_of_nonneg_right h hpos2.le
    rw [hone] at this
    linarith
  calc |x| * (Real.exp (-(|x| / 4)) * Real.exp (-(1 / 4 * |x|)))
      = (|x| * Real.exp (-(|x| / 4))) * Real.exp (-(1 / 4 * |x|)) := by ring
    _ ≤ 4 * Real.exp (-(1 / 4 * |x|)) := mul_le_mul_of_nonneg_right hmain hpos.le

/-- `x² ≤ 128 e^{|x|/8}`. -/
theorem sq_le_mul_exp (x : ℝ) : x ^ 2 ≤ 128 * Real.exp (|x| / 8) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := |x| / 8) (by positivity)
  have hsq : (|x| / 8) ^ 2 = x ^ 2 / 64 := by
    rw [div_pow, sq_abs]
    norm_num
  rw [hsq] at h
  have : 0 ≤ |x| / 8 := by positivity
  linarith

theorem integrable_moment_putnamTwist (a ξ : ℝ) :
    Integrable (fun x : ℝ => (x : ℂ) * putnamTwist a ξ x) := by
  refine Integrable.mono' (g := fun x : ℝ => 4 * Real.exp (-(1 / 4 * |x|)))
    ((integrable_exp_neg_mul_abs' (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 4)
    ((Complex.measurable_ofReal.mul (measurable_putnamTwist a ξ)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact le_trans (mul_le_mul_of_nonneg_left (norm_putnamTwist_le a ξ x) (abs_nonneg x))
    (abs_mul_exp_neg_half_le x)

/-- Samples of the Fourier transform of `x C_a(x)`. -/
def putnamMoment (a ξ : ℝ) : ℂ := ∫ x : ℝ, (x : ℂ) * putnamTwist a ξ x

/-- The universal constant of the second-order Taylor remainder. -/
def putnamTaylorConstant : ℝ := ∫ x : ℝ, 128 * Real.exp (-(1 / 8 * |x|))

/-- **Second-order Taylor bound.**  Within distance `1/4` the Laplace representation is its first
order expansion up to `K |η|²`, uniformly in the base point. -/
theorem norm_integral_putnamTwist_taylor_le (a ξ : ℝ) {η : ℂ} (hη : ‖η‖ ≤ 1 / 4)
    (h0 : 0 < (1 / 2 + ((a + ξ : ℝ) : ℂ) * I + η).re)
    (h1 : (1 / 2 + ((a + ξ : ℝ) : ℂ) * I + η).re < 1) :
    ‖(∫ x : ℝ, putnamTwist a ξ x * Complex.exp (-η * (x : ℂ)))
        - (∫ x : ℝ, putnamTwist a ξ x) + η * putnamMoment a ξ‖
      ≤ putnamTaylorConstant * ‖η‖ ^ 2 := by
  have hI1 := integrable_putnamTwist_mul_cexp a ξ h0 h1
  have hI2 := integrable_putnamTwist a ξ
  have hI3 := integrable_moment_putnamTwist a ξ
  have hmaj : Integrable (fun x : ℝ => 128 * Real.exp (-(1 / 8 * |x|))) :=
    (integrable_exp_neg_mul_abs' (by norm_num : (0 : ℝ) < 1 / 8)).const_mul 128
  have hsum : (∫ x : ℝ, putnamTwist a ξ x * Complex.exp (-η * (x : ℂ)))
        - (∫ x : ℝ, putnamTwist a ξ x) + η * putnamMoment a ξ
      = ∫ x : ℝ, putnamTwist a ξ x *
          (Complex.exp (-η * (x : ℂ)) - 1 - (-η * (x : ℂ))) := by
    have e1 : (∫ x : ℝ, putnamTwist a ξ x * Complex.exp (-η * (x : ℂ)))
          - (∫ x : ℝ, putnamTwist a ξ x)
        = ∫ x : ℝ, (putnamTwist a ξ x * Complex.exp (-η * (x : ℂ)) - putnamTwist a ξ x) :=
      (integral_sub hI1 hI2).symm
    have e2 : η * putnamMoment a ξ = ∫ x : ℝ, η * ((x : ℂ) * putnamTwist a ξ x) := by
      rw [putnamMoment, integral_const_mul]
    have e3 : (∫ x : ℝ, (putnamTwist a ξ x * Complex.exp (-η * (x : ℂ)) - putnamTwist a ξ x))
          + (∫ x : ℝ, η * ((x : ℂ) * putnamTwist a ξ x))
        = ∫ x : ℝ, ((putnamTwist a ξ x * Complex.exp (-η * (x : ℂ)) - putnamTwist a ξ x)
            + η * ((x : ℂ) * putnamTwist a ξ x)) :=
      (integral_add (hI1.sub hI2) (hI3.const_mul η)).symm
    rw [e1, e2, e3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hbound : ∀ x : ℝ, ‖putnamTwist a ξ x * (Complex.exp (-η * (x : ℂ)) - 1 - (-η * (x : ℂ)))‖
      ≤ ‖η‖ ^ 2 * (128 * Real.exp (-(1 / 8 * |x|))) := by
    intro x
    have hw : ‖(-η * (x : ℂ))‖ = ‖η‖ * |x| := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have hT := Complex.norm_exp_sub_sum_le_norm_mul_exp (-η * (x : ℂ)) 2
    have hsumT : ∑ m ∈ Finset.range 2, (-η * (x : ℂ)) ^ m / (m.factorial : ℂ)
        = 1 + (-η * (x : ℂ)) := by
      simp [Finset.sum_range_succ]
    rw [hsumT, ← sub_sub, hw] at hT
    have hsmall : ‖η‖ * |x| ≤ |x| / 4 := by nlinarith [abs_nonneg x]
    have hexp : Real.exp (‖η‖ * |x|) ≤ Real.exp (|x| / 4) := Real.exp_le_exp.mpr hsmall
    have hT' : ‖Complex.exp (-η * (x : ℂ)) - 1 - (-η * (x : ℂ))‖
        ≤ ‖η‖ ^ 2 * x ^ 2 * Real.exp (|x| / 4) := by
      refine le_trans hT ?_
      have hpow : (‖η‖ * |x|) ^ 2 = ‖η‖ ^ 2 * x ^ 2 := by
        rw [mul_pow, sq_abs]
      rw [hpow]
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    rw [norm_mul]
    have hk := norm_putnamTwist_le a ξ x
    have hx2 := sq_le_mul_exp x
    have hηnn : 0 ≤ ‖η‖ ^ 2 := by positivity
    calc ‖putnamTwist a ξ x‖ * ‖Complex.exp (-η * (x : ℂ)) - 1 - (-η * (x : ℂ))‖
        ≤ Real.exp (-(|x| / 2)) * (‖η‖ ^ 2 * x ^ 2 * Real.exp (|x| / 4)) :=
          mul_le_mul hk hT' (norm_nonneg _) (Real.exp_pos _).le
      _ = ‖η‖ ^ 2 * (x ^ 2 * Real.exp (-(|x| / 4))) := by
          have : Real.exp (-(|x| / 2)) * Real.exp (|x| / 4) = Real.exp (-(|x| / 4)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc Real.exp (-(|x| / 2)) * (‖η‖ ^ 2 * x ^ 2 * Real.exp (|x| / 4))
              = ‖η‖ ^ 2 * x ^ 2 * (Real.exp (-(|x| / 2)) * Real.exp (|x| / 4)) := by ring
            _ = ‖η‖ ^ 2 * (x ^ 2 * Real.exp (-(|x| / 4))) := by rw [this]; ring
      _ ≤ ‖η‖ ^ 2 * (128 * Real.exp (-(1 / 8 * |x|))) := by
          refine mul_le_mul_of_nonneg_left ?_ hηnn
          have hprod : Real.exp (|x| / 8) * Real.exp (-(|x| / 4)) = Real.exp (-(1 / 8 * |x|)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc x ^ 2 * Real.exp (-(|x| / 4))
              ≤ (128 * Real.exp (|x| / 8)) * Real.exp (-(|x| / 4)) :=
                mul_le_mul_of_nonneg_right hx2 (Real.exp_pos _).le
            _ = 128 * Real.exp (-(1 / 8 * |x|)) := by rw [mul_assoc, hprod]
  rw [hsum]
  refine le_trans (norm_integral_le_of_norm_le (hmaj.const_mul (‖η‖ ^ 2))
    (Filter.Eventually.of_forall hbound)) ?_
  rw [integral_const_mul, putnamTaylorConstant]
  exact le_of_eq (mul_comm _ _)

/-! ### Bessel on the dual lattice -/

/-- The lattice character of frequency `d n`. -/
def latticeCharacter (d : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (-(((d * n : ℝ) : ℂ) * I) * (x : ℂ))

theorem continuous_latticeCharacter (d : ℝ) (n : ℕ) : Continuous (latticeCharacter d n) := by
  unfold latticeCharacter
  fun_prop

theorem norm_latticeCharacter (d : ℝ) (n : ℕ) (x : ℝ) : ‖latticeCharacter d n x‖ = 1 := by
  rw [latticeCharacter, Complex.norm_exp]
  have hre : (-(((d * n : ℝ) : ℂ) * I) * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

/-- Orthogonality of the lattice characters on any window of one period. -/
theorem integral_latticeCharacter_mul_conj {d : ℝ} (hd : 0 < d) (n m : ℕ) (u : ℝ) :
    (∫ x in u..(u + putnamPeriod d), latticeCharacter d n x * (starRingEnd ℂ) (latticeCharacter d m x))
      = if n = m then ((putnamPeriod d : ℝ) : ℂ) else 0 := by
  have hconj : ∀ x : ℝ, latticeCharacter d n x * (starRingEnd ℂ) (latticeCharacter d m x)
      = Complex.exp ((-((d : ℂ) * ((n : ℂ) - (m : ℂ)) * I)) * (x : ℂ)) := by
    intro x
    rw [latticeCharacter, latticeCharacter, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [hconj]
  by_cases h : n = m
  · subst h
    simp only [sub_self, mul_zero, zero_mul, neg_zero, Complex.exp_zero, if_true,
      intervalIntegral.integral_const]
    simp
  · rw [if_neg h]
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hnm : (n : ℂ) - (m : ℂ) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast h
    have hc : -((d : ℂ) * ((n : ℂ) - (m : ℂ)) * I) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hdC hnm) Complex.I_ne_zero)
    rw [integral_exp_mul_complex hc]
    have hper : Complex.exp ((-((d : ℂ) * ((n : ℂ) - (m : ℂ)) * I)) * ((u + putnamPeriod d : ℝ) : ℂ))
        = Complex.exp ((-((d : ℂ) * ((n : ℂ) - (m : ℂ)) * I)) * (u : ℂ)) := by
      have hP : (d : ℂ) * ((putnamPeriod d : ℝ) : ℂ) = 2 * Real.pi := by
        rw [putnamPeriod]
        push_cast
        field_simp
      have hsplit : (-((d : ℂ) * ((n : ℂ) - (m : ℂ)) * I)) * ((u + putnamPeriod d : ℝ) : ℂ)
          = (-((d : ℂ) * ((n : ℂ) - (m : ℂ)) * I)) * (u : ℂ)
            + ((-((n : ℤ) - (m : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * I) := by
        push_cast
        rw [← hP]
        ring
      rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hper, sub_self, zero_div]

/-- **Parseval on one period.** -/
theorem integral_norm_sq_latticeSum {d : ℝ} (hd : 0 < d) (N : ℕ) (t : ℕ → ℂ) (u : ℝ) :
    (∫ x in u..(u + putnamPeriod d),
        ‖∑ n ∈ Finset.range N, t n * latticeCharacter d n x‖ ^ 2)
      = putnamPeriod d * ∑ n ∈ Finset.range N, ‖t n‖ ^ 2 := by
  have hcast : (((∫ x in u..(u + putnamPeriod d),
        ‖∑ n ∈ Finset.range N, t n * latticeCharacter d n x‖ ^ 2) : ℝ) : ℂ)
      = ((putnamPeriod d * ∑ n ∈ Finset.range N, ‖t n‖ ^ 2 : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_ofReal.symm]
    have hpt : ∀ x : ℝ, ((‖∑ n ∈ Finset.range N, t n * latticeCharacter d n x‖ ^ 2 : ℝ) : ℂ)
        = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
            (t n * (starRingEnd ℂ) (t m)) *
              (latticeCharacter d n x * (starRingEnd ℂ) (latticeCharacter d m x)) := by
      intro x
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul]
      ring
    simp_rw [hpt]
    have hcont : ∀ n m : ℕ, Continuous (fun x : ℝ =>
        (t n * (starRingEnd ℂ) (t m)) *
          (latticeCharacter d n x * (starRingEnd ℂ) (latticeCharacter d m x))) := fun n m =>
      continuous_const.mul ((continuous_latticeCharacter d n).mul
        (Complex.continuous_conj.comp (continuous_latticeCharacter d m)))
    rw [intervalIntegral.integral_finsetSum (fun n _ =>
      (continuous_finsetSum _ fun m _ => hcont n m).intervalIntegrable _ _)]
    have hinner : ∀ n ∈ Finset.range N,
        (∫ x in u..(u + putnamPeriod d), ∑ m ∈ Finset.range N,
            (t n * (starRingEnd ℂ) (t m)) *
              (latticeCharacter d n x * (starRingEnd ℂ) (latticeCharacter d m x)))
          = ((putnamPeriod d : ℝ) : ℂ) * ((‖t n‖ ^ 2 : ℝ) : ℂ) := by
      intro n hn
      rw [intervalIntegral.integral_finsetSum (fun m _ => (hcont n m).intervalIntegrable _ _)]
      simp_rw [intervalIntegral.integral_const_mul, integral_latticeCharacter_mul_conj hd]
      rw [Finset.sum_eq_single n]
      · rw [if_pos rfl, Complex.ofReal_pow, ← Complex.mul_conj']
        ring
      · intro m _ hmn
        rw [if_neg (Ne.symm hmn), mul_zero]
      · intro hn'
        exact absurd hn hn'
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
    push_cast
    rfl
  exact_mod_cast hcast

/-- The lattice envelope of the majorant `4 e^{-|x|/4}`. -/
def latticeEnvelope (P : ℝ) (k : ℤ) : ℝ :=
  4 * Real.exp (P / 4) * Real.exp (-(P / 4 * |(k : ℝ)|))

theorem summable_latticeEnvelope {P : ℝ} (hP : 0 < P) : Summable (latticeEnvelope P) := by
  unfold latticeEnvelope
  exact (summable_exp_neg_abs_int (r := P / 4) (by positivity)).mul_left _

theorem majorant_le_latticeEnvelope {P : ℝ} (hP : 0 < P) (k : ℤ) {x : ℝ}
    (hx : x ∈ Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P)) :
    4 * Real.exp (-(1 / 4 * |x|)) ≤ latticeEnvelope P k := by
  have habs : (|(k : ℝ)| - 1) * P ≤ |x| := by
    rcases le_or_gt 0 k with hk | hk
    · have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      rw [abs_of_nonneg hk0]
      have h1 : (k : ℝ) * P < x := hx.1
      have h2 := le_abs_self x
      nlinarith
    · have hk1 : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast Int.add_one_le_of_lt hk
      have hk0 : (k : ℝ) < 0 := by linarith
      rw [abs_of_neg hk0]
      have h1 : x ≤ ((k : ℝ) + 1) * P := hx.2
      have h2 := neg_le_abs x
      nlinarith
  rw [latticeEnvelope, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  nlinarith

/-- **Bessel for the first moments.**  The samples of the Fourier transform of `x C_a(x)` on the
lattice `dℕ` have square sums bounded independently of the number of terms. -/
theorem sum_norm_sq_putnamMoment_le {a d : ℝ} (hd : 0 < d) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖putnamMoment a (d * n)‖ ^ 2
      ≤ (∑' k : ℤ, latticeEnvelope (putnamPeriod d) k) * putnamPeriod d *
        ∫ x : ℝ, 4 * Real.exp (-(1 / 4 * |x|)) := by
  classical
  set P := putnamPeriod d with hPdef
  have hP : 0 < P := putnamPeriod_pos hd
  set W : ℝ := ∑' k : ℤ, latticeEnvelope P k with hWdef
  have hWsum := summable_latticeEnvelope hP
  have hW : 0 < W := by
    refine hWsum.tsum_pos (fun k => ?_) 0 ?_
    · unfold latticeEnvelope
      positivity
    · unfold latticeEnvelope
      positivity
  set β : ℝ → ℝ := fun x => 4 * Real.exp (-(1 / 4 * |x|)) with hβdef
  have hβint : Integrable β :=
    (integrable_exp_neg_mul_abs' (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 4
  have hβnn : ∀ x, 0 ≤ β x := fun x => by
    rw [hβdef]
    positivity
  set b : ℕ → ℂ := fun n => putnamMoment a (d * n) with hbdef
  set t : ℕ → ℂ := fun n => (starRingEnd ℂ) (b n) with htdef
  set T : ℝ → ℂ := fun x => ∑ n ∈ Finset.range N, t n * latticeCharacter d n x with hTdef
  set X : ℝ := ∑ n ∈ Finset.range N, ‖b n‖ ^ 2 with hXdef
  have hXnn : 0 ≤ X := Finset.sum_nonneg fun _ _ => by positivity
  have htnorm : ∀ n, ‖t n‖ = ‖b n‖ := fun n => RCLike.norm_conj _
  have hTcont : Continuous T :=
    continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_latticeCharacter d n)
  set S : ℝ := ∑ n ∈ Finset.range N, ‖t n‖ with hSdef
  have hTbound : ∀ x, ‖T x‖ ≤ S := fun x => by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, norm_latticeCharacter, mul_one]
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- the pairing equals `X`
  have hpair : (∫ x : ℝ, (x : ℂ) * putnamKernel a x * T x) = (X : ℂ) := by
    have hpt : ∀ x : ℝ, (x : ℂ) * putnamKernel a x * T x
        = ∑ n ∈ Finset.range N, t n * ((x : ℂ) * putnamTwist a (d * n) x) := by
      intro x
      rw [hTdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [putnamTwist, latticeCharacter]
      ring
    simp_rw [hpt]
    rw [MeasureTheory.integral_finsetSum (s := Finset.range N)
      (f := fun (n : ℕ) (x : ℝ) => t n * ((x : ℂ) * putnamTwist a (d * n) x))
      (fun n _ => (integrable_moment_putnamTwist a (d * n)).const_mul (t n))]
    simp_rw [integral_const_mul]
    rw [hXdef]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    have : (∫ x : ℝ, (x : ℂ) * putnamTwist a (d * n) x) = b n := rfl
    rw [this, htdef]
    simp only
    rw [mul_comm, Complex.mul_conj']
  -- the weighted Parseval bound
  set f : ℝ → ℝ := fun x => β x * ‖T x‖ ^ 2 with hfdef
  have hfint : Integrable f := by
    refine Integrable.mono' (hβint.mul_const (S ^ 2))
      ((hβint.aestronglyMeasurable).mul
        ((hTcont.norm.pow 2).aestronglyMeasurable)) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hβnn x) (by positivity))]
    refine mul_le_mul_of_nonneg_left ?_ (hβnn x)
    exact pow_le_pow_left₀ (norm_nonneg _) (hTbound x) 2
  have hweighted : (∫ x : ℝ, f x) ≤ W * (P * X) := by
    have hunion := iUnion_Ioc_period (P := P) hP
    have hdisj := pairwise_disjoint_Ioc_period (P := P) hP
    have hHS := hasSum_integral_iUnion (μ := (volume : Measure ℝ)) (f := f)
      (s := fun k : ℤ => Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P))
      (fun k => measurableSet_Ioc) hdisj
      (by rw [hunion, integrableOn_univ]; exact hfint)
    rw [hunion, MeasureTheory.setIntegral_univ] at hHS
    have hbd : ∀ k : ℤ, (∫ x in Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P), f x)
        ≤ latticeEnvelope P k * (P * X) := by
      intro k
      have hle : (k : ℝ) * P ≤ ((k : ℝ) + 1) * P := by nlinarith
      have hNormInt : IntegrableOn (fun x : ℝ => ‖T x‖ ^ 2)
          (Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P)) := by
        have hc : Continuous (fun x : ℝ => ‖T x‖ ^ 2) := hTcont.norm.pow 2
        exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      have hmono : (∫ x in Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P), f x)
          ≤ ∫ x in Ioc ((k : ℝ) * P) (((k : ℝ) + 1) * P), latticeEnvelope P k * ‖T x‖ ^ 2 := by
        refine setIntegral_mono_on hfint.integrableOn (hNormInt.const_mul _) measurableSet_Ioc
          (fun x hx => ?_)
        exact mul_le_mul_of_nonneg_right (majorant_le_latticeEnvelope hP k hx) (by positivity)
      refine le_trans hmono ?_
      rw [integral_const_mul, ← intervalIntegral.integral_of_le hle]
      have hpar := integral_norm_sq_latticeSum (d := d) hd N t ((k : ℝ) * P)
      rw [← hPdef, show (k : ℝ) * P + P = ((k : ℝ) + 1) * P by ring] at hpar
      have hsame : (∑ n ∈ Finset.range N, ‖t n‖ ^ 2) = X := by
        rw [hXdef]
        exact Finset.sum_congr rfl fun n _ => by rw [htnorm]
      rw [hsame] at hpar
      exact le_of_eq (by rw [hpar])
    have hHS2 : HasSum (fun k : ℤ => latticeEnvelope P k * (P * X)) (W * (P * X)) :=
      hWsum.hasSum.mul_right _
    exact hasSum_le hbd hHS hHS2
  -- absorb with `λ = W P`
  set lam : ℝ := W * P with hlamdef
  have hlam : 0 < lam := mul_pos hW hP
  have hpoint : ∀ x : ℝ, ‖(x : ℂ) * putnamKernel a x * T x‖
      ≤ lam / 2 * β x + 1 / (2 * lam) * f x := by
    intro x
    have hk : ‖(x : ℂ) * putnamKernel a x‖ ≤ β x := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact le_trans (mul_le_mul_of_nonneg_left (norm_putnamKernel_le a x) (abs_nonneg x))
        (abs_mul_exp_neg_half_le x)
    rw [norm_mul]
    have hAM : ‖T x‖ ≤ lam / 2 + 1 / (2 * lam) * ‖T x‖ ^ 2 := by
      have hsq : 0 ≤ (lam - ‖T x‖) ^ 2 := sq_nonneg _
      have hrw : lam / 2 + 1 / (2 * lam) * ‖T x‖ ^ 2 - ‖T x‖ = (lam - ‖T x‖) ^ 2 / (2 * lam) := by
        field_simp
        ring
      have : 0 ≤ (lam - ‖T x‖) ^ 2 / (2 * lam) := by positivity
      linarith
    calc ‖(x : ℂ) * putnamKernel a x‖ * ‖T x‖
        ≤ β x * ‖T x‖ := mul_le_mul_of_nonneg_right hk (norm_nonneg _)
      _ ≤ β x * (lam / 2 + 1 / (2 * lam) * ‖T x‖ ^ 2) := mul_le_mul_of_nonneg_left hAM (hβnn x)
      _ = lam / 2 * β x + 1 / (2 * lam) * f x := by
          rw [hfdef]
          ring
  have hgint : Integrable (fun x : ℝ => lam / 2 * β x + 1 / (2 * lam) * f x) :=
    (hβint.const_mul _).add (hfint.const_mul _)
  have hmain : X ≤ lam / 2 * (∫ x, β x) + 1 / (2 * lam) * ∫ x, f x := by
    have hnorm : ‖(∫ x : ℝ, (x : ℂ) * putnamKernel a x * T x)‖ = X := by
      rw [hpair, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hXnn]
    rw [← hnorm]
    refine le_trans (norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpoint)) ?_
    have h1 : (∫ x, lam / 2 * β x) = lam / 2 * ∫ x, β x := integral_const_mul _ _
    have h2 : (∫ x, 1 / (2 * lam) * f x) = 1 / (2 * lam) * ∫ x, f x := integral_const_mul _ _
    refine le_of_eq ?_
    rw [integral_add (hβint.const_mul _) (hfint.const_mul _), h1, h2]
  have hhalf : 1 / (2 * lam) * ∫ x, f x ≤ X / 2 := by
    have h1 : 1 / (2 * lam) * ∫ x, f x ≤ 1 / (2 * lam) * (W * (P * X)) :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    have h2 : 1 / (2 * lam) * (W * (P * X)) = X / 2 := by
      rw [hlamdef]
      field_simp
    linarith
  have hfinal : X ≤ lam * ∫ x, β x := by
    nlinarith
  exact hfinal

/-- The first moments on the lattice are square summable. -/
theorem summable_norm_sq_putnamMoment {a d : ℝ} (hd : 0 < d) :
    Summable fun n : ℕ => ‖putnamMoment a (d * n)‖ ^ 2 :=
  summable_of_sum_range_le (fun _ => by positivity) (sum_norm_sq_putnamMoment_le (a := a) hd)

/-! ### The ladder theorem -/

/-- **No near-arithmetic ladder of zeros.**  Along any arithmetic progression of the critical line and
any square-summable complex perturbation, the perturbed points miss the zeros infinitely often. -/
theorem not_eventually_riemannZeta_eq_zero_of_sq_summable {a d : ℝ} (hd : 0 < d) {η : ℕ → ℂ}
    (hη : Summable fun n => ‖η n‖ ^ 2) :
    ¬ ∀ᶠ n : ℕ in atTop, riemannZeta (1 / 2 + ((a + d * n : ℝ) : ℂ) * I + η n) = 0 := by
  intro hzero
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖η n‖ ≤ 1 / 4 := by
    have hlim := hη.tendsto_atTop_zero
    have hev : ∀ᶠ n : ℕ in atTop, ‖η n‖ ^ 2 < (1 / 4 : ℝ) ^ 2 :=
      hlim.eventually (gt_mem_nhds (by norm_num))
    filter_upwards [hev] with n hn
    exact (abs_le_of_sq_le_sq' hn.le (by norm_num)).2
  have hmom := summable_norm_sq_putnamMoment (a := a) hd
  have hmaj : Summable fun n : ℕ =>
      (‖η n‖ ^ 2 + ‖putnamMoment a (d * n)‖ ^ 2) / 2 + putnamTaylorConstant * ‖η n‖ ^ 2 :=
    ((hη.add hmom).div_const 2).add (hη.mul_left _)
  refine not_summable_norm_riemannZeta_div (a := a) hd ?_
  refine Summable.of_norm_bounded_eventually_nat hmaj ?_
  filter_upwards [hzero, hsmall] with n hz hs
  rw [norm_norm]
  set z : ℂ := 1 / 2 + ((a + d * n : ℝ) : ℂ) * I with hzdef
  have hre : (1 / 2 + ((a + d * n : ℝ) : ℂ) * I + η n).re = 1 / 2 + (η n).re := by
    simp [Complex.add_re, Complex.mul_re]
  have hηre : |(η n).re| ≤ 1 / 4 := le_trans (Complex.abs_re_le_norm _) hs
  have h0 : 0 < (1 / 2 + ((a + d * n : ℝ) : ℂ) * I + η n).re := by
    rw [hre]
    linarith [(abs_le.mp hηre).1]
  have h1 : (1 / 2 + ((a + d * n : ℝ) : ℂ) * I + η n).re < 1 := by
    rw [hre]
    linarith [(abs_le.mp hηre).2]
  have hlap := integral_putnamTwist_mul_cexp a (d * n) h0 h1
  have hbase := integral_putnamTwist a (d * n)
  have htay := norm_integral_putnamTwist_taylor_le a (d * n) hs h0 h1
  rw [hlap, hz, neg_zero, zero_div, hbase, zero_sub] at htay
  have hmono : ‖riemannZeta z / z‖
      ≤ ‖η n‖ * ‖putnamMoment a (d * n)‖ + putnamTaylorConstant * ‖η n‖ ^ 2 := by
    have hrw : riemannZeta z / z
        = (-(-riemannZeta z / z) + η n * putnamMoment a (d * n))
          - η n * putnamMoment a (d * n) := by
      ring
    rw [← hzdef] at htay
    rw [hrw]
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul (η n)]
    linarith [htay]
  have hAM : ‖η n‖ * ‖putnamMoment a (d * n)‖
      ≤ (‖η n‖ ^ 2 + ‖putnamMoment a (d * n)‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖η n‖ - ‖putnamMoment a (d * n)‖)]
  linarith

/-- **Real form.**  No sequence of critical zero ordinates lies within an `ℓ²` perturbation of an
arithmetic progression. -/
theorem not_eventually_riemannZeta_critical_eq_zero_of_sq_summable {a d : ℝ} (hd : 0 < d)
    {ε : ℕ → ℝ} (hε : Summable fun n => ε n ^ 2) :
    ¬ ∀ᶠ n : ℕ in atTop, riemannZeta (1 / 2 + ((a + d * n + ε n : ℝ) : ℂ) * I) = 0 := by
  have hη : Summable fun n => ‖((ε n : ℂ) * I)‖ ^ 2 := by
    refine hε.congr fun n => ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  intro h
  refine not_eventually_riemannZeta_eq_zero_of_sq_summable (a := a) hd hη ?_
  filter_upwards [h] with n hn
  rw [← hn]
  congr 1
  push_cast
  ring

/-- **Eikonal form.**  A real sequence `ω_l = Ω l + b + O(1/l)` is not eventually a sequence of
critical zero ordinates. -/
theorem not_eventually_riemannZeta_critical_eq_zero_of_eikonal {ω : ℕ → ℝ} {Ω b C : ℝ} (hΩ : 0 < Ω)
    (hω : ∀ᶠ l : ℕ in atTop, |ω l - (b + Ω * l)| ≤ C / (l + 1)) :
    ¬ ∀ᶠ l : ℕ in atTop, riemannZeta (1 / 2 + ((ω l : ℝ) : ℂ) * I) = 0 := by
  set ε : ℕ → ℝ := fun l => ω l - (b + Ω * l) with hεdef
  have hbase : Summable fun l : ℕ => C ^ 2 * (1 / ((l : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (one_lt_two))
    refine (h.mul_left (C ^ 2)).congr fun l => ?_
    push_cast
    rfl
  have hε : Summable fun l => ε l ^ 2 := by
    refine Summable.of_norm_bounded_eventually_nat hbase ?_
    filter_upwards [hω] with l hl
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have hl1 : (0 : ℝ) < (l : ℝ) + 1 := by positivity
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hl 2
    refine le_trans hsq (le_of_eq ?_)
    field_simp
  intro h
  refine not_eventually_riemannZeta_critical_eq_zero_of_sq_summable (a := b) hΩ hε ?_
  filter_upwards [h] with l hl
  rw [← hl]
  congr 3
  rw [hεdef]
  ring

end RHTower

end
