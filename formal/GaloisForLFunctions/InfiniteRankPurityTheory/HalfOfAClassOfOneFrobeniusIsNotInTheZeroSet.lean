import GaloisForLFunctions.InfiniteRankPurityTheory.NoSequenceOfZerosApproachesAClassOfOneFrobenius
import GaloisForLFunctions.RHTower.PutnamJumpBlowUp
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Half of a class of one Frobenius is not in the zero set

A class of one Frobenius is a two-sided vertical progression. This module treats each half
separately: along `ρ + inT`, `n ≥ 0`, in the open strip, at any real part, the zeta values are not
summable against `1/n`, and no sequence of zeros approaches the half progression in `ℓ²`.

* `endpoint_limits_eq_of_summable_halfCoeff`: a bounded measurable function on a period whose
  Fourier coefficients of non-negative index are absolutely summable has equal one-sided limits at
  the two ends of the period. The conjugate Cauchy kernel `(1 - r e^{-idy})^{-1}` pairs with these
  coefficients only, so its pairing is bounded uniformly in `r`; its real part is a Poisson kernel
  and its imaginary part has mass `d^{-1} log((1+r)/(1-r))` on a half period, which a jump would
  detect.
* `not_summable_nat_norm_riemannZeta_div`: `Σ_{n ≥ 0} |ζ(ρ + inT)|/|ρ + inT| = ∞`.
* `exists_nat_riemannZeta_ne_zero_progression`, `exists_nat_riemannZeta_ne_zero_progression_down`:
  both halves of every vertical progression in the strip contain infinitely many non-zeros.
* `not_eventually_riemannZeta_eq_zero_near_halfClass`: no sequence of zeros lies within a square
  summable distance of a half progression.
* `exists_nat_conjugate_not_zero`: for a Frobenius `q > 1`, infinitely many of the conjugates
  `ρ + 2πin/log q`, `n ≥ 0`, of any `ρ` are not zeros of `ξ`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower _root_.HTGeometry GaloisForLFunctions.BlackHoleRingdown

/-! ### Summable coefficients of non-negative index leave no jump -/

/-- The Fourier coefficient of index `m ≥ 0` of `D` on the period `2π/d`. -/
def halfCoeff (d : ℝ) (D : ℝ → ℂ) (m : ℕ) : ℂ :=
  ∫ y in Ioc (0 : ℝ) (putnamPeriod d), D y * Complex.exp (-(d : ℂ) * (y : ℂ) * I) ^ m

theorem integrableOn_of_measurable_of_bound {D : ℝ → ℂ} (hDm : Measurable D) {a b M : ℝ}
    (hDb : ∀ y ∈ Ioc a b, ‖D y‖ ≤ M) : IntegrableOn D (Ioc a b) :=
  Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hDm.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hDb))

/-- The pairing with the conjugate Cauchy kernel is the Abel sum of the coefficients of
non-negative index. -/
theorem norm_integral_mul_conjCauchy_le {d : ℝ} (hd : 0 < d) {D : ℝ → ℂ} (hDm : Measurable D)
    {M : ℝ} (hDb : ∀ y ∈ Ioc (0 : ℝ) (putnamPeriod d), ‖D y‖ ≤ M)
    (hsum : Summable fun m : ℕ => ‖halfCoeff d D m‖) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        D y * (1 - (r : ℂ) * Complex.exp (-(d : ℂ) * (y : ℂ) * I))⁻¹‖
      ≤ ∑' m : ℕ, ‖halfCoeff d D m‖ := by
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  set w : ℝ → ℂ := fun y => (r : ℂ) * Complex.exp (-(d : ℂ) * (y : ℂ) * I) with hw
  have hwn : ∀ y, ‖w y‖ = r := fun y => norm_conjArg r d y hr0
  have hfin : volume (Ioc (0 : ℝ) (putnamPeriod d)) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hbd : ∀ m : ℕ, ∀ y ∈ Ioc (0 : ℝ) (putnamPeriod d), ‖D y * w y ^ m‖ ≤ M * r ^ m := by
    intro m y hy
    rw [norm_mul, norm_pow, hwn]
    exact mul_le_mul_of_nonneg_right (hDb y hy) (by positivity)
  have hint : ∀ m : ℕ, IntegrableOn (fun y => D y * w y ^ m) (Ioc (0 : ℝ) (putnamPeriod d)) :=
    fun m => Integrable.mono' (g := fun _ : ℝ => M * r ^ m) (integrableOn_const hfin)
      (hDm.mul ((continuous_conjArg r d).measurable.pow_const m)).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall (hbd m)))
  have hsumF : Summable fun m : ℕ => ∫ y in Ioc (0 : ℝ) (putnamPeriod d), ‖D y * w y ^ m‖ := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun _ => norm_nonneg _) (fun m => ?_)
      (((summable_geometric_of_lt_one hr0 hr1).mul_left M).mul_left (putnamPeriod d))
    calc (∫ y in Ioc (0 : ℝ) (putnamPeriod d), ‖D y * w y ^ m‖)
        ≤ ∫ _y in Ioc (0 : ℝ) (putnamPeriod d), M * r ^ m :=
          setIntegral_mono_on (hint m).norm (integrableOn_const hfin) measurableSet_Ioc (hbd m)
      _ = putnamPeriod d * (M * r ^ m) := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le hP.le, smul_eq_mul, sub_zero]
  have hhas := hasSum_integral_of_summable_integral_norm hint hsumF
  have hpt : ∀ y : ℝ, ∑' m : ℕ, D y * w y ^ m = D y * (1 - w y)⁻¹ := fun y => by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by rw [hwn]; exact hr1)]
  have hcoef : ∀ m : ℕ, (∫ y in Ioc (0 : ℝ) (putnamPeriod d), D y * w y ^ m)
      = (r : ℂ) ^ m * halfCoeff d D m := by
    intro m
    rw [halfCoeff, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
    simp only [hw, mul_pow]
    ring
  have heq : (∫ y in Ioc (0 : ℝ) (putnamPeriod d), D y * (1 - w y)⁻¹)
      = ∑' m : ℕ, (r : ℂ) ^ m * halfCoeff d D m := by
    rw [← tsum_congr hcoef, hhas.tsum_eq]
    exact setIntegral_congr_fun measurableSet_Ioc fun y _ => (hpt y).symm
  have hterm : ∀ m : ℕ, ‖(r : ℂ) ^ m * halfCoeff d D m‖ ≤ ‖halfCoeff d D m‖ := fun m => by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hr0 hr1.le)
  have hs' : Summable fun m : ℕ => ‖(r : ℂ) ^ m * halfCoeff d D m‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum
  show ‖∫ y in Ioc (0 : ℝ) (putnamPeriod d), D y * (1 - w y)⁻¹‖ ≤ _
  rw [heq]
  exact (norm_tsum_le_tsum_norm hs').trans (Summable.tsum_le_tsum hterm hs' hsum)

/-- From `2i X = a + b - 2c` with `‖a‖ ≤ p` and `‖b‖, ‖c‖ ≤ q`. -/
theorem norm_le_of_two_I_mul_eq {X a b c : ℂ} {p q : ℝ} (h : (2 * I) * X = a + b - 2 * c)
    (ha : ‖a‖ ≤ p) (hb : ‖b‖ ≤ q) (hc : ‖c‖ ≤ q) : ‖X‖ ≤ (p + 3 * q) / 2 := by
  have h2 : ‖(2 : ℂ) * I‖ = 2 := by
    rw [norm_mul, Complex.norm_I, mul_one]
    norm_num
  have hn := congrArg norm h
  rw [norm_mul, h2] at hn
  have h1 := norm_sub_le (a + b) (2 * c)
  have h3 := norm_add_le a b
  have h4 : ‖2 * c‖ = 2 * ‖c‖ := by
    rw [norm_mul]
    norm_num
  linarith

/-- The pairing with the imaginary part of the Cauchy kernel is bounded uniformly in the radius:
the kernel is the Poisson kernel plus one minus its conjugate. -/
theorem norm_integral_mul_kernelIm_le {d : ℝ} (hd : 0 < d) {D : ℝ → ℂ} (hDm : Measurable D)
    {M : ℝ} (hDb : ∀ y ∈ Ioc (0 : ℝ) (putnamPeriod d), ‖D y‖ ≤ M)
    (hsum : Summable fun m : ℕ => ‖halfCoeff d D m‖) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖∫ y in Ioc (0 : ℝ) (putnamPeriod d), D y * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ)‖
      ≤ (M * putnamPeriod d + 3 * ∑' m : ℕ, ‖halfCoeff d D m‖) / 2 := by
  set P := putnamPeriod d with hPdef
  set A : ℝ := ∑' m : ℕ, ‖halfCoeff d D m‖ with hA
  have hDint : IntegrableOn D (Ioc (0 : ℝ) P) := integrableOn_of_measurable_of_bound hDm hDb
  have hint1 : IntegrableOn (fun y => D y * (circleFactor r d y)⁻¹) (Ioc (0 : ℝ) P) :=
    integrableOn_mul_bdd hDint (continuous_circleKernel hr0 hr1 d) (norm_circleKernel_le hr0 hr1 d)
  have hint2 : IntegrableOn (fun y => D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹))
      (Ioc (0 : ℝ) P) :=
    integrableOn_mul_bdd hDint (Complex.continuous_conj.comp (continuous_circleKernel hr0 hr1 d))
      (C := (1 - r)⁻¹) fun y => by rw [RCLike.norm_conj]; exact norm_circleKernel_le hr0 hr1 d y
  have hconjBound :
      ‖∫ y in Ioc (0 : ℝ) P, D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹)‖ ≤ A := by
    have h := norm_integral_mul_conjCauchy_le hd hDm hDb hsum hr0 hr1
    refine le_of_eq_of_le (congrArg norm (setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_)) h
    rw [map_inv₀, conj_circleFactor]
  have hmean : ‖∫ y in Ioc (0 : ℝ) P, D y‖ ≤ A := by
    have h0 : halfCoeff d D 0 = ∫ y in Ioc (0 : ℝ) P, D y :=
      setIntegral_congr_fun measurableSet_Ioc fun y _ => by rw [pow_zero, mul_one]
    rw [← h0]
    exact hsum.le_tsum 0 fun _ _ => norm_nonneg _
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
      integral_sub (hint1.add hint2) hDint
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
    refine hDint.norm.bdd_mul (c := 2 * (1 - r)⁻¹ + 1)
      ((continuous_poissonFactor hr0 hr1 d).aestronglyMeasurable.restrict)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact abs_poissonFactor_le hr0 hr1 d y
  have hmono : (∫ y in Ioc (0 : ℝ) P, poissonFactor r d y * ‖D y‖)
      ≤ ∫ y in Ioc (0 : ℝ) P, poissonFactor r d y * M :=
    setIntegral_mono_on hintNorm (hPint.mul_const M) measurableSet_Ioc fun y hy =>
      mul_le_mul_of_nonneg_left (hDb y hy) (poissonFactor_nonneg hr0 hr1 d y)
  have hval : (∫ y in Ioc (0 : ℝ) P, poissonFactor r d y * M) = P * M := by
    rw [integral_mul_const, integral_poissonFactor hd hr0 hr1]
  have hpoissonBound :
      ‖∫ y in Ioc (0 : ℝ) P, D y * ((poissonFactor r d y : ℝ) : ℂ)‖ ≤ P * M := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    rw [setIntegral_congr_fun measurableSet_Ioc (fun y _ => hpoint y)]
    rw [hval] at hmono
    exact hmono
  -- the imaginary part is half the difference of the kernel and its conjugate
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
      = (∫ y in Ioc (0 : ℝ) P, D y * ((poissonFactor r d y : ℝ) : ℂ))
        + (∫ y in Ioc (0 : ℝ) P, D y)
        - 2 * ∫ y in Ioc (0 : ℝ) P, D y * (starRingEnd ℂ) ((circleFactor r d y)⁻¹) := by
    rw [← integral_const_mul, hpoisson,
      ← setIntegral_congr_fun measurableSet_Ioc (fun y _ => hptIm y), hsub]
    ring
  exact norm_le_of_two_I_mul_eq hkey (hpoissonBound.trans_eq (mul_comm P M)) hmean hconjBound

/-- **Folding the pairing onto the first half period.** -/
theorem integral_mul_kernelIm_fold {d : ℝ} (hd : 0 < d) {D : ℝ → ℂ}
    (hDint : IntegrableOn D (Ioc (0 : ℝ) (putnamPeriod d))) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∫ y in Ioc (0 : ℝ) (putnamPeriod d), D y * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ))
      = ∫ y in Ioc (0 : ℝ) (putnamPeriod d / 2),
          (D y - D (putnamPeriod d - y)) * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ) := by
  set P := putnamPeriod d with hPdef
  set f : ℝ → ℂ := fun y => D y * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ) with hfdef
  have hP : 0 < P := putnamPeriod_pos hd
  have hH : 0 < P / 2 := by linarith
  have hHP : P / 2 ≤ P := by linarith
  have hhalf : P - P / 2 = P / 2 := by ring
  have hdP : d * P = 2 * Real.pi := by
    rw [hPdef, putnamPeriod]
    field_simp
  have hfint : IntegrableOn f (Ioc (0 : ℝ) P) :=
    integrableOn_mul_bdd hDint (continuous_circleKernel_im hr0 hr1 d)
      (norm_ofReal_circleKernelIm_le hr0 hr1 d)
  have hf1 : IntervalIntegrable f volume 0 (P / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hH.le).mpr
      (hfint.mono_set (Ioc_subset_Ioc_right hHP))
  have hf2 : IntervalIntegrable f volume (P / 2) P :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hHP).mpr
      (hfint.mono_set (Ioc_subset_Ioc_left hH.le))
  have hgint : IntervalIntegrable (fun x => f (P - x)) volume 0 (P / 2) := by
    have h := hf2.comp_sub_left P
    rw [hhalf, sub_self] at h
    exact h.symm
  have hrefl : ∀ x : ℝ, f (P - x) = -(D (P - x) * ((((circleFactor r d x)⁻¹).im : ℝ) : ℂ)) := by
    intro x
    rw [hfdef]
    simp only
    rw [circleKernel_im_reflect hdP r x]
    push_cast
    ring
  have hcomp : (∫ x in (0 : ℝ)..(P / 2), f (P - x)) = ∫ x in (P / 2)..P, f x := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := P / 2) f P
    rw [h, hhalf, sub_zero]
  have hsplit : (∫ y in (0 : ℝ)..P, f y)
      = (∫ y in (0 : ℝ)..(P / 2), f y) + ∫ y in (0 : ℝ)..(P / 2), f (P - y) := by
    rw [hcomp]
    exact (intervalIntegral.integral_add_adjacent_intervals hf1 hf2).symm
  have hcombine : (∫ y in (0 : ℝ)..(P / 2), f y) + ∫ y in (0 : ℝ)..(P / 2), f (P - y)
      = ∫ y in (0 : ℝ)..(P / 2), (f y + f (P - y)) :=
    (intervalIntegral.integral_add hf1 hgint).symm
  have hpt : ∀ y : ℝ, f y + f (P - y)
      = (D y - D (P - y)) * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ) := by
    intro y
    rw [hrefl y, hfdef]
    ring
  rw [← intervalIntegral.integral_of_le hP.le, hsplit, hcombine,
    intervalIntegral.integral_congr (g := fun y =>
      (D y - D (P - y)) * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ)) (fun y _ => hpt y),
    intervalIntegral.integral_of_le hH.le]

/-- **A nonnegative kernel against a function close to `J` near the origin.** If `‖Ψ - J‖ ≤ ‖J‖/2`
on `(0, δ]` and `‖(Ψ - J) K‖ ≤ C` on `(δ, H]`, then `(‖J‖/2) ∫K ≤ ‖∫ΨK‖ + CH`. -/
theorem half_norm_mul_integral_kernel_le {Ψ : ℝ → ℂ} {K : ℝ → ℝ} {H δ C : ℝ} {J : ℂ}
    (hδ0 : 0 < δ) (hδH : δ ≤ H) (hC : 0 ≤ C) (hKnn : ∀ y ∈ Ioc (0 : ℝ) H, 0 ≤ K y)
    (hKint : IntegrableOn K (Ioc (0 : ℝ) H))
    (hΨK : IntegrableOn (fun y => Ψ y * ((K y : ℝ) : ℂ)) (Ioc (0 : ℝ) H))
    (hnear : ∀ y ∈ Ioc (0 : ℝ) δ, ‖Ψ y - J‖ ≤ ‖J‖ / 2)
    (hfar : ∀ y ∈ Ioc δ H, ‖(Ψ y - J) * ((K y : ℝ) : ℂ)‖ ≤ C) :
    ‖J‖ / 2 * ∫ y in Ioc (0 : ℝ) H, K y
      ≤ ‖∫ y in Ioc (0 : ℝ) H, Ψ y * ((K y : ℝ) : ℂ)‖ + C * H := by
  have hJK : IntegrableOn (fun y => J * ((K y : ℝ) : ℂ)) (Ioc (0 : ℝ) H) :=
    hKint.ofReal.const_mul J
  have hdiff : IntegrableOn (fun y => (Ψ y - J) * ((K y : ℝ) : ℂ)) (Ioc (0 : ℝ) H) :=
    (hΨK.sub hJK).congr (Eventually.of_forall fun y => (sub_mul _ _ _).symm)
  have hsub1 : Ioc (0 : ℝ) δ ⊆ Ioc (0 : ℝ) H := Ioc_subset_Ioc_right hδH
  have hsub2 : Ioc δ H ⊆ Ioc (0 : ℝ) H := Ioc_subset_Ioc_left hδ0.le
  have hΛnn : 0 ≤ ∫ y in Ioc (0 : ℝ) H, K y := setIntegral_nonneg measurableSet_Ioc hKnn
  -- the main term
  have hJval : (∫ y in Ioc (0 : ℝ) H, J * ((K y : ℝ) : ℂ))
      = J * (((∫ y in Ioc (0 : ℝ) H, K y : ℝ)) : ℂ) := by
    have hco : (∫ y in Ioc (0 : ℝ) H, ((K y : ℝ) : ℂ))
        = (((∫ y in Ioc (0 : ℝ) H, K y : ℝ)) : ℂ) := integral_ofReal
    rw [integral_const_mul, hco]
  have hsplit : (∫ y in Ioc (0 : ℝ) H, (Ψ y - J) * ((K y : ℝ) : ℂ))
      = (∫ y in Ioc (0 : ℝ) H, Ψ y * ((K y : ℝ) : ℂ))
        - J * (((∫ y in Ioc (0 : ℝ) H, K y : ℝ)) : ℂ) := by
    rw [← hJval, ← integral_sub hΨK hJK]
    exact integral_congr_ae (Eventually.of_forall fun y => sub_mul _ _ _)
  have hJnorm : ‖J * (((∫ y in Ioc (0 : ℝ) H, K y : ℝ)) : ℂ)‖
      = ‖J‖ * ∫ y in Ioc (0 : ℝ) H, K y := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΛnn]
  have hmain : ‖J‖ * ∫ y in Ioc (0 : ℝ) H, K y
      ≤ ‖∫ y in Ioc (0 : ℝ) H, Ψ y * ((K y : ℝ) : ℂ)‖
        + ‖∫ y in Ioc (0 : ℝ) H, (Ψ y - J) * ((K y : ℝ) : ℂ)‖ := by
    rw [← hJnorm, hsplit]
    have h := norm_sub_le (∫ y in Ioc (0 : ℝ) H, Ψ y * ((K y : ℝ) : ℂ))
      ((∫ y in Ioc (0 : ℝ) H, Ψ y * ((K y : ℝ) : ℂ))
        - J * (((∫ y in Ioc (0 : ℝ) H, K y : ℝ)) : ℂ))
    rwa [sub_sub_cancel] at h
  -- the error term, near and far
  have hunion : Ioc (0 : ℝ) δ ∪ Ioc δ H = Ioc (0 : ℝ) H := Ioc_union_Ioc_eq_Ioc hδ0.le hδH
  have hdisj : Disjoint (Ioc (0 : ℝ) δ) (Ioc δ H) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx'.1 (not_lt.mpr hx.2)
  have herr : (∫ y in Ioc (0 : ℝ) H, ‖(Ψ y - J) * ((K y : ℝ) : ℂ)‖)
      = (∫ y in Ioc (0 : ℝ) δ, ‖(Ψ y - J) * ((K y : ℝ) : ℂ)‖)
        + ∫ y in Ioc δ H, ‖(Ψ y - J) * ((K y : ℝ) : ℂ)‖ := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioc
      (hdiff.mono_set hsub1).norm (hdiff.mono_set hsub2).norm]
  have hKsplit : (∫ y in Ioc (0 : ℝ) H, K y)
      = (∫ y in Ioc (0 : ℝ) δ, K y) + ∫ y in Ioc δ H, K y := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioc
      (hKint.mono_set hsub1) (hKint.mono_set hsub2)]
  have hKmass : (∫ y in Ioc (0 : ℝ) δ, K y) ≤ ∫ y in Ioc (0 : ℝ) H, K y :=
    (le_add_of_nonneg_right (setIntegral_nonneg measurableSet_Ioc fun y hy =>
      hKnn y (hsub2 hy))).trans_eq hKsplit.symm
  have hnear' : (∫ y in Ioc (0 : ℝ) δ, ‖(Ψ y - J) * ((K y : ℝ) : ℂ)‖)
      ≤ ‖J‖ / 2 * ∫ y in Ioc (0 : ℝ) H, K y := by
    have hmono : (∫ y in Ioc (0 : ℝ) δ, ‖(Ψ y - J) * ((K y : ℝ) : ℂ)‖)
        ≤ ∫ y in Ioc (0 : ℝ) δ, ‖J‖ / 2 * K y := by
      refine setIntegral_mono_on (hdiff.mono_set hsub1).norm
        ((hKint.mono_set hsub1).const_mul _) measurableSet_Ioc fun y hy => ?_
      have hKy : 0 ≤ K y := hKnn y (hsub1 hy)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hKy]
      exact mul_le_mul_of_nonneg_right (hnear y hy) hKy
    rw [integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left hKmass (by positivity))
  have hfar' : (∫ y in Ioc δ H, ‖(Ψ y - J) * ((K y : ℝ) : ℂ)‖) ≤ C * H := by
    have hmono : (∫ y in Ioc δ H, ‖(Ψ y - J) * ((K y : ℝ) : ℂ)‖) ≤ ∫ _y in Ioc δ H, C :=
      setIntegral_mono_on (hdiff.mono_set hsub2).norm (integrableOn_const measure_Ioc_lt_top.ne)
        measurableSet_Ioc hfar
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hδH, smul_eq_mul, mul_comm] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left (by linarith) hC)
  have herrnorm : ‖∫ y in Ioc (0 : ℝ) H, (Ψ y - J) * ((K y : ℝ) : ℂ)‖
      ≤ ‖J‖ / 2 * (∫ y in Ioc (0 : ℝ) H, K y) + C * H :=
    (norm_integral_le_integral_norm _).trans (herr.le.trans (add_le_add hnear' hfar'))
  linarith

/-- **A jump makes the folded pairing grow like the mass of the conjugate kernel.** -/
theorem jump_mul_log_le {d : ℝ} (hd : 0 < d) {D : ℝ → ℂ} (hDm : Measurable D) {M : ℝ}
    (hM : 0 ≤ M) (hDb : ∀ y ∈ Ioc (0 : ℝ) (putnamPeriod d), ‖D y‖ ≤ M) {J : ℂ} {δ : ℝ}
    (hδ0 : 0 < δ) (hδH : δ < putnamPeriod d / 2)
    (hδ : ∀ y ∈ Ioc (0 : ℝ) δ, ‖(D y - D (putnamPeriod d - y)) - J‖ ≤ ‖J‖ / 2)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {B₀ : ℝ}
    (hB : ‖∫ y in Ioc (0 : ℝ) (putnamPeriod d),
        D y * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ)‖ ≤ B₀) :
    ‖J‖ / 2 * ((Real.log (1 + r) - Real.log (1 - r)) / d)
      ≤ B₀ + (2 * M + ‖J‖) * (putnamPeriod d / 2) * (1 / (1 - Real.cos (d * δ) ^ 2)) := by
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  have hDint : IntegrableOn D (Ioc (0 : ℝ) (putnamPeriod d)) :=
    integrableOn_of_measurable_of_bound hDm hDb
  have hreflmem : ∀ y ∈ Ioc (0 : ℝ) (putnamPeriod d / 2),
      putnamPeriod d - y ∈ Ioc (0 : ℝ) (putnamPeriod d) := fun y hy =>
    ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hKbdd := norm_ofReal_circleKernelIm_le hr0 hr1 d
  have hKint : IntegrableOn (fun y : ℝ => ((circleFactor r d y)⁻¹).im)
      (Ioc (0 : ℝ) (putnamPeriod d / 2)) := by
    refine Integrable.mono' (g := fun _ : ℝ => (1 - r)⁻¹)
      (integrableOn_const measure_Ioc_lt_top.ne)
      ((Complex.continuous_im.comp
        (continuous_circleKernel hr0 hr1 d)).aestronglyMeasurable.restrict)
      (Eventually.of_forall fun y => ?_)
    have := hKbdd y
    rwa [Complex.norm_real] at this
  have hΨint : IntegrableOn (fun y : ℝ => D y - D (putnamPeriod d - y))
      (Ioc (0 : ℝ) (putnamPeriod d / 2)) :=
    (hDint.mono_set (Ioc_subset_Ioc_right (by linarith))).sub
      (integrableOn_of_measurable_of_bound (hDm.comp (measurable_const.sub measurable_id))
        fun y hy => hDb _ (hreflmem y hy))
  have hΨK := integrableOn_mul_bdd hΨint (continuous_circleKernel_im hr0 hr1 d) hKbdd
  have hCδnn : 0 ≤ 1 / (1 - Real.cos (d * δ) ^ 2) :=
    (abs_nonneg _).trans (abs_circleKernelIm_le_of_far (d := d) (r := r) hd hr0 hr1 hδ0 hδH
      (y := putnamPeriod d / 2) ⟨hδH, le_refl _⟩)
  have hfar : ∀ y ∈ Ioc δ (putnamPeriod d / 2),
      ‖((D y - D (putnamPeriod d - y)) - J) * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ)‖
        ≤ (2 * M + ‖J‖) * (1 / (1 - Real.cos (d * δ) ^ 2)) := by
    intro y hy
    have hyH : y ∈ Ioc (0 : ℝ) (putnamPeriod d / 2) := ⟨hδ0.trans hy.1, hy.2⟩
    have h1 : ‖D y - D (putnamPeriod d - y)‖ ≤ M + M :=
      (norm_sub_le _ _).trans
        (add_le_add (hDb y ⟨hyH.1, hyH.2.trans (by linarith)⟩) (hDb _ (hreflmem y hyH)))
    have h2 : ‖(D y - D (putnamPeriod d - y)) - J‖ ≤ 2 * M + ‖J‖ :=
      (norm_sub_le _ _).trans (by linarith)
    have h3 : ‖((((circleFactor r d y)⁻¹).im : ℝ) : ℂ)‖ ≤ 1 / (1 - Real.cos (d * δ) ^ 2) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_circleKernelIm_le_of_far hd hr0 hr1 hδ0 hδH hy
    rw [norm_mul]
    exact mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
  have hmain := half_norm_mul_integral_kernel_le (J := J) hδ0 hδH.le
    (mul_nonneg (by positivity) hCδnn)
    (fun y hy => circleKernelIm_nonneg_of_mem hd hr0 hr1 hy) hKint hΨK hδ hfar
  have hB' : ‖∫ y in Ioc (0 : ℝ) (putnamPeriod d / 2),
      (D y - D (putnamPeriod d - y)) * ((((circleFactor r d y)⁻¹).im : ℝ) : ℂ)‖ ≤ B₀ := by
    rwa [integral_mul_kernelIm_fold hd hDint hr0 hr1] at hB
  rw [← integral_circleKernel_im_half hd hr0 hr1]
  exact hmain.trans (add_le_add hB' (le_of_eq (by ring)))

/-- **Summable coefficients of non-negative index leave no jump across the period.** For a bounded
measurable function on the period `2π/d` whose Fourier coefficients of index `m ≥ 0` are
absolutely summable, the right limit at `0` and the left limit at the period coincide. -/
theorem endpoint_limits_eq_of_summable_halfCoeff {d : ℝ} (hd : 0 < d) {D : ℝ → ℂ}
    (hDm : Measurable D) {M : ℝ} (hDb : ∀ y ∈ Ioc (0 : ℝ) (putnamPeriod d), ‖D y‖ ≤ M)
    (hsum : Summable fun m : ℕ => ‖halfCoeff d D m‖) {La Lb : ℂ}
    (hLa : Tendsto D (𝓝[>] 0) (𝓝 La)) (hLb : Tendsto D (𝓝[<] putnamPeriod d) (𝓝 Lb)) :
    La = Lb := by
  by_contra hne
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  have hMnn : 0 ≤ M :=
    (norm_nonneg _).trans (hDb (putnamPeriod d / 2) ⟨by linarith, by linarith⟩)
  have hJpos : 0 < ‖La - Lb‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  -- the folded difference tends to the jump
  have hrefl : Tendsto (fun y : ℝ => putnamPeriod d - y) (𝓝[>] 0) (𝓝[<] putnamPeriod d) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_const.sub continuous_id).tendsto' 0 (putnamPeriod d)
        (sub_zero _)).mono_left nhdsWithin_le_nhds)
      (by filter_upwards [self_mem_nhdsWithin] with y hy
          exact sub_lt_self _ (mem_Ioi.mp hy))
  have hlim : Tendsto (fun y : ℝ => D y - D (putnamPeriod d - y)) (𝓝[>] 0) (𝓝 (La - Lb)) :=
    hLa.sub (hLb.comp hrefl)
  obtain ⟨δ, hδ0, hδH, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < putnamPeriod d / 2 ∧
      ∀ y ∈ Ioc (0 : ℝ) δ, ‖(D y - D (putnamPeriod d - y)) - (La - Lb)‖ ≤ ‖La - Lb‖ / 2 := by
    rw [Metric.tendsto_nhdsWithin_nhds] at hlim
    obtain ⟨δ₀, hδ₀, hδ₀'⟩ := hlim (‖La - Lb‖ / 2) (by positivity)
    refine ⟨min (δ₀ / 2) (putnamPeriod d / 4), by positivity,
      (min_le_right _ _).trans_lt (by linarith), fun y hy => ?_⟩
    have hylt : y < δ₀ := hy.2.trans_lt ((min_le_left _ _).trans_lt (by linarith))
    have hres := hδ₀' (mem_Ioi.mpr hy.1)
      (by rw [Real.dist_eq, sub_zero, abs_of_pos hy.1]; exact hylt)
    rw [dist_eq_norm] at hres
    exact hres.le
  -- the bound that the pairing obeys at every radius
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ r : ℝ, 0 ≤ r → r < 1 →
      ‖La - Lb‖ / 2 * ((Real.log (1 + r) - Real.log (1 - r)) / d) ≤ B :=
    ⟨_, fun r hr0 hr1 => jump_mul_log_le hd hDm hMnn hDb hδ0 hδH hδ hr0 hr1
      (norm_integral_mul_kernelIm_le hd hDm hDb hsum hr0 hr1)⟩
  -- a radius at which the conjugate kernel has more mass than the bound allows
  have hj : 0 < ‖La - Lb‖ / 2 := half_pos hJpos
  set L : ℝ := |B| / (‖La - Lb‖ / 2) + 1 with hLdef
  have hLpos : 0 < L := by positivity
  have hdL : 0 < d * L := mul_pos hd hLpos
  have hr0 : 0 ≤ 1 - Real.exp (-(d * L)) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hr1 : 1 - Real.exp (-(d * L)) < 1 := sub_lt_self _ (Real.exp_pos _)
  have hΛge : L ≤ (Real.log (1 + (1 - Real.exp (-(d * L))))
      - Real.log (1 - (1 - Real.exp (-(d * L))))) / d := by
    rw [sub_sub_cancel, Real.log_exp, le_div_iff₀ hd]
    have hlog : 0 ≤ Real.log (1 + (1 - Real.exp (-(d * L)))) := Real.log_nonneg (by linarith)
    linarith
  have h1 : ‖La - Lb‖ / 2 * L ≤ B :=
    (mul_le_mul_of_nonneg_left hΛge hj.le).trans (hB _ hr0 hr1)
  have h2 : ‖La - Lb‖ / 2 * L = |B| + ‖La - Lb‖ / 2 := by
    rw [hLdef]
    field_simp
  linarith [le_abs_self B]

/-! ### Half progressions -/

theorem measurable_ladderDefect (s : ℂ) (P : ℝ) : Measurable (ladderDefect s P) :=
  (measurable_ladderSum s P).add
    (by fun_prop : Continuous fun y : ℝ =>
      Complex.exp ((1 - s) * (y : ℂ)) / (Complex.exp ((1 - s) * (P : ℂ)) - 1)).measurable

theorem norm_ladderDefect_le {s : ℂ} (hs : 0 < s.re) {P : ℝ} (hP : 0 < P) {y : ℝ}
    (hy : y ∈ Ioc (0 : ℝ) P) :
    ‖ladderDefect s P y‖ ≤ (1 - Real.exp (-(s.re * P)))⁻¹
      + Real.exp (|1 - s.re| * P) / ‖Complex.exp ((1 - s) * (P : ℂ)) - 1‖ := by
  refine (norm_add_le _ _).trans (add_le_add (norm_ladderSum_le hs hP hy.1.le) ?_)
  rw [norm_div, Complex.norm_exp]
  refine div_le_div_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hre : ((1 - s) * (y : ℂ)).re = (1 - s.re) * y := by simp
  rw [hre]
  exact (mul_le_mul_of_nonneg_right (le_abs_self _) hy.1.le).trans
    (mul_le_mul_of_nonneg_left hy.2 (abs_nonneg _))

/-- The coefficients of non-negative index of the periodized Laplace kernel are the zeta values on
the upper half progression. -/
theorem halfCoeff_ladderDefect {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {T : ℝ} (hT : 0 < T)
    (m : ℕ) :
    halfCoeff T (ladderDefect ρ (putnamPeriod T)) m
      = -(riemannZeta (ρ + ((m * T : ℝ) : ℂ) * I) / (ρ + ((m * T : ℝ) : ℂ) * I)) := by
  have hP : 0 < putnamPeriod T := putnamPeriod_pos hT
  have hfreq : (2 * π * ((m : ℤ) : ℝ) / putnamPeriod T : ℝ) = m * T := by
    rw [putnamPeriod]
    push_cast
    field_simp
  have h := integral_ladderDefect_mul_exp h0 h1 hP (m : ℤ)
  rw [hfreq] at h
  rw [← h, halfCoeff, intervalIntegral.integral_of_le hP.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Divergence along every half progression.** For `ρ` in the open strip and `T > 0`,
`Σ_{n ≥ 0} |ζ(ρ + inT)| / |ρ + inT| = ∞`. -/
theorem not_summable_nat_norm_riemannZeta_div {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {T : ℝ}
    (hT : 0 < T) :
    ¬ Summable fun n : ℕ =>
      ‖riemannZeta (ρ + ((n * T : ℝ) : ℂ) * I) / (ρ + ((n * T : ℝ) : ℂ) * I)‖ := by
  intro hsum
  have hP : 0 < putnamPeriod T := putnamPeriod_pos hT
  have hcoef : Summable fun m : ℕ => ‖halfCoeff T (ladderDefect ρ (putnamPeriod T)) m‖ :=
    hsum.congr fun m => by rw [halfCoeff_ladderDefect h0 h1 hT m, norm_neg]
  have hcontP : Continuous fun y : ℝ => Complex.exp ((1 - ρ) * (y : ℂ))
      / (Complex.exp ((1 - ρ) * (putnamPeriod T : ℂ)) - 1) := by fun_prop
  have hLa : Tendsto (ladderDefect ρ (putnamPeriod T)) (𝓝[>] 0)
      (𝓝 ((∑' k : ℕ, ladderKernel ρ (0 + (k : ℝ) * putnamPeriod T))
        + Complex.exp ((1 - ρ) * ((0 : ℝ) : ℂ))
          / (Complex.exp ((1 - ρ) * (putnamPeriod T : ℂ)) - 1))) :=
    (tendsto_ladderSum_right h0 hP).add hcontP.continuousAt.continuousWithinAt
  have hLb : Tendsto (ladderDefect ρ (putnamPeriod T)) (𝓝[<] putnamPeriod T)
      (𝓝 ((∑' k : ℕ, ladderKernelLeft ρ (putnamPeriod T + (k : ℝ) * putnamPeriod T))
        + Complex.exp ((1 - ρ) * (putnamPeriod T : ℂ))
          / (Complex.exp ((1 - ρ) * (putnamPeriod T : ℂ)) - 1))) :=
    (tendsto_ladderSum_left h0 hP).add hcontP.continuousAt.continuousWithinAt
  have heq := endpoint_limits_eq_of_summable_halfCoeff hT (measurable_ladderDefect ρ _)
    (fun y hy => norm_ladderDefect_le h0 hP hy) hcoef hLa hLb
  have hjump := ladderDefect_limits_sub h0 h1 hP
  rw [heq, sub_self] at hjump
  exact tsum_jumpTerm_ne_zero h0 hP (neg_eq_zero.mp hjump.symm)

/-- **The upper half of a vertical progression in the strip has infinitely many non-zeros.** -/
theorem exists_nat_riemannZeta_ne_zero_progression {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {T : ℝ} (hT : 0 < T) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ riemannZeta (ρ + ((n * T : ℝ) : ℂ) * I) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine not_summable_nat_norm_riemannZeta_div h0 h1 hT
    (summable_of_ne_finset_zero (s := Finset.range N) fun n hn => ?_)
  rw [hcon n (not_lt.mp fun h => hn (Finset.mem_range.mpr h)), zero_div, norm_zero]

/-- **So has the lower half**, by complex conjugation. -/
theorem exists_nat_riemannZeta_ne_zero_progression_down {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {T : ℝ} (hT : 0 < T) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ riemannZeta (ρ - ((n * T : ℝ) : ℂ) * I) ≠ 0 := by
  obtain ⟨n, hn, hne⟩ := exists_nat_riemannZeta_ne_zero_progression (ρ := conj ρ)
    (by rwa [Complex.conj_re]) (by rwa [Complex.conj_re]) hT N
  refine ⟨n, hn, fun h => hne ?_⟩
  have hpt : conj ρ + ((n * T : ℝ) : ℂ) * I = conj (ρ - ((n * T : ℝ) : ℂ) * I) := by
    simp [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [hpt, riemannZeta_conj, h, map_zero]

/-- **No sequence of zeros approaches half of a class.** For `ρ` in the open strip, `T > 0` and a
square summable `η`, the points `ρ + inT + η_n`, `n ≥ 0`, are not eventually zeros of `ζ`. -/
theorem not_eventually_riemannZeta_eq_zero_near_halfClass {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {T : ℝ} (hT : 0 < T) {η : ℕ → ℂ} (hη : Summable fun n => ‖η n‖ ^ 2) :
    ¬ ∀ᶠ n : ℕ in atTop, riemannZeta (ρ + ((n * T : ℝ) : ℂ) * I + η n) = 0 := by
  intro hzero
  have hP : 0 < 2 * π / T := by positivity
  have hfreq : ∀ n : ℕ, (2 * π * ((n : ℤ) : ℝ) / (2 * π / T) : ℝ) = n * T := by
    intro n
    push_cast
    field_simp
  have h := summable_norm_riemannZeta_div_of_ladder (k := fun n : ℕ => (n : ℤ))
    Nat.cast_injective h0 h1 hP hη
    (by rw [Nat.cofinite_eq_atTop]; simpa only [hfreq] using hzero)
  simp only [hfreq] at h
  exact not_summable_nat_norm_riemannZeta_div h0 h1 hT h

/-- **Half of a class of one Frobenius is not in the zero set.** For a Frobenius `q > 1` and any
`ρ`, infinitely many of the conjugates `ρ + 2πin/log q`, `n ≥ 0`, are not zeros of `ξ`. -/
theorem exists_nat_conjugate_not_zero {q : ℝ} (hq : 1 < q) (ρ : ℂ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ xi (ρ + ((n * (2 * π / Real.log q) : ℝ) : ℂ) * I) ≠ 0 := by
  have hT : 0 < 2 * π / Real.log q := div_pos (by positivity) (Real.log_pos hq)
  by_cases hρ : 0 < ρ.re ∧ ρ.re < 1
  · obtain ⟨n, hn, hne⟩ := exists_nat_riemannZeta_ne_zero_progression hρ.1 hρ.2 hT N
    refine ⟨n, hn, fun h => hne ?_⟩
    have hre : (ρ + ((n * (2 * π / Real.log q) : ℝ) : ℂ) * I).re = ρ.re := by simp
    refine (xi_eq_zero_iff (by rw [hre]; exact hρ.1) fun h1' => ?_).mp h
    rw [h1', Complex.one_re] at hre
    linarith [hρ.2]
  · refine ⟨N, le_rfl, fun h => hρ ?_⟩
    have hre : (ρ + ((N * (2 * π / Real.log q) : ℝ) : ℂ) * I).re = ρ.re := by simp
    exact ⟨hre ▸ re_pos_of_xi_eq_zero h, hre ▸ re_lt_one_of_xi_eq_zero h⟩

end GaloisForLFunctions.InfiniteRankPurityTheory
