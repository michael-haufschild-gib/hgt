import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualBorelLaplace
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualHardyPolarization

/-!
# Source-ordered Borel--Laplace reconstruction of the Route-T Wold residual

Coefficientwise absolute Fubini loses the adjacent-prime cancellation on the negative Borel ray.
Source ordering retains that cancellation: the second-factorial kernel becomes `J₀(2√r)`, whose
flat origin preserves one full prime-log gap.  The resulting global negative-ray carrier agrees
with the local holomorphic Borel germ near zero and Laplace-transforms exactly to the established
lower-half-plane Hardy residual.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One source-ordered atom of the residual Borel carrier on its negative imaginary ray. -/
def xiHeatCassiniWoldResidualBorelLowerRaySourceAtom
    (x s : ℝ) (N : ℕ) : ℂ :=
  (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
    (xiHeatCassiniOrderedPrimeNegativePhase N x *
        secondFactorialBorelKernel
          (-((xiMassNthPrimeLogHeight N * s : ℝ) : ℂ)) -
      xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x *
        secondFactorialBorelKernel
          (-((xiMassNthPrimeLogHeight (N + 1) * s : ℝ) : ℂ)))

/-- The source-ordered negative-ray Borel carrier. -/
def xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier
    (x s : ℝ) : ℂ :=
  ∑' N : ℕ, xiHeatCassiniWoldResidualBorelLowerRaySourceAtom x s N

private theorem norm_secondFactorialBorelKernel_neg_mul_le_one
    {h s : ℝ} (hh : 0 ≤ h) (hs : 0 ≤ s) :
    ‖secondFactorialBorelKernel (-((h * s : ℝ) : ℂ))‖ ≤ 1 := by
  rw [secondFactorialBorelKernel_neg_real_eq_besselJ0 (mul_nonneg hh hs),
    Complex.norm_real, Real.norm_eq_abs]
  exact GaloisForLFunctions.RHTower.abs_besselJ0_le_one _

theorem norm_xiHeatCassiniWoldResidualBorelLowerRaySourceAtom_le
    (x : ℝ) {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    ‖xiHeatCassiniWoldResidualBorelLowerRaySourceAtom x s N‖ ≤
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N * (|x| + 2 * s) := by
  let h : ℝ := xiMassNthPrimeLogHeight N
  let H : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let A : ℂ := xiHeatCassiniOrderedPrimeNegativePhase N x
  let B : ℂ := xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x
  let F : ℂ := secondFactorialBorelKernel (-((h * s : ℝ) : ℂ))
  let G : ℂ := secondFactorialBorelKernel (-((H * s : ℝ) : ℂ))
  have hh : 0 ≤ h := (xiMassNthPrimeLogHeight_pos N).le
  have hH : h ≤ H :=
    nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N)
  have hF : ‖F‖ ≤ 1 := by
    simpa only [F] using norm_secondFactorialBorelKernel_neg_mul_le_one hh hs
  have hB : ‖B‖ = 1 := by
    dsimp only [B, xiHeatCassiniOrderedPrimeNegativePhase]
    rw [Complex.norm_exp]
    simp
  have hAB : ‖A - B‖ ≤ xiHeatCassiniOrderedPrimeLogGap N * |x| := by
    simpa only [A, B] using
      norm_xiHeatCassiniOrderedPrimeNegativePhase_sub_succ_le x N
  have hFG : ‖F - G‖ ≤ 2 * xiHeatCassiniOrderedPrimeLogGap N * s := by
    simpa only [F, G, h, H, xiHeatCassiniOrderedPrimeLogGap] using
      norm_secondFactorialBorelKernel_neg_mul_sub_le hh hH hs
  rw [xiHeatCassiniWoldResidualBorelLowerRaySourceAtom, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have hinner : ‖A * F - B * G‖ ≤
      xiHeatCassiniOrderedPrimeLogGap N * (|x| + 2 * s) := by
    calc
      ‖A * F - B * G‖ = ‖(A - B) * F + B * (F - G)‖ := by
        congr 1
        ring
      _ ≤ ‖A - B‖ * ‖F‖ + ‖B‖ * ‖F - G‖ := by
        exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
      _ ≤ (xiHeatCassiniOrderedPrimeLogGap N * |x|) * 1 +
          1 * (2 * xiHeatCassiniOrderedPrimeLogGap N * s) := by
        exact add_le_add
          (mul_le_mul hAB hF (norm_nonneg _)
            (mul_nonneg (xiHeatCassiniOrderedPrimeLogGap_nonneg N) (abs_nonneg x)))
          (mul_le_mul hB.le hFG (norm_nonneg _) zero_le_one)
      _ = xiHeatCassiniOrderedPrimeLogGap N * (|x| + 2 * s) := by ring
  calc
    |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        ‖xiHeatCassiniOrderedPrimeNegativePhase N x *
            secondFactorialBorelKernel
              (-((xiMassNthPrimeLogHeight N * s : ℝ) : ℂ)) -
          xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x *
            secondFactorialBorelKernel
              (-((xiMassNthPrimeLogHeight (N + 1) * s : ℝ) : ℂ))‖ =
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| * ‖A * F - B * G‖ := by
        rfl
    _ ≤ |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        (xiHeatCassiniOrderedPrimeLogGap N * (|x| + 2 * s)) :=
      mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
    _ = |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N * (|x| + 2 * s) := by ring

theorem summable_norm_xiHeatCassiniWoldResidualBorelLowerRaySourceAtom
    (x : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Summable (fun N : ℕ =>
      ‖xiHeatCassiniWoldResidualBorelLowerRaySourceAtom x s N‖) := by
  have hmajor :=
    summable_abs_xiHeatCassiniOrderedWoldResidual_mul_primeLogGap.mul_right
      (|x| + 2 * s)
  exact Summable.of_nonneg_of_le (fun N => norm_nonneg _)
    (fun N => norm_xiHeatCassiniWoldResidualBorelLowerRaySourceAtom_le x hs N)
    hmajor

theorem summable_xiHeatCassiniWoldResidualBorelLowerRaySourceAtom
    (x : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Summable (xiHeatCassiniWoldResidualBorelLowerRaySourceAtom x s) :=
  (summable_norm_xiHeatCassiniWoldResidualBorelLowerRaySourceAtom x hs).of_norm

private theorem summable_secondFactorialBorelKernelTerm (z : ℂ) :
    Summable (fun k : ℕ => z ^ k / ((k.factorial : ℂ) ^ (2 : ℕ))) := by
  apply Summable.of_norm
  have hmajor := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) ‖z‖).summable
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hmajor
  rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  have hkNat : 1 ≤ k.factorial :=
    Nat.one_le_iff_ne_zero.mpr k.factorial_ne_zero
  have hk : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast hkNat
  have hkpos : 0 < (k.factorial : ℝ) := by positivity
  calc
    ‖z‖ ^ k / (k.factorial : ℝ) ^ (2 : ℕ) ≤
        ‖z‖ ^ k / (k.factorial : ℝ) := by
      exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg z) k) hkpos
        (by nlinarith [sq_nonneg ((k.factorial : ℝ) - 1)])
    _ = ‖z‖ ^ k / (k.factorial : ℝ) := rfl

/-- Each source fibre of the original double Borel series is exactly its source-ordered
negative-ray atom. -/
theorem tsum_xiHeatCassiniWoldResidualBorelAtom_fixedSource_lowerRay
    (x s : ℝ) (N : ℕ) :
    (∑' k : ℕ,
      xiHeatCassiniWoldResidualBorelAtom x (-(I * (s : ℂ))) (N, k)) =
      xiHeatCassiniWoldResidualBorelLowerRaySourceAtom x s N := by
  let R : ℂ := xiHeatCassiniOrderedWoldResidualLogDiscrepancy N
  let A : ℂ := xiHeatCassiniOrderedPrimeNegativePhase N x
  let B : ℂ := xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x
  let h : ℝ := xiMassNthPrimeLogHeight N
  let H : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let f : ℕ → ℂ := fun k => A *
    (-((h * s : ℝ) : ℂ)) ^ k / ((k.factorial : ℂ) ^ (2 : ℕ))
  let g : ℕ → ℂ := fun k => B *
    (-((H * s : ℝ) : ℂ)) ^ k / ((k.factorial : ℂ) ^ (2 : ℕ))
  have hf : Summable f := by
    dsimp only [f]
    exact ((summable_secondFactorialBorelKernelTerm
      (-((h * s : ℝ) : ℂ))).mul_left A).congr (fun k => by ring)
  have hg : Summable g := by
    dsimp only [g]
    exact ((summable_secondFactorialBorelKernelTerm
      (-((H * s : ℝ) : ℂ))).mul_left B).congr (fun k => by ring)
  calc
    (∑' k : ℕ,
      xiHeatCassiniWoldResidualBorelAtom x (-(I * (s : ℂ))) (N, k)) =
        ∑' k : ℕ, R * (f k - g k) := by
      apply tsum_congr
      intro k
      have hhpow :
          (-I * (h : ℂ)) ^ k * (-(I * (s : ℂ))) ^ k =
            (-((h * s : ℝ) : ℂ)) ^ k := by
        rw [← mul_pow]
        congr 1
        calc
          -I * (h : ℂ) * -(I * (s : ℂ)) =
              (I * I) * ((h : ℂ) * (s : ℂ)) := by ring
          _ = -((h * s : ℝ) : ℂ) := by
            rw [Complex.I_mul_I]
            push_cast
            ring
      have hHpow :
          (-I * (H : ℂ)) ^ k * (-(I * (s : ℂ))) ^ k =
            (-((H * s : ℝ) : ℂ)) ^ k := by
        rw [← mul_pow]
        congr 1
        calc
          -I * (H : ℂ) * -(I * (s : ℂ)) =
              (I * I) * ((H : ℂ) * (s : ℂ)) := by ring
          _ = -((H * s : ℝ) : ℂ) := by
            rw [Complex.I_mul_I]
            push_cast
            ring
      rw [xiHeatCassiniWoldResidualBorelAtom,
        xiHeatCassiniWoldResidualLowerHalfPhaseConnectionJetAtom]
      dsimp only [R, A, B, h, H, f, g]
      rw [← hhpow, ← hHpow]
      ring
    _ = R * (∑' k : ℕ, (f k - g k)) := by rw [tsum_mul_left]
    _ = R * ((∑' k : ℕ, f k) - ∑' k : ℕ, g k) := by
      rw [Summable.tsum_sub hf hg]
    _ = xiHeatCassiniWoldResidualBorelLowerRaySourceAtom x s N := by
      rw [xiHeatCassiniWoldResidualBorelLowerRaySourceAtom,
        secondFactorialBorelKernel, secondFactorialBorelKernel]
      dsimp only [R, A, B, h, H, f, g]
      congr 2
      · rw [← tsum_mul_left]
        apply tsum_congr
        intro k
        ring
      · rw [← tsum_mul_left]
        apply tsum_congr
        intro k
        ring

/-- On a nontrivial initial ray segment, source ordering is exactly the analytic Borel germ, not a
separate resummation. -/
theorem exists_radius_xiHeatCassiniWoldResidualBorelCarrier_lowerRay_eq_sourceCarrier :
    ∃ r : ℝ, 0 < r ∧ ∀ (x s : ℝ), 0 ≤ s → s < r →
      xiHeatCassiniWoldResidualBorelCarrier x (-(I * (s : ℂ))) =
        xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier x s := by
  obtain ⟨r, hr, hsum⟩ :=
    exists_radius_summable_xiHeatCassiniWoldResidualBorelAtom
  refine ⟨r, hr, fun x s hs hsr => ?_⟩
  have hnorm : ‖-(I * (s : ℂ))‖ < r := by
    simpa [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs] using hsr
  have htotal := hsum x (-(I * (s : ℂ))) hnorm
  calc
    xiHeatCassiniWoldResidualBorelCarrier x (-(I * (s : ℂ))) =
        ∑' N : ℕ, ∑' k : ℕ,
          xiHeatCassiniWoldResidualBorelAtom x (-(I * (s : ℂ))) (N, k) := by
      rw [xiHeatCassiniWoldResidualBorelCarrier, htotal.tsum_prod]
    _ = ∑' N : ℕ,
        xiHeatCassiniWoldResidualBorelLowerRaySourceAtom x s N := by
      apply tsum_congr
      exact tsum_xiHeatCassiniWoldResidualBorelAtom_fixedSource_lowerRay x s
    _ = xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier x s := rfl

/-- Atomwise Borel--Laplace integrand after preserving source order. -/
def xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom
    (x y : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ((Real.exp (-t) : ℝ) : ℂ) *
    xiHeatCassiniWoldResidualBorelLowerRaySourceAtom x (y * t) N

private theorem secondFactorialBorelKernel_lowerRay_mul
    (h y t : ℝ) :
    secondFactorialBorelKernel (-((h * (y * t) : ℝ) : ℂ)) =
      secondFactorialBorelKernel ((-((h * y : ℝ) : ℂ)) * (t : ℂ)) := by
  congr 1
  push_cast
  ring

private theorem primeComplexNegativePhase_sub_mul_I
    (N : ℕ) (x y : ℝ) :
    xiHeatCassiniOrderedPrimeNegativePhase N x *
        Complex.exp (-((xiMassNthPrimeLogHeight N * y : ℝ) : ℂ)) =
      xiHeatCassiniOrderedPrimeComplexNegativePhase N
        ((x : ℂ) - (y : ℂ) * I) := by
  rw [xiHeatCassiniOrderedPrimeNegativePhase,
    xiHeatCassiniOrderedPrimeComplexNegativePhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  simp
  ring

theorem integrableOn_xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom
    (x y : ℝ) (N : ℕ) :
    IntegrableOn
      (xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom x y N) (Ioi 0) := by
  let R : ℂ := xiHeatCassiniOrderedWoldResidualLogDiscrepancy N
  let A : ℂ := xiHeatCassiniOrderedPrimeNegativePhase N x
  let B : ℂ := xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x
  let h : ℝ := xiMassNthPrimeLogHeight N
  let H : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let w : ℂ := -((h * y : ℝ) : ℂ)
  let W : ℂ := -((H * y : ℝ) : ℂ)
  have hf := (integrableOn_exp_neg_mul_secondFactorialBorelKernel w).const_mul A
  have hg := (integrableOn_exp_neg_mul_secondFactorialBorelKernel W).const_mul B
  apply MeasureTheory.IntegrableOn.congr_fun ((hf.sub hg).const_mul R)
  · intro t ht
    rw [xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom,
      xiHeatCassiniWoldResidualBorelLowerRaySourceAtom,
      secondFactorialBorelKernel_lowerRay_mul,
      secondFactorialBorelKernel_lowerRay_mul]
    dsimp only [R, A, B, h, H, w, W]
    simp only [Pi.sub_apply]
    ring
  · exact measurableSet_Ioi

/-- One source atom Laplace-transforms exactly to the corresponding physical lower-Hardy edge. -/
theorem integral_xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom
    (x y : ℝ) (N : ℕ) :
    (∫ t : ℝ in Ioi 0,
      xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom x y N t) =
      xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        ((x : ℂ) - (y : ℂ) * I) N := by
  let R : ℂ := xiHeatCassiniOrderedWoldResidualLogDiscrepancy N
  let A : ℂ := xiHeatCassiniOrderedPrimeNegativePhase N x
  let B : ℂ := xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x
  let h : ℝ := xiMassNthPrimeLogHeight N
  let H : ℝ := xiMassNthPrimeLogHeight (N + 1)
  let w : ℂ := -((h * y : ℝ) : ℂ)
  let W : ℂ := -((H * y : ℝ) : ℂ)
  have hf := integrableOn_exp_neg_mul_secondFactorialBorelKernel w
  have hg := integrableOn_exp_neg_mul_secondFactorialBorelKernel W
  rw [show xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom x y N =
      fun t : ℝ => R *
        (A * (((Real.exp (-t) : ℝ) : ℂ) *
            secondFactorialBorelKernel (w * (t : ℂ))) -
          B * (((Real.exp (-t) : ℝ) : ℂ) *
            secondFactorialBorelKernel (W * (t : ℂ)))) by
    funext t
    rw [xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom,
      xiHeatCassiniWoldResidualBorelLowerRaySourceAtom,
      secondFactorialBorelKernel_lowerRay_mul,
      secondFactorialBorelKernel_lowerRay_mul]
    dsimp only [R, A, B, h, H, w, W]
    ring]
  rw [integral_const_mul, integral_sub
      (hf.const_mul A) (hg.const_mul B),
    integral_const_mul, integral_const_mul,
    integral_secondFactorialBorelKernel_eq_exp,
    integral_secondFactorialBorelKernel_eq_exp]
  rw [xiHeatCassiniWoldResidualComplexPhaseConnectionAtom]
  dsimp only [R, A, B, h, H, w, W]
  rw [primeComplexNegativePhase_sub_mul_I,
    primeComplexNegativePhase_sub_mul_I]

private theorem integrableOn_exp_neg_mul_affine (x y : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * (|x| + 2 * y * t)) (Ioi 0) := by
  have h0raw := integrableOn_pow_mul_exp_neg_mul_Ioi (r := 1) (by norm_num) 0
  have h1raw := integrableOn_pow_mul_exp_neg_mul_Ioi (r := 1) (by norm_num) 1
  have h0 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    convert h0raw using 1
    funext t
    simp
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi 0) := by
    convert h1raw using 1
    funext t
    simp
  apply MeasureTheory.IntegrableOn.congr_fun
    ((h0.const_mul |x|).add (h1.const_mul (2 * y)))
  · intro t ht
    change |x| * Real.exp (-t) + (2 * y) * (t * Real.exp (-t)) = _
    ring
  · exact measurableSet_Ioi

private theorem integral_exp_neg_mul_affine (x y : ℝ) :
    (∫ t : ℝ in Ioi 0, Real.exp (-t) * (|x| + 2 * y * t)) =
      |x| + 2 * y := by
  have h0raw := integrableOn_pow_mul_exp_neg_mul_Ioi (r := 1) (by norm_num) 0
  have h1raw := integrableOn_pow_mul_exp_neg_mul_Ioi (r := 1) (by norm_num) 1
  have h0 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    convert h0raw using 1
    funext t
    simp
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi 0) := by
    convert h1raw using 1
    funext t
    simp
  rw [show (fun t : ℝ => Real.exp (-t) * (|x| + 2 * y * t)) =
      fun t : ℝ => |x| * Real.exp (-t) + (2 * y) * (t * Real.exp (-t)) by
    funext t
    ring]
  rw [MeasureTheory.integral_add (h0.const_mul |x|) (h1.const_mul (2 * y)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hm0 := integral_pow_mul_exp_neg_mul_Ioi (r := 1) (by norm_num) 0
  have hm1 := integral_pow_mul_exp_neg_mul_Ioi (r := 1) (by norm_num) 1
  have hi0 : (∫ t : ℝ in Ioi 0, Real.exp (-t)) = 1 := by
    simpa using hm0
  have hi1 : (∫ t : ℝ in Ioi 0, t * Real.exp (-t)) = 1 := by
    simpa using hm1
  rw [hi0, hi1]
  ring

theorem integral_norm_xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom_le
    (x : ℝ) {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    (∫ t : ℝ in Ioi 0,
      ‖xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom x y N t‖) ≤
      (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N) * (|x| + 2 * y) := by
  let b : ℝ := |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
    xiHeatCassiniOrderedPrimeLogGap N
  have hb : 0 ≤ b := by
    dsimp only [b]
    exact mul_nonneg (abs_nonneg _)
      (xiHeatCassiniOrderedPrimeLogGap_nonneg N)
  have hatom :=
    integrableOn_xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom x y N
  have henv := (integrableOn_exp_neg_mul_affine x y).const_mul b
  calc
    (∫ t : ℝ in Ioi 0,
      ‖xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom x y N t‖) ≤
        ∫ t : ℝ in Ioi 0,
          b * (Real.exp (-t) * (|x| + 2 * y * t)) := by
      apply integral_mono_ae hatom.norm henv
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      rw [xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_pos (-t)).le]
      have hsource :=
        norm_xiHeatCassiniWoldResidualBorelLowerRaySourceAtom_le x
          (mul_nonneg hy ht0) N
      calc
        Real.exp (-t) *
            ‖xiHeatCassiniWoldResidualBorelLowerRaySourceAtom x (y * t) N‖ ≤
          Real.exp (-t) *
            (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
              xiHeatCassiniOrderedPrimeLogGap N * (|x| + 2 * (y * t))) :=
            mul_le_mul_of_nonneg_left hsource (Real.exp_pos _).le
        _ = b * (Real.exp (-t) * (|x| + 2 * y * t)) := by
          dsimp only [b]
          ring
    _ = b * (∫ t : ℝ in Ioi 0,
          Real.exp (-t) * (|x| + 2 * y * t)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = b * (|x| + 2 * y) := by
      rw [integral_exp_neg_mul_affine]
    _ = (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N) * (|x| + 2 * y) := rfl

theorem summable_integral_norm_xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom
    (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    Summable (fun N : ℕ => ∫ t : ℝ in Ioi 0,
      ‖xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom x y N t‖) := by
  have hmajor :=
    summable_abs_xiHeatCassiniOrderedWoldResidual_mul_primeLogGap.mul_right
      (|x| + 2 * y)
  exact Summable.of_nonneg_of_le
    (fun N => integral_nonneg fun _ => norm_nonneg _)
    (fun N =>
      integral_norm_xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom_le
        x hy N)
    hmajor

theorem integrableOn_exp_neg_mul_xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier
    (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (fun t : ℝ =>
      ((Real.exp (-t) : ℝ) : ℂ) *
        xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier x (y * t)) (Ioi 0) := by
  rw [show (fun t : ℝ =>
      ((Real.exp (-t) : ℝ) : ℂ) *
        xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier x (y * t)) =
      fun t : ℝ => ∑' N : ℕ,
        xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom x y N t by
    funext t
    rw [xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier,
      ← tsum_mul_left]
    rfl]
  exact GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (fun N =>
      integrableOn_xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom x y N)
    (summable_integral_norm_xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom
      x hy)

/-- Exact source-ordered Borel--Laplace reconstruction on the safe lower half-plane.  The
negative-ray continuation of the local Borel germ Laplace-transforms to the pre-existing residual
Hardy carrier, with no coefficientwise absolute-Fubini assumption. -/
theorem integral_exp_neg_mul_xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier_eq_lowerHardy
    (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (∫ t : ℝ in Ioi 0,
      ((Real.exp (-t) : ℝ) : ℂ) *
        xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier x (y * t)) =
      xiHeatCassiniWoldResidualLowerHardyKernel
        ((x : ℂ) - (y : ℂ) * I) := by
  let F : ℕ → ℝ → ℂ := fun N t =>
    xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom x y N t
  have hFint : ∀ N, IntegrableOn (F N) (Ioi 0) := fun N =>
    integrableOn_xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom x y N
  have hFsum : Summable (fun N : ℕ => ∫ t : ℝ in Ioi 0, ‖F N t‖) :=
    summable_integral_norm_xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom
      x hy
  calc
    (∫ t : ℝ in Ioi 0,
      ((Real.exp (-t) : ℝ) : ℂ) *
        xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier x (y * t)) =
        ∫ t : ℝ in Ioi 0, ∑' N : ℕ, F N t := by
      congr 1
      funext t
      rw [xiHeatCassiniWoldResidualBorelLowerRaySourceCarrier,
        ← tsum_mul_left]
      rfl
    _ = ∑' N : ℕ, ∫ t : ℝ in Ioi 0, F N t :=
      (MeasureTheory.integral_tsum_of_summable_integral_norm hFint hFsum).symm
    _ = ∑' N : ℕ,
        xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
          ((x : ℂ) - (y : ℂ) * I) N := by
      apply tsum_congr
      exact integral_xiHeatCassiniWoldResidualBorelLowerRaySourceLaplaceAtom x y
    _ = xiHeatCassiniWoldResidualLowerHardyKernel
        ((x : ℂ) - (y : ℂ) * I) := rfl

end

end RHTower
