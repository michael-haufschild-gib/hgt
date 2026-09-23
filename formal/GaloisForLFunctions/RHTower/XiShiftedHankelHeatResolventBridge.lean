import GaloisForLFunctions.RHTower.HeatMomentDerivativeLadder
import GaloisForLFunctions.RHTower.XiShiftedMomentSourceJet
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryFlux
import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

open Complex Matrix MeasureTheory Set
open scoped BigOperators

namespace RHTower
noncomputable section

def xiHeatResolventAtom (y : ℝ) (n : ℕ) (q : XiZeroCopy) (t : ℝ) : ℂ :=
  (t : ℂ) ^ n * Complex.exp (-(((y : ℂ) + xiSquaredNode q) * t))

theorem norm_xiHeatResolventAtom_of_pos
    (y : ℝ) (n : ℕ) (q : XiZeroCopy) {t : ℝ} (ht : 0 < t) :
    ‖xiHeatResolventAtom y n q t‖ =
      t ^ n * Real.exp (-((y + (xiSquaredNode q).re) * t)) := by
  rw [xiHeatResolventAtom, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem integral_pow_mul_exp_shiftedSquaredNode
    {y : ℝ} (hy : 0 ≤ y) (n : ℕ) (q : XiZeroCopy) :
    (∫ t in Ioi (0 : ℝ), xiHeatResolventAtom y n q t) =
      (n.factorial : ℂ) * xiShiftedReciprocalSquare y q ^ (n + 1) := by
  have hrate : 0 < ((y : ℂ) + xiSquaredNode q).re := by
    rw [ofReal_add_xiSquaredNode_re]
    exact add_pos_of_nonneg_of_pos hy (xiSquaredNode_re_pos q)
  have hs : 0 < (((n + 1 : ℕ) : ℂ)).re := by
    norm_num
    exact_mod_cast Nat.succ_pos n
  have h := GaloisForLFunctions.HTGeometry.integral_cpow_mul_exp_neg_mul_Ioi
    (s := ((n + 1 : ℕ) : ℂ)) (w := (y : ℂ) + xiSquaredNode q)
    hs hrate
  have hGamma : Complex.Gamma ((n + 1 : ℕ) : ℂ) = (n.factorial : ℂ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.Gamma_nat_eq_factorial n
  rw [hGamma] at h
  rw [xiShiftedReciprocalSquare_eq_inv hy]
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    rw [show (((n + 1 : ℕ) : ℂ) - 1) = (n : ℂ) by push_cast; ring]
    change xiHeatResolventAtom y n q t = (t : ℂ) ^ (n : ℂ) * _
    rw [xiHeatResolventAtom]
    rw [Complex.cpow_natCast]
  · rw [Complex.cpow_neg, Complex.cpow_natCast, inv_pow]

theorem integrableOn_xiHeatResolventAtom
    {y : ℝ} (hy : 0 ≤ y) (n : ℕ) (q : XiZeroCopy) :
    IntegrableOn (xiHeatResolventAtom y n q) (Ioi (0 : ℝ)) := by
  have hrate : 0 < y + (xiSquaredNode q).re :=
    add_pos_of_nonneg_of_pos hy (xiSquaredNode_re_pos q)
  have hg := integrableOn_pow_mul_exp_neg_mul_Ioi hrate n
  have hmeas : AEStronglyMeasurable (xiHeatResolventAtom y n q)
      (volume.restrict (Ioi (0 : ℝ))) := by
    apply Continuous.aestronglyMeasurable
    unfold xiHeatResolventAtom
    fun_prop
  refine Integrable.mono' hg hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_xiHeatResolventAtom_of_pos y n q ht]

theorem integral_norm_xiHeatResolventAtom
    {y : ℝ} (hy : 0 ≤ y) (n : ℕ) (q : XiZeroCopy) :
    (∫ t in Ioi (0 : ℝ), ‖xiHeatResolventAtom y n q t‖) =
      (n.factorial : ℝ) / (y + (xiSquaredNode q).re) ^ (n + 1) := by
  have hrate : 0 < y + (xiSquaredNode q).re :=
    add_pos_of_nonneg_of_pos hy (xiSquaredNode_re_pos q)
  rw [← integral_pow_mul_exp_neg_mul_Ioi hrate n]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact norm_xiHeatResolventAtom_of_pos y n q ht

theorem norm_shiftedSquaredNode_le_two_mul_re
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    ‖(y : ℂ) + xiSquaredNode q‖ ≤ 2 * (y + (xiSquaredNode q).re) := by
  let A : ℝ := y + (xiSquaredNode q).re
  let B : ℝ := (xiSquaredNode q).im
  have hA : 0 < A := add_pos hy (xiSquaredNode_re_pos q)
  have hsector : 84 * B ^ (2 : ℕ) < A ^ (2 : ℕ) := by
    simpa [A, B] using eightyFour_mul_xiSquaredNode_im_sq_lt hy q
  have hB : B ^ (2 : ℕ) ≤ A ^ (2 : ℕ) := by nlinarith [sq_nonneg B]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hA.le)).mp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im,
    zero_add]
  dsimp [A, B] at hB hA ⊢
  nlinarith [sq_nonneg (y + (xiSquaredNode q).re)]

theorem integral_norm_xiHeatResolventAtom_le
    {y : ℝ} (hy : 0 < y) (n : ℕ) (q : XiZeroCopy) :
    (∫ t in Ioi (0 : ℝ), ‖xiHeatResolventAtom y n q t‖) ≤
      (n.factorial : ℝ) *
        (2 * ‖xiShiftedReciprocalSquare y q‖) ^ (n + 1) := by
  rw [integral_norm_xiHeatResolventAtom hy.le]
  let A : ℝ := y + (xiSquaredNode q).re
  let z : ℂ := (y : ℂ) + xiSquaredNode q
  have hA : 0 < A := add_pos hy (xiSquaredNode_re_pos q)
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr (ofReal_add_xiSquaredNode_ne_zero hy.le q)
  have hnorm : ‖z‖ ≤ 2 * A := by
    simpa [z, A] using norm_shiftedSquaredNode_le_two_mul_re hy q
  have hinv : A⁻¹ ≤ 2 * ‖xiShiftedReciprocalSquare y q‖ := by
    rw [xiShiftedReciprocalSquare_eq_inv hy.le, norm_inv]
    have hraw : (2 * A)⁻¹ ≤ ‖z‖⁻¹ :=
      (inv_le_inv₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hA) hz).2 hnorm
    calc
      A⁻¹ = 2 * (2 * A)⁻¹ := by field_simp
      _ ≤ 2 * ‖z‖⁻¹ := mul_le_mul_of_nonneg_left hraw (by norm_num)
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr hA.le) hinv (n + 1)
  rw [show y + (xiSquaredNode q).re = A by rfl, div_eq_mul_inv, ← inv_pow]
  exact mul_le_mul_of_nonneg_left hp (by positivity)

theorem summable_integral_norm_xiHeatResolventAtom
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    Summable (fun q : XiZeroCopy =>
      ∫ t in Ioi (0 : ℝ), ‖xiHeatResolventAtom y n q t‖) := by
  have hs : Summable (fun q : XiZeroCopy =>
      (n.factorial : ℝ) *
        (2 * ‖xiShiftedReciprocalSquare y q‖) ^ (n + 1)) := by
    have hnorm := (summable_xiShiftedReciprocalSquare_pow hy.le n).norm
    have hscaled := hnorm.mul_left
      ((n.factorial : ℝ) * 2 ^ (n + 1))
    refine hscaled.congr (fun q => ?_)
    rw [norm_pow]
    ring
  apply Summable.of_nonneg_of_le
  · intro q
    exact integral_nonneg fun _ => norm_nonneg _
  · exact fun q => integral_norm_xiHeatResolventAtom_le hy n q
  · exact hs

/-- Gamma--Laplace kernel built from the ordinary Xi Gaussian heat trace. -/
def xiHeatResolventKernel (y : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ n * Complex.exp (-((y : ℂ) * t)) * xiGaussianHeatMoment 0 t

theorem tsum_xiHeatResolventAtom_eq_kernel
    (y : ℝ) (n : ℕ) (t : ℝ) :
    (∑' q : XiZeroCopy, xiHeatResolventAtom y n q t) =
      xiHeatResolventKernel y n t := by
  rw [xiHeatResolventKernel, xiGaussianHeatMoment]
  simp only [pow_zero, one_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  rw [xiHeatResolventAtom, xiGaussianHeatTerm, xiSquaredNode]
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  ring

/-- **Heat--resolvent bridge.** Every shifted reciprocal-Xi moment is the exact Gamma-normalized
Laplace transform of the ordinary Xi Gaussian heat trace. -/
theorem integral_xiHeatResolventKernel_eq_xiShiftedReciprocalMoment
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), xiHeatResolventKernel y n t) =
      (n.factorial : ℂ) * xiShiftedReciprocalMoment y n := by
  have hFint : ∀ q : XiZeroCopy,
      Integrable (xiHeatResolventAtom y n q)
        (volume.restrict (Ioi (0 : ℝ))) :=
    fun q => integrableOn_xiHeatResolventAtom hy.le n q
  have hswap :
      (∫ t in Ioi (0 : ℝ), ∑' q : XiZeroCopy, xiHeatResolventAtom y n q t) =
        ∑' q : XiZeroCopy,
          ∫ t in Ioi (0 : ℝ), xiHeatResolventAtom y n q t :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm hFint
      (summable_integral_norm_xiHeatResolventAtom hy n)).symm
  calc
    (∫ t in Ioi (0 : ℝ), xiHeatResolventKernel y n t) =
        ∫ t in Ioi (0 : ℝ),
          ∑' q : XiZeroCopy, xiHeatResolventAtom y n q t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (tsum_xiHeatResolventAtom_eq_kernel y n t).symm
    _ = ∑' q : XiZeroCopy,
          ∫ t in Ioi (0 : ℝ), xiHeatResolventAtom y n q t := hswap
    _ = ∑' q : XiZeroCopy,
          (n.factorial : ℂ) * xiShiftedReciprocalSquare y q ^ (n + 1) := by
      apply tsum_congr
      intro q
      exact integral_pow_mul_exp_shiftedSquaredNode hy.le n q
    _ = (n.factorial : ℂ) * xiShiftedReciprocalMoment y n := by
      rw [xiShiftedReciprocalMoment, tsum_mul_left]

theorem integrableOn_xiHeatResolventKernel
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    IntegrableOn (xiHeatResolventKernel y n) (Ioi (0 : ℝ)) := by
  have hsum : Integrable
      (fun t => ∑' q : XiZeroCopy, xiHeatResolventAtom y n q t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
      (fun q => integrableOn_xiHeatResolventAtom hy.le n q)
      (summable_integral_norm_xiHeatResolventAtom hy n)
  refine hsum.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact tsum_xiHeatResolventAtom_eq_kernel y n t

/-- Real Gamma--Laplace kernel; the Gaussian heat trace is real unconditionally. -/
def xiHeatResolventKernelReal (y : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  t ^ n * Real.exp (-(y * t)) * xiGaussianHeatMomentReal 0 t

theorem xiHeatResolventKernel_re
    (y : ℝ) (n : ℕ) (t : ℝ) :
    (xiHeatResolventKernel y n t).re = xiHeatResolventKernelReal y n t := by
  have hpow : (t : ℂ) ^ n = ((t ^ n : ℝ) : ℂ) := by push_cast; rfl
  have hexp : Complex.exp (-((y : ℂ) * t)) = ((Real.exp (-(y * t)) : ℝ) : ℂ) := by
    push_cast
    rfl
  change (((t : ℂ) ^ n * Complex.exp (-((y : ℂ) * t))) *
    xiGaussianHeatMoment 0 t).re = _
  rw [hpow, hexp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero, xiHeatResolventKernelReal,
    xiGaussianHeatMomentReal]

theorem integrableOn_xiHeatResolventKernelReal
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    IntegrableOn (xiHeatResolventKernelReal y n) (Ioi (0 : ℝ)) := by
  have h := (integrableOn_xiHeatResolventKernel hy n).re
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact xiHeatResolventKernel_re y n t

/-- Real form of the heat--resolvent bridge. -/
theorem integral_xiHeatResolventKernelReal_eq_re_xiShiftedReciprocalMoment
    {y : ℝ} (hy : 0 < y) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), xiHeatResolventKernelReal y n t) =
      (n.factorial : ℝ) * (xiShiftedReciprocalMoment y n).re := by
  calc
    (∫ t in Ioi (0 : ℝ), xiHeatResolventKernelReal y n t) =
        ∫ t in Ioi (0 : ℝ), (xiHeatResolventKernel y n t).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      exact (xiHeatResolventKernel_re y n t).symm
    _ = ((∫ t in Ioi (0 : ℝ), xiHeatResolventKernel y n t) : ℂ).re :=
      integral_re (integrableOn_xiHeatResolventKernel hy n)
    _ = (n.factorial : ℝ) * (xiShiftedReciprocalMoment y n).re := by
      rw [integral_xiHeatResolventKernel_eq_xiShiftedReciprocalMoment hy n]
      simp

/-- Consecutive factorial primitive of a finite coefficient vector.  Incrementing `r` takes the
unique primitive with vanishing jet at the origin. -/
def xiFactorialVolterraPolynomial
    (r : ℕ) {N : ℕ} (c : Fin N → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin N, (c j / ((r + (j : ℕ)).factorial : ℝ)) * t ^ (r + (j : ℕ))

/-- Xi heat source tested against one rung of the factorial-Volterra flag. -/
def xiFactorialVolterraHeatKernel
    (y : ℝ) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) (t : ℝ) : ℝ :=
  xiFactorialVolterraPolynomial r c t *
    Real.exp (-(y * t)) * xiGaussianHeatMomentReal 0 t

theorem hasDerivAt_xiFactorialVolterraPolynomial_succ
    (r : ℕ) {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    HasDerivAt (xiFactorialVolterraPolynomial (r + 1) c)
      (xiFactorialVolterraPolynomial r c t) t := by
  unfold xiFactorialVolterraPolynomial
  apply HasDerivAt.fun_sum
  intro j _
  let k := r + (j : ℕ)
  have hk : (r + 1) + (j : ℕ) = k + 1 := by omega
  rw [hk]
  have hcoeff :
      (c j / (((k + 1).factorial : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ)) =
        c j / ((k.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp [Nat.factorial_ne_zero]
  have hderiv : HasDerivAt
      (fun x : ℝ => (c j / (((k + 1).factorial : ℕ) : ℝ)) * x ^ (k + 1))
      ((c j / (((k + 1).factorial : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ)) *
        t ^ k) t := by
    simpa [Nat.succ_eq_add_one, mul_assoc] using
      (hasDerivAt_pow (k + 1) t).const_mul
        (c j / (((k + 1).factorial : ℕ) : ℝ))
  simpa only [hcoeff] using hderiv

theorem integrableOn_xiFactorialVolterraHeatKernel
    {y : ℝ} (hy : 0 < y) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    IntegrableOn (xiFactorialVolterraHeatKernel y r c) (Ioi (0 : ℝ)) := by
  have hsum : IntegrableOn (fun t => ∑ j : Fin N,
      (c j / ((r + (j : ℕ)).factorial : ℝ)) *
        xiHeatResolventKernelReal y (r + (j : ℕ)) t) (Ioi (0 : ℝ)) :=
    integrable_finsetSum Finset.univ fun j _ =>
      (integrableOn_xiHeatResolventKernelReal hy
        (r + (j : ℕ))).const_mul _
  refine hsum.congr ?_
  filter_upwards with t
  simp only [xiFactorialVolterraHeatKernel, xiFactorialVolterraPolynomial,
    xiHeatResolventKernelReal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every factorial-Volterra heat rung integrates to the matching consecutive shifted reciprocal
moment pairing. -/
theorem integral_xiFactorialVolterraHeatKernel_eq_momentPairing
    {y : ℝ} (hy : 0 < y) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    (∫ t in Ioi (0 : ℝ), xiFactorialVolterraHeatKernel y r c t) =
      ∑ j : Fin N, c j * (xiShiftedReciprocalMoment y (r + (j : ℕ))).re := by
  have hterm (j : Fin N) : IntegrableOn (fun t =>
      (c j / ((r + (j : ℕ)).factorial : ℝ)) *
        xiHeatResolventKernelReal y (r + (j : ℕ)) t) (Ioi (0 : ℝ)) :=
    (integrableOn_xiHeatResolventKernelReal hy (r + (j : ℕ))).const_mul _
  calc
    (∫ t in Ioi (0 : ℝ), xiFactorialVolterraHeatKernel y r c t) =
        ∫ t in Ioi (0 : ℝ), ∑ j : Fin N,
          (c j / ((r + (j : ℕ)).factorial : ℝ)) *
            xiHeatResolventKernelReal y (r + (j : ℕ)) t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      simp only [xiFactorialVolterraHeatKernel, xiFactorialVolterraPolynomial,
        xiHeatResolventKernelReal, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j : Fin N, ∫ t in Ioi (0 : ℝ),
          (c j / ((r + (j : ℕ)).factorial : ℝ)) *
            xiHeatResolventKernelReal y (r + (j : ℕ)) t :=
      integral_finsetSum Finset.univ fun j _ => hterm j
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul,
        integral_xiHeatResolventKernelReal_eq_re_xiShiftedReciprocalMoment
          hy (r + (j : ℕ))]
      field_simp [Nat.factorial_ne_zero]

/-- A Hankel null vector annihilates every rung of its complete factorial-Volterra heat flag. -/
theorem integral_xiFactorialVolterraHeatKernel_eq_zero_of_kernel
    {y : ℝ} (hy : 0 < y) {N : ℕ} (c : Fin N → ℝ)
    (hc : xiShiftedMomentHankelMatrix y N *ᵥ c = 0) (i : Fin N) :
    (∫ t in Ioi (0 : ℝ),
      xiFactorialVolterraHeatKernel y (i : ℕ) c t) = 0 := by
  rw [integral_xiFactorialVolterraHeatKernel_eq_momentPairing hy]
  have hi := congrFun hc i
  calc
    (∑ j : Fin N, c j *
        (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ))).re) =
        ∑ j : Fin N,
          (xiShiftedReciprocalMoment y ((i : ℕ) + (j : ℕ))).re * c j := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by
      simpa [xiShiftedMomentHankelMatrix,
        GaloisForLFunctions.HTGeometry.finiteHankelMatrix, Matrix.mulVec,
        dotProduct] using hi

/-- Factorial-normalized heat-resolvent kernel attached to the first moment column omitted from an
`n x n` shifted-Xi Hankel block. -/
def xiShiftedHankelBoundaryHeatKernel
    (y : ℝ) (n : ℕ) (c : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin n,
    (c j / ((n + (j : ℕ)).factorial : ℝ)) *
      xiHeatResolventKernelReal y (n + (j : ℕ)) t

/-- Factorial-normalized polynomial selected by the current Hankel null vector. -/
def xiShiftedHankelBoundaryHeatPolynomial
    (n : ℕ) (c : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin n, (c j / ((n + (j : ℕ)).factorial : ℝ)) * t ^ (n + (j : ℕ))

/-- The boundary kernel is the ordinary Xi heat trace times a Laplace weight and one explicit
moving-degree polynomial. -/
theorem xiShiftedHankelBoundaryHeatKernel_eq_polynomial_mul_heat
    (y : ℝ) (n : ℕ) (c : Fin n → ℝ) (t : ℝ) :
    xiShiftedHankelBoundaryHeatKernel y n c t =
      xiShiftedHankelBoundaryHeatPolynomial n c t *
        Real.exp (-(y * t)) * xiGaussianHeatMomentReal 0 t := by
  simp only [xiShiftedHankelBoundaryHeatKernel,
    xiShiftedHankelBoundaryHeatPolynomial, xiHeatResolventKernelReal]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integrableOn_xiShiftedHankelBoundaryHeatKernel
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin n → ℝ) :
    IntegrableOn (xiShiftedHankelBoundaryHeatKernel y n c) (Ioi (0 : ℝ)) := by
  unfold xiShiftedHankelBoundaryHeatKernel
  exact integrable_finsetSum Finset.univ fun j _ =>
    (integrableOn_xiHeatResolventKernelReal hy (n + (j : ℕ))).const_mul _

theorem integral_factorialNormalized_xiHeatResolventKernelReal
    {y : ℝ} (hy : 0 < y) (k : ℕ) (a : ℝ) :
    (∫ t in Ioi (0 : ℝ),
      (a / (k.factorial : ℝ)) * xiHeatResolventKernelReal y k t) =
      a * (xiShiftedReciprocalMoment y k).re := by
  rw [integral_const_mul,
    integral_xiHeatResolventKernelReal_eq_re_xiShiftedReciprocalMoment hy k]
  field_simp [Nat.factorial_ne_zero]

/-- **Boundary heat--resolvent bridge.** The sole extension coordinate governing first crossing of
the shifted-Xi Hankel cone is one exact signed integral against the ordinary Xi Gaussian heat
trace.  The moving polynomial is canonically factorial-normalized by the Gamma transform. -/
theorem integral_xiShiftedHankelBoundaryHeatKernel_eq_firstOmittedCoupling
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin n → ℝ) :
    (∫ t in Ioi (0 : ℝ), xiShiftedHankelBoundaryHeatKernel y n c t) =
      xiShiftedHankelFirstOmittedCoupling y n c := by
  change (∫ t in Ioi (0 : ℝ), ∑ j : Fin n,
      (c j / ((n + (j : ℕ)).factorial : ℝ)) *
        xiHeatResolventKernelReal y (n + (j : ℕ)) t) = _
  rw [integral_finsetSum Finset.univ (fun (j : Fin n) _ =>
    (integrableOn_xiHeatResolventKernelReal hy (n + (j : ℕ))).const_mul _)]
  rw [xiShiftedHankelFirstOmittedCoupling,
    GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_factorialNormalized_xiHeatResolventKernelReal
    hy (n + (j : ℕ)) (c j)

/-- At a singular shifted-Xi Hankel face, its null quadratic has derivative equal to a universal
positive transport factor times the exact boundary heat-resolvent integral. -/
theorem hasDerivAt_xiShiftedMomentHankelQuadratic_of_kernel_succ_heatIntegral
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0) :
    HasDerivAt (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c)
      (-(2 * (n : ℝ) + 1) * c (Fin.last n) *
        (∫ t in Ioi (0 : ℝ),
          xiShiftedHankelBoundaryHeatKernel y (n + 1) c t)) y := by
  rw [integral_xiShiftedHankelBoundaryHeatKernel_eq_firstOmittedCoupling hy]
  exact hasDerivAt_xiShiftedMomentHankelQuadratic_of_kernel_succ hy n c hc

end
end RHTower
