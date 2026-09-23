import GaloisForLFunctions.HTGeometry.NonlocalSourceChiralPolarization
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantTraceRecovery
import GaloisForLFunctions.HTGeometry.PolydiscAnalytic

/-!
# Quadratic-jet obstruction to positive Hermitian dilation

For a Hilbert--Schmidt source kernel `K`, its ordinary Hermitian dilation

`D(K) = [[0, K], [Kᴴ, 0]]`

has real spectrum, but its quadratic determinant trace is the positive Gram mass
`tr(D(K)²) = 2 ‖K‖²_HS`.  The original holomorphic trace only satisfies
`|tr(K²)| ≤ ‖K‖²_HS`.  Therefore their Hilbert--Carleman determinants have a sharp quadratic
Taylor-jet separation of at least `‖K‖²_HS / 2`; equality of the full determinants is possible
exactly for the zero source.

This identifies the representation failure in positive chiralization: a divisor-faithful
replacement must preserve the signed holomorphic square trace rather than replace it by Gram
energy.
-/

open Filter Metric

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt

noncomputable section

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
private theorem hasDerivAt_resolventTrace_term
    (K : ι × ι → ℂ) (n : ℕ) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => w ^ (n + 1) * (∑' i, hsPow K (n + 1) (i, i)))
      (((n + 1 : ℕ) : ℂ) * z ^ n * (∑' i, hsPow K (n + 1) (i, i))) z := by
  simpa only [Nat.add_sub_cancel, mul_assoc] using
    (hasDerivAt_pow (n + 1) z).mul_const (∑' i, hsPow K (n + 1) (i, i))

omit [DecidableEq ι] in
/-- The derivative at the origin of the regularized resolvent trace is the holomorphic square
trace. -/
theorem hasDerivAt_resolventTrace_zero {K : ι × ι → ℂ} (hK : IsHS K) :
    HasDerivAt (resolventTrace K) (∑' i, hsPow K 1 (i, i)) 0 := by
  let r : ℝ := detRadius K
  have hr0 : 0 < r := detRadius_pos K
  have hr : r * hsNorm K < 1 := detRadius_mul_hsNorm_lt K
  have hx0 : 0 ≤ r * hsNorm K :=
    mul_nonneg hr0.le (hsNorm_nonneg K)
  have hgeom : Summable (fun n : ℕ => ((n : ℝ) + 1) * (r * hsNorm K) ^ n) := by
    convert summable_succ_pow_mul_geometric 1 hx0 hr using 1
    funext n
    norm_num
  have hu : Summable (fun n : ℕ =>
      (hsNorm K) ^ (2 : ℕ) * (((n : ℝ) + 1) * (r * hsNorm K) ^ n)) :=
    hgeom.mul_left _
  have hderiv := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected
    (fun n z _ => hasDerivAt_resolventTrace_term K n z) (fun n z hz => by
      have hzr : ‖z‖ < r := by rwa [mem_ball_zero_iff] at hz
      rw [norm_mul, norm_mul, norm_natCast, norm_pow]
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have htrace := hsTrace_hsPow_norm_le hK n
      have hpow : ‖z‖ ^ n ≤ r ^ n := by gcongr
      calc
        ((n : ℝ) + 1) * ‖z‖ ^ n * ‖∑' i, hsPow K (n + 1) (i, i)‖
            ≤ ((n : ℝ) + 1) * r ^ n * hsNorm K ^ (n + 2) := by
              gcongr
        _ = hsNorm K ^ (2 : ℕ) * (((n : ℝ) + 1) * (r * hsNorm K) ^ n) := by
              rw [mul_pow]
              ring)
    (show (0 : ℂ) ∈ ball 0 r by simpa using hr0)
    (resolventTrace_summable hK 0 (by simp))
    (show (0 : ℂ) ∈ ball 0 r by simpa using hr0)
  have hsum :
      (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) * (0 : ℂ) ^ n *
        (∑' i, hsPow K (n + 1) (i, i)))) =
      ∑' i, hsPow K 1 (i, i) := by
    rw [tsum_eq_single 0]
    · norm_num
    · intro n hn
      simp [zero_pow hn]
  change HasDerivAt
    (fun z => ∑' n : ℕ, z ^ (n + 1) * (∑' i, hsPow K (n + 1) (i, i)))
    (∑' i, hsPow K 1 (i, i)) 0
  simpa only [hsum] using hderiv

omit [DecidableEq ι] in
/-- The quadratic coefficient of `det₂(1-zK)` is `-tr(K²)/2`. -/
theorem detCoeff_two_eq_neg_half_traceSquare {K : ι × ι → ℂ} (hK : IsHS K) :
    detCoeff K 2 = -(∑' i, hsPow K 1 (i, i)) / 2 := by
  let r : ℝ := detRadius K
  have hr0 : 0 < r := detRadius_pos K
  have hr : r * hsNorm K < 1 := detRadius_mul_hsNorm_lt K
  have hzero : resolventTrace K 0 = 0 := by
    simp [resolventTrace]
  have hdet0 : fredholmDet K 0 = 1 := by
    simp [fredholmDet, fredholmExp]
  have hdet : HasDerivAt (fredholmDet K) 0 0 := by
    simpa [hzero, hdet0] using hasDerivAt_fredholmDet hK r hr 0
      (show (0 : ℂ) ∈ ball 0 r by simpa using hr0)
  have hres := hasDerivAt_resolventTrace_zero hK
  have hprod : HasDerivAt
      (fredholmDet K * (-resolventTrace K))
      (-(∑' i, hsPow K 1 (i, i))) 0 := by
    simpa only [hzero, hdet0, neg_zero, mul_zero, zero_mul, one_mul, zero_add] using
      hdet.mul hres.neg
  have hlocal :
      deriv (fredholmDet K) =ᶠ[nhds (0 : ℂ)]
        fredholmDet K * (-resolventTrace K) := by
    filter_upwards [isOpen_ball.mem_nhds
      (show (0 : ℂ) ∈ ball 0 r by simpa using hr0)] with z hz
    exact (hasDerivAt_fredholmDet hK r hr z hz).deriv
  have hsecond : deriv (deriv (fredholmDet K)) 0 =
      -(∑' i, hsPow K 1 (i, i)) := by
    rw [hlocal.deriv_eq]
    exact hprod.deriv
  rw [detCoeff, taylorCoeff]
  norm_num [iteratedDeriv_succ, hsecond]
  ring

/-- The Taylor coefficients of the entire completion agree with the local determinant
coefficients. -/
theorem taylorCoeff_entireDet2_eq_detCoeff {K : ι × ι → ℂ} (hK : IsHS K) (n : ℕ) :
    taylorCoeff (entireDet2 K) n = detCoeff K n := by
  obtain ⟨-, r, hr, -, heq⟩ := isRegularizedDet_entireDet2 hK
  have hev : entireDet2 K =ᶠ[nhds (0 : ℂ)] fredholmDet K := by
    filter_upwards [isOpen_ball.mem_nhds
      (show (0 : ℂ) ∈ ball 0 r by simpa using hr)] with z hz
    exact heq z hz
  rw [taylorCoeff, detCoeff, taylorCoeff,
    (GaloisForLFunctions.eventuallyEq_iteratedDeriv hev n).eq_of_nhds]

theorem taylorCoeff_entireDet2_two {K : ι × ι → ℂ} (hK : IsHS K) :
    taylorCoeff (entireDet2 K) 2 = -(∑' i, hsPow K 1 (i, i)) / 2 := by
  rw [taylorCoeff_entireDet2_eq_detCoeff hK,
    detCoeff_two_eq_neg_half_traceSquare hK]

omit [DecidableEq ι] in
/-- Cauchy--Schwarz gives the universal one-copy energy ceiling for the holomorphic square trace. -/
theorem norm_traceSquare_le_hsNormSq {K : ι × ι → ℂ} (hK : IsHS K) :
    ‖∑' i, hsPow K 1 (i, i)‖ ≤ hsNormSq K := by
  have h := hsTrace_hsPow_norm_le hK 0
  norm_num at h
  rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg K)] at h
  exact h

omit [DecidableEq ι] in
/-- The infinite source Hermitian dilation is self-adjoint at kernel level. -/
theorem hsAdjoint_sourceHermitianDilationKernel (K : ι × ι → ℂ) :
    hsAdjoint (sourceHermitianDilationKernel K) =
      sourceHermitianDilationKernel K := by
  funext p
  rcases p with ⟨i, j⟩
  rcases i with i | i <;> rcases j with j | j <;>
    simp [hsAdjoint, sourceHermitianDilationKernel]

omit [DecidableEq ι] in
/-- Hermitian dilation replaces the source square trace by exactly twice its positive energy. -/
theorem traceSquare_sourceHermitianDilationKernel {K : ι × ι → ℂ} (hK : IsHS K) :
    (∑' q, hsPow (sourceHermitianDilationKernel K) 1 (q, q)) =
      ((2 * hsNormSq K : ℝ) : ℂ) := by
  let D := sourceHermitianDilationKernel K
  have hD : IsHS D := isHS_sourceHermitianDilationKernel hK
  calc
    (∑' q, hsPow D 1 (q, q)) = hsInner (hsAdjoint D) (hsPow D 0) := by
      simpa using hsTrace_hsPow_succ hD 0
    _ = hsInner D D := by
      rw [hsAdjoint_sourceHermitianDilationKernel]
      rfl
    _ = (hsNormSq D : ℂ) := hsInner_self D
    _ = ((2 * hsNormSq K : ℝ) : ℂ) := by
      rw [hsNormSq_sourceHermitianDilationKernel hK]

omit [DecidableEq ι] in
/-- Sharp trace-coordinate gap: positive dilation lies at least one source energy away from the
holomorphic square trace. -/
theorem hsNormSq_le_norm_dilationTraceGap {K : ι × ι → ℂ} (hK : IsHS K) :
    hsNormSq K ≤
      ‖((2 * hsNormSq K : ℝ) : ℂ) - (∑' i, hsPow K 1 (i, i))‖ := by
  let a : ℂ := ((2 * hsNormSq K : ℝ) : ℂ)
  let b : ℂ := ∑' i, hsPow K 1 (i, i)
  have hb : ‖b‖ ≤ hsNormSq K := norm_traceSquare_le_hsNormSq hK
  have ha : ‖a‖ = 2 * hsNormSq K := by
    dsimp [a]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by norm_num) (hsNormSq_nonneg K))]
  have htri : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    have haeq : a = (a - b) + b := by ring
    calc
      ‖a‖ = ‖(a - b) + b‖ := congrArg norm haeq
      _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le (a - b) b
  dsimp only [a, b] at htri ⊢
  rw [ha] at htri
  linarith

/-- Positive dilation pays a sharp, source-sized quadratic Taylor-jet floor. -/
theorem half_hsNormSq_le_norm_taylorCoeff_dilation_sub {K : ι × ι → ℂ} (hK : IsHS K) :
    hsNormSq K / 2 ≤
      ‖taylorCoeff (entireDet2 (sourceHermitianDilationKernel K)) 2 -
        taylorCoeff (entireDet2 K) 2‖ := by
  have hgap := hsNormSq_le_norm_dilationTraceGap hK
  rw [taylorCoeff_entireDet2_two (isHS_sourceHermitianDilationKernel hK),
    taylorCoeff_entireDet2_two hK,
    traceSquare_sourceHermitianDilationKernel hK]
  have hnorm :
      ‖(-((2 * hsNormSq K : ℝ) : ℂ) / 2) -
          (-(∑' i, hsPow K 1 (i, i)) / 2)‖ =
        ‖((2 * hsNormSq K : ℝ) : ℂ) - (∑' i, hsPow K 1 (i, i))‖ / 2 := by
    rw [show
      (-((2 * hsNormSq K : ℝ) : ℂ) / 2) -
          (-(∑' i, hsPow K 1 (i, i)) / 2) =
        -((((2 * hsNormSq K : ℝ) : ℂ) -
          (∑' i, hsPow K 1 (i, i))) / 2) by ring,
      norm_neg, norm_div]
    norm_num
  rw [hnorm]
  linarith

/-- The entire determinant of a zero kernel is the constant one, independently of index type. -/
theorem entireDet2_zero_kernel {κ : Type*} [DecidableEq κ] :
    entireDet2 (0 : κ × κ → ℂ) = fun _ => 1 := by
  have h0 : IsHS (0 : κ × κ → ℂ) := isHS_zero
  have hpow : ∀ n : ℕ, hsPow (0 : κ × κ → ℂ) n = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [hsPow, ih]
        funext p
        simp [hsComp]
  obtain ⟨-, r, hr, -, heq⟩ := isRegularizedDet_entireDet2 h0
  have hev : entireDet2 (0 : κ × κ → ℂ) =ᶠ[nhds (0 : ℂ)] fun _ => 1 := by
    filter_upwards [isOpen_ball.mem_nhds
      (show (0 : ℂ) ∈ ball 0 r by simpa using hr)] with z hz
    rw [heq z hz]
    simp [fredholmDet, fredholmExp, hpow]
  have hA : AnalyticOnNhd ℂ (entireDet2 (0 : κ × κ → ℂ)) Set.univ :=
    (differentiable_entireDet2 h0).differentiableOn.analyticOnNhd isOpen_univ
  have h1 : Differentiable ℂ (fun _ : ℂ => (1 : ℂ)) := differentiable_const (c := 1)
  have hB : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) Set.univ :=
    h1.differentiableOn.analyticOnNhd isOpen_univ
  funext z
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_univ
    (Set.mem_univ (0 : ℂ)) hev (Set.mem_univ z)

/-- Ordinary Hermitian dilation preserves its source determinant exactly only for the zero source. -/
theorem entireDet2_sourceHermitianDilationKernel_eq_iff {K : ι × ι → ℂ} (hK : IsHS K) :
    entireDet2 (sourceHermitianDilationKernel K) = entireDet2 K ↔ K = 0 := by
  have hD := isHS_sourceHermitianDilationKernel hK
  constructor
  · intro heq
    have hcoeff := congrArg (fun f : ℂ → ℂ => taylorCoeff f 2) heq
    rw [taylorCoeff_entireDet2_two hD,
      taylorCoeff_entireDet2_two hK,
      traceSquare_sourceHermitianDilationKernel hK] at hcoeff
    have htrace : (∑' i, hsPow K 1 (i, i)) = ((2 * hsNormSq K : ℝ) : ℂ) := by
      linear_combination 2 * hcoeff
    have hbound := norm_traceSquare_le_hsNormSq hK
    rw [htrace, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg] at hbound
    · have hz : hsNormSq K = 0 := by
        nlinarith [hsNormSq_nonneg K]
      exact (hsNormSq_eq_zero_iff hK).mp hz
    · exact mul_nonneg (by norm_num) (hsNormSq_nonneg K)
  · rintro rfl
    have hzero : sourceHermitianDilationKernel (0 : ι × ι → ℂ) = 0 := by
      funext p
      rcases p with ⟨i, j⟩
      rcases i with i | i <;> rcases j with j | j <;>
        simp [sourceHermitianDilationKernel]
    rw [hzero, entireDet2_zero_kernel, entireDet2_zero_kernel]

end

end GaloisForLFunctions.HTGeometry
