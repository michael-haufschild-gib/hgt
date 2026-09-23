import GaloisForLFunctions.RHTower.XiWeilPositivityBand
import GaloisForLFunctions.RHTower.XiSchwartzMetricSupport
import GaloisForLFunctions.RHTower.XiDivisorHilbertCarrier

/-!
# The divisor Hilbert space carrying the Weil form

A test function enters the Weil polarization only through its values on the
multiplicity-exact divisor, and the genus-one bound places the regularized Cauchy
kernels inside `ℓ²` of the divisor: their restrictions are absolutely summable,
hence bounded, hence square-summable.

Conjugation of the centered coordinate permutes the divisor, so on that space the
Weil pairing is

`Q a = ∑' q, a q * conj (a (lineConj q))`,

which the arithmetic–geometric bound `|xy| ≤ (|x|² + |y|²)/2` shows is absolutely
convergent for every `ℓ²` sequence.  Boundedness of this form is what allows a
value at one test function to be transported to any test function approximating
it — the mechanism by which a detection performed inside the critical strip is
carried out to base points lying outside it.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## §1 Kernels restrict into `ℓ²` -/

/-- The regularized Cauchy kernel restricted to the divisor is absolutely
summable — this is the genus-one convergence of the relative resolvent trace. -/
theorem summable_norm_kernel_restriction {z : ℂ} (hz : XiC z ≠ 0) :
    Summable (fun q : XiZeroCopy =>
      ‖xiCauchyRegularizedKernel z (xiSpectralPoint q)‖) :=
  summable_norm_iff.mpr (summable_xiRelativeResolventTerm hz)

/-- An absolutely summable family of complex numbers is square-summable. -/
theorem summable_sq_of_summable_norm {f : XiZeroCopy → ℂ}
    (h : Summable (fun q => ‖f q‖)) :
    Summable (fun q => ‖f q‖ ^ (2 : ℝ)) := by
  set M := ∑' q : XiZeroCopy, ‖f q‖ with hM
  have hbound : ∀ q, ‖f q‖ ≤ M :=
    fun q => h.le_tsum q (fun j _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    (h.mul_left M)
  have hpow : ‖f q‖ ^ (2 : ℝ) = ‖f q‖ * ‖f q‖ := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hpow]
  exact mul_le_mul_of_nonneg_right (hbound q) (norm_nonneg _)

/-- **Kernels live in the divisor Hilbert space.** -/
theorem memℓp_kernel_restriction {z : ℂ} (hz : XiC z ≠ 0) :
    Memℓp (fun q : XiZeroCopy =>
      xiCauchyRegularizedKernel z (xiSpectralPoint q)) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  exact summable_sq_of_summable_norm (summable_norm_kernel_restriction hz)

/-- The kernel of a base point as a vector of the divisor Hilbert space. -/
def xiKernelVec {z : ℂ} (hz : XiC z ≠ 0) : XiDivisorL2 :=
  ⟨fun q => xiCauchyRegularizedKernel z (xiSpectralPoint q),
    memℓp_kernel_restriction hz⟩

@[simp] theorem xiKernelVec_apply {z : ℂ} (hz : XiC z ≠ 0) (q : XiZeroCopy) :
    xiKernelVec hz q = xiCauchyRegularizedKernel z (xiSpectralPoint q) := rfl

/-! ## §2 The Weil form on the divisor Hilbert space -/

/-- Square-summability transfers along the conjugation involution of the
divisor. -/
theorem summable_sq_lineConj (a : XiDivisorL2) :
    Summable (fun q : XiZeroCopy =>
      ‖a (xiZeroCopyLineConjEquiv q)‖ ^ (2 : ℝ)) := by
  have hsum : Summable (fun q : XiZeroCopy => ‖a q‖ ^ (2 : ℝ)) := by
    have h := lp.memℓp a
    rwa [memℓp_gen_iff (by norm_num : (0:ℝ) < (2:ENNReal).toReal)] at h
  exact (Equiv.summable_iff xiZeroCopyLineConjEquiv).mpr hsum

/-- The Weil summand is absolutely summable on the divisor Hilbert space, by the
arithmetic–geometric bound against the two square-summable families. -/
theorem summable_weilL2Summand (a : XiDivisorL2) :
    Summable (fun q : XiZeroCopy =>
      a q * (starRingEnd ℂ) (a (xiZeroCopyLineConjEquiv q))) := by
  have h1 : Summable (fun q : XiZeroCopy => ‖a q‖ ^ (2 : ℝ)) := by
    have h := lp.memℓp a
    rwa [memℓp_gen_iff (by norm_num : (0:ℝ) < (2:ENNReal).toReal)] at h
  have h2 := summable_sq_lineConj a
  refine summable_norm_iff.mp ?_
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    ((h1.add h2).mul_left (1 / 2))
  rw [norm_mul, RCLike.norm_conj]
  have hxy : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      x * y ≤ 1 / 2 * (x ^ (2 : ℝ) + y ^ (2 : ℝ)) := by
    intro x y hx hy
    have hx2 : x ^ (2 : ℝ) = x * x := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    have hy2 : y ^ (2 : ℝ) = y * y := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [hx2, hy2]
    nlinarith [sq_nonneg (x - y)]
  exact hxy _ _ (norm_nonneg _) (norm_nonneg _)

/-- **The Weil form on the divisor Hilbert space.**  Conjugation permutes the
divisor, so pairing a sequence with its conjugate-reindexed conjugate is the
Weil polarization written intrinsically. -/
def xiWeilL2Form (a : XiDivisorL2) : ℂ :=
  ∑' q : XiZeroCopy, a q * (starRingEnd ℂ) (a (xiZeroCopyLineConjEquiv q))

/-- **The form computes the Weil polarization of a Cauchy kernel.** -/
theorem xiWeilL2Form_kernelVec {z : ℂ} (hz : XiC z ≠ 0) :
    xiWeilL2Form (xiKernelVec hz) =
      xiWeilPolarization (xiCauchyRegularizedKernel z)
        (xiCauchyRegularizedKernel z) := by
  rw [xiWeilL2Form, xiWeilPolarization]
  refine tsum_congr fun q => ?_
  rw [xiKernelVec_apply, xiKernelVec_apply, xiWeilSharp,
    xiSpectralPoint_lineConj]

/-! ## §3 Continuity of the form -/

/-- Reindexing an `ℓ²` sequence along the conjugation involution of the
divisor. -/
def xiLineConjVec (a : XiDivisorL2) : XiDivisorL2 :=
  ⟨fun q => a (xiZeroCopyLineConjEquiv q),
    (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mpr
      (summable_sq_lineConj a)⟩

@[simp] theorem xiLineConjVec_apply (a : XiDivisorL2) (q : XiZeroCopy) :
    xiLineConjVec a q = a (xiZeroCopyLineConjEquiv q) := rfl

/-- Reindexing is an isometry: the divisor conjugation is a bijection. -/
theorem xiLineConjVec_norm (a : XiDivisorL2) : ‖xiLineConjVec a‖ = ‖a‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  congr 1
  exact xiZeroCopyLineConjEquiv.tsum_eq
    (fun q => ‖a q‖ ^ (2 : ENNReal).toReal)

theorem xiLineConjVec_sub (a b : XiDivisorL2) :
    xiLineConjVec (a - b) = xiLineConjVec a - xiLineConjVec b := by
  ext q
  show (a - b) (xiZeroCopyLineConjEquiv q) =
    (xiLineConjVec a - xiLineConjVec b) q
  rw [lp.coeFn_sub, lp.coeFn_sub]
  rfl

/-- Hölder on the divisor Hilbert space. -/
theorem tsum_norm_mul_le (a b : XiDivisorL2) :
    ∑' q : XiZeroCopy, ‖a q‖ * ‖b q‖ ≤ ‖a‖ * ‖b‖ :=
  (lp.tsum_mul_le_mul_norm
    (by simpa using Real.HolderConjugate.two_two) a b).2

theorem summable_norm_mul (a b : XiDivisorL2) :
    Summable (fun q : XiZeroCopy => ‖a q‖ * ‖b q‖) :=
  (lp.tsum_mul_le_mul_norm
    (by simpa using Real.HolderConjugate.two_two) a b).1

/-- **The Weil form is Lipschitz on bounded sets.**  This is what transports a
value of the form from one test function to any test function approximating it
in the divisor Hilbert space. -/
theorem xiWeilL2Form_sub_norm_le (a b : XiDivisorL2) :
    ‖xiWeilL2Form a - xiWeilL2Form b‖ ≤ ‖a - b‖ * ‖a‖ + ‖b‖ * ‖a - b‖ := by
  have hsa := summable_weilL2Summand a
  have hsb := summable_weilL2Summand b
  have hg : Summable (fun q : XiZeroCopy =>
      (a q - b q) * (starRingEnd ℂ) (a (xiZeroCopyLineConjEquiv q)) +
        b q * (starRingEnd ℂ)
          (a (xiZeroCopyLineConjEquiv q) - b (xiZeroCopyLineConjEquiv q))) := by
    apply (hsa.sub hsb).congr
    intro q
    rw [map_sub]
    ring
  have hsplit : xiWeilL2Form a - xiWeilL2Form b =
      ∑' q : XiZeroCopy,
        ((a q - b q) * (starRingEnd ℂ) (a (xiZeroCopyLineConjEquiv q)) +
          b q * (starRingEnd ℂ)
            (a (xiZeroCopyLineConjEquiv q) -
              b (xiZeroCopyLineConjEquiv q))) := by
    rw [xiWeilL2Form, xiWeilL2Form, ← hsa.tsum_sub hsb]
    refine tsum_congr fun q => ?_
    rw [map_sub]
    ring
  have hmaj : Summable (fun q : XiZeroCopy =>
      ‖(a - b) q‖ * ‖xiLineConjVec a q‖ +
        ‖b q‖ * ‖(xiLineConjVec a - xiLineConjVec b) q‖) :=
    (summable_norm_mul (a - b) (xiLineConjVec a)).add
      (summable_norm_mul b (xiLineConjVec a - xiLineConjVec b))
  have hpoint : ∀ q : XiZeroCopy,
      ‖(a q - b q) * (starRingEnd ℂ) (a (xiZeroCopyLineConjEquiv q)) +
        b q * (starRingEnd ℂ)
          (a (xiZeroCopyLineConjEquiv q) -
            b (xiZeroCopyLineConjEquiv q))‖ ≤
      ‖(a - b) q‖ * ‖xiLineConjVec a q‖ +
        ‖b q‖ * ‖(xiLineConjVec a - xiLineConjVec b) q‖ := by
    intro q
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
    have h1 : ‖a q - b q‖ = ‖(a - b) q‖ := by
      rw [lp.coeFn_sub]
      rfl
    have h2 : ‖a (xiZeroCopyLineConjEquiv q)‖ = ‖xiLineConjVec a q‖ := rfl
    have h3 : ‖a (xiZeroCopyLineConjEquiv q) -
        b (xiZeroCopyLineConjEquiv q)‖ =
        ‖(xiLineConjVec a - xiLineConjVec b) q‖ := by
      rw [lp.coeFn_sub]
      rfl
    rw [h1, h2, h3]
  rw [hsplit]
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_iff.mpr hg)) ?_
  refine le_trans
    (Summable.tsum_mono (summable_norm_iff.mpr hg) hmaj hpoint) ?_
  rw [Summable.tsum_add (summable_norm_mul (a - b) (xiLineConjVec a))
    (summable_norm_mul b (xiLineConjVec a - xiLineConjVec b))]
  have hb1 := tsum_norm_mul_le (a - b) (xiLineConjVec a)
  have hb2 := tsum_norm_mul_le b (xiLineConjVec a - xiLineConjVec b)
  rw [xiLineConjVec_norm] at hb1
  have hnorm : ‖xiLineConjVec a - xiLineConjVec b‖ = ‖a - b‖ := by
    rw [← xiLineConjVec_sub, xiLineConjVec_norm]
  rw [hnorm] at hb2
  linarith

/-! ## §4 Analyticity of the annihilator function -/

/-- The reciprocals of the centered divisor points form an `ℓ²` vector: this is
the genus-one bound. -/
def xiInvVec : XiDivisorL2 :=
  ⟨fun q => (xiSpectralPoint q)⁻¹,
    (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mpr (by
      refine xiSpectralPoint_inv_sq_summable.congr fun q => ?_
      have hpos : 0 < ‖xiSpectralPoint q‖ :=
        norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
      rw [norm_inv, show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      field_simp)⟩

@[simp] theorem xiInvVec_apply (q : XiZeroCopy) :
    xiInvVec q = (xiSpectralPoint q)⁻¹ := rfl

/-- **Uniform separation.**  If the centered zeta does not vanish on a ball,
every divisor copy stays at distance at least `r₀/2` from the half ball.  This
uses only continuity, not local finiteness of the divisor. -/
theorem half_le_norm_sub_of_ball {s : ℂ} {r₀ : ℝ}
    (hfree : ∀ y ∈ Metric.ball s r₀, XiC y ≠ 0)
    {z : ℂ} (hz : z ∈ Metric.ball s (r₀ / 2)) (q : XiZeroCopy) :
    r₀ / 2 ≤ ‖xiSpectralPoint q - z‖ := by
  by_contra hcon
  push Not at hcon
  have hzs : ‖z - s‖ < r₀ / 2 := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hz
  have hin : xiSpectralPoint q ∈ Metric.ball s r₀ := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖xiSpectralPoint q - s‖
        ≤ ‖xiSpectralPoint q - z‖ + ‖z - s‖ := by
          simpa using norm_sub_le_norm_sub_add_norm_sub
            (xiSpectralPoint q) z s
      _ < r₀ / 2 + r₀ / 2 := by linarith
      _ = r₀ := by ring
  exact hfree _ hin ((XiC_eq_zero_iff_exists_xiZeroCopy _).mpr ⟨q, rfl⟩)

/-- **Pointwise kernel bound on a divisor-free ball.**  If the centered zeta does
not vanish on a ball, every kernel with base point in the half-ball is dominated
there by a fixed multiple of the reciprocal divisor point. -/
theorem norm_kernel_le_of_ball {s : ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hfree : ∀ y ∈ Metric.ball s r₀, XiC y ≠ 0)
    {z : ℂ} (hz : z ∈ Metric.ball s (r₀ / 2)) (q : XiZeroCopy) :
    ‖xiCauchyRegularizedKernel z (xiSpectralPoint q)‖ ≤
      (2 * (‖s‖ + r₀) / r₀) * ‖(xiSpectralPoint q)⁻¹‖ := by
  have hpne : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hpnorm : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr hpne
  -- the divisor avoids the ball, so it is far from every point of the half-ball
  have hfar : r₀ / 2 ≤ ‖xiSpectralPoint q - z‖ :=
    half_le_norm_sub_of_ball hfree hz q
  have hznorm : ‖z‖ ≤ ‖s‖ + r₀ := by
    have hzs : ‖z - s‖ < r₀ / 2 := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hz
    calc ‖z‖ ≤ ‖z - s‖ + ‖s‖ := by simpa using norm_le_norm_sub_add _ _
      _ ≤ r₀ / 2 + ‖s‖ := by linarith
      _ ≤ ‖s‖ + r₀ := by linarith
  have hzne : xiSpectralPoint q ≠ z := by
    intro hcon
    rw [hcon, sub_self, norm_zero] at hfar
    linarith
  have hCpos : (0 : ℝ) < 2 * (‖s‖ + r₀) / r₀ := by
    have : (0 : ℝ) < ‖s‖ + r₀ := by
      have := norm_nonneg s
      linarith
    positivity
  rw [xiCauchyRegularizedKernel_eq_div hpne hzne, norm_div, norm_neg, norm_mul,
    norm_inv, div_le_iff₀ (mul_pos hpnorm
      (norm_pos_iff.mpr (sub_ne_zero.mpr hzne)))]
  have hsimp : (2 * (‖s‖ + r₀) / r₀) * ‖xiSpectralPoint q‖⁻¹ *
      (‖xiSpectralPoint q‖ * ‖xiSpectralPoint q - z‖) =
      (2 * (‖s‖ + r₀) / r₀) * ‖xiSpectralPoint q - z‖ := by
    field_simp
  rw [hsimp]
  have hstep : (2 * (‖s‖ + r₀) / r₀) * (r₀ / 2) ≤
      (2 * (‖s‖ + r₀) / r₀) * ‖xiSpectralPoint q - z‖ :=
    mul_le_mul_of_nonneg_left hfar (le_of_lt hCpos)
  have hval : (2 * (‖s‖ + r₀) / r₀) * (r₀ / 2) = ‖s‖ + r₀ := by
    field_simp
  rw [hval] at hstep
  linarith [hznorm, hstep]

/-- **The annihilator function is analytic off the divisor.**  For an `ℓ²`
sequence on the divisor, the superposition of kernels against it is
differentiable at every point where the centered zeta does not vanish: the
uniform separation dominates the terms by a summable majorant on a half ball,
which is exactly locally normal convergence. -/
theorem differentiableAt_annihilator (a : XiDivisorL2) {s : ℂ}
    (hs : XiC s ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => ∑' q : XiZeroCopy,
      (starRingEnd ℂ) (a q) *
        xiCauchyRegularizedKernel z (xiSpectralPoint q)) s := by
  have hcont : ContinuousAt XiC s :=
    (XiC_analytic s (Set.mem_univ s)).continuousAt
  obtain ⟨r₀, hr₀, hball⟩ :=
    Metric.eventually_nhds_iff.mp (hcont.eventually_ne hs)
  have hfree : ∀ y ∈ Metric.ball s r₀, XiC y ≠ 0 := by
    intro y hy
    exact hball (by rwa [Metric.mem_ball] at hy)
  set U : Set ℂ := Metric.ball s (r₀ / 2) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hsU : s ∈ U := Metric.mem_ball_self (by linarith)
  set C : ℝ := 2 * (‖s‖ + r₀) / r₀ with hC
  have hmaj : Summable (fun q : XiZeroCopy => C * (‖a q‖ * ‖xiInvVec q‖)) :=
    (summable_norm_mul a xiInvVec).mul_left C
  have hterm : ∀ q : XiZeroCopy, DifferentiableOn ℂ
      (fun z : ℂ => (starRingEnd ℂ) (a q) *
        xiCauchyRegularizedKernel z (xiSpectralPoint q)) U := by
    intro q
    apply DifferentiableOn.const_mul
    intro z hz
    have hne : xiSpectralPoint q - z ≠ 0 := by
      intro hcon
      have hsep := half_le_norm_sub_of_ball hfree hz q
      rw [hcon, norm_zero] at hsep
      linarith
    have hd : DifferentiableAt ℂ
        (fun z : ℂ => xiCauchyRegularizedKernel z (xiSpectralPoint q)) z := by
      unfold xiCauchyRegularizedKernel
      exact (differentiableAt_const _).sub
        (((differentiableAt_const _).sub differentiableAt_id).inv hne)
    exact hd.differentiableWithinAt
  have hbound : ∀ (q : XiZeroCopy) (w : ℂ), w ∈ U →
      ‖(starRingEnd ℂ) (a q) *
        xiCauchyRegularizedKernel w (xiSpectralPoint q)‖ ≤
        C * (‖a q‖ * ‖xiInvVec q‖) := by
    intro q w hw
    rw [norm_mul, RCLike.norm_conj]
    have hk := norm_kernel_le_of_ball hr₀ hfree hw q
    have hnn : 0 ≤ ‖a q‖ := norm_nonneg _
    calc ‖a q‖ * ‖xiCauchyRegularizedKernel w (xiSpectralPoint q)‖
        ≤ ‖a q‖ * (C * ‖xiInvVec q‖) :=
          mul_le_mul_of_nonneg_left hk hnn
      _ = C * (‖a q‖ * ‖xiInvVec q‖) := by ring
  have hdiff := differentiableOn_tsum_of_summable_norm hmaj hterm hUopen hbound
  exact hdiff.differentiableAt (hUopen.mem_nhds hsU)

/-! ## §5 The identity theorem on the divisor complement -/

noncomputable local instance xiWeilDivisorHilbertInst1 : Countable XiDivisorSupport :=
  Set.countable_univ_iff.mp xiDivisorSupport_univ_countable

noncomputable local instance xiWeilDivisorHilbertInst2 : Countable XiZeroCopy := inferInstance

/-- The zero set of the centered completed zeta is countable: it is the range of
the spectral-point map on a countable index. -/
theorem XiC_zeroSet_countable : {z : ℂ | XiC z = 0}.Countable := by
  apply (Set.countable_range xiSpectralPoint).mono
  intro z hz
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hz
  exact ⟨q, hq⟩

/-- The complement of the divisor is preconnected: removing a countable set from
the plane leaves a path-connected set. -/
theorem isPreconnected_XiC_ne_zero :
    IsPreconnected {z : ℂ | XiC z ≠ 0} := by
  have hpath : IsPathConnected {z : ℂ | XiC z = 0}ᶜ := by
    apply Set.Countable.isPathConnected_compl_of_one_lt_rank _ XiC_zeroSet_countable
    rw [Complex.rank_real_complex]
    norm_num
  have hset : {z : ℂ | XiC z = 0}ᶜ = {z : ℂ | XiC z ≠ 0} := rfl
  rw [hset] at hpath
  exact hpath.isConnected.isPreconnected

theorem isOpen_XiC_ne_zero : IsOpen {z : ℂ | XiC z ≠ 0} := by
  have hcont : Continuous XiC := continuousOn_univ.mp XiC_analytic.continuousOn
  exact isOpen_compl_singleton.preimage hcont

/-- The annihilator function is the inner product against the kernel vector. -/
theorem inner_kernelVec_eq (a : XiDivisorL2) {z : ℂ} (hz : XiC z ≠ 0) :
    (inner ℂ a (xiKernelVec hz) : ℂ) =
      ∑' q : XiZeroCopy, (starRingEnd ℂ) (a q) *
        xiCauchyRegularizedKernel z (xiSpectralPoint q) := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun q => ?_
  rw [xiKernelVec_apply]
  simp only [RCLike.inner_apply]
  ring

/-- **The identity theorem for the annihilator.**  If the annihilator vanishes on
a nonempty open set of admissible base points, it vanishes at every point off the
divisor: an analytic function on a preconnected domain that vanishes on an open
subset vanishes identically. -/
theorem annihilator_eq_zero_of_vanishing_open (a : XiDivisorL2) {Ω : Set ℂ}
    (hΩopen : IsOpen Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hΩsub : Ω ⊆ {z : ℂ | XiC z ≠ 0})
    (hvanish : ∀ z ∈ Ω, (∑' q : XiZeroCopy, (starRingEnd ℂ) (a q) *
      xiCauchyRegularizedKernel z (xiSpectralPoint q)) = 0)
    {w : ℂ} (hw : XiC w ≠ 0) :
    (∑' q : XiZeroCopy, (starRingEnd ℂ) (a q) *
      xiCauchyRegularizedKernel w (xiSpectralPoint q)) = 0 := by
  set φ : ℂ → ℂ := fun z => ∑' q : XiZeroCopy, (starRingEnd ℂ) (a q) *
    xiCauchyRegularizedKernel z (xiSpectralPoint q) with hφ
  have hdiff : DifferentiableOn ℂ φ {z : ℂ | XiC z ≠ 0} := by
    intro z hz
    exact (differentiableAt_annihilator a hz).differentiableWithinAt
  have han : AnalyticOnNhd ℂ φ {z : ℂ | XiC z ≠ 0} :=
    hdiff.analyticOnNhd isOpen_XiC_ne_zero
  have hev : φ =ᶠ[nhds z₀] 0 := by
    filter_upwards [hΩopen.mem_nhds hz₀] with y hy
    exact hvanish y hy
  have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_XiC_ne_zero (hΩsub hz₀) hev
  exact heq hw

/-! ## §6 Outside-strip detection -/

/-- Base points off the closed strip avoid the divisor. -/
theorem XiC_ne_zero_of_half_le_abs_im {z : ℂ} (hz : 1 / 2 ≤ |z.im|) :
    XiC z ≠ 0 := by
  intro h
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp h
  have hlt := abs_im_xiSpectralPoint_lt_half q
  rw [hq] at hlt
  linarith

/-- The kernels based off the strip. -/
def outsideKernelSet : Set XiDivisorL2 :=
  {v | ∃ (z : ℂ) (hz : XiC z ≠ 0), 1 / 2 < |z.im| ∧ v = xiKernelVec hz}

/-- **Every kernel is approximated by outside-strip kernels.**  A vector
orthogonal to all outside-strip kernels is, by the identity theorem, orthogonal
to every kernel; so no kernel escapes the closed span. -/
theorem kernelVec_mem_closure_span {w : ℂ} (hw : XiC w ≠ 0) :
    xiKernelVec hw ∈
      (Submodule.span ℂ outsideKernelSet).topologicalClosure := by
  set S := (Submodule.span ℂ outsideKernelSet).topologicalClosure with hS
  have hmem : xiKernelVec hw ∈ Sᗮᗮ := by
    intro a ha
    have hvan : ∀ z ∈ {z : ℂ | 1 / 2 < |z.im|},
        (∑' q : XiZeroCopy, (starRingEnd ℂ) (a q) *
          xiCauchyRegularizedKernel z (xiSpectralPoint q)) = 0 := by
      intro z hz
      have hz' : XiC z ≠ 0 := XiC_ne_zero_of_half_le_abs_im (le_of_lt hz)
      have hin : xiKernelVec hz' ∈ S := by
        apply Submodule.le_topologicalClosure
        exact Submodule.subset_span ⟨z, hz', hz, rfl⟩
      have := ha _ hin
      rw [← inner_kernelVec_eq a hz']
      simpa [inner_conj_symm] using congrArg (starRingEnd ℂ) this
    have hopen : IsOpen {z : ℂ | 1 / 2 < |z.im|} :=
      isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)
    have hz₀ : (Complex.I : ℂ) ∈ {z : ℂ | 1 / 2 < |z.im| } := by
      simp
      norm_num
    have hsub : {z : ℂ | 1 / 2 < |z.im|} ⊆ {z : ℂ | XiC z ≠ 0} := by
      intro z hz
      exact XiC_ne_zero_of_half_le_abs_im (le_of_lt hz)
    have hkey := annihilator_eq_zero_of_vanishing_open a hopen hz₀ hsub hvan hw
    rw [inner_kernelVec_eq a hw] at *
    simpa [inner_conj_symm] using congrArg (starRingEnd ℂ) hkey
  rwa [Submodule.orthogonal_orthogonal] at hmem

/-- **Rung 0.**  An off-critical zero makes the Weil form negative at a FINITE
combination of kernels whose base points all lie off the critical strip. -/
theorem exists_neg_weilL2Form_outsideStrip {s : ℂ} (hs : s ∈ rightHalf)
    (hzero : xi s = 0) :
    ∃ F : XiDivisorL2, F ∈ Submodule.span ℂ outsideKernelSet ∧
      (xiWeilL2Form F).re < 0 := by
  obtain ⟨w, hXw, hXwc, hw0, hwim, hneg⟩ :=
    exists_neg_weilDiagonal_of_offAxis_zero
      (by
        set pt₁ : ℂ := -Complex.I * (s - 1 / 2) with hpt
        have hre : 1 / 2 < s.re := hs
        have hXpt : XiC pt₁ = 0 := by
          show xi ((1 / 2 : ℂ) + pt₁ * Complex.I) = 0
          have harg : (1 / 2 : ℂ) + pt₁ * Complex.I = s := by
            rw [hpt, show (-Complex.I * (s - 1 / 2) * Complex.I) =
              -(Complex.I * Complex.I) * (s - 1 / 2) from by ring,
              Complex.I_mul_I]
            ring
          rw [harg]
          exact hzero
        exact (by rw [XiC_conj', hXpt, map_zero] :
          XiC ((starRingEnd ℂ) pt₁) = 0))
      (by
        set pt₁ : ℂ := -Complex.I * (s - 1 / 2) with hpt
        have hre : 1 / 2 < s.re := hs
        have hval : pt₁.im = -(s.re - 1 / 2) := by
          rw [hpt]
          simp [Complex.mul_im, Complex.sub_re]
        have : ((starRingEnd ℂ) pt₁).im = s.re - 1 / 2 := by
          simp [hval]
        rw [this]
        linarith)
      (by
        set pt₁ : ℂ := -Complex.I * (s - 1 / 2) with hpt
        have hre : 1 / 2 < s.re := hs
        have hval : pt₁.im = -(s.re - 1 / 2) := by
          rw [hpt]
          simp [Complex.mul_im, Complex.sub_re]
        intro hcon
        have him0 : ((starRingEnd ℂ) pt₁).im = 0 := by rw [hcon]; simp
        rw [show ((starRingEnd ℂ) pt₁).im = -pt₁.im from by simp, hval] at him0
        simp at him0
        linarith)
  -- the kernel vector at `w` already has negative form
  have hQw : (xiWeilL2Form (xiKernelVec hXw)).re < 0 := by
    rw [xiWeilL2Form_kernelVec]
    exact hneg
  -- transport to the closed span, then to a finite combination
  set K := xiKernelVec hXw with hK
  set c : ℝ := -(xiWeilL2Form K).re with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  set M : ℝ := ‖K‖ with hM
  have hMnn : 0 ≤ M := norm_nonneg _
  set ε : ℝ := min 1 (c / (2 * M + 2)) with hε
  have hεpos : 0 < ε := lt_min one_pos (div_pos hcpos (by linarith))
  obtain ⟨F, hFmem, hFdist⟩ :=
    Metric.mem_closure_iff.mp (kernelVec_mem_closure_span hXw) ε hεpos
  refine ⟨F, hFmem, ?_⟩
  have hd : ‖F - K‖ < ε := by
    rw [dist_comm, dist_eq_norm] at hFdist
    exact hFdist
  have hFnorm : ‖F‖ ≤ M + 1 := by
    have h1 : ‖F‖ ≤ ‖F - K‖ + ‖K‖ := by
      simpa using norm_le_norm_sub_add _ _
    have h2 : ε ≤ 1 := min_le_left _ _
    linarith
  have hlip := xiWeilL2Form_sub_norm_le F K
  have hεle : ε ≤ c / (2 * M + 2) := min_le_right _ _
  have hbound : ‖xiWeilL2Form F - xiWeilL2Form K‖ < c := by
    have h1 : ‖F - K‖ * ‖F‖ + ‖K‖ * ‖F - K‖ ≤ ε * (M + 1) + M * ε := by
      have hA : ‖F - K‖ * ‖F‖ ≤ ε * (M + 1) :=
        mul_le_mul (le_of_lt hd) hFnorm (norm_nonneg _) (le_of_lt hεpos)
      have hB : ‖K‖ * ‖F - K‖ ≤ M * ε :=
        mul_le_mul_of_nonneg_left (le_of_lt hd) hMnn
      linarith
    have h2 : ε * (M + 1) + M * ε < c := by
      have hpos : (0 : ℝ) < 2 * M + 2 := by linarith
      have : ε * (2 * M + 1) < c := by
        calc ε * (2 * M + 1) ≤ (c / (2 * M + 2)) * (2 * M + 1) :=
              mul_le_mul_of_nonneg_right hεle (by linarith)
          _ < c := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
              nlinarith [hcpos]
      linarith
    linarith [hlip, h1, h2]
  have hre : (xiWeilL2Form F).re ≤ (xiWeilL2Form K).re +
      ‖xiWeilL2Form F - xiWeilL2Form K‖ := by
    have := Complex.re_le_norm (xiWeilL2Form F - xiWeilL2Form K)
    rw [Complex.sub_re] at this
    linarith
  rw [hc] at hcpos
  linarith [hre, hbound]

/-! ## §7 The criterion -/

/-- A divisor sequence that depends only on the spectral point.  Test functions
have this property; general `ℓ²` sequences do not. -/
def FactorsThroughSpectral (a : XiDivisorL2) : Prop :=
  ∀ q q' : XiZeroCopy, xiSpectralPoint q = xiSpectralPoint q' → a q = a q'

theorem factorsThroughSpectral_kernelVec {z : ℂ} (hz : XiC z ≠ 0) :
    FactorsThroughSpectral (xiKernelVec hz) := by
  intro q q' hqq
  rw [xiKernelVec_apply, xiKernelVec_apply, hqq]

/-- Membership in the span preserves factoring through the spectral point. -/
theorem factorsThroughSpectral_of_mem_span {a : XiDivisorL2}
    (ha : a ∈ Submodule.span ℂ outsideKernelSet) :
    FactorsThroughSpectral a := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨z, hz, -, rfl⟩ := hx
      exact factorsThroughSpectral_kernelVec hz
  | zero =>
      intro q q' _
      rw [lp.coeFn_zero]
      rfl
  | add x y _ _ hx hy =>
      intro q q' h
      rw [lp.coeFn_add]
      simp only [Pi.add_apply]
      rw [hx q q' h, hy q q' h]
  | smul c x _ hx =>
      intro q q' h
      rw [lp.coeFn_smul]
      simp only [Pi.smul_apply]
      rw [hx q q' h]

/-- **Under RH the form is nonnegative on test functions.**  All spectral points
are real, so conjugation fixes them and the form becomes a sum of squares. -/
theorem xiWeilL2Form_re_nonneg_of_rh (hRH : RiemannHypothesis) {a : XiDivisorL2}
    (ha : FactorsThroughSpectral a) : 0 ≤ (xiWeilL2Form a).re := by
  have hfix : ∀ q : XiZeroCopy, a (xiZeroCopyLineConjEquiv q) = a q := by
    intro q
    apply ha
    rw [xiSpectralPoint_lineConj]
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [ht, Complex.conj_ofReal]
  have hsum := summable_weilL2Summand a
  have hcongr : xiWeilL2Form a =
      ∑' q : XiZeroCopy, ((Complex.normSq (a q) : ℝ) : ℂ) := by
    rw [xiWeilL2Form]
    refine tsum_congr fun q => ?_
    rw [hfix q, Complex.mul_conj]
  rw [hcongr]
  have hsum' : Summable (fun q : XiZeroCopy =>
      ((Complex.normSq (a q) : ℝ) : ℂ)) := by
    apply hsum.congr
    intro q
    rw [hfix q, Complex.mul_conj]
  rw [Complex.re_tsum hsum']
  apply tsum_nonneg
  intro q
  simp only [Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- **RH is equivalent to positivity of the Weil form on kernels based off the
critical strip.**  Every entry of that family is an absolutely convergent prime
expression, since the base points avoid the strip in which no Dirichlet series
converges. -/
theorem riemannHypothesis_iff_outsideStrip_nonneg :
    RiemannHypothesis ↔
      ∀ F ∈ Submodule.span ℂ outsideKernelSet, 0 ≤ (xiWeilL2Form F).re := by
  constructor
  · intro hRH F hF
    refine xiWeilL2Form_re_nonneg_of_rh hRH ?_
    exact factorsThroughSpectral_of_mem_span hF
  · intro hpos
    rw [rh_iff_xi_ne_zero_right]
    intro s hs hzero
    obtain ⟨F, hFmem, hFneg⟩ := exists_neg_weilL2Form_outsideStrip hs hzero
    linarith [hpos F hFmem]

/-! ## §8 The form as a unitary involution pairing -/

/-- The Weil form is the pairing of a vector with its conjugation-reindexed
partner: `Q a = ⟪σ a, a⟫` for the reindexing `σ` along divisor conjugation. -/
theorem xiWeilL2Form_eq_inner (a : XiDivisorL2) :
    xiWeilL2Form a = (inner ℂ (xiLineConjVec a) a : ℂ) := by
  rw [lp.inner_eq_tsum, xiWeilL2Form]
  refine tsum_congr fun q => ?_
  rw [xiLineConjVec_apply]
  simp only [RCLike.inner_apply]

/-- **Sharp two-sided bound.**  Reindexing is an isometry, so the Weil form of a
vector never exceeds its squared norm in absolute value.  The criterion asks
which end of this range the test-function span occupies: `‖a‖²` exactly when the
vector is fixed by divisor conjugation, which under RH every test function is. -/
theorem norm_xiWeilL2Form_le (a : XiDivisorL2) :
    ‖xiWeilL2Form a‖ ≤ ‖a‖ ^ 2 := by
  rw [xiWeilL2Form_eq_inner]
  calc ‖(inner ℂ (xiLineConjVec a) a : ℂ)‖
      ≤ ‖xiLineConjVec a‖ * ‖a‖ := norm_inner_le_norm _ _
    _ = ‖a‖ * ‖a‖ := by rw [xiLineConjVec_norm]
    _ = ‖a‖ ^ 2 := (sq ‖a‖).symm

/-- A vector fixed by divisor conjugation has form equal to its squared norm. -/
theorem xiWeilL2Form_eq_normSq_of_lineConj_eq {a : XiDivisorL2}
    (ha : xiLineConjVec a = a) :
    xiWeilL2Form a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  rw [xiWeilL2Form_eq_inner, ha, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Under RH every test function is fixed by divisor conjugation. -/
theorem xiLineConjVec_eq_self_of_rh (hRH : RiemannHypothesis) {a : XiDivisorL2}
    (ha : FactorsThroughSpectral a) : xiLineConjVec a = a := by
  ext q
  show a (xiZeroCopyLineConjEquiv q) = a q
  apply ha
  rw [xiSpectralPoint_lineConj]
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  rw [ht, Complex.conj_ofReal]

/-- **Under RH the form is exactly the squared norm on test functions**, the
extreme value of the range allowed by the unitary-involution bound. -/
theorem xiWeilL2Form_eq_normSq_of_rh (hRH : RiemannHypothesis) {a : XiDivisorL2}
    (ha : FactorsThroughSpectral a) :
    xiWeilL2Form a = ((‖a‖ ^ 2 : ℝ) : ℂ) :=
  xiWeilL2Form_eq_normSq_of_lineConj_eq (xiLineConjVec_eq_self_of_rh hRH ha)

end

end RHTower
