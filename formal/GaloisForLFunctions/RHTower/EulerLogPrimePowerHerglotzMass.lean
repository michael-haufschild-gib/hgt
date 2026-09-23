import GaloisForLFunctions.RHTower.EulerLogPrimePowerHerglotzSupport
import GaloisForLFunctions.RHTower.GammaDampedPrimeLogCauchyDomain
import GaloisForLFunctions.HTGeometry.RegularizedHerglotzTransform

/-!
# Nevanlinna mass of the Euler-log prime-power carrier

The exact Euler-log atoms have finite mass against `(1 + t²)⁻¹`.  The proof uses the existing
summable prime logarithmic inverse-square majorant and a geometric depth tail; it neither assumes
a prime-number theorem nor uses a finite cutoff.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every normalized Euler-log atom is bounded by a summable prime-log majorant times its
geometric depth factor. -/
lemma eulerLogPrimePower_nevanlinna_majorant (p : Nat.Primes) (k : ℕ) :
    eulerLogPrimePowerWeight p k *
        nevanlinnaWeight (eulerLogPrimePowerTime p k) ≤
      RHTower.invNatLogSq p * (1 / 2 : ℝ) ^ k := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hp0 : (0 : ℝ) < p := by positivity
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hpow : (2 : ℝ) ^ k ≤ (p : ℝ) ^ k :=
    pow_le_pow_left₀ (by norm_num) hp k
  have htime : Real.log (p : ℝ) ≤
      ((k + 1 : ℕ) : ℝ) * Real.log (p : ℝ) := by
    exact le_mul_of_one_le_left hlog.le hk
  have htimeSq : (Real.log (p : ℝ)) ^ (2 : ℕ) ≤
      1 + (((k + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) ^ (2 : ℕ) := by
    calc
      (Real.log (p : ℝ)) ^ (2 : ℕ) ≤
          (((k + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) ^ (2 : ℕ) :=
        (sq_le_sq₀ hlog.le (mul_nonneg (zero_le_one.trans hk) hlog.le)).2 htime
      _ ≤ 1 + (((k + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) ^ (2 : ℕ) := by linarith
  have hmain :
      ((p : ℝ) * (Real.log (p : ℝ)) ^ (2 : ℕ)) * (2 : ℝ) ^ k ≤
        (((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + 1)) *
          (1 + (((k + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) ^ (2 : ℕ)) := by
    have hleft : (p : ℝ) * (Real.log (p : ℝ)) ^ (2 : ℕ) * (2 : ℝ) ^ k ≤
        (p : ℝ) * (Real.log (p : ℝ)) ^ (2 : ℕ) * (p : ℝ) ^ k := by
      gcongr
    calc
      (p : ℝ) * (Real.log (p : ℝ)) ^ (2 : ℕ) * (2 : ℝ) ^ k ≤
          (p : ℝ) * (Real.log (p : ℝ)) ^ (2 : ℕ) * (p : ℝ) ^ k := hleft
      _ = (p : ℝ) ^ (k + 1) * (Real.log (p : ℝ)) ^ (2 : ℕ) := by
        rw [pow_succ]
        ring
      _ ≤ ((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + 1) *
          (Real.log (p : ℝ)) ^ (2 : ℕ) := by
        have hmult : (p : ℝ) ^ (k + 1) ≤
            ((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + 1) :=
          le_mul_of_one_le_left (pow_nonneg hp0.le _) hk
        exact mul_le_mul_of_nonneg_right hmult (sq_nonneg _)
      _ ≤ ((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + 1) *
          (1 + (((k + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) ^ (2 : ℕ)) := by
        gcongr
  have hdenL : 0 <
      (((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + 1)) *
        (1 + (((k + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) ^ (2 : ℕ)) := by positivity
  have hdenR : 0 < ((p : ℝ) * (Real.log (p : ℝ)) ^ (2 : ℕ)) * (2 : ℝ) ^ k := by positivity
  unfold eulerLogPrimePowerWeight eulerLogPrimePowerTime nevanlinnaWeight
    RHTower.invNatLogSq
  calc
    (1 / (((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + 1))) *
        (1 + (((k + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) ^ (2 : ℕ))⁻¹ =
      1 / ((((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ (k + 1)) *
        (1 + (((k + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) ^ (2 : ℕ))) := by
          field_simp
    _ ≤ 1 / (((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ)) * (2 : ℝ) ^ k) :=
      one_div_le_one_div_of_le hdenR hmain
    _ = (1 / ((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ))) * (1 / 2 : ℝ) ^ k := by
      field_simp
      rw [← mul_pow]
      norm_num

/-- The exact Euler-log prime-power atoms have finite Nevanlinna mass. -/
lemma summable_eulerLogPrimePower_nevanlinnaMass :
    Summable fun x : PrimePowerClockIndex =>
      eulerLogPrimePowerWeight x.1 x.2 *
        nevanlinnaWeight (eulerLogPrimePowerTime x.1 x.2) := by
  let major : PrimePowerClockIndex → ℝ := fun x =>
    RHTower.invNatLogSq x.1 * (1 / 2 : ℝ) ^ x.2
  have hmajorNonneg : 0 ≤ major := by
    intro x
    dsimp only [major]
    rw [RHTower.invNatLogSq]
    positivity
  have hmajor : Summable major := by
    rw [summable_prod_of_nonneg hmajorNonneg]
    constructor
    · intro p
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
        (RHTower.invNatLogSq p)
    · have hprime := RHTower.summable_prime_invNatLogSq.mul_right (2 : ℝ)
      apply hprime.congr
      intro p
      dsimp only [major]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
  apply Summable.of_nonneg_of_le
    (fun x => mul_nonneg (eulerLogPrimePowerWeight_pos x.1 x.2).le
      (nevanlinnaWeight_pos _).le)
    (fun x => ?_) hmajor
  exact eulerLogPrimePower_nevanlinna_majorant x.1 x.2

/-- Off the real axis, the regularized Herglotz kernel is bounded by the Nevanlinna weight. -/
lemma norm_regularizedHerglotzKernel_le_nevanlinna
    (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    ‖regularizedHerglotzKernel t z‖ ≤
      (‖z‖ + ‖1 + z ^ (2 : ℕ)‖ * |z.im|⁻¹) * nevanlinnaWeight t := by
  rw [regularizedHerglotzKernel_eq hz t, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (nevanlinnaWeight_pos t)]
  have hinner : ‖z + (1 + z ^ (2 : ℕ)) / ((t : ℂ) - z)‖ ≤
      ‖z‖ + ‖1 + z ^ (2 : ℕ)‖ * |z.im|⁻¹ := by
    calc
      ‖z + (1 + z ^ (2 : ℕ)) / ((t : ℂ) - z)‖ ≤
          ‖z‖ + ‖(1 + z ^ (2 : ℕ)) / ((t : ℂ) - z)‖ := norm_add_le _ _
      _ = ‖z‖ + ‖1 + z ^ (2 : ℕ)‖ * ‖((t : ℂ) - z)⁻¹‖ := by
        rw [div_eq_mul_inv, norm_mul]
      _ ≤ ‖z‖ + ‖1 + z ^ (2 : ℕ)‖ * |z.im|⁻¹ := by
        gcongr
        exact norm_inv_real_sub_le hz t
  calc
    nevanlinnaWeight t * ‖z + (1 + z ^ (2 : ℕ)) / ((t : ℂ) - z)‖ ≤
        nevanlinnaWeight t * (‖z‖ + ‖1 + z ^ (2 : ℕ)‖ * |z.im|⁻¹) :=
      mul_le_mul_of_nonneg_left hinner (nevanlinnaWeight_pos t).le
    _ = (‖z‖ + ‖1 + z ^ (2 : ℕ)‖ * |z.im|⁻¹) * nevanlinnaWeight t := mul_comm _ _

/-- Exact normalized Euler-log Herglotz Cauchy carrier. -/
def eulerLogPrimePowerHerglotz (z : ℂ) : ℂ :=
  ∑' x : PrimePowerClockIndex,
    (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
      regularizedHerglotzKernel (eulerLogPrimePowerTime x.1 x.2) z

/-- The normalized Euler-log Herglotz carrier converges absolutely at every non-real point. -/
theorem summable_eulerLogPrimePowerHerglotzTerm
    (z : ℂ) (hz : z.im ≠ 0) :
    Summable fun x : PrimePowerClockIndex =>
      (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
        regularizedHerglotzKernel (eulerLogPrimePowerTime x.1 x.2) z := by
  let C : ℝ := ‖z‖ + ‖1 + z ^ (2 : ℕ)‖ * |z.im|⁻¹
  have hmajor := summable_eulerLogPrimePower_nevanlinnaMass.mul_left C
  apply Summable.of_norm_bounded hmajor
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (eulerLogPrimePowerWeight_pos x.1 x.2)]
  calc
    eulerLogPrimePowerWeight x.1 x.2 *
        ‖regularizedHerglotzKernel (eulerLogPrimePowerTime x.1 x.2) z‖ ≤
      eulerLogPrimePowerWeight x.1 x.2 *
        (C * nevanlinnaWeight (eulerLogPrimePowerTime x.1 x.2)) := by
          apply mul_le_mul_of_nonneg_left
            (norm_regularizedHerglotzKernel_le_nevanlinna z hz _)
          exact (eulerLogPrimePowerWeight_pos x.1 x.2).le
    _ = C * (eulerLogPrimePowerWeight x.1 x.2 *
        nevanlinnaWeight (eulerLogPrimePowerTime x.1 x.2)) := by ring

/-- The regularizing subtraction is real, so it leaves the Cauchy imaginary part unchanged. -/
lemma regularizedHerglotzKernel_im
    (t : ℝ) (z : ℂ) :
    (regularizedHerglotzKernel t z).im = z.im / ‖(t : ℂ) - z‖ ^ (2 : ℕ) := by
  rw [regularizedHerglotzKernel, Complex.sub_im]
  have hreal : ((t : ℂ) / (1 + (t : ℂ) ^ (2 : ℕ))).im = 0 := by
    have him : (1 + (t : ℂ) ^ (2 : ℕ)).im = 0 := by
      rw [pow_two, Complex.add_im, Complex.mul_im]
      simp
    rw [Complex.div_im, him]
    simp
  rw [hreal, sub_zero, one_div, Complex.inv_im, Complex.sub_im]
  rw [Complex.normSq_eq_norm_sq]
  simp

/-- Every individual normalized Euler-log atom has strictly positive upper-half-plane imaginary
part. -/
lemma regularizedHerglotzKernel_im_pos
    (t : ℝ) (z : ℂ) (hz : 0 < z.im) :
    0 < (regularizedHerglotzKernel t z).im := by
  rw [regularizedHerglotzKernel_im]
  apply div_pos hz
  apply sq_pos_of_ne_zero
  exact norm_ne_zero_iff.mpr (real_sub_ne_zero_of_im_ne_zero hz.ne' t)

/-- The exact normalized Euler-log carrier is strictly Herglotz in the upper half-plane. -/
theorem eulerLogPrimePowerHerglotz_im_pos
    (z : ℂ) (hz : 0 < z.im) :
    0 < (eulerLogPrimePowerHerglotz z).im := by
  let f : PrimePowerClockIndex → ℂ := fun x =>
    (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
      regularizedHerglotzKernel (eulerLogPrimePowerTime x.1 x.2) z
  have hs : Summable f := summable_eulerLogPrimePowerHerglotzTerm z hz.ne'
  rw [eulerLogPrimePowerHerglotz, Complex.im_tsum hs]
  have hsReal : Summable fun x => (f x).im := by
    simpa only [Complex.imCLM_apply] using Complex.imCLM.summable hs
  apply hsReal.tsum_pos
  · intro x
    rw [show f x = (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
      regularizedHerglotzKernel (eulerLogPrimePowerTime x.1 x.2) z by rfl,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_nonneg (eulerLogPrimePowerWeight_pos x.1 x.2).le
      (regularizedHerglotzKernel_im_pos _ _ hz).le
  · let p2 : Nat.Primes := ⟨2, by norm_num⟩
    let x2 : PrimePowerClockIndex := (p2, 0)
    rw [show f x2 = (eulerLogPrimePowerWeight x2.1 x2.2 : ℂ) *
      regularizedHerglotzKernel (eulerLogPrimePowerTime x2.1 x2.2) z by rfl,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos (eulerLogPrimePowerWeight_pos x2.1 x2.2)
      (regularizedHerglotzKernel_im_pos _ _ hz)

/-- The normalized Euler-log carrier converges locally uniformly throughout the upper half-plane.
The majorant is its exact Nevanlinna mass, not the divergent unregularized atom mass. -/
theorem summableLocallyUniformlyOn_eulerLogPrimePowerHerglotz :
    SummableLocallyUniformlyOn
      (fun x : PrimePowerClockIndex => fun z : ℂ =>
        (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
          regularizedHerglotzKernel (eulerLogPrimePowerTime x.1 x.2) z)
      upperHalfPlane := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z hz
  change 0 < z.im at hz
  let r : ℝ := z.im / 2
  have hr : 0 < r := by
    dsimp [r]
    exact half_pos hz
  refine ⟨Metric.ball z r,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hr), ?_⟩
  let B : ℝ := ‖z‖ + r
  let C : ℝ := B + (1 + B ^ (2 : ℕ)) * r⁻¹
  apply HasSumUniformlyOn.of_norm_le_summable
    (summable_eulerLogPrimePower_nevanlinnaMass.mul_left C)
  intro x w hw
  have hdist : ‖w - z‖ < r := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hw
  have habsdiff : |w.im - z.im| < r := by
    calc
      |w.im - z.im| = |(w - z).im| := by rw [Complex.sub_im]
      _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      _ < r := hdist
  rw [abs_lt] at habsdiff
  have hwim : r < w.im := by
    dsimp [r] at habsdiff ⊢
    linarith [habsdiff.1]
  have hwim0 : 0 < w.im := hr.trans hwim
  have habsle : r ≤ |w.im| := by
    rw [abs_of_pos hwim0]
    exact hwim.le
  have hwinv : |w.im|⁻¹ ≤ r⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hr habsle
  have hwnorm : ‖w‖ ≤ B := by
    calc
      ‖w‖ = ‖(w - z) + z‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ r + ‖z‖ := add_le_add_left hdist.le _
      _ = B := by dsimp [B]; ring
  have hwone : ‖1 + w ^ (2 : ℕ)‖ ≤ 1 + B ^ (2 : ℕ) := by
    calc
      ‖1 + w ^ (2 : ℕ)‖ ≤ ‖(1 : ℂ)‖ + ‖w ^ (2 : ℕ)‖ := norm_add_le _ _
      _ = 1 + ‖w‖ ^ (2 : ℕ) := by rw [norm_one, norm_pow]
      _ ≤ 1 + B ^ (2 : ℕ) := by gcongr
  have hbound : ‖w‖ + ‖1 + w ^ (2 : ℕ)‖ * |w.im|⁻¹ ≤ C := by
    calc
      ‖w‖ + ‖1 + w ^ (2 : ℕ)‖ * |w.im|⁻¹ ≤ B + (1 + B ^ (2 : ℕ)) * r⁻¹ := by
        gcongr
      _ = C := rfl
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (eulerLogPrimePowerWeight_pos x.1 x.2)]
  calc
    eulerLogPrimePowerWeight x.1 x.2 *
        ‖regularizedHerglotzKernel (eulerLogPrimePowerTime x.1 x.2) w‖ ≤
      eulerLogPrimePowerWeight x.1 x.2 *
        ((‖w‖ + ‖1 + w ^ (2 : ℕ)‖ * |w.im|⁻¹) *
          nevanlinnaWeight (eulerLogPrimePowerTime x.1 x.2)) := by
        apply mul_le_mul_of_nonneg_left
          (norm_regularizedHerglotzKernel_le_nevanlinna w hwim0.ne' _)
        exact (eulerLogPrimePowerWeight_pos x.1 x.2).le
    _ ≤ eulerLogPrimePowerWeight x.1 x.2 *
        (C * nevanlinnaWeight (eulerLogPrimePowerTime x.1 x.2)) := by
        gcongr
        exact (eulerLogPrimePowerWeight_pos x.1 x.2).le
        exact (nevanlinnaWeight_pos _).le
    _ = C * (eulerLogPrimePowerWeight x.1 x.2 *
        nevanlinnaWeight (eulerLogPrimePowerTime x.1 x.2)) := by ring

/-- The locally uniform normalized Euler-log carrier is holomorphic on the upper half-plane. -/
theorem differentiableOn_eulerLogPrimePowerHerglotz_upperHalfPlane :
    DifferentiableOn ℂ eulerLogPrimePowerHerglotz upperHalfPlane := by
  apply SummableLocallyUniformlyOn.differentiableOn isOpen_upperHalfPlane
    summableLocallyUniformlyOn_eulerLogPrimePowerHerglotz
  intro x z hz
  change 0 < z.im at hz
  unfold regularizedHerglotzKernel
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.sub
  · have hne : (eulerLogPrimePowerTime x.1 x.2 : ℂ) - z ≠ 0 := by
      intro hzero
      have heq : (eulerLogPrimePowerTime x.1 x.2 : ℂ) = z := sub_eq_zero.mp hzero
      have him : z.im = 0 := by rw [← heq]; simp
      exact hz.ne' him
    have hbase : DifferentiableAt ℂ
        (fun y : ℂ => (eulerLogPrimePowerTime x.1 x.2 : ℂ) - y) z :=
      (differentiableAt_const (c := (eulerLogPrimePowerTime x.1 x.2 : ℂ))).sub
        differentiableAt_id
    have hdiff : DifferentiableAt ℂ
        (fun y : ℂ => ((eulerLogPrimePowerTime x.1 x.2 : ℂ) - y)⁻¹) z := hbase.inv hne
    simpa [one_div] using hdiff
  · exact differentiableAt_const _

end

end GaloisForLFunctions.RHTower
