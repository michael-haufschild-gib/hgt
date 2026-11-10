import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.AnalyticSmoothingBranch
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.QuadraticResidueScaling

/-!
# Universal quadratic scaling of analytic prime smoothing

Taylor coefficients determine the full spectral profile after the
quadratic residue scale is removed. The first nonzero coefficient fixes
the sharp scaling half-plane and its nonremovable logarithmic branch.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- The logarithmic profile, starting at the first nonzero Taylor order. -/
def analyticSmoothingScalingLog (Φ : ℂ → ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, smoothingTaylorCoefficient Φ (n + m) * Complex.log (w + ((n + m : ℕ) : ℂ))

/-- The universal profile after removal of the quadratic residue scale. -/
def analyticSmoothingScalingProfile (Φ : ℂ → ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  riemannZeta 2 * Complex.exp (-analyticSmoothingScalingLog Φ m w)

private theorem summable_norm_smoothingTail {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (m : ℕ) :
    Summable (fun n : ℕ => ‖smoothingTaylorCoefficient Φ (n + m)‖) :=
  (summable_nat_add_iff m).mpr (summable_norm_smoothingTaylorCoefficient hR hΦ)

private theorem summable_smoothingTail_weight {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (m : ℕ) (C : ℝ) :
    Summable (fun n : ℕ => ‖smoothingTaylorCoefficient Φ (n + m)‖ * (C + (n : ℝ) + 1)) := by
  have hs := (summable_nat_add_iff m).mpr (summable_smoothingTaylorCoefficient_weight hR hΦ (C - m))
  refine hs.congr (fun n => ?_)
  push_cast
  ring

private theorem tsum_smoothingTail {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (h1 : Φ 1 = -1)
    {m : ℕ} (hbelow : ∀ k < m, smoothingTaylorCoefficient Φ k = 0) :
    (∑' n : ℕ, smoothingTaylorCoefficient Φ (n + m)) = -2 := by
  have hs := (Summable.of_norm (summable_norm_smoothingTaylorCoefficient hR hΦ)).sum_add_tsum_nat_add m
  have hzero : ∑ k ∈ Finset.range m, smoothingTaylorCoefficient Φ k = 0 :=
    Finset.sum_eq_zero (fun k hk => hbelow k (Finset.mem_range.mp hk))
  rw [hzero, zero_add, tsum_smoothingTaylorCoefficient hR hΦ h1] at hs
  exact hs

private theorem smoothingTail_hasSum {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    {m : ℕ} (hbelow : ∀ k < m, smoothingTaylorCoefficient Φ k = 0)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => smoothingTaylorCoefficient Φ (n + m) * z ^ (n + m)) (Φ z - 1) := by
  have hh := smoothingTaylor_hasSum hR hΦ hz
  have hs := hh.summable.sum_add_tsum_nat_add m
  have hzero : ∑ k ∈ Finset.range m, smoothingTaylorCoefficient Φ k * z ^ k = 0 :=
    Finset.sum_eq_zero (fun k hk => by rw [hbelow k (Finset.mem_range.mp hk), zero_mul])
  rw [hzero, zero_add, hh.tsum_eq] at hs
  exact hs ▸ ((summable_nat_add_iff m).mpr hh.summable).hasSum

/-- Every analytic Taylor logarithm tail has a normally convergent holomorphic region. -/
private theorem smoothingLogTail_normal_bound {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (j : ℕ) {w : ℂ}
    (hw : -(j : ℝ) < w.re) :
    ∃ r : ℝ, 0 < r ∧ ∃ b : ℕ → ℝ, Summable b ∧
      ∀ n : ℕ, ∀ z ∈ Metric.ball w r,
        ‖smoothingTaylorCoefficient Φ (n + j) *
          Complex.log (z + ((n + j : ℕ) : ℂ))‖ ≤ b n ∧
        0 < (z + ((n + j : ℕ) : ℂ)).re := by
  let r := (w.re + (j : ℝ)) / 2
  have hr : 0 < r := by dsimp [r]; linarith only [hw]
  let C := |Real.log r| + ‖w‖ + r + Real.pi - 1
  let b : ℕ → ℝ := fun n => ‖smoothingTaylorCoefficient Φ (n + j)‖ *
    (C + ((n + j : ℕ) : ℝ) + 1)
  have hb : Summable b := by
    exact (summable_nat_add_iff j).mpr (summable_smoothingTaylorCoefficient_weight hR hΦ C)
  refine ⟨r, hr, b, hb, ?_⟩
  intro n z hz
  have hzn : ‖z - w‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hRe := Complex.re_le_norm (w - z)
  rw [norm_sub_rev] at hRe
  simp only [Complex.sub_re] at hRe
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl : r ≤ (z + ((n + j : ℕ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re, Nat.cast_add]
    dsimp [r] at hzn ⊢
    linarith only [hRe, hzn, hn]
  have hzbound : ‖z‖ ≤ ‖w‖ + r := by
    calc
      ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ‖w‖ + r := by linarith only [hzn]
  have hu : ‖z + ((n + j : ℕ) : ℂ)‖ ≤ ‖w‖ + r + (n + j : ℕ) := by
    calc
      _ ≤ ‖z‖ + ‖((n + j : ℕ) : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + (n + j : ℕ) := by rw [Complex.norm_natCast]
      _ ≤ _ := add_le_add hzbound le_rfl
  have hlog := norm_log_le_linear hr hl hu (by positivity)
  refine ⟨?_, hr.trans_le hl⟩
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left hlog (norm_nonneg _)).trans_eq
  dsimp [b, C]
  push_cast
  ring

private theorem summable_smoothingLogTail {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (j : ℕ) {w : ℂ} (hw : -(j : ℝ) < w.re) :
    Summable (fun n : ℕ => smoothingTaylorCoefficient Φ (n + j) *
      Complex.log (w + ((n + j : ℕ) : ℂ))) := by
  obtain ⟨r, hr, b, hb, hbound⟩ := smoothingLogTail_normal_bound hR hΦ j hw
  exact Summable.of_norm_bounded hb (fun n => (hbound n w (Metric.mem_ball_self hr)).1)

private theorem analyticAt_smoothingLogTail {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (j : ℕ) {w : ℂ} (hw : -(j : ℝ) < w.re) :
    AnalyticAt ℂ (fun z => ∑' n : ℕ, smoothingTaylorCoefficient Φ (n + j) *
      Complex.log (z + ((n + j : ℕ) : ℂ))) w := by
  obtain ⟨r, hr, b, hb, hbound⟩ := smoothingLogTail_normal_bound hR hΦ j hw
  have hd : DifferentiableOn ℂ (fun z => ∑' n : ℕ, smoothingTaylorCoefficient Φ (n + j) *
      Complex.log (z + ((n + j : ℕ) : ℂ))) (Metric.ball w r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hb (fun n => ?_) Metric.isOpen_ball
      (fun n z hz => (hbound n z hz).1)
    intro z hz
    have hslit : z + ((n + j : ℕ) : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (hbound n z hz).2)
    exact (analyticAt_const.mul ((analyticAt_id.add analyticAt_const).clog hslit)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))


/-- The complete scaling logarithm is analytic up to its first shifted branch. -/
theorem analyticOnNhd_analyticSmoothingScalingLog {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (m : ℕ) :
    AnalyticOnNhd ℂ (analyticSmoothingScalingLog Φ m) {w | -(m : ℝ) < w.re} :=
  fun _ hw => analyticAt_smoothingLogTail hR hΦ m hw

theorem analyticOnNhd_analyticSmoothingScalingProfile {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (m : ℕ) :
    AnalyticOnNhd ℂ (analyticSmoothingScalingProfile Φ m) {w | -(m : ℝ) < w.re} :=
  fun w hw => analyticAt_const.mul (analyticOnNhd_analyticSmoothingScalingLog hR hΦ m w hw).neg.cexp

theorem analyticSmoothingScalingProfile_ne_zero (Φ : ℂ → ℂ) (m : ℕ) (w : ℂ) :
    analyticSmoothingScalingProfile Φ m w ≠ 0 := by
  have hζ : riemannZeta (2 : ℂ) ≠ 0 := by
    rw [← exp_canonicalEulerLogZeta_eq_riemannZeta (s := (2 : ℂ)) (by norm_num)]
    exact Complex.exp_ne_zero _
  exact mul_ne_zero hζ (Complex.exp_ne_zero _)

/-- Removing the leading logarithm leaves the next Taylor tail. -/
theorem analyticSmoothingScalingProfile_factorization {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (m : ℕ) {w : ℂ} (hw : -(m : ℝ) < w.re) :
    analyticSmoothingScalingProfile Φ m w = analyticSmoothingScalingProfile Φ (m + 1) w *
      Complex.exp (-smoothingTaylorCoefficient Φ m * Complex.log (w + (m : ℂ))) := by
  have hs := summable_smoothingLogTail hR hΦ m hw
  have he := hs.tsum_eq_zero_add
  change analyticSmoothingScalingLog Φ m w =
    smoothingTaylorCoefficient Φ (0 + m) * Complex.log (w + ((0 + m : ℕ) : ℂ)) +
      (∑' n : ℕ, smoothingTaylorCoefficient Φ (n + 1 + m) *
        Complex.log (w + ((n + 1 + m : ℕ) : ℂ))) at he
  simp only [Nat.zero_add] at he
  have htail : (∑' n : ℕ, smoothingTaylorCoefficient Φ (n + 1 + m) *
      Complex.log (w + ((n + 1 + m : ℕ) : ℂ))) = analyticSmoothingScalingLog Φ (m + 1) w := by
    apply tsum_congr
    intro n
    rw [show n + 1 + m = n + (m + 1) by omega]
  rw [htail] at he
  rw [analyticSmoothingScalingProfile, he, neg_add, Complex.exp_add,
    analyticSmoothingScalingProfile, neg_mul]
  ring

/-- The first imaginary Taylor coefficient makes the full limit nonpolynomial. -/
theorem analyticSmoothingScalingProfile_not_polynomial {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    {m : ℕ} {b : ℝ} (hb : b ≠ 0) (hc : smoothingTaylorCoefficient Φ m = (b : ℂ) * I) :
    ¬ ∃ P : Polynomial ℂ, ∀ w : ℂ, -(m : ℝ) < w.re →
      analyticSmoothingScalingProfile Φ m w = P.eval w := by
  rintro ⟨P, hP⟩
  have ha : AnalyticAt ℂ (analyticSmoothingScalingProfile Φ (m + 1)) (-(m : ℂ)) :=
    analyticOnNhd_analyticSmoothingScalingProfile hR hΦ (m + 1) _ (by
      simp only [mem_setOf_eq, Complex.neg_re, Complex.natCast_re, Nat.cast_add, Nat.cast_one]
      linarith)
  apply imaginaryLogBranch_no_continuous_extension hb ha.continuousAt
    (analyticSmoothingScalingProfile_ne_zero Φ (m + 1) (-(m : ℂ))) P.continuous.continuousAt
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  have hw : -(m : ℝ) < (-(m : ℂ) + (x : ℂ)).re := by
    simp only [Complex.add_re, Complex.neg_re, Complex.natCast_re, Complex.ofReal_re]
    linarith only [hx]
  rw [← hP _ hw, analyticSmoothingScalingProfile_factorization hR hΦ m hw, hc,
    show -(m : ℂ) + (x : ℂ) + (m : ℂ) = (x : ℂ) by ring, neg_mul]
  congr 2
  ring


private def smoothingShiftTerm (Φ : ℂ → ℂ) (m : ℕ) (t : ℝ) (s : ℂ)
    (p : Nat.Primes) (n : ℕ) : ℂ :=
  smoothingTaylorCoefficient Φ (n + m) *
    Complex.exp (-(s + ((n + m : ℕ) : ℂ) * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))

private theorem norm_smoothingShiftTerm_le (Φ : ℂ → ℂ) (m : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (s : ℂ) (p : Nat.Primes) (n : ℕ) :
    ‖smoothingShiftTerm Φ m t s p n‖ ≤
      (p : ℝ) ^ (-(s.re + (m : ℝ) * t)) * ‖smoothingTaylorCoefficient Φ (n + m)‖ := by
  rw [smoothingShiftTerm, norm_mul, norm_exponentialPrime_damping]
  apply (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)).trans_eq (mul_comm _ _)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le)
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Nat.cast_add]
  nlinarith only [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) ht]

private theorem summable_smoothingShiftTerm {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (m : ℕ) {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re + (m : ℝ) * t) :
    Summable (fun pn : Nat.Primes × ℕ => smoothingShiftTerm Φ m t s pn.1 pn.2) := by
  have hp := summable_primes_rpow (show -(s.re + (m : ℝ) * t) < -1 by linarith only [hs])
  have hb := Summable.mul_of_nonneg hp (summable_norm_smoothingTail hR hΦ m)
    (fun p => by positivity) (fun n => norm_nonneg _)
  exact Summable.of_norm_bounded hb (fun pn => norm_smoothingShiftTerm_le Φ m ht s pn.1 pn.2)

private theorem smoothingShiftTerm_eq (Φ : ℂ → ℂ) (m : ℕ) (t : ℝ) (s : ℂ)
    (p : Nat.Primes) (n : ℕ) :
    smoothingShiftTerm Φ m t s p n =
      (smoothingTaylorCoefficient Φ (n + m) *
        Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ)) ^ (n + m)) *
          Complex.exp (-s * (Real.log (p : ℝ) : ℂ)) := by
  rw [smoothingShiftTerm,
    show -(s + ((n + m : ℕ) : ℂ) * (t : ℂ)) * (Real.log (p : ℝ) : ℂ) =
      ((n + m : ℕ) : ℂ) * (-(t : ℂ) * (Real.log (p : ℝ) : ℂ)) +
        (-s * (Real.log (p : ℝ) : ℂ)) by ring,
    Complex.exp_add, Complex.exp_nat_mul]
  ring

private theorem tsum_smoothingShiftTerm {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    {m : ℕ} (hbelow : ∀ k < m, smoothingTaylorCoefficient Φ k = 0)
    {t : ℝ} (ht : 0 ≤ t) (s : ℂ) (p : Nat.Primes) :
    (∑' n : ℕ, smoothingShiftTerm Φ m t s p n) =
      (analyticSmoothingPrimePhase Φ p (t : ℂ) - 1) * Complex.exp (-s * (Real.log (p : ℝ) : ℂ)) := by
  have hz : ‖Complex.exp (-(t : ℂ) * (Real.log (p : ℝ) : ℂ))‖ ≤ 1 := by
    rw [norm_exponentialPrime_damping, Complex.ofReal_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.2.one_le) (neg_nonpos.mpr ht)
  have hh := (smoothingTail_hasSum hR hΦ hbelow hz).mul_right
    (Complex.exp (-s * (Real.log (p : ℝ) : ℂ)))
  rw [tsum_congr (fun n => smoothingShiftTerm_eq Φ m t s p n)]
  exact hh.tsum_eq

/-- Taylor expansion and absolute Fubini identify every shifted prime logarithm. -/
theorem deformationPrimeSum_analyticSmoothing_shifted {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    {m : ℕ} (hbelow : ∀ k < m, smoothingTaylorCoefficient Φ k = 0)
    {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re + (m : ℝ) * t) :
    deformationPrimeSum (analyticSmoothingGauge Φ t) s =
      ∑' n : ℕ, smoothingTaylorCoefficient Φ (n + m) *
        coronaPrimeZeta (s + ((n + m : ℕ) : ℂ) * (t : ℂ)) := by
  have hp := summable_smoothingShiftTerm hR hΦ m ht hs
  calc
    _ = ∑' p : Nat.Primes, ∑' n : ℕ, smoothingShiftTerm Φ m t s p n := by
      unfold deformationPrimeSum
      apply tsum_congr
      intro p
      rw [tsum_smoothingShiftTerm hR hΦ hbelow ht,
        ← analyticSmoothingPrimePhase_eq_twist hunit ht, ← prime_cexp_decay p s]
      simp only [primeFrequency, neg_mul]
    _ = ∑' n : ℕ, ∑' p : Nat.Primes, smoothingShiftTerm Φ m t s p n :=
      (Summable.tsum_comm (f := fun p n => smoothingShiftTerm Φ m t s p n) hp).symm
    _ = _ := by
      apply tsum_congr
      intro n
      unfold smoothingShiftTerm
      rw [tsum_mul_left]
      congr 1
      unfold coronaPrimeZeta
      apply tsum_congr
      intro p
      rw [coronaPrimeEigenvalue, ← prime_cexp_decay]
      simp only [primeFrequency, neg_mul]

/-- The finite regular contribution after subtracting all shifted prime logarithms. -/
def analyticSmoothingScaledRemainder (Φ : ℂ → ℂ) (m : ℕ) (t : ℝ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, smoothingTaylorCoefficient Φ (n + m) *
    regularizedPrimeLog (1 + (t : ℂ) * (w + ((n + m : ℕ) : ℂ)))

theorem analyticSmoothingScaledRemainder_zero {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (h1 : Φ 1 = -1)
    {m : ℕ} (hbelow : ∀ k < m, smoothingTaylorCoefficient Φ k = 0) (w : ℂ) :
    analyticSmoothingScaledRemainder Φ m 0 w = 2 * hullRem 1 (twist 0) := by
  simp only [analyticSmoothingScaledRemainder, Complex.ofReal_zero, zero_mul, add_zero,
    regularizedPrimeLog_one, tsum_mul_right, tsum_smoothingTail hR hΦ h1 hbelow]
  ring

/-- Translation moves the sharp half-plane to the universal prime-logarithm sector bound. -/
private theorem smoothing_regularizedPrimeLog_bound (m : ℕ) {η M : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ w : ℂ,
      η ≤ w.re + m → ‖w‖ ≤ M → ∀ n : ℕ,
        ‖regularizedPrimeLog (1 + (t : ℂ) * (w + ((n + m : ℕ) : ℂ)))‖ ≤ C + n + 1 := by
  let M' := M + |(m : ℝ) - 1|
  have hM' : 1 ≤ M' := by dsimp only [M']; linarith only [hM, abs_nonneg ((m : ℝ) - 1)]
  obtain ⟨C, hC, hb⟩ := regularizedPrimeLog_scaled_bound hη hη1 hM'
  refine ⟨C, hC, fun t ht ht1 w hw hMw n => ?_⟩
  have hre : η ≤ (w + (((m : ℝ) - 1 : ℝ) : ℂ)).re + 1 := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith only [hw]
  have hn : ‖w + (((m : ℝ) - 1 : ℝ) : ℂ)‖ ≤ M' := by
    apply (norm_add_le _ _).trans
    rw [norm_real, Real.norm_eq_abs]
    exact add_le_add hMw le_rfl
  have hh := hb t ht ht1 (w + (((m : ℝ) - 1 : ℝ) : ℂ)) hre hn n
  have he : w + (((m : ℝ) - 1 : ℝ) : ℂ) + ((n + 1 : ℕ) : ℂ) = w + ((n + m : ℕ) : ℂ) := by
    push_cast
    ring
  rw [he] at hh
  simpa only [add_assoc] using hh

/-- Compact spectral sets admit a jointly continuous renormalized prime sum through `t=0`. -/
theorem continuousOn_analyticSmoothingScaledRemainder {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (m : ℕ) {K : Set ℂ} (hK : IsCompact K)
    (hhalf : K ⊆ {w | -(m : ℝ) < w.re}) :
    ContinuousOn (fun q : ℝ × ℂ => analyticSmoothingScaledRemainder Φ m q.1 q.2) (Icc 0 1 ×ˢ K) := by
  by_cases hK0 : K = ∅
  · subst K
    simp
  have hne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK0
  obtain ⟨v, hv, hmin⟩ := hK.exists_isMinOn (f := fun w : ℂ => w.re + (m : ℝ)) hne
    ((Complex.continuous_re.add continuous_const).continuousOn)
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn (f := fun w : ℂ => ‖w‖) hne continuous_norm.continuousOn
  have hmBound : ∀ w ∈ K, v.re + (m : ℝ) ≤ w.re + (m : ℝ) := hmin
  have hbBound : ∀ w ∈ K, ‖w‖ ≤ ‖b‖ := hmax
  let η := min (v.re + (m : ℝ)) 1
  let M := max 1 ‖b‖
  have hvre : -(m : ℝ) < v.re := hhalf hv
  have hη : 0 < η := lt_min (by linarith only [hvre]) zero_lt_one
  have hη1 : η ≤ 1 := min_le_right _ _
  have hM : 1 ≤ M := le_max_left _ _
  have hηw (w : ℂ) (hw : w ∈ K) : η ≤ w.re + (m : ℝ) :=
    (min_le_left _ _).trans (hmBound w hw)
  have hMw (w : ℂ) (hw : w ∈ K) : ‖w‖ ≤ M :=
    (hbBound w hw).trans (le_max_right _ _)
  obtain ⟨C, _, hbound⟩ := smoothing_regularizedPrimeLog_bound m hη hη1 hM
  change ContinuousOn (fun q : ℝ × ℂ => ∑' n : ℕ, smoothingTaylorCoefficient Φ (n + m) *
    regularizedPrimeLog (1 + (q.1 : ℂ) * (q.2 + ((n + m : ℕ) : ℂ)))) (Icc 0 1 ×ˢ K)
  refine continuousOn_tsum (fun n q hq => ?_)
    (summable_smoothingTail_weight hR hΦ m C) (fun n q hq => ?_)
  · have hmap : ContinuousAt (fun v : ℝ × ℂ =>
        1 + (v.1 : ℂ) * (v.2 + ((n + m : ℕ) : ℂ))) q := by fun_prop
    have hE : ContinuousAt regularizedPrimeLog
        (1 + (q.1 : ℂ) * (q.2 + ((n + m : ℕ) : ℂ))) := by
      by_cases ht0 : q.1 = 0
      · simpa only [ht0, Complex.ofReal_zero, zero_mul, add_zero] using
          analyticAt_regularizedPrimeLog_one.continuousAt
      · apply (analyticAt_regularizedPrimeLog_right ?_).continuousAt
        have ht : 0 < q.1 := lt_of_le_of_ne hq.1.1 (Ne.symm ht0)
        have hw : -(m : ℝ) < q.2.re := hhalf hq.2
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hp : 0 < q.1 * (q.2.re + ((n : ℝ) + m)) :=
          mul_pos ht (by linarith only [hw, hn])
        simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, Complex.natCast_re, Nat.cast_add]
        linarith only [hp]
    exact ((hE.comp (g := regularizedPrimeLog)
      (f := fun v : ℝ × ℂ => 1 + (v.1 : ℂ) * (v.2 + ((n + m : ℕ) : ℂ))) hmap).const_mul
        (smoothingTaylorCoefficient Φ (n + m))).continuousWithinAt
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hbound q.1 hq.1.1 hq.1.2 q.2 (hηw q.2 hq.2) (hMw q.2 hq.2) n) (norm_nonneg _)



private theorem continuousAt_analyticSmoothing_twist {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    (p : Nat.Primes) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun v : ℝ => twist (analyticSmoothingGauge Φ v) p) t := by
  have hf : ContinuousAt (fun v : ℝ => analyticSmoothingPrimePhase Φ p (v : ℂ)) t :=
    (analyticAt_analyticSmoothingPrimePhase hR hΦ p ht).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have hn : ‖analyticSmoothingPrimePhase Φ p (t : ℂ)‖ ≠ 0 := by
    rw [norm_analyticSmoothingPrimePhase_real hunit ht p]
    exact one_ne_zero
  have he (v : ℝ) (hv : analyticSmoothingPrimePhase Φ p (v : ℂ) ≠ 0) :
      twist (analyticSmoothingGauge Φ v) p =
        analyticSmoothingPrimePhase Φ p (v : ℂ) / (‖analyticSmoothingPrimePhase Φ p (v : ℂ)‖ : ℂ) := by
    rw [analyticSmoothingGauge, twist_linearPhaseGauge_prime]
    simp only [linearPrimePhase, Complex.ofReal_one, mul_one]
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv))).mpr
    rw [mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I _
  have hne : analyticSmoothingPrimePhase Φ p (t : ℂ) ≠ 0 := norm_ne_zero_iff.mp hn
  have hquot := hf.div (Complex.continuous_ofReal.continuousAt.comp hf.norm)
    (Complex.ofReal_ne_zero.mpr hn)
  change Tendsto (fun v : ℝ => twist (analyticSmoothingGauge Φ v) (p : ℕ))
    (𝓝 t) (𝓝 (twist (analyticSmoothingGauge Φ t) (p : ℕ)))
  rw [he t hne]
  apply hquot.tendsto.congr'
  filter_upwards [hf.eventually_ne hne] with v hv
  exact (he v hv).symm

private theorem continuousAt_analyticSmoothing_eulerVar {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    (p : Nat.Primes) {q : ℝ × ℂ} (ht : 0 ≤ q.1) :
    ContinuousAt (fun v : ℝ × ℂ => eulerVar v.2 (twist (analyticSmoothingGauge Φ v.1)) p) q := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hpow : Continuous (fun s : ℂ => (p : ℂ) ^ (-s)) := by
    have hd : Differentiable ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) := fun s =>
      (differentiableAt_id.neg).const_cpow (Or.inl hp)
    exact hd.continuous
  change ContinuousAt (fun v : ℝ × ℂ => (p : ℂ) ^ (-v.2) * twist (analyticSmoothingGauge Φ v.1) p) q
  exact (hpow.continuousAt.comp continuous_snd.continuousAt).mul
    ((continuousAt_analyticSmoothing_twist hR hΦ hunit p ht).comp continuous_fst.continuousAt)

private theorem continuousAt_analyticSmoothing_localRem {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    (p : Nat.Primes) {q : ℝ × ℂ} (ht : 0 ≤ q.1) (hs : 1 / 2 < q.2.re) :
    ContinuousAt (fun v : ℝ × ℂ => localRem v.2 (twist (analyticSmoothingGauge Φ v.1)) p) q := by
  have he := continuousAt_analyticSmoothing_eulerVar hR hΦ hunit p ht
  have hslit : 1 - eulerVar q.2 (twist (analyticSmoothingGauge Φ q.1)) p ∈ Complex.slitPlane :=
    one_sub_mem_slitPlane ((norm_eulerVar_le (norm_twist_prime (analyticSmoothingGauge Φ q.1)) p.2 hs).trans_lt
      (by norm_num))
  exact ((continuousAt_const.sub he).clog hslit).neg.sub he

/-- Normal convergence of higher prime powers gives joint continuity, including the Liouville endpoint. -/
theorem continuousAt_analyticSmoothing_hullRem {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 / 2 < s.re) :
    ContinuousAt (fun q : ℝ × ℂ => hullRem q.2 (twist (analyticSmoothingGauge Φ q.1))) (t, s) := by
  let c := (1 / 2 + s.re) / 2
  have hc : 1 / 2 < c := by dsimp [c]; linarith only [hs]
  have hcs : c < s.re := by dsimp [c]; linarith only [hs]
  have ho : IsOpen {q : ℝ × ℂ | c < q.2.re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd)
  have hb := (summable_primes_rpow (show -(2 * c) < -1 by linarith only [hc])).mul_left 2
  change Tendsto (fun q : ℝ × ℂ => ∑' p : Nat.Primes, localRem q.2 (twist (analyticSmoothingGauge Φ q.1)) p)
    (𝓝 (t, s)) (𝓝 (∑' p : Nat.Primes, localRem s (twist (analyticSmoothingGauge Φ t)) p))
  refine tendsto_tsum_of_dominated_convergence hb
    (fun p => (continuousAt_analyticSmoothing_localRem hR hΦ hunit p ht hs).tendsto) ?_
  filter_upwards [ho.mem_nhds hcs] with q hq p
  apply (norm_localRem_le (norm_twist_prime (analyticSmoothingGauge Φ q.1)) p.2 (hc.trans hq)).trans
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le)
  have hqc : c < q.2.re := hq
  linarith only [hqc]

private theorem exp_analyticSmoothing_hullRem_pair {Φ : ℂ → ℂ}
    (h1 : Φ 1 = -1) (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1) :
    Complex.exp (hullRem 1 (twist 0) + hullRem 1 (twist (analyticSmoothingGauge Φ 0))) =
      riemannZeta 2 := by
  have hh : hullRem 1 (twist (analyticSmoothingGauge Φ 0)) =
      hullRem 1 (twist (exponentialPhaseGauge 0)) := by
    unfold hullRem
    apply tsum_congr
    intro p
    have hp : twist (analyticSmoothingGauge Φ 0) p = twist (exponentialPhaseGauge 0) p := by
      rw [← analyticSmoothingPrimePhase_eq_twist hunit (le_refl 0),
        ← exponentialPrimePhase_eq_twist, Complex.ofReal_zero, analyticSmoothingPrimePhase_zero,
        exponentialPrimePhase_zero, h1]
    simp only [localRem, eulerVar, powCoeff, hp]
  rw [hh, exp_liouville_hullRem_pair]

/-- The quadratic scale with the divergent prime logarithm removed. -/
def normalizedAnalyticSmoothingProfile (Φ : ℂ → ℂ) (m : ℕ) (t : ℝ) (w : ℂ) : ℂ :=
  zetaResidueFactor (1 + (t : ℂ) * w) * Complex.exp
    (-analyticSmoothingScalingLog Φ m w + analyticSmoothingScaledRemainder Φ m t w +
      hullRem (1 + (t : ℂ) * w) (twist (analyticSmoothingGauge Φ t)) -
        hullRem (1 + (t : ℂ) * w) (twist 0))

theorem normalizedAnalyticSmoothingProfile_zero {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (h1 : Φ 1 = -1)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1) {m : ℕ} (hbelow : ∀ k < m, smoothingTaylorCoefficient Φ k = 0) (w : ℂ) :
    normalizedAnalyticSmoothingProfile Φ m 0 w = analyticSmoothingScalingProfile Φ m w := by
  rw [normalizedAnalyticSmoothingProfile, Complex.ofReal_zero, zero_mul, add_zero,
    zetaResidueFactor_one, one_mul, analyticSmoothingScaledRemainder_zero hR hΦ h1 hbelow]
  rw [show -analyticSmoothingScalingLog Φ m w + 2 * hullRem 1 (twist 0) +
      hullRem 1 (twist (analyticSmoothingGauge Φ 0)) - hullRem 1 (twist 0) =
      (hullRem 1 (twist 0) + hullRem 1 (twist (analyticSmoothingGauge Φ 0))) +
        -analyticSmoothingScalingLog Φ m w by ring,
    Complex.exp_add, exp_analyticSmoothing_hullRem_pair h1 hunit, analyticSmoothingScalingProfile]

/-- A compact spectral set has a common real parameter interval of continuous normalized values. -/
theorem exists_continuousOn_normalizedAnalyticSmoothingProfile {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1) (m : ℕ) {K : Set ℂ} (hK : IsCompact K)
    (hhalf : K ⊆ {w | -(m : ℝ) < w.re}) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      (∀ t ∈ Icc 0 a, ∀ w ∈ K, 1 / 2 < (1 + (t : ℂ) * w).re) ∧
      ContinuousOn (fun q : ℝ × ℂ => normalizedAnalyticSmoothingProfile Φ m q.1 q.2) (Icc 0 a ×ˢ K) := by
  by_cases hK0 : K = ∅
  · subst K
    refine ⟨1, zero_lt_one, le_rfl, ?_, ?_⟩
    · intro t ht w hw
      exact False.elim hw
    · simp
  have hne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK0
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn (f := fun w : ℂ => ‖w‖) hne continuous_norm.continuousOn
  have hbBound : ∀ w ∈ K, ‖w‖ ≤ ‖b‖ := hmax
  let B := max 1 ‖b‖
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hBw (w : ℂ) (hw : w ∈ K) : ‖w‖ ≤ B := (hbBound w hw).trans (le_max_right _ _)
  let a := 1 / (4 * (B + 1))
  have hden : 0 < 4 * (B + 1) := by linarith only [hB]
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ hden).mpr
    linarith only [hB]
  have hclear : a * (4 * (B + 1)) = 1 := by
    dsimp [a]
    exact div_mul_cancel₀ 1 hden.ne'
  have haB : a * B < 1 / 2 := by nlinarith only [hclear, ha]
  have hspectral (t : ℝ) (ht : t ∈ Icc 0 a) (w : ℂ) (hw : w ∈ K) :
      1 / 2 < (1 + (t : ℂ) * w).re := by
    have hn : ‖(t : ℂ) * w‖ < 1 / 2 := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact ((mul_le_mul_of_nonneg_left (hBw w hw) ht.1).trans
        (mul_le_mul_of_nonneg_right ht.2 hB0)).trans_lt haB
    have hre := Complex.re_le_norm (-((t : ℂ) * w))
    rw [Complex.neg_re, norm_neg] at hre
    simp only [Complex.add_re, Complex.one_re]
    linarith only [hre, hn]
  have hscaled : ContinuousOn (fun q : ℝ × ℂ => analyticSmoothingScaledRemainder Φ m q.1 q.2) (Icc 0 a ×ˢ K) :=
    (continuousOn_analyticSmoothingScaledRemainder hR hΦ m hK hhalf).mono
      (fun q hq => ⟨⟨hq.1.1, hq.1.2.trans ha1⟩, hq.2⟩)
  refine ⟨a, ha, ha1, hspectral, ?_⟩
  intro q hq
  have hs := hspectral q.1 hq.1 q.2 hq.2
  have hm : ContinuousAt (fun v : ℝ × ℂ => 1 + (v.1 : ℂ) * v.2) q := by fun_prop
  have hp : ContinuousAt (fun v : ℝ × ℂ => (v.1, 1 + (v.1 : ℂ) * v.2)) q := by fun_prop
  have hZ := differentiable_zetaResidueFactor.continuous.continuousAt.comp
    (g := zetaResidueFactor) (f := fun v : ℝ × ℂ => 1 + (v.1 : ℂ) * v.2) hm
  have hL := (analyticOnNhd_analyticSmoothingScalingLog hR hΦ m q.2 (hhalf hq.2)).continuousAt.comp
    (g := analyticSmoothingScalingLog Φ m) (f := fun v : ℝ × ℂ => v.2) continuous_snd.continuousAt
  have hH := (continuousAt_analyticSmoothing_hullRem hR hΦ hunit hq.1.1 hs).comp
    (g := fun v : ℝ × ℂ => hullRem v.2 (twist (analyticSmoothingGauge Φ v.1)))
    (f := fun v : ℝ × ℂ => (v.1, 1 + (v.1 : ℂ) * v.2)) hp
  have h0 := (analyticOnNhd_hullRem (norm_twist_prime 0) _ hs).continuousAt.comp
    (g := fun s : ℂ => hullRem s (twist 0)) (f := fun v : ℝ × ℂ => 1 + (v.1 : ℂ) * v.2) hm
  exact hZ.continuousWithinAt.mul
    (((hL.continuousWithinAt.neg.add (hscaled q hq)).add hH.continuousWithinAt).sub
      h0.continuousWithinAt).cexp

/-- The continuously renormalized profile tends uniformly to its exact endpoint value. -/
theorem tendstoUniformlyOn_normalizedAnalyticSmoothingProfile {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (h1 : Φ 1 = -1)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1) {m : ℕ} (hbelow : ∀ k < m, smoothingTaylorCoefficient Φ k = 0) {K : Set ℂ} (hK : IsCompact K)
    (hhalf : K ⊆ {w | -(m : ℝ) < w.re}) :
    TendstoUniformlyOn (normalizedAnalyticSmoothingProfile Φ m) (analyticSmoothingScalingProfile Φ m)
      (𝓝[>] (0 : ℝ)) K := by
  obtain ⟨a, ha, _, _, hc⟩ := exists_continuousOn_normalizedAnalyticSmoothingProfile hR hΦ hunit m hK hhalf
  have hu : TendstoUniformlyOn (normalizedAnalyticSmoothingProfile Φ m) (normalizedAnalyticSmoothingProfile Φ m 0)
      (𝓝[Icc (0 : ℝ) a] 0) K :=
    ((isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc).tendstoUniformlyOn
      ⟨le_rfl, ha.le⟩
  have hu' : TendstoUniformlyOn (normalizedAnalyticSmoothingProfile Φ m) (normalizedAnalyticSmoothingProfile Φ m 0)
      (𝓝[>] (0 : ℝ)) K := fun V hV =>
    Filter.Eventually.filter_mono (nhdsGT_zero_le_Icc ha) (hu V hV)
  have hzero : normalizedAnalyticSmoothingProfile Φ m 0 = analyticSmoothingScalingProfile Φ m :=
    funext (normalizedAnalyticSmoothingProfile_zero hR hΦ h1 hunit hbelow)
  rwa [hzero] at hu'



private theorem summable_analyticSmoothingScaledRemainder {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (m : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    {w : ℂ} (hw : -(m : ℝ) < w.re) :
    Summable (fun n : ℕ => smoothingTaylorCoefficient Φ (n + m) *
      regularizedPrimeLog (1 + (t : ℂ) * (w + ((n + m : ℕ) : ℂ)))) := by
  let η := min (w.re + (m : ℝ)) 1
  let M := max 1 ‖w‖
  have hη : 0 < η := lt_min (by linarith only [hw]) zero_lt_one
  obtain ⟨C, _, hb⟩ := smoothing_regularizedPrimeLog_bound m (η := η) (M := M) hη (min_le_right _ _) (le_max_left _ _)
  apply Summable.of_norm_bounded (summable_smoothingTail_weight hR hΦ m C)
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (hb t ht ht1 w (min_le_left _ _) (le_max_right _ _) n) (norm_nonneg _)

private theorem smoothing_scaling_prime_halfplane (m : ℕ) {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : -(m : ℝ) < w.re) :
    1 < (1 + (t : ℂ) * w).re + (m : ℝ) * t := by
  have hp : 0 < t * (w.re + (m : ℝ)) := mul_pos ht (by linarith only [hw])
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith only [hp]

/-- Exact cancellation of the shifted prime logarithmic divergence. -/
theorem deformationPrimeSum_analyticSmoothing_scaled {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (h1 : Φ 1 = -1)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1) {m : ℕ} (hbelow : ∀ k < m, smoothingTaylorCoefficient Φ k = 0) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {w : ℂ} (hw : -(m : ℝ) < w.re) :
    deformationPrimeSum (analyticSmoothingGauge Φ t) (1 + (t : ℂ) * w) =
      2 * (Real.log t : ℂ) - analyticSmoothingScalingLog Φ m w + analyticSmoothingScaledRemainder Φ m t w := by
  have hE := summable_analyticSmoothingScaledRemainder hR hΦ m ht.le ht1 hw
  have hL := summable_smoothingLogTail hR hΦ m hw
  have hconst := (Summable.of_norm (summable_norm_smoothingTail hR hΦ m)).mul_right (Real.log t : ℂ)
  rw [deformationPrimeSum_analyticSmoothing_shifted hR hΦ hunit hbelow ht.le (smoothing_scaling_prime_halfplane m ht hw)]
  calc
    _ = ∑' n : ℕ, ((smoothingTaylorCoefficient Φ (n + m) *
        regularizedPrimeLog (1 + (t : ℂ) * (w + ((n + m : ℕ) : ℂ))) -
          smoothingTaylorCoefficient Φ (n + m) * Complex.log (w + ((n + m : ℕ) : ℂ))) -
            smoothingTaylorCoefficient Φ (n + m) * (Real.log t : ℂ)) := by
      apply tsum_congr
      intro n
      have hRe : 0 < (w + ((n + m : ℕ) : ℂ)).re := by
        simp only [Complex.add_re, Complex.natCast_re, Nat.cast_add]
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith only [hw, hn]
      have hne : w + ((n + m : ℕ) : ℂ) ≠ 0 := by
        intro hz
        rw [hz, Complex.zero_re] at hRe
        exact lt_irrefl 0 hRe
      have hz : 1 < (1 + (t : ℂ) * (w + ((n + m : ℕ) : ℂ))).re := by
        simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, Complex.natCast_re, Nat.cast_add] at hRe ⊢
        nlinarith only [mul_pos ht hRe]
      have he := regularizedPrimeLog_of_re_gt_one hz
      rw [add_sub_cancel_left, Complex.log_ofReal_mul ht hne] at he
      rw [show 1 + (t : ℂ) * w + ((n + m : ℕ) : ℂ) * (t : ℂ) =
        1 + (t : ℂ) * (w + ((n + m : ℕ) : ℂ)) by ring]
      linear_combination -(smoothingTaylorCoefficient Φ (n + m)) * he
    _ = analyticSmoothingScaledRemainder Φ m t w - analyticSmoothingScalingLog Φ m w -
        (∑' n : ℕ, smoothingTaylorCoefficient Φ (n + m)) * (Real.log t : ℂ) := by
      rw [(hE.sub hL).tsum_sub hconst, hE.tsum_sub hL, tsum_mul_right]
      rfl
    _ = _ := by rw [tsum_smoothingTail hR hΦ h1 hbelow]; ring

/-- The continuous profile is exactly the actual pole regularization divided by `t²`. -/
theorem jointGaugeRegularization_analyticSmoothing_normalized {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (h1 : Φ 1 = -1)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1) {m : ℕ} (hbelow : ∀ k < m, smoothingTaylorCoefficient Φ k = 0) {C : ℝ}
    (hdecay : ∀ p : Nat.Primes, ∀ z : ℂ, 0 ≤ z.re →
      ‖analyticSmoothingPrimePhase Φ p z - 1‖ ≤ C * (p : ℝ) ^ (-((m : ℝ) * z.re))) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {w : ℂ} (hw : -(m : ℝ) < w.re) (hh : 1 / 2 < (1 + (t : ℂ) * w).re) :
    jointGaugeRegularization (analyticSmoothingPrimePhase Φ) ((t : ℂ), 1 + (t : ℂ) * w) / (t : ℂ) ^ 2 =
      normalizedAnalyticSmoothingProfile Φ m t w := by
  have he : deformationExponent (analyticSmoothingGauge Φ t) (1 + (t : ℂ) * w) =
      2 * (Real.log t : ℂ) + (-analyticSmoothingScalingLog Φ m w + analyticSmoothingScaledRemainder Φ m t w +
        hullRem (1 + (t : ℂ) * w) (twist (analyticSmoothingGauge Φ t)) -
          hullRem (1 + (t : ℂ) * w) (twist 0)) := by
    rw [deformationExponent, deformationPrimeSum_analyticSmoothing_scaled hR hΦ h1 hunit hbelow ht ht1 hw]
    ring
  have hexp : Complex.exp (2 * (Real.log t : ℂ)) = (t : ℂ) ^ 2 := by
    simp only [two_mul, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ht, pow_two]
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [jointGaugeRegularization, jointExponent_analyticSmoothing_eq hunit hdecay ht.le (smoothing_scaling_prime_halfplane m ht hw) hh,
    he, Complex.exp_add, hexp, normalizedAnalyticSmoothingProfile]
  field_simp [htC]



/-- The actual regularization converges locally uniformly to the complete Taylor logarithm profile. -/
theorem tendstoLocallyUniformlyOn_analyticSmoothing_quadratic_of_jet {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (h1 : Φ 1 = -1)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    {m : ℕ} (hbelow : ∀ k < m, smoothingTaylorCoefficient Φ k = 0) {C : ℝ}
    (hdecay : ∀ p : Nat.Primes, ∀ z : ℂ, 0 ≤ z.re →
      ‖analyticSmoothingPrimePhase Φ p z - 1‖ ≤ C * (p : ℝ) ^ (-((m : ℝ) * z.re))) :
    TendstoLocallyUniformlyOn
      (fun t : ℝ => fun w : ℂ => jointGaugeRegularization (analyticSmoothingPrimePhase Φ)
        ((t : ℂ), 1 + (t : ℂ) * w) / (t : ℂ) ^ 2)
      (analyticSmoothingScalingProfile Φ m) (𝓝[>] (0 : ℝ)) {w : ℂ | -(m : ℝ) < w.re} := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Complex.continuous_re)).mpr
  intro K hhalf hK
  have hu := tendstoUniformlyOn_normalizedAnalyticSmoothingProfile hR hΦ h1 hunit hbelow hK hhalf
  obtain ⟨a, ha, ha1, hspectral, _⟩ := exists_continuousOn_normalizedAnalyticSmoothingProfile
    hR hΦ hunit m hK hhalf
  intro V hV
  filter_upwards [hu V hV, self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds ha)] with t hlim ht hta
  change 0 < t at ht
  intro w hw
  rw [jointGaugeRegularization_analyticSmoothing_normalized hR hΦ h1 hunit hbelow hdecay
    ht (hta.le.trans ha1) (hhalf hw) (hspectral t ⟨ht.le, hta.le⟩ w hw)]
  exact hlim w hw

/-- Zero coefficients before the leading order identify the tail with the full nonconstant series. -/
theorem analyticSmoothingScalingProfile_eq_full {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (h0 : Φ 0 = 1)
    {m : ℕ} (hbelow : ∀ k < m, smoothingTaylorCoefficient Φ k = 0)
    {w : ℂ} (hw : -(m : ℝ) < w.re) :
    analyticSmoothingScalingProfile Φ m w = riemannZeta 2 * Complex.exp
      (-(∑' n : ℕ, smoothingTaylorCoefficient Φ (n + 1) * Complex.log (w + ((n + 1 : ℕ) : ℂ)))) := by
  have ht := summable_smoothingLogTail hR hΦ m hw
  have hall : Summable (fun n : ℕ => smoothingTaylorCoefficient Φ n * Complex.log (w + (n : ℂ))) :=
    (summable_nat_add_iff m).mp ht
  have hsplit := hall.sum_add_tsum_nat_add m
  have hzero : ∑ k ∈ Finset.range m, smoothingTaylorCoefficient Φ k * Complex.log (w + (k : ℂ)) = 0 :=
    Finset.sum_eq_zero (fun k hk => by rw [hbelow k (Finset.mem_range.mp hk), zero_mul])
  rw [hzero, zero_add] at hsplit
  have hhead := hall.tsum_eq_zero_add
  rw [smoothingTaylorCoefficient_zero hR hΦ h0, zero_mul, zero_add] at hhead
  change riemannZeta 2 * Complex.exp (-analyticSmoothingScalingLog Φ m w) = _
  rw [show analyticSmoothingScalingLog Φ m w = _ from hsplit, hhead]

/-- A limit of the full profile gives the exact nonzero quadratic coefficient of the pole residue. -/
private theorem smoothing_residue_limit {Φ : ℂ → ℂ} {m : ℕ} (hm : 0 < m)
    (hlim : TendstoLocallyUniformlyOn
      (fun t : ℝ => fun w : ℂ => jointGaugeRegularization (analyticSmoothingPrimePhase Φ)
        ((t : ℂ), 1 + (t : ℂ) * w) / (t : ℂ) ^ 2)
      (analyticSmoothingScalingProfile Φ m) (𝓝[>] (0 : ℝ)) {w : ℂ | -(m : ℝ) < w.re}) :
    Tendsto (fun t : ℝ => jointGaugeRegularization (analyticSmoothingPrimePhase Φ) ((t : ℂ), 1) / (t : ℂ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (analyticSmoothingScalingProfile Φ m 0)) := by
  have hsub : ({0} : Set ℂ) ⊆ {w | -(m : ℝ) < w.re} := by
    intro w hw
    have hw0 : w = 0 := Set.mem_singleton_iff.mp hw
    rw [hw0]
    change -(m : ℝ) < 0
    exact neg_neg_of_pos (by exact_mod_cast hm)
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Complex.continuous_re)).mp hlim
      ({0} : Set ℂ) hsub isCompact_singleton
  have hzero := tendstoUniformlyOn_singleton_iff_tendsto.mp hu
  simpa only [mul_zero, add_zero] using hzero

/-- Every analytic unit-modulus smoothing has the same quadratic scale and a nonpolynomial full limit. -/
theorem analyticSmoothing_universal_quadratic_profile {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (h0 : Φ 0 = 1) (h1 : Φ 1 = -1)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : ℝ, b ≠ 0 ∧
      smoothingTaylorCoefficient Φ m = (b : ℂ) * I ∧
      (∀ k < m, smoothingTaylorCoefficient Φ k = 0) ∧
      AnalyticOnNhd ℂ (analyticSmoothingScalingProfile Φ m) {w | -(m : ℝ) < w.re} ∧
      (∀ w : ℂ, analyticSmoothingScalingProfile Φ m w ≠ 0) ∧
      (¬ ∃ P : Polynomial ℂ, ∀ w : ℂ, -(m : ℝ) < w.re →
        analyticSmoothingScalingProfile Φ m w = P.eval w) ∧
      (∀ w : ℂ, -(m : ℝ) < w.re →
        analyticSmoothingScalingProfile Φ m w = riemannZeta 2 * Complex.exp
          (-(∑' n : ℕ, smoothingTaylorCoefficient Φ (n + 1) * Complex.log (w + ((n + 1 : ℕ) : ℂ))))) ∧
      TendstoLocallyUniformlyOn
        (fun t : ℝ => fun w : ℂ => jointGaugeRegularization (analyticSmoothingPrimePhase Φ)
          ((t : ℂ), 1 + (t : ℂ) * w) / (t : ℂ) ^ 2)
        (analyticSmoothingScalingProfile Φ m) (𝓝[>] (0 : ℝ)) {w : ℂ | -(m : ℝ) < w.re} ∧
      Tendsto (fun t : ℝ => jointGaugeRegularization (analyticSmoothingPrimePhase Φ) ((t : ℂ), 1) / (t : ℂ) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (analyticSmoothingScalingProfile Φ m 0)) := by
  obtain ⟨m, hm, b, hb, G, hG, hG0, hfac, hcoeff, hbelow, C, hC, hrem⟩ :=
    analyticPhase_first_jet hR hΦ h0 h1 hunit
  obtain ⟨D, hD, hdecay⟩ := analyticSmoothingPrimePhase_decay_of_factor hR hG hfac
  have hlim := tendstoLocallyUniformlyOn_analyticSmoothing_quadratic_of_jet hR hΦ h1 hunit hbelow hdecay
  exact ⟨m, hm, b, hb, hcoeff, hbelow,
    analyticOnNhd_analyticSmoothingScalingProfile hR hΦ m,
    analyticSmoothingScalingProfile_ne_zero Φ m,
    analyticSmoothingScalingProfile_not_polynomial hR hΦ hb hcoeff,
    fun w hw => analyticSmoothingScalingProfile_eq_full hR hΦ h0 hbelow hw,
    hlim, smoothing_residue_limit hm hlim⟩

/-- The nonzero interior residues converge to zero at the Liouville endpoint. -/
theorem tendsto_analyticSmoothing_residue_zero {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (h0 : Φ 0 = 1) (h1 : Φ 1 = -1)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1) :
    Tendsto (fun t : ℝ => jointGaugeRegularization (analyticSmoothingPrimePhase Φ) ((t : ℂ), 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨m, _, b, _, _, _, _, _, _, _, _, hlim⟩ :=
    analyticSmoothing_universal_quadratic_profile hR hΦ h0 h1 hunit
  have ht : Tendsto (fun t : ℝ => (t : ℂ) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hbase : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [Complex.ofReal_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hbase.pow 2
  have hp : Tendsto (fun t : ℝ =>
      (jointGaugeRegularization (analyticSmoothingPrimePhase Φ) ((t : ℂ), 1) / (t : ℂ) ^ 2) * (t : ℂ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using hlim.mul ht
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  exact div_mul_cancel₀ _ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt htpos)))

#print axioms analyticOnNhd_analyticSmoothingScalingProfile
#print axioms analyticSmoothingScalingProfile_not_polynomial
#print axioms deformationPrimeSum_analyticSmoothing_shifted
#print axioms continuousAt_analyticSmoothing_hullRem
#print axioms analyticSmoothing_universal_quadratic_profile
#print axioms tendsto_analyticSmoothing_residue_zero

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
