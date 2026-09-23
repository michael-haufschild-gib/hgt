import GaloisForLFunctions.RHTower.XiMassTwoRapiditySourceOrderNoGo
import GaloisForLFunctions.RHTower.XiMassTwoRapidityStationaryPairPositivity
import GaloisForLFunctions.RHTower.XiMassCriticalCenteredAtomCone

/-!
# Centered source-order obstruction for the T1 rapidity covariance

Subtracting the integer vacuum changes the prime weights from `Λ(n)` to `Λ(n)-1`.
This changes the sign of the prime-two weight, but every prime at least three still has a
strictly positive weight.  Thus the literal `3 × 5` stationary pair remains anti-ordered
and nonzero after centering.  A termwise source-order rule cannot bound the centered cone.
-/

open Complex Filter MeasureTheory

namespace RHTower

noncomputable section

/-- The exact centered coefficient in the mass-rapidity cone. -/
def xiMassCriticalCenteredConeRapidityWeight (a : ℝ) (k : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt (k + 2) - 1 : ℝ) : ℂ) *
    ((Real.exp (-Real.log ((k : ℝ) + 2) / 2) : ℝ) : ℂ) * (a : ℂ)

/-- The literal centered atom cone before the rapidity integral. -/
def xiMassCriticalCenteredConeRapidityKernel (a sigma d u t : ℝ) : ℂ :=
  ∑ k ∈ xiMassCriticalPrimeConeIndexSet d u,
    xiMassCriticalCenteredConeRapidityWeight a k *
      xiMassRapidityPhaseKernel a sigma u (Real.log ((k : ℝ) + 2)) t

/-- The centered source, not an auxiliary signed model, is this rapidity integral. -/
theorem xiMassCriticalCenteredAtomConeSum_eq_integral_rapidityKernel
    {a sigma d u : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    xiMassCriticalCenteredAtomConeSum a sigma d u =
      ∫ t : ℝ, xiMassCriticalCenteredConeRapidityKernel a sigma d u t := by
  unfold xiMassCriticalCenteredAtomConeSum
    xiMassCriticalCenteredConeRapidityKernel xiMassCriticalPrimeConeIndexSet
  rw [MeasureTheory.integral_finsetSum _ (by
    intro k _
    exact (integrable_xiMassRapidityPhaseKernel ha hsigma).const_mul
      (xiMassCriticalCenteredConeRapidityWeight a k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [xiMassCriticalDampedFourierProfile_eq_integral_rapidityPhase ha hsigma,
    MeasureTheory.integral_const_mul]
  simp only [xiMassCriticalCenteredConeRapidityWeight]
  ring

/-- Every true-prime centered weight from prime three onward is positive. -/
theorem xiMassCriticalCenteredConeRapidityWeight_re_pos_of_prime_ge_three
    {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : (k + 2).Prime) (hthree : 3 ≤ k + 2) :
    0 < (xiMassCriticalCenteredConeRapidityWeight a k).re := by
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    linarith [Real.log_three_gt_d9]
  have hthreeR : (3 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast hthree
  have hlog : 1 < Real.log ((k + 2 : ℕ) : ℝ) :=
    lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hthreeR)
  unfold xiMassCriticalCenteredConeRapidityWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime hk]
  have hcast : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hlog
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  have hfactor : 0 < Real.log ((k : ℝ) + 2) - 1 := sub_pos.mpr hlog
  rw [hcast]
  exact mul_pos (mul_pos hfactor (Real.exp_pos _)) ha

/-- One centered labelled term of the exact two-rapidity covariance. -/
def xiMassCriticalCenteredConeTwoRapidityTerm
    (a sigma u : ℝ) (i j : ℕ) (t s : ℝ) : ℂ :=
  xiMassCriticalCenteredConeRapidityWeight a i *
      (starRingEnd ℂ) (xiMassCriticalCenteredConeRapidityWeight a j) *
        xiMassTwoRapidityCorrelationAmplitude a sigma t s *
          Complex.exp (-(Complex.I * ((a * xiMassTwoRapidityCorrelationPhase u
            (Real.log ((i : ℝ) + 2)) (Real.log ((j : ℝ) + 2)) t s : ℝ) : ℂ)))

/-- All signed prime/integer-vacuum channels of the physical centered covariance. -/
def xiMassCriticalCenteredConeTwoRapidityCovariance
    (a sigma d u t s : ℝ) : ℂ :=
  ∑ i ∈ xiMassCriticalPrimeConeIndexSet d u,
    ∑ j ∈ xiMassCriticalPrimeConeIndexSet d u,
      xiMassCriticalCenteredConeTwoRapidityTerm a sigma u i j t s

/-- The centered Hermitian square retains every signed two-rapidity channel. -/
theorem xiMassCriticalCenteredConeRapidityKernel_mul_star_eq_covariance
    (a sigma d u t s : ℝ) :
    xiMassCriticalCenteredConeRapidityKernel a sigma d u t *
      (starRingEnd ℂ) (xiMassCriticalCenteredConeRapidityKernel a sigma d u s) =
        xiMassCriticalCenteredConeTwoRapidityCovariance a sigma d u t s := by
  unfold xiMassCriticalCenteredConeRapidityKernel
    xiMassCriticalCenteredConeTwoRapidityCovariance
  rw [map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]
  calc
    _ = (xiMassCriticalCenteredConeRapidityWeight a i *
        (starRingEnd ℂ) (xiMassCriticalCenteredConeRapidityWeight a j)) *
      (xiMassRapidityPhaseKernel a sigma u (Real.log ((i : ℝ) + 2)) t *
        (starRingEnd ℂ) (xiMassRapidityPhaseKernel a sigma u
          (Real.log ((j : ℝ) + 2)) s)) := by ring
    _ = _ := by
      rw [xiMassRapidityPhaseKernel_mul_star_eq_twoRapidityCorrelation]
      unfold xiMassCriticalCenteredConeTwoRapidityTerm
      ring

/-- Exact product-measure covariance of the RH-equivalent centered atom source. -/
theorem xiMassCriticalCenteredAtomConeSum_mul_star_eq_covariance
    {a sigma d u : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    xiMassCriticalCenteredAtomConeSum a sigma d u *
      (starRingEnd ℂ) (xiMassCriticalCenteredAtomConeSum a sigma d u) =
        ∫ z : ℝ × ℝ, xiMassCriticalCenteredConeTwoRapidityCovariance
          a sigma d u z.1 z.2 := by
  rw [xiMassCriticalCenteredAtomConeSum_eq_integral_rapidityKernel ha hsigma,
    ← integral_conj, ← MeasureTheory.integral_prod_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  exact xiMassCriticalCenteredConeRapidityKernel_mul_star_eq_covariance
    a sigma d u z.1 z.2

/-- Positive centered weights give a nonzero labelled covariance term at every rapidity pair. -/
theorem xiMassCriticalCenteredConeTwoRapidityTerm_ne_zero_of_pos
    {a : ℝ} {i j : ℕ}
    (hi : 0 < (xiMassCriticalCenteredConeRapidityWeight a i).re)
    (hj : 0 < (xiMassCriticalCenteredConeRapidityWeight a j).re)
    (sigma u t s : ℝ) :
    xiMassCriticalCenteredConeTwoRapidityTerm a sigma u i j t s ≠ 0 := by
  unfold xiMassCriticalCenteredConeTwoRapidityTerm
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · intro h
        simp [h] at hi
      · have hjne : xiMassCriticalCenteredConeRapidityWeight a j ≠ 0 := by
          intro h
          simp [h] at hj
        simpa using hjne
    · exact xiMassTwoRapidityCorrelationAmplitude_ne_zero a sigma t s
  · exact Complex.exp_ne_zero _

private theorem xiMassCriticalCenteredConeRapidityWeight_eq_ofReal (a : ℝ) (k : ℕ) :
    xiMassCriticalCenteredConeRapidityWeight a k =
      ((ArithmeticFunction.vonMangoldt (k + 2) - 1) *
        Real.exp (-Real.log ((k : ℝ) + 2) / 2) * a : ℝ) := by
  unfold xiMassCriticalCenteredConeRapidityWeight
  push_cast
  ring

/-- The real part of a centered labelled cell is its signed weight product times cosine. -/
theorem xiMassCriticalCenteredConeTwoRapidityTerm_re_eq
    (a sigma u : ℝ) (i j : ℕ) (t s : ℝ) :
    (xiMassCriticalCenteredConeTwoRapidityTerm a sigma u i j t s).re =
      (xiMassCriticalCenteredConeRapidityWeight a i).re *
        (xiMassCriticalCenteredConeRapidityWeight a j).re *
          (xiMassTwoRapidityCorrelationAmplitude a sigma t s).re *
            Real.cos (a * xiMassTwoRapidityCorrelationPhase u
              (Real.log ((i : ℝ) + 2)) (Real.log ((j : ℝ) + 2)) t s) := by
  unfold xiMassCriticalCenteredConeTwoRapidityTerm
  rw [xiMassCriticalCenteredConeRapidityWeight_eq_ofReal,
    xiMassCriticalCenteredConeRapidityWeight_eq_ofReal]
  unfold xiMassTwoRapidityCorrelationAmplitude
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, add_zero]
  rw [show -(Complex.I *
      ((a * xiMassTwoRapidityCorrelationPhase u (Real.log ((i : ℝ) + 2))
        (Real.log ((j : ℝ) + 2)) t s : ℝ) : ℂ)) =
        ((-(a * xiMassTwoRapidityCorrelationPhase u (Real.log ((i : ℝ) + 2))
          (Real.log ((j : ℝ) + 2)) t s) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]
  rw [Real.cos_neg]

/-- The centered `3 × 5` saddle has positive real part at sufficiently deep common mass. -/
theorem xiMassCriticalCenteredCone_three_five_timelike_stationary_term_re_pos
    {a sigma u : ℝ} (ha : 0 < a) (hu : 0 < u)
    (hlog3 : 0 ≤ Real.log 3) (hlog5 : 0 ≤ Real.log 5)
    (h35 : Real.log 3 < Real.log 5)
    (h3u : Real.log 3 < u) (h5u : Real.log 5 < u)
    (hdeep : 2 * Real.log 5 ≤ u)
    (hphase : a * (2 * (Real.log 5) ^ (2 : ℕ) / u) < Real.pi / 2) :
    0 < (xiMassCriticalCenteredConeTwoRapidityTerm a sigma u 1 3
      (-timelikeRapidity u (Real.log 3))
      (-timelikeRapidity u (Real.log 5))).re := by
  have hPhi :
      0 < xiMassTwoRapidityCorrelationPhase u (Real.log 3) (Real.log 5)
        (-timelikeRapidity u (Real.log 3)) (-timelikeRapidity u (Real.log 5)) :=
    xiMassTwoRapidityCorrelationPhase_at_timelike_stationary_pos
      hu hlog3 hlog5 h3u h5u h35
  have hPhi_le :
      xiMassTwoRapidityCorrelationPhase u (Real.log 3) (Real.log 5)
        (-timelikeRapidity u (Real.log 3)) (-timelikeRapidity u (Real.log 5)) ≤
        2 * (Real.log 5) ^ (2 : ℕ) / u :=
    xiMassTwoRapidityCorrelationPhase_at_timelike_stationary_le
      hu hlog3 hlog5 h3u h5u h35 hdeep
  have hcos : 0 < Real.cos (a * xiMassTwoRapidityCorrelationPhase u
      (Real.log 3) (Real.log 5)
      (-timelikeRapidity u (Real.log 3)) (-timelikeRapidity u (Real.log 5))) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos, mul_pos ha hPhi]
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hPhi_le ha.le) hphase
  rw [xiMassCriticalCenteredConeTwoRapidityTerm_re_eq]
  norm_num
  exact mul_pos (mul_pos
    (mul_pos
      (xiMassCriticalCenteredConeRapidityWeight_re_pos_of_prime_ge_three
        ha (by norm_num) (by norm_num))
      (xiMassCriticalCenteredConeRapidityWeight_re_pos_of_prime_ge_three
        ha (by norm_num) (by norm_num)))
    (xiMassTwoRapidityCorrelationAmplitude_re_pos a sigma _ _)) hcos

/-- The positive centered anti-ordered saddle persists cofinally. -/
theorem eventually_xiMassCriticalCenteredCone_three_five_stationary_term_re_pos
    {a sigma : ℝ} (ha : 0 < a) :
    ∀ᶠ u : ℝ in atTop,
      0 < (xiMassCriticalCenteredConeTwoRapidityTerm a sigma u 1 3
        (-timelikeRapidity u (Real.log 3))
        (-timelikeRapidity u (Real.log 5))).re := by
  have hsmall : Tendsto
      (fun u : ℝ => (2 * a * (Real.log 5) ^ (2 : ℕ)) / u)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hphase : ∀ᶠ u : ℝ in atTop,
      a * (2 * (Real.log 5) ^ (2 : ℕ) / u) < Real.pi / 2 := by
    have h := hsmall.eventually (Iio_mem_nhds (half_pos Real.pi_pos))
    filter_upwards [h] with u hu
    simpa only [← mul_div_assoc, mul_assoc, mul_left_comm, mul_comm] using hu
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have h35 : Real.log 3 < Real.log 5 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_gt_atTop (2 * Real.log 5),
    eventually_gt_atTop (Real.log 5), hphase] with u hdeep h5u hphase
  exact xiMassCriticalCenteredCone_three_five_timelike_stationary_term_re_pos ha
    (lt_trans (Real.log_pos (by norm_num)) h5u) hlog3 hlog5 h35
    (h35.trans h5u) h5u hdeep.le hphase

/-- The termwise same-order hypothesis for the centered cone. -/
def XiMassCriticalCenteredConeTermwiseSameOrderSupported (a sigma d u : ℝ) : Prop :=
  ∀ i ∈ xiMassCriticalPrimeConeIndexSet d u, ∀ j ∈ xiMassCriticalPrimeConeIndexSet d u,
    ∀ t s : ℝ, xiMassCriticalCenteredConeTwoRapidityTerm a sigma u i j t s ≠ 0 →
      0 ≤ (Real.log ((i : ℝ) + 2) - Real.log ((j : ℝ) + 2)) * (t - s)

/-- The centered `3 × 5` pair remains a nonzero anti-ordered stationary cell. -/
theorem not_xiMassCriticalCenteredConeTermwiseSameOrderSupported_of_three_five_mem
    {a sigma d u : ℝ} (ha : 0 < a) (hu : Real.log 5 < u)
    (hthree : 1 ∈ xiMassCriticalPrimeConeIndexSet d u)
    (hfive : 3 ∈ xiMassCriticalPrimeConeIndexSet d u) :
    ¬ XiMassCriticalCenteredConeTermwiseSameOrderSupported a sigma d u := by
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have h35 : Real.log 3 < Real.log 5 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hu0 : 0 < u := lt_of_le_of_lt h5 hu
  obtain ⟨t, s, hstat⟩ := exists_xiMassTwoRapidityCorrelationStationary
    hu0 h3 h5 (lt_trans h35 hu) hu
  have hneg : (Real.log 3 - Real.log 5) * (t - s) < 0 :=
    hstat.frequency_rapidity_orientation_neg hu0 (ne_of_lt h35)
  have hterm : xiMassCriticalCenteredConeTwoRapidityTerm a sigma u 1 3 t s ≠ 0 :=
    xiMassCriticalCenteredConeTwoRapidityTerm_ne_zero_of_pos
      (xiMassCriticalCenteredConeRapidityWeight_re_pos_of_prime_ge_three ha
        (by norm_num) (by norm_num))
      (xiMassCriticalCenteredConeRapidityWeight_re_pos_of_prime_ge_three ha
        (by norm_num) (by norm_num)) sigma u t s
  intro hsame
  have hnonneg := hsame 1 hthree 3 hfive t s hterm
  norm_num at hnonneg
  exact (not_le_of_gt hneg) hnonneg

/-- Every physical moving cone eventually retains the centered anti-ordered `3 × 5` cell. -/
theorem eventually_not_xiMassCriticalCenteredConeTermwiseSameOrderSupported
    {a sigma d : ℝ} (ha : 0 < a) (hd : 1 / 2 < d) :
    ∀ᶠ u : ℝ in atTop,
      ¬ XiMassCriticalCenteredConeTermwiseSameOrderSupported a sigma d u := by
  have hcoef : 0 < d / (d - 1 / 2) := by
    apply div_pos <;> linarith
  have harg : Tendsto (fun u : ℝ => d * u / (d - 1 / 2)) atTop atTop := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, id_eq] using
      tendsto_id.const_mul_atTop hcoef
  have hexp : Tendsto (fun u : ℝ => Real.exp (d * u / (d - 1 / 2)))
      atTop atTop := Real.tendsto_exp_atTop.comp harg
  filter_upwards [hexp.eventually (eventually_ge_atTop (7 : ℝ)),
    eventually_gt_atTop (Real.log 5)] with u hucone hu
  have hfloor : 7 ≤ ⌊Real.exp (d * u / (d - 1 / 2))⌋₊ := Nat.le_floor hucone
  have hthree : 1 ∈ xiMassCriticalPrimeConeIndexSet d u := by
    rw [xiMassCriticalPrimeConeIndexSet, Finset.mem_range]
    omega
  have hfive : 3 ∈ xiMassCriticalPrimeConeIndexSet d u := by
    rw [xiMassCriticalPrimeConeIndexSet, Finset.mem_range]
    omega
  exact not_xiMassCriticalCenteredConeTermwiseSameOrderSupported_of_three_five_mem
    ha hu hthree hfive

end

end RHTower
