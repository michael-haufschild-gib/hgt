import GaloisForLFunctions.HTGeometry.HalfLineSteinRobertson
import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenBootstrap

/-!
# Robin anomalous Stein--Ward values of the theta Born--Witten state

The translation generator on the half-line retains its endpoint contact current.  Applying the
anomaly-corrected Stein identity to the exact theta Born--Witten density gives an all-order
recurrence between mixed position--superpotential values and the existing Morse Born moments.

For the first atom the superpotential is negative at the boundary.  Thus the mixed Ward values
are nonnegative by their exact recurrence, but their integrand is not a positive measure density;
ordinary Stieltjes/Hankel positivity cannot be applied directly to them.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The superpotential-weighted density is a first logarithmic-derivative atom. -/
theorem thetaCuspBornWittenSuperpotential_mul_amplitude_sq_eq_polynomialAtom
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    thetaCuspBornWittenSuperpotential n x *
        thetaCuspBornWittenAmplitude n x ^ (2 : ℕ) =
      -(2 * Real.pi)⁻¹ *
        thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 1) n x := by
  have heq :
      (fun y : ℝ => thetaCuspSourceTerm y n) =ᶠ[nhds x]
        fun y : ℝ => Real.pi * thetaCuspBornWittenAmplitude n y ^ (2 : ℕ) := by
    filter_upwards [show ∀ᶠ y : ℝ in nhds x, y ∈ Ioi 0 from Ioi_mem_nhds hx] with y hy
    exact thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq hn hy.le
  have hamp : HasDerivAt
      (fun y : ℝ => Real.pi * thetaCuspBornWittenAmplitude n y ^ (2 : ℕ))
      (Real.pi * (-2 * thetaCuspBornWittenSuperpotential n x *
        thetaCuspBornWittenAmplitude n x ^ (2 : ℕ))) x :=
    (hasDerivAt_thetaCuspBornWittenAmplitude_sq hn hx.le).const_mul Real.pi
  have hsourceFromAmp := hamp.congr_of_eventuallyEq heq
  have hsourcePoly : HasDerivAt (fun y : ℝ => thetaCuspSourceTerm y n)
      (thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 1) n x) x := by
    rw [thetaCuspSourceTerm_eq_polynomialAtom]
    simpa only [thetaCuspLogDerivativePolynomial] using
      hasDerivAt_thetaCuspPolynomialAtom thetaCuspSeedPolynomial n x
  have hunique := hsourcePoly.unique hsourceFromAmp
  field_simp [Real.pi_ne_zero]
  nlinarith

/-- Every polynomially weighted Born--Witten density is integrable on the half-line. -/
theorem integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq
    (m : ℕ) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ =>
      x ^ m * thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) (Ioi 0) := by
  have hsource := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    m thetaCuspSeedPolynomial hn
  have hscaled := hsource.const_mul (Real.pi)⁻¹
  apply hscaled.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [← congrFun (thetaCuspSourceTerm_eq_polynomialAtom n) x,
    thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq hn hx.le]
  field_simp [Real.pi_ne_zero]

/-- Polynomially weighted mixed superpotential values need no extra integrability hypothesis. -/
theorem integrableOn_pow_mul_thetaCuspBornWittenSuperpotential_mul_amplitude_sq
    (m : ℕ) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ =>
      x ^ m * thetaCuspBornWittenSuperpotential n x *
        thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) (Ioi 0) := by
  have hpoly := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    m (thetaCuspLogDerivativePolynomial 1) hn
  have hscaled := hpoly.const_mul (-(2 * Real.pi)⁻¹)
  apply hscaled.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  calc
    -(2 * Real.pi)⁻¹ *
        (x ^ m * thetaCuspPolynomialAtom
          (thetaCuspLogDerivativePolynomial 1) n x) =
        x ^ m * (-(2 * Real.pi)⁻¹ *
          thetaCuspPolynomialAtom
            (thetaCuspLogDerivativePolynomial 1) n x) := by ring
    _ = x ^ m * (thetaCuspBornWittenSuperpotential n x *
          thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) := by
      rw [← thetaCuspBornWittenSuperpotential_mul_amplitude_sq_eq_polynomialAtom hn hx]
    _ = x ^ m * thetaCuspBornWittenSuperpotential n x *
          thetaCuspBornWittenAmplitude n x ^ (2 : ℕ) := by ring

/-- Polynomially weighted Born--Witten densities have zero current at infinity. -/
theorem pow_mul_thetaCuspBornWittenAmplitude_sq_tendsto_atTop_zero
    (m : ℕ) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun x : ℝ =>
      x ^ m * thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) atTop (nhds 0) := by
  have hsource : Tendsto (fun x : ℝ => x ^ m * thetaCuspSourceTerm x n)
      atTop (nhds 0) := by
    simpa only [← congrFun (thetaCuspSourceTerm_eq_polynomialAtom n)] using
      pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
        m thetaCuspSeedPolynomial hn
  have hscaled := hsource.const_mul (Real.pi)⁻¹
  have hscaled' : Tendsto
      (fun x : ℝ => (Real.pi)⁻¹ * (x ^ m * thetaCuspSourceTerm x n))
      atTop (nhds 0) := by
    simpa using hscaled
  apply hscaled'.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq hn hx]
  field_simp [Real.pi_ne_zero]

/-- Half-line anomalous translation Ward identity.  Degree zero retains the Robin contact charge;
all positive monomials have zero endpoint current. -/
theorem thetaCuspBornWitten_monomial_anomalousSteinWard
    (m : ℕ) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ in Ioi 0,
        x ^ m * thetaCuspBornWittenSuperpotential n x *
          thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) =
      (1 / 2 : ℝ) *
        ((if m = 0 then thetaCuspBornWittenAmplitude n 0 ^ (2 : ℕ) else 0) +
          ∫ x : ℝ in Ioi 0,
            (m : ℝ) * x ^ (m - 1) *
              thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) := by
  have hright : IntegrableOn (fun x : ℝ =>
      ((m : ℝ) * x ^ (m - 1)) * 1 *
        thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) (Ioi 0) := by
    have h := (integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq
      (m - 1) hn).const_mul (m : ℝ)
    exact IntegrableOn.congr_fun h (fun x _ => by ring) measurableSet_Ioi
  have hboundary : Tendsto (fun x : ℝ =>
      x ^ m * 1 * thetaCuspBornWittenAmplitude n x ^ (2 : ℕ))
      (nhdsWithin 0 (Ioi 0))
      (nhds (if m = 0 then thetaCuspBornWittenAmplitude n 0 ^ (2 : ℕ) else 0)) := by
    have hcont : ContinuousAt (fun x : ℝ =>
        x ^ m * 1 * thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) 0 :=
      ((continuousAt_id.pow m).mul continuousAt_const).mul
        ((hasDerivAt_thetaCuspBornWittenAmplitude hn (by norm_num)).continuousAt.pow 2)
    have ht : Tendsto (fun x : ℝ =>
        x ^ m * 1 * thetaCuspBornWittenAmplitude n x ^ (2 : ℕ))
        (nhdsWithin 0 (Ioi 0))
        (nhds (0 ^ m * 1 * thetaCuspBornWittenAmplitude n 0 ^ (2 : ℕ))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    cases m with
    | zero => simpa using ht
    | succ m => simpa using ht
  have hinfty : Tendsto (fun x : ℝ =>
      x ^ m * 1 * thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) atTop (nhds 0) := by
    simpa only [mul_one] using
      pow_mul_thetaCuspBornWittenAmplitude_sq_tendsto_atTop_zero m hn
  have h := HTGeometry.integral_Ioi_mul_halfLineSteinScore_with_boundary
    (f := fun x : ℝ => x ^ m)
    (f' := fun x : ℝ => (m : ℝ) * x ^ (m - 1))
    (P := fun _ : ℝ => 1) (P' := fun _ : ℝ => 0)
    (ρ := fun x : ℝ => thetaCuspBornWittenAmplitude n x ^ (2 : ℕ))
    (W := thetaCuspBornWittenSuperpotential n)
    (c := if m = 0 then thetaCuspBornWittenAmplitude n 0 ^ (2 : ℕ) else 0)
    (fun x _ => hasDerivAt_pow m x)
    (fun x _ => hasDerivAt_const x 1)
    (fun x hx => hasDerivAt_thetaCuspBornWittenAmplitude_sq hn hx.le)
    (by
      simpa only [HTGeometry.halfLineSteinScore, one_mul, zero_div, sub_zero,
        mul_assoc] using
        integrableOn_pow_mul_thetaCuspBornWittenSuperpotential_mul_amplitude_sq m hn)
    hright hboundary hinfty
  simpa only [HTGeometry.halfLineSteinScore, one_mul, zero_div, sub_zero,
    mul_assoc] using h

/-- The translation Ward identity at degree zero is exactly the Robin contact charge. -/
theorem thetaCuspBornWitten_translation_contact_charge {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ in Ioi 0,
        thetaCuspBornWittenSuperpotential n x *
          thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) =
      (1 / 2 : ℝ) * thetaCuspBornWittenAmplitude n 0 ^ (2 : ℕ) := by
  simpa only [pow_zero, one_mul, if_pos, Nat.cast_zero, Nat.zero_sub,
    zero_mul, integral_zero, add_zero] using
    thetaCuspBornWitten_monomial_anomalousSteinWard 0 hn

/-- Odd superpotential values are exactly scaled existing Born moments. -/
theorem thetaCuspBornWitten_odd_superpotential_moment
    (j : ℕ) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ in Ioi 0,
        x ^ (2 * j + 1) * thetaCuspBornWittenSuperpotential n x *
          thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) =
      ((2 * j + 1 : ℕ) : ℝ) / 2 * thetaCuspMorseBornMoment j n := by
  have h := thetaCuspBornWitten_monomial_anomalousSteinWard (2 * j + 1) hn
  rw [if_neg (by omega : 2 * j + 1 ≠ 0)] at h
  simp only [zero_add] at h
  rw [show 2 * j + 1 - 1 = 2 * j by omega] at h
  rw [show (∫ x : ℝ in Ioi 0,
      ((2 * j + 1 : ℕ) : ℝ) * x ^ (2 * j) *
        thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) =
      ((2 * j + 1 : ℕ) : ℝ) *
        ∫ x : ℝ in Ioi 0,
          x ^ (2 * j) * thetaCuspBornWittenAmplitude n x ^ (2 : ℕ) by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring] at h
  rw [← thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq] at h
  linarith

/-- Odd mixed position--superpotential value of one exact theta Born--Witten state. -/
def thetaCuspBornWittenSuperpotentialMoment (j n : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    x ^ (2 * j + 1) * thetaCuspBornWittenSuperpotential n x *
      thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)

theorem thetaCuspBornWittenSuperpotentialMoment_eq_morseBornMoment
    (j : ℕ) {n : ℕ} (hn : 0 < n) :
    thetaCuspBornWittenSuperpotentialMoment j n =
      ((2 * j + 1 : ℕ) : ℝ) / 2 * thetaCuspMorseBornMoment j n :=
  thetaCuspBornWitten_odd_superpotential_moment j hn

theorem thetaCuspBornWittenSuperpotentialMoment_nonneg
    (j : ℕ) {n : ℕ} (hn : 0 < n) :
    0 ≤ thetaCuspBornWittenSuperpotentialMoment j n := by
  rw [thetaCuspBornWittenSuperpotentialMoment_eq_morseBornMoment j hn]
  exact mul_nonneg (by positivity) (thetaCuspMorseBornMoment_nonneg j hn)

/-- Exact Ward-coordinate form of the independent first-atom relaxed fourth-moment condition. -/
theorem thetaCusp_firstAtom_relaxed_iff_superpotentialMoment :
    16 * ((3005 / 2997 : ℝ) * thetaCuspMorseBornMoment 0 1) *
          ((3005 / 2997 : ℝ) * thetaCuspMorseBornMoment 2 1) ≤
        45 * thetaCuspMorseBornMoment 1 1 ^ (2 : ℕ) ↔
      16 * (3005 / 2997 : ℝ) ^ (2 : ℕ) *
          thetaCuspBornWittenSuperpotentialMoment 0 1 *
            thetaCuspBornWittenSuperpotentialMoment 2 1 ≤
        25 * thetaCuspBornWittenSuperpotentialMoment 1 1 ^ (2 : ℕ) := by
  rw [thetaCuspBornWittenSuperpotentialMoment_eq_morseBornMoment 0 (by norm_num),
    thetaCuspBornWittenSuperpotentialMoment_eq_morseBornMoment 1 (by norm_num),
    thetaCuspBornWittenSuperpotentialMoment_eq_morseBornMoment 2 (by norm_num)]
  norm_num
  constructor <;> intro h <;> nlinarith

/-- The first Robin superpotential has a genuinely negative boundary value.  Consequently its
mixed Ward integrand is not a positive measure density. -/
theorem thetaCuspFirstBornWittenSuperpotential_zero_neg :
    thetaCuspBornWittenSuperpotential 1 0 < 0 := by
  have hden : 0 < Real.pi - 3 / 2 := by
    nlinarith [Real.pi_gt_three]
  have hpiSq : Real.pi ^ (2 : ℕ) < (3.1416 : ℝ) ^ (2 : ℕ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hpoly :
      (Real.pi - 5 / 4) * (Real.pi - 3 / 2) < Real.pi := by
    nlinarith [Real.pi_gt_d4]
  simp only [thetaCuspBornWittenSuperpotential,
    thetaCuspMorseSuperpotential, thetaCuspBornWittenWeight_eq,
    thetaCuspMorseScale, Nat.cast_one, one_mul, Real.exp_zero, one_pow]
  rw [sub_lt_zero]
  norm_num only [mul_one]
  rw [lt_div_iff₀ hden]
  exact hpoly

/-- Direct Ward-coordinate interface to the linear prime-archimedean Hankel consumer.  The upper
radial condition is unchanged; the independent relaxed condition is exposed in the exact mixed
superpotential values selected by the anomalous translation identity. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_bornWittenSuperpotentialMoment
    (hupper :
      14 * ((3005 / 2997 : ℝ) *
          (∫ x : ℝ in Ioi 0,
            x ^ (4 : ℕ) * thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ))) ^ (2 : ℕ) ≤
        9 *
          (∫ x : ℝ in Ioi 0,
            x ^ (2 : ℕ) * thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ)) *
          (∫ x : ℝ in Ioi 0,
            x ^ (6 : ℕ) * thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ)))
    (hward :
      16 * (3005 / 2997 : ℝ) ^ (2 : ℕ) *
          thetaCuspBornWittenSuperpotentialMoment 0 1 *
            thetaCuspBornWittenSuperpotentialMoment 2 1 ≤
        25 * thetaCuspBornWittenSuperpotentialMoment 1 1 ^ (2 : ℕ)) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  apply forall_primeArchSourceTraceHankel_linear_nonneg_of_bornWittenAmplitude hupper
  have hmorse := thetaCusp_firstAtom_relaxed_iff_superpotentialMoment.mpr hward
  rw [thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq,
    thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq,
    thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq] at hmorse
  norm_num only [Nat.reduceMul, pow_zero, one_mul] at hmorse
  exact hmorse

end

end RHTower

namespace RHTower

noncomputable section

/-- Full-source odd mixed position--superpotential Ward value.  This aggregates the exact
half-line quantum value over every theta atom. -/
def thetaCuspFullBornWittenSuperpotentialMoment (j : ℕ) : ℝ :=
  ∑' n : ℕ, thetaCuspBornWittenSuperpotentialMoment j n

/-- The total Robin translation contact charge carried by the theta source. -/
def thetaCuspFullBornWittenTranslationContactCharge : ℝ :=
  ∑' n : ℕ, ∫ x : ℝ in Ioi 0,
    thetaCuspBornWittenSuperpotential n x *
      thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)

lemma thetaCuspBornWittenSuperpotentialMoment_zero (j : ℕ) :
    thetaCuspBornWittenSuperpotentialMoment j 0 = 0 := by
  simp [thetaCuspBornWittenSuperpotentialMoment,
    thetaCuspBornWittenAmplitude, thetaCuspMorseGroundState,
    thetaCuspMorseZeroMode]

/-- The atomwise Robin anomaly sums to the endpoint value of the complete theta source. -/
theorem thetaCuspFullBornWittenTranslationContactCharge_eq :
    thetaCuspFullBornWittenTranslationContactCharge =
      (2 * Real.pi)⁻¹ * thetaCuspFullSource 0 := by
  rw [thetaCuspFullBornWittenTranslationContactCharge,
    thetaCuspFullSource_eq_pi_mul_tsum_bornWittenAmplitude_sq (by norm_num)]
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro n
  cases n with
  | zero =>
      simp [thetaCuspBornWittenAmplitude, thetaCuspMorseGroundState,
        thetaCuspMorseZeroMode]
  | succ n =>
      rw [thetaCuspBornWitten_translation_contact_charge (by omega)]
      field_simp [Real.pi_ne_zero]

/-- Every full theta raw moment is exactly one all-atom Born--Witten superpotential value. -/
theorem thetaCuspFullBornWittenSuperpotentialMoment_eq_rawEvenMoment (j : ℕ) :
    thetaCuspFullBornWittenSuperpotentialMoment j =
      (((2 * j + 1 : ℕ) : ℝ) / (4 * Real.pi)) *
        thetaCuspRawEvenMoment j := by
  rw [thetaCuspFullBornWittenSuperpotentialMoment,
    thetaCuspRawEvenMoment_eq_tsum_integral_bornWittenAmplitude_sq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  cases n with
  | zero =>
      simp [thetaCuspBornWittenSuperpotentialMoment_zero,
        thetaCuspBornWittenAmplitude, thetaCuspMorseGroundState,
        thetaCuspMorseZeroMode]
  | succ n =>
      rw [thetaCuspBornWittenSuperpotentialMoment_eq_morseBornMoment j (by omega),
        thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq]
      field_simp [Real.pi_ne_zero]
      ring

/-- The full mixed Ward values inherit positivity from the theta raw moments, despite their
pointwise integrands not having a fixed sign. -/
theorem thetaCuspFullBornWittenSuperpotentialMoment_nonneg (j : ℕ) :
    0 ≤ thetaCuspFullBornWittenSuperpotentialMoment j := by
  rw [thetaCuspFullBornWittenSuperpotentialMoment_eq_rawEvenMoment]
  exact mul_nonneg (by positivity) (thetaCuspRawEvenMoment_nonneg j)

/-- The relaxed fourth-moment condition has the natural square-coefficient form in the full
Born--Witten Ward coordinates. -/
theorem thetaCuspRelaxedFourthMomentConcentration_iff_fullBornWittenSuperpotentialMoment :
    ThetaCuspRelaxedFourthMomentConcentration ↔
      16 * thetaCuspFullBornWittenSuperpotentialMoment 0 *
          thetaCuspFullBornWittenSuperpotentialMoment 2 ≤
        25 * thetaCuspFullBornWittenSuperpotentialMoment 1 ^ (2 : ℕ) := by
  rw [ThetaCuspRelaxedFourthMomentConcentration,
    thetaCuspFullBornWittenSuperpotentialMoment_eq_rawEvenMoment,
    thetaCuspFullBornWittenSuperpotentialMoment_eq_rawEvenMoment,
    thetaCuspFullBornWittenSuperpotentialMoment_eq_rawEvenMoment]
  norm_num
  constructor <;> intro h
  · field_simp [Real.pi_ne_zero]
    nlinarith
  · field_simp [Real.pi_ne_zero] at h
    nlinarith

/-- Every even central Xi jet is an exact all-atom quantum Ward value.  This is the direct
application of the half-line Robin relation to the existing Xi-jet corpus. -/
theorem iteratedDeriv_XiC_zero_eq_fullBornWittenSuperpotentialMoment (j : ℕ) :
    iteratedDeriv (2 * j) XiC 0 =
      (((-1 : ℝ) ^ j *
        (4 * Real.pi / (((2 * j + 1 : ℕ) : ℝ))) *
          thetaCuspFullBornWittenSuperpotentialMoment j : ℝ) : ℂ) := by
  rw [iteratedDeriv_XiC_zero_eq_rawEvenMoment,
    thetaCuspFullBornWittenSuperpotentialMoment_eq_rawEvenMoment]
  have hc : (((2 * j + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hc, Real.pi_ne_zero]

end

end RHTower
