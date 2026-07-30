import GaloisForLFunctions.RHTower.XiHurwitzAnchorPrimeTwoOrientationEnergy

/-!
# Cofinal decay collapses coherent prime seam charges to zero

For an open-strip point `rho`, attach to every positive scale `x` the FE--Schwarz seam

`log x * (x^(-conj rho) - x^(-(1-rho)))`.

Both terms tend to zero as `x` tends to infinity because their real decay exponents are positive.
Consequently, if the values at all prime scales are equal, their common value is automatically
zero: unboundedness of the primes supplies a cofinal subnet on which the common value meets the
zero limit.

This discharges the extra normalization in the paper-proven two-particle Sonin prime-coherence
route.  Once an operator theorem forces equality of the canonical prime potentials, no separate
archimedean assertion is needed to kill the surviving constant.  The open input remains the
source-side uniform Calkin bound that produces coherence; it is not asserted here.
-/

open Complex Filter Real

namespace RHTower

noncomputable section

/-- The canonical FE--Schwarz seam charge at an arbitrary positive real scale. -/
def orbitwiseScaleSeamCharge (x : ℝ) (rho : ℂ) : ℂ :=
  (Real.log x : ℂ) *
    ((x : ℂ) ^ (-(starRingEnd ℂ) rho) - (x : ℂ) ^ (-(1 - rho)))

/-- The same charge at an integer scale; the prime-indexed subfamily is used below. -/
def orbitwiseNatPrimeSeamCharge (p : ℕ) (rho : ℂ) : ℂ :=
  orbitwiseScaleSeamCharge (p : ℝ) rho

/-- Every scale seam is odd under the centered FE--Schwarz reflection.  No positivity assumption
on the scale is needed because the reflection only exchanges the two complex powers. -/
theorem orbitwiseScaleSeamCharge_lineReflect (x : ℝ) (rho : ℂ) :
    orbitwiseScaleSeamCharge x (1 - (starRingEnd ℂ) rho) =
      -orbitwiseScaleSeamCharge x rho := by
  simp only [orbitwiseScaleSeamCharge, map_sub, map_one, Complex.conj_conj]
  ring

/-- Integer-scale specialization of centered seam oddness. -/
theorem orbitwiseNatPrimeSeamCharge_lineReflect (p : ℕ) (rho : ℂ) :
    orbitwiseNatPrimeSeamCharge p (1 - (starRingEnd ℂ) rho) =
      -orbitwiseNatPrimeSeamCharge p rho := by
  exact orbitwiseScaleSeamCharge_lineReflect (p : ℝ) rho

private lemma star_real_cpow_of_pos (x : ℝ) (hx : 0 < x) (w : ℂ) :
    (starRingEnd ℂ) ((x : ℂ) ^ w) =
      (x : ℂ) ^ ((starRingEnd ℂ) w) := by
  have harg : ((x : ℂ).arg ≠ Real.pi) := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (x : ℂ) w harg
  simpa using h.symm

/-- At a positive real scale, Schwarz conjugation of the spectral point conjugates the canonical
seam value. -/
theorem orbitwiseScaleSeamCharge_conj
    (x : ℝ) (hx : 0 < x) (rho : ℂ) :
    orbitwiseScaleSeamCharge x ((starRingEnd ℂ) rho) =
      (starRingEnd ℂ) (orbitwiseScaleSeamCharge x rho) := by
  simp only [orbitwiseScaleSeamCharge, map_mul, map_sub, Complex.conj_conj]
  rw [star_real_cpow_of_pos x hx, star_real_cpow_of_pos x hx,
    Complex.conj_ofReal]
  simp only [map_neg, map_sub, map_one, Complex.conj_conj]

/-- At a positive real scale, functional-equation reflection is negative value conjugation. -/
theorem orbitwiseScaleSeamCharge_one_sub
    (x : ℝ) (hx : 0 < x) (rho : ℂ) :
    orbitwiseScaleSeamCharge x (1 - rho) =
      -(starRingEnd ℂ) (orbitwiseScaleSeamCharge x rho) := by
  calc
    orbitwiseScaleSeamCharge x (1 - rho) =
        -orbitwiseScaleSeamCharge x ((starRingEnd ℂ) rho) := by
      simpa using orbitwiseScaleSeamCharge_lineReflect x
        ((starRingEnd ℂ) rho)
    _ = _ := by rw [orbitwiseScaleSeamCharge_conj x hx rho]

/-- Positive-integer Schwarz reflection law for the canonical seam charge. -/
theorem orbitwiseNatPrimeSeamCharge_conj
    (p : ℕ) (hp : 0 < p) (rho : ℂ) :
    orbitwiseNatPrimeSeamCharge p ((starRingEnd ℂ) rho) =
      (starRingEnd ℂ) (orbitwiseNatPrimeSeamCharge p rho) := by
  exact orbitwiseScaleSeamCharge_conj (p : ℝ) (by exact_mod_cast hp) rho

/-- Positive-integer functional-equation reflection law for the canonical seam charge. -/
theorem orbitwiseNatPrimeSeamCharge_one_sub
    (p : ℕ) (hp : 0 < p) (rho : ℂ) :
    orbitwiseNatPrimeSeamCharge p (1 - rho) =
      -(starRingEnd ℂ) (orbitwiseNatPrimeSeamCharge p rho) := by
  exact orbitwiseScaleSeamCharge_one_sub (p : ℝ) (by exact_mod_cast hp) rho

private theorem tendsto_log_mul_rpow_neg_atTop
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => Real.log x * x ^ (-r)) atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le, div_eq_mul_inv]

/-- Every canonical scale seam decays to zero at infinity throughout the open critical strip. -/
theorem tendsto_orbitwiseScaleSeamCharge
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Tendsto (fun x : ℝ => orbitwiseScaleSeamCharge x rho) atTop (nhds 0) := by
  have hleftReal :
      Tendsto (fun x : ℝ => Real.log x * x ^ (-rho.re)) atTop (nhds 0) :=
    tendsto_log_mul_rpow_neg_atTop hstrip.1
  have hleftNorm :
      Tendsto (fun x : ℝ =>
        ‖(Real.log x : ℂ) * (x : ℂ) ^ (-(starRingEnd ℂ) rho)‖)
        atTop (nhds 0) := by
    apply hleftReal.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hx.le),
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
    simp
  have hleft : Tendsto
      (fun x : ℝ => (Real.log x : ℂ) *
        (x : ℂ) ^ (-(starRingEnd ℂ) rho)) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hleftNorm
  have hrightReal :
      Tendsto (fun x : ℝ => Real.log x * x ^ (-(1 - rho.re)))
        atTop (nhds 0) :=
    tendsto_log_mul_rpow_neg_atTop (by linarith)
  have hrightNorm :
      Tendsto (fun x : ℝ =>
        ‖(Real.log x : ℂ) * (x : ℂ) ^ (-(1 - rho))‖)
        atTop (nhds 0) := by
    apply hrightReal.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hx.le),
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
    simp
  have hright : Tendsto
      (fun x : ℝ => (Real.log x : ℂ) * (x : ℂ) ^ (-(1 - rho)))
      atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hrightNorm
  simpa only [sub_zero] using (hleft.sub hright).congr' (by
    filter_upwards with x
    simp only [orbitwiseScaleSeamCharge]
    ring)

/-- The integer-scale seam sequence, and hence its prime subsequence, has zero cofinal limit. -/
theorem tendsto_orbitwiseNatPrimeSeamCharge
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Tendsto (fun p : ℕ => orbitwiseNatPrimeSeamCharge p rho) atTop (nhds 0) :=
  (tendsto_orbitwiseScaleSeamCharge hstrip).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- A value shared by every prime seam charge must vanish.  The proof uses only decay and the
existence of arbitrarily large primes. -/
theorem common_eq_zero_of_primeSeamCharge_eq
    {rho c : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hcoh : ∀ p : ℕ, Nat.Prime p → orbitwiseNatPrimeSeamCharge p rho = c) :
    c = 0 := by
  have hlim := tendsto_orbitwiseNatPrimeSeamCharge hstrip
  by_contra hne
  have hc0 : 0 < dist c 0 := dist_pos.mpr hne
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) (dist c 0) hc0
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes N
  have hlt := hN p hNp
  rw [hcoh p hp] at hlt
  exact (lt_irrefl _ hlt).elim

/-- Pairwise coherence of all canonical prime seam charges at one open-strip point. -/
def OrbitwisePrimeSeamChargesCoherent (rho : ℂ) : Prop :=
  ∀ p q : ℕ, Nat.Prime p → Nat.Prime q →
    orbitwiseNatPrimeSeamCharge p rho = orbitwiseNatPrimeSeamCharge q rho

/-- The scale-two member of the coherent family is the previously formalized first-prime seam. -/
theorem orbitwiseNatPrimeSeamCharge_two_eq_firstPrime (rho : ℂ) :
    orbitwiseNatPrimeSeamCharge 2 rho = orbitwiseFirstPrimeSeamCharge rho := by
  simp [orbitwiseNatPrimeSeamCharge, orbitwiseScaleSeamCharge,
    orbitwiseFirstPrimeSeamCharge]

/-- **Coherence collapse.**  On the open strip, prime-scale coherence is equivalent to the
critical-line fixed-point equation.  The forward implication passes through cofinal decay, not an
assumed vanishing charge. -/
theorem orbitwisePrimeSeamChargesCoherent_iff_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    OrbitwisePrimeSeamChargesCoherent rho ↔ rho.re = 1 / 2 := by
  constructor
  · intro hcoh
    have hzero : orbitwiseNatPrimeSeamCharge 2 rho = 0 :=
      common_eq_zero_of_primeSeamCharge_eq hstrip
        (fun p hp => hcoh p 2 hp (by norm_num))
    apply (orbitwiseFirstPrimeSeamCharge_eq_zero_iff rho).mp
    rw [← orbitwiseNatPrimeSeamCharge_two_eq_firstPrime]
    exact hzero
  · intro hre p q _ _
    have horbit : (starRingEnd ℂ) rho = 1 - rho := by
      apply Complex.ext
      · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
        linarith
      · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im]
        ring
    simp [orbitwiseNatPrimeSeamCharge, orbitwiseScaleSeamCharge, horbit]

/-- Every Xi divisor fibre has one coherent family of canonical prime seam charges. -/
def XiPrimeSeamChargesCoherent : Prop :=
  ∀ rho : XiDivisorSupport, OrbitwisePrimeSeamChargesCoherent (rho : ℂ)

/-- Global prime coherence is exactly vanishing of the already isolated common first-prime seam. -/
theorem xiPrimeSeamChargesCoherent_iff_firstPrimeSeamChargesVanish :
    XiPrimeSeamChargesCoherent ↔ XiFirstPrimeSeamChargesVanish := by
  constructor
  · intro h rho
    apply (orbitwiseFirstPrimeSeamCharge_eq_zero_iff (rho : ℂ)).mpr
    exact (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)).mp (h rho)
  · intro h rho
    apply (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)).mpr
    exact (orbitwiseFirstPrimeSeamCharge_eq_zero_iff (rho : ℂ)).mp (h rho)

/-- Global prime coherence is exactly zero Xi--Hurwitz orientation energy. -/
theorem xiPrimeSeamChargesCoherent_iff_orientationEnergy_zero :
    XiPrimeSeamChargesCoherent ↔ xiHurwitzOrientationEnergy = 0 :=
  xiPrimeSeamChargesCoherent_iff_firstPrimeSeamChargesVanish.trans
    xiFirstPrimeSeamChargesVanish_iff_orientationEnergy_zero

/-- The global coherent-prime constraint is equivalent to RH.  Its proposed non-circular producer
is the paper-proven two-particle Sonin Calkin bound, not this equivalence itself. -/
theorem xiPrimeSeamChargesCoherent_iff_riemannHypothesis :
    XiPrimeSeamChargesCoherent ↔ RiemannHypothesis :=
  xiPrimeSeamChargesCoherent_iff_orientationEnergy_zero.trans
    riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.symm

/-- Coherence of the canonical prime seam potentials at every Xi divisor point implies RH. -/
theorem riemannHypothesis_of_xiPrimeSeamChargesCoherent
    (h : XiPrimeSeamChargesCoherent) : RiemannHypothesis :=
  xiPrimeSeamChargesCoherent_iff_riemannHypothesis.mp h

end

end RHTower

namespace RHTower

noncomputable section

/-- The centered prime-clock mismatch between functional-equation inverse transport and
Schwarz-adjoint transport, written without an inverse so its relation to the existing seam charge
is algebraically transparent. -/
def primeCpowDualityAdjunctionFracture (p : ℕ) (rho : ℂ) : ℂ :=
  (p : ℂ) ^ (rho - 1 / 2) -
    (p : ℂ) ^ (1 / 2 - (starRingEnd ℂ) rho)

/-- The canonical FE--Schwarz prime seam is exactly the half-density-renormalized
duality--adjunction fracture. -/
theorem orbitwiseNatPrimeSeamCharge_eq_cpow_fracture
    (p : ℕ) (hp : 0 < p) (rho : ℂ) :
    orbitwiseNatPrimeSeamCharge p rho =
      -((Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-(1 / 2 : ℂ))) *
        primeCpowDualityAdjunctionFracture p rho := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold orbitwiseNatPrimeSeamCharge orbitwiseScaleSeamCharge
    primeCpowDualityAdjunctionFracture
  have hpCast : ((p : ℝ) : ℂ) = (p : ℂ) := by norm_num
  rw [hpCast]
  rw [show -(starRingEnd ℂ) rho =
        -(1 / 2 : ℂ) + (1 / 2 - (starRingEnd ℂ) rho) by ring_nf,
      show -(1 - rho) = -(1 / 2 : ℂ) + (rho - 1 / 2) by ring_nf,
      Complex.cpow_add _ _ hpC, Complex.cpow_add _ _ hpC]
  ring_nf

end

end RHTower
