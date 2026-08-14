import GaloisForLFunctions.RHTower.GaussReciprocalCharacterAdmission
import GaloisForLFunctions.RHTower.GaussHodgeWeightedResolventEdge
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixCurvedSuspensionHodgeTrace
import GaloisForLFunctions.RHTower.XiHorizontalCollisionChargeEndpoint
import GaloisForLFunctions.RHTower.XiHurwitzOrientationEnergyConsumers
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import GaloisForLFunctions.HTGeometry.HyperbolicBounds

/-!
# Horizontal collision charge as a multiplicity-faithful Gauss--Hodge prime current

This module splices two previously separate endpoints.  A finite Xi support packet is expanded
into its literal analytic-multiplicity copies and each copy drives the label-faithful Gauss--Hodge
prime current.  Positivity prevents cancellation between copies, while the reciprocal-character
admission theorem makes a single off-line copy nonsummable over the primes.

For a positive-height strip window, summability of the resulting finite aggregate is therefore
equivalent to vanishing of the horizontal collision charge.  This is stronger than an asymptotic
density estimate: one retained off-line copy already destroys summability of the whole prime
current.  No RH assumption occurs in the construction or classification.
-/

open Complex Set Filter
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Finite multiplicity-faithful prime currents -/

/-- Literal divisor-copy expansion of a finite Xi support packet. -/
def xiFiniteMultiplicityCopyPacket (S : Finset XiDivisorSupport) : Finset XiZeroCopy :=
  S.sigma fun _ => Finset.univ

@[simp] theorem mem_xiFiniteMultiplicityCopyPacket
    {S : Finset XiDivisorSupport} {q : XiZeroCopy} :
    q ∈ xiFiniteMultiplicityCopyPacket S ↔ q.1 ∈ S := by
  simp [xiFiniteMultiplicityCopyPacket]

/-- Multiplicity-faithful Gauss--Hodge current of a finite Xi support packet.  Prime labels are
not scalarized: the output remains a function on `Nat.Primes`. -/
def xiFiniteGaussHodgePrimeCurrent
    (m : ℕ) (S : Finset XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  ∑ q ∈ xiFiniteMultiplicityCopyPacket S, gaussHodgeMassCurrent m q p

theorem xiFiniteGaussHodgePrimeCurrent_nonneg
    {m : ℕ} (hm : 1 ≤ m) (S : Finset XiDivisorSupport) (p : Nat.Primes) :
    0 ≤ xiFiniteGaussHodgePrimeCurrent m S p := by
  rw [xiFiniteGaussHodgePrimeCurrent]
  exact Finset.sum_nonneg fun q _ => gaussHodgeMassCurrent_nonneg hm q p

/-- **Finite packet classification.**  The positive multiplicity-faithful aggregate is summable
over prime labels exactly when every retained Xi support point lies on the critical line. -/
theorem summable_xiFiniteGaussHodgePrimeCurrent_iff
    {m : ℕ} (hm : 1 ≤ m) (S : Finset XiDivisorSupport) :
    Summable (xiFiniteGaussHodgePrimeCurrent m S) ↔
      ∀ rho ∈ S, (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hsum rho hrho
    let q : XiZeroCopy := xiFirstZeroCopy rho
    have hq : q ∈ xiFiniteMultiplicityCopyPacket S := by
      rw [mem_xiFiniteMultiplicityCopyPacket]
      exact hrho
    have hterm : Summable (gaussHodgeMassCurrent m q) := by
      apply Summable.of_nonneg_of_le
      · exact gaussHodgeMassCurrent_nonneg hm q
      · intro p
        exact Finset.single_le_sum
          (fun q' _ => gaussHodgeMassCurrent_nonneg hm q' p) hq
      · exact hsum
    have hrate :=
      (summable_gaussHodgeMassCurrent_iff_centeredRate_eq_zero hm q).1 hterm
    rw [primeDepthBVWoldXiCenteredRate] at hrate
    change 2 * (rho : ℂ).re - 1 = 0 at hrate
    change (rho : ℂ).re = 1 / 2
    linarith
  · intro hline
    have hzero : xiFiniteGaussHodgePrimeCurrent m S = 0 := by
      funext p
      change xiFiniteGaussHodgePrimeCurrent m S p = 0
      rw [xiFiniteGaussHodgePrimeCurrent]
      apply Finset.sum_eq_zero
      intro q hq
      apply (gaussHodgeMassCurrent_eq_zero_iff hm q p).2
      exact hline q.1 (mem_xiFiniteMultiplicityCopyPacket.mp hq)
    rw [hzero]
    exact summable_zero

/-! ## Strip-window carrier -/

/-- The Xi-divisor support points represented by the raw positive-height strip-zero finset. -/
def xiStripWindowDivisorSupportFinset (T : ℝ) : Finset XiDivisorSupport :=
  (stripZeros_finite T).toFinset.attach.map
    ⟨fun rho =>
        ⟨rho.1, mem_xi_divisor_support_of_eq_zero
          (((stripZeros_finite T).mem_toFinset.mp rho.2).2)⟩,
      by
        intro rho sigma h
        apply Subtype.ext
        exact congrArg (fun x : XiDivisorSupport => (x : ℂ)) h⟩

@[simp] theorem mem_xiStripWindowDivisorSupportFinset
    {T : ℝ} {rho : XiDivisorSupport} :
    rho ∈ xiStripWindowDivisorSupportFinset T ↔
      (rho : ℂ) ∈ (stripZeros_finite T).toFinset := by
  constructor
  · intro hrho
    obtain ⟨z, hz, hzr⟩ := Finset.mem_map.mp hrho
    have hzmem : (z : ℂ) ∈ (stripZeros_finite T).toFinset := z.2
    have hcoe : (z : ℂ) = (rho : ℂ) := congrArg Subtype.val hzr
    simpa only [hcoe] using hzmem
  · intro hrho
    apply Finset.mem_map.mpr
    refine ⟨⟨(rho : ℂ), hrho⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

/-- Prime-labelled source current attached to one horizontal-collision window. -/
def xiHorizontalCollisionGaussHodgePrimeCurrent
    (m : ℕ) (T : ℝ) (p : Nat.Primes) : ℝ :=
  xiFiniteGaussHodgePrimeCurrent m (xiStripWindowDivisorSupportFinset T) p

/-! ## Exact collision/summability bridge -/

/-- A strip window has zero collision charge exactly when all of its divisor-support points lie
on the critical line.  This is a finite-window statement and uses neither RH nor a limit. -/
theorem xiHorizontalCollisionCharge_eq_zero_iff_stripSupport_onLine (T : ℝ) :
    xiHorizontalCollisionCharge T = 0 ↔
      ∀ rho ∈ xiStripWindowDivisorSupportFinset T, (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hcharge rho hrho
    have hraw : (rho : ℂ) ∈ (stripZeros_finite T).toFinset :=
      mem_xiStripWindowDivisorSupportFinset.mp hrho
    have hoffOrder : xiStripWindowOffLineOrder T = 0 := by
      have hle := xiStripWindowOffLineOrder_le_horizontalCollisionCharge T
      rw [hcharge] at hle
      omega
    by_contra hoff
    have hfiltered :
        (rho : ℂ) ∈ (stripZeros_finite T).toFinset.filter
          (fun z => z.re ≠ 1 / 2) := Finset.mem_filter.mpr ⟨hraw, hoff⟩
    have hpos : 1 ≤ (analyticOrderAt xi (rho : ℂ)).toNat :=
      Nat.one_le_iff_ne_zero.mpr
        (xi_order_toNat_ne_zero (xi_eq_zero_of_mem_divisor_support rho))
    have hle : (analyticOrderAt xi (rho : ℂ)).toNat ≤
        xiStripWindowOffLineOrder T := by
      rw [xiStripWindowOffLineOrder]
      exact Finset.single_le_sum
        (fun z _ => Nat.zero_le (analyticOrderAt xi z).toNat) hfiltered
    rw [hoffOrder] at hle
    omega
  · intro hline
    rw [xiHorizontalCollisionCharge, Finset.sum_eq_zero]
    intro rho hrho
    let rhoSupport : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero
        (((stripZeros_finite T).mem_toFinset.mp hrho).2)⟩
    have hrhoLine : rho.re = 1 / 2 := by
      exact hline rhoSupport
        (mem_xiStripWindowDivisorSupportFinset.mpr hrho)
    have hfiber : stripHeightFinset rho.im = {rho} := by
      rw [stripHeightFinset_eq_stripZeros_filter_im hrho]
      ext z
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, hzim⟩
        let zSupport : XiDivisorSupport :=
          ⟨z, mem_xi_divisor_support_of_eq_zero
            (((stripZeros_finite T).mem_toFinset.mp hz).2)⟩
        have hzLine : z.re = 1 / 2 := by
          exact hline zSupport
            (mem_xiStripWindowDivisorSupportFinset.mpr hz)
        apply Complex.ext
        · simp only [hzLine, hrhoLine]
        · exact hzim
      · intro hz
        subst z
        exact ⟨hrho, rfl⟩
    rw [xiHorizontalMultiplicity, hfiber, Finset.sum_singleton,
      Nat.sub_self, mul_zero]

/-- **Source-zero-to-horizontal-carrier bridge.**  For every finite strip window, summability of
the coefficient-faithful prime current is exactly zero horizontal collision charge. -/
theorem summable_xiHorizontalCollisionGaussHodgePrimeCurrent_iff_charge_eq_zero
    {m : ℕ} (hm : 1 ≤ m) (T : ℝ) :
    Summable (xiHorizontalCollisionGaussHodgePrimeCurrent m T) ↔
      xiHorizontalCollisionCharge T = 0 := by
  change Summable
    (xiFiniteGaussHodgePrimeCurrent m (xiStripWindowDivisorSupportFinset T)) ↔
      xiHorizontalCollisionCharge T = 0
  rw [summable_xiFiniteGaussHodgePrimeCurrent_iff hm]
  exact (xiHorizontalCollisionCharge_eq_zero_iff_stripSupport_onLine T).symm

/-- Global summability of the multiplicity-faithful source current is an exact RH endpoint. -/
theorem riemannHypothesis_iff_forall_summable_horizontalCollisionGaussHodgePrimeCurrent
    {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔
      ∀ T : ℝ, Summable (xiHorizontalCollisionGaussHodgePrimeCurrent m T) := by
  rw [riemannHypothesis_iff_forall_horizontalCollisionCharge_eq_zero]
  exact forall_congr' fun T =>
    (summable_xiHorizontalCollisionGaussHodgePrimeCurrent_iff_charge_eq_zero hm T).symm

/-- Natural-height source windows are cofinal: proving summability there already proves RH. -/
theorem riemannHypothesis_of_forall_nat_summable_horizontalCollisionGaussHodgePrimeCurrent
    {m : ℕ} (hm : 1 ≤ m)
    (hsource : ∀ n : ℕ,
      Summable (xiHorizontalCollisionGaussHodgePrimeCurrent m n)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_forall_nat_horizontalCollisionCharge_lt_two
  intro n
  have hzero :=
    (summable_xiHorizontalCollisionGaussHodgePrimeCurrent_iff_charge_eq_zero hm n).1
      (hsource n)
  rw [hzero]
  omega

/-! ## One-trace compression of every finite window -/

/-- Real part of the zeroth full-divisor Gauss--Hodge resolvent moment, now read as one sequence
over ordinary-prime labels.  The divisor sum is already unconditionally summable at each label. -/
def gaussHodgePrimeSourceResolventTrace (m : ℕ) (X : ℝ) (p : Nat.Primes) : ℝ :=
  (gaussHodgeSourceResolventMoment m p 0 X).re

theorem gaussHodgePrimeSourceResolventTrace_nonneg
    {m : ℕ} (hm : 1 ≤ m) {X : ℝ} (hX : 0 < X) (p : Nat.Primes) :
    0 ≤ gaussHodgePrimeSourceResolventTrace m X p := by
  exact gaussHodgeSourceResolventMoment_re_nonneg_of_le_or_far
    hm p hX (Or.inl (by omega))

/-- Every multiplicity-labelled divisor term is bounded by the full positive source trace at the
same prime label. -/
theorem gaussHodgeMassCurrent_mul_resolvent_re_le_primeSourceTrace
    {m : ℕ} (hm : 1 ≤ m) {X : ℝ} (hX : 0 < X)
    (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgeMassCurrent m q p * (xiResolventPoint X q).re ≤
      gaussHodgePrimeSourceResolventTrace m X p := by
  have hsumNorm : Summable (fun r : XiZeroCopy =>
      ‖(gaussHodgeMassCurrent m r p : ℂ) * xiResolventPoint X r‖) := by
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gaussHodgeMassCurrent_nonneg hm _ p)] using
      summable_gaussHodgeMassCurrent_mul_norm_resolventPoint hm p hX.le
  have hsum : Summable (fun r : XiZeroCopy =>
      (gaussHodgeMassCurrent m r p : ℂ) * xiResolventPoint X r) :=
    hsumNorm.of_norm
  have hsumRe : Summable (fun r : XiZeroCopy =>
      ((gaussHodgeMassCurrent m r p : ℂ) * xiResolventPoint X r).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  have hle := hsumRe.le_tsum q (fun r _ => by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (gaussHodgeMassCurrent_nonneg hm r p)
      (xiResolventPoint_re_pos hX.le r).le)
  rw [gaussHodgePrimeSourceResolventTrace, gaussHodgeSourceResolventMoment]
  simp only [zero_add, pow_one]
  rw [Complex.re_tsum hsum]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hle

/-- **Single-source-trace compression.**  Prime summability of one full-divisor source trace at
one positive resolvent shift is equivalent to RH.  Positivity prevents cancellation across
divisor copies, and strict positivity of each resolvent atom transfers summability back to every
individual Gauss--Hodge current. -/
theorem summable_gaussHodgePrimeSourceResolventTrace_iff_riemannHypothesis
    {m : ℕ} (hm : 1 ≤ m) {X : ℝ} (hX : 0 < X) :
    Summable (gaussHodgePrimeSourceResolventTrace m X) ↔ RiemannHypothesis := by
  constructor
  · intro hsource
    apply (forall_summable_gaussHodgeMassCurrent_iff_riemannHypothesis hm).1
    intro q
    have hweighted : Summable (fun p : Nat.Primes =>
        gaussHodgeMassCurrent m q p * (xiResolventPoint X q).re) := by
      apply Summable.of_nonneg_of_le
      · intro p
        exact mul_nonneg (gaussHodgeMassCurrent_nonneg hm q p)
          (xiResolventPoint_re_pos hX.le q).le
      · exact gaussHodgeMassCurrent_mul_resolvent_re_le_primeSourceTrace hm hX q
      · exact hsource
    exact (summable_mul_right_iff (xiResolventPoint_re_pos hX.le q).ne').1 hweighted
  · intro hRH
    have hzero : gaussHodgePrimeSourceResolventTrace m X = 0 := by
      funext p
      rw [gaussHodgePrimeSourceResolventTrace,
        gaussHodgeSourceResolventMoment_eq_zero_of_rh hRH hm]
      rfl
    rw [hzero]
    exact summable_zero

/-! ## Literal two-orientation source determinant -/

/-- Full-divisor resolvent trace formed before scalar landing from the Euler derivative of the
literal two-orientation Gamma-six suspension determinant.  Ordinary-prime label, Xi multiplicity
copy, horizontal rate, and both reflected cyclic legs remain explicit in every summand. -/
def gammaSixSuspensionPrimeSourceResolventTrace
    (m : ℕ) (X : ℝ) (p : Nat.Primes) : ℝ :=
  (∑' q : XiZeroCopy,
    ((primeDepthBVWoldXiCenteredRate q.1 *
        deriv (fun t : ℝ =>
          gaussReciprocalCharacterWeight m p *
            (Matrix.det (sourceHorizontalGammaSixCurvedSuspension
              (Real.log (p : ℝ) * t))).re)
          (primeDepthBVWoldXiCenteredRate q.1) : ℝ) : ℂ) *
      xiResolventPoint X q).re

/-- The compressed positive Gauss--Hodge trace is exactly the Euler trace of the literal curved
Gamma-six source suspension.  This is the source identification absent from the divisor-only
presentation: it uses no fitted coefficients and no RH premise. -/
theorem gammaSixSuspensionPrimeSourceResolventTrace_eq_gaussHodge
    (m : ℕ) (X : ℝ) (p : Nat.Primes) :
    gammaSixSuspensionPrimeSourceResolventTrace m X p =
      gaussHodgePrimeSourceResolventTrace m X p := by
  rw [gammaSixSuspensionPrimeSourceResolventTrace,
    gaussHodgePrimeSourceResolventTrace, gaussHodgeSourceResolventMoment]
  simp only [zero_add, pow_one]
  congr 1
  apply tsum_congr
  intro q
  rw [← gaussHodgeMassCurrent_eq_euler_gaussGammaSixSuspensionDeterminant]

theorem gammaSixSuspensionPrimeSourceResolventTrace_nonneg
    {m : ℕ} (hm : 1 ≤ m) {X : ℝ} (hX : 0 < X) (p : Nat.Primes) :
    0 ≤ gammaSixSuspensionPrimeSourceResolventTrace m X p := by
  rw [gammaSixSuspensionPrimeSourceResolventTrace_eq_gaussHodge]
  exact gaussHodgePrimeSourceResolventTrace_nonneg hm hX p

/-- **Frankenstein source endpoint.**  Prime summability of one literal two-orientation
Gamma-six suspension determinant trace is equivalent to RH.  Unlike the earlier compressed name,
the left side is visibly built from a source cyclic boundary, its reflected leg, determinant,
Euler response, analytic multiplicity copies, and ordinary-prime labels. -/
theorem summable_gammaSixSuspensionPrimeSourceResolventTrace_iff_riemannHypothesis
    {m : ℕ} (hm : 1 ≤ m) {X : ℝ} (hX : 0 < X) :
    Summable (gammaSixSuspensionPrimeSourceResolventTrace m X) ↔
      RiemannHypothesis := by
  have htrace : gammaSixSuspensionPrimeSourceResolventTrace m X =
      gaussHodgePrimeSourceResolventTrace m X := by
    funext p
    exact gammaSixSuspensionPrimeSourceResolventTrace_eq_gaussHodge m X p
  rw [htrace]
  exact summable_gaussHodgePrimeSourceResolventTrace_iff_riemannHypothesis hm hX

/-! ## Derivative-free source curvature endpoint -/

private theorem sq_le_two_mul_cosh_sub_one (x : ℝ) :
    x ^ 2 ≤ 2 * (Real.cosh x - 1) := by
  rw [show x = 2 * (x / 2) by ring, Real.cosh_two_mul]
  have hsquare : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := by
    by_cases hx : 0 ≤ x / 2
    · have hsinh : x / 2 ≤ Real.sinh (x / 2) :=
        Real.self_le_sinh_iff.mpr hx
      have hsinh0 : 0 ≤ Real.sinh (x / 2) := Real.sinh_nonneg_iff.mpr hx
      nlinarith
    · have hx' : x / 2 ≤ 0 := le_of_not_ge hx
      have hsinh : Real.sinh (x / 2) ≤ x / 2 :=
        Real.sinh_le_self_iff.mpr hx'
      have hsinh0 : Real.sinh (x / 2) ≤ 0 := Real.sinh_nonpos_iff.mpr hx'
      nlinarith
  nlinarith [Real.cosh_sq (x / 2)]

/-- Raw determinant curvature of the literal two-orientation Gamma-six suspension at one Xi
multiplicity copy and one ordinary-prime label.  No Euler derivative is taken. -/
def gammaSixSuspensionDeterminantPrimeCurrent
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  gaussGammaSixSuspensionTraceEnergy m p
    (primeDepthBVWoldXiCenteredRate q.1)

/-- Raw suspension determinant current already pays a harmonic-prime quantum off center. -/
theorem gammaSixSuspensionDeterminantPrimeCurrent_harmonic_lower
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gaussVirialAdmissionConstant m q / 2 * (1 / (p : ℝ)) ≤
      gammaSixSuspensionDeterminantPrimeCurrent m q p := by
  let t : ℝ := primeDepthBVWoldXiCenteredRate q.1
  let L : ℝ := Real.log (p : ℝ)
  let a : ℝ := gaussReciprocalCharacterWeight m p
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact (gaussReciprocalCharacterWeight_pos hm p).le
  have hgap := sq_le_two_mul_cosh_sub_one (L * t)
  have hsplit : a * (L * t) ^ 2 ≤
      reciprocalCharacterSplitEnergy a L t := by
    rw [reciprocalCharacterSplitEnergy]
    calc
      a * (L * t) ^ 2 ≤ a * (2 * (Real.cosh (L * t) - 1)) :=
        mul_le_mul_of_nonneg_left hgap ha
      _ = 2 * a * (Real.cosh (L * t) - 1) := by ring
  have hbase := gaussResidueFisherLog_harmonic_lower hm p
  have hscale : 0 ≤ Real.log 2 / 2 * t ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hbase hscale
  have hleft :
      (Real.log 2 / 2 * t ^ 2) *
          (((1 / 2 : ℝ) ^ (2 * m) / (2 * (m : ℝ) ^ 2)) *
            (1 / (p : ℝ))) =
        gaussVirialAdmissionConstant m q / 2 * (1 / (p : ℝ)) := by
    rw [gaussVirialAdmissionConstant]
    dsimp only [t]
    ring
  have hright :
      (Real.log 2 / 2 * t ^ 2) *
          (gaussChannelResidueCurrent m p *
            primeActivationOccupancyFisherDensity p * Real.log (p : ℝ)) =
        a * (L * t) ^ 2 := by
    dsimp only [a, L]
    rw [gaussReciprocalCharacterWeight]
    field_simp [hL.ne']
  rw [hleft, hright] at hscaled
  rw [gammaSixSuspensionDeterminantPrimeCurrent,
    gaussGammaSixSuspensionTraceEnergy_eq_pairedBoundaryEnergy,
    gaussGammaSixPairedBoundaryEnergy_eq_splitEnergy]
  exact hscaled.trans hsplit

theorem gammaSixSuspensionDeterminantPrimeCurrent_nonneg
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    0 ≤ gammaSixSuspensionDeterminantPrimeCurrent m q p := by
  rw [gammaSixSuspensionDeterminantPrimeCurrent,
    gaussGammaSixSuspensionTraceEnergy_eq_pairedBoundaryEnergy,
    gaussGammaSixPairedBoundaryEnergy_eq_splitEnergy,
    reciprocalCharacterSplitEnergy]
  exact mul_nonneg
    (mul_nonneg (by norm_num) (gaussReciprocalCharacterWeight_pos hm p).le)
    (sub_nonneg.mpr (Real.one_le_cosh _))

/-- Raw determinant curvature is pointwise no larger than its Euler/virial Gauss--Hodge response.
Thus removing the derivative preserves fixed-prime divisor summability. -/
theorem gammaSixSuspensionDeterminantPrimeCurrent_le_gaussHodge
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixSuspensionDeterminantPrimeCurrent m q p ≤
      gaussHodgeMassCurrent m q p := by
  let a : ℝ := gaussReciprocalCharacterWeight m p
  let u : ℝ := Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate q.1
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact (gaussReciprocalCharacterWeight_pos hm p).le
  have hu : 0 ≤ u * Real.sinh u := by
    exact (sq_le_mul_sinh u).trans' (sq_nonneg u)
  have hscalar := HTGeometry.two_cosh_sub_two_le_self_mul_sinh u
  rw [gammaSixSuspensionDeterminantPrimeCurrent,
    gaussGammaSixSuspensionTraceEnergy_eq_pairedBoundaryEnergy,
    gaussGammaSixPairedBoundaryEnergy_eq_splitEnergy,
    gaussHodgeMassCurrent_eq_reciprocalCharacterVirial,
    reciprocalCharacterSplitEnergy, reciprocalCharacterVirialCurrent]
  change 2 * a * (Real.cosh u - 1) ≤ 2 * a * u * Real.sinh u
  calc
    2 * a * (Real.cosh u - 1) = a * (2 * Real.cosh u - 2) := by ring
    _ ≤ a * (u * Real.sinh u) := mul_le_mul_of_nonneg_left hscalar ha
    _ ≤ 2 * a * (u * Real.sinh u) := by nlinarith
    _ = 2 * a * u * Real.sinh u := by ring

/-- Prime summability of raw source curvature at one retained divisor copy is exactly horizontal
neutrality.  The Euler derivative in the previous C25 endpoint was not essential. -/
theorem summable_gammaSixSuspensionDeterminantPrimeCurrent_iff_centeredRate_eq_zero
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) :
    Summable (gammaSixSuspensionDeterminantPrimeCurrent m q) ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  constructor
  · intro hsum
    by_contra hq
    have hC := gaussVirialAdmissionConstant_pos hm q hq
    have hscaled : Summable (fun p : Nat.Primes =>
        gaussVirialAdmissionConstant m q / 2 * (1 / (p : ℝ))) :=
      Summable.of_nonneg_of_le (fun _ => by positivity)
        (gammaSixSuspensionDeterminantPrimeCurrent_harmonic_lower hm q) hsum
    have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
      (summable_mul_left_iff (by positivity :
        gaussVirialAdmissionConstant m q / 2 ≠ 0)).mp hscaled
    exact Nat.Primes.not_summable_one_div hharmonic
  · intro hrate
    have hzero : gammaSixSuspensionDeterminantPrimeCurrent m q = 0 := by
      funext p
      rw [gammaSixSuspensionDeterminantPrimeCurrent,
        gaussGammaSixSuspensionTraceEnergy_eq_pairedBoundaryEnergy,
        gaussGammaSixPairedBoundaryEnergy_eq_splitEnergy,
        reciprocalCharacterSplitEnergy, hrate]
      simp
    rw [hzero]
    exact summable_zero

theorem forall_summable_gammaSixSuspensionDeterminantPrimeCurrent_iff_riemannHypothesis
    {m : ℕ} (hm : 1 ≤ m) :
    (∀ q : XiZeroCopy,
      Summable (gammaSixSuspensionDeterminantPrimeCurrent m q)) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_summable_gaussHodgeMassCurrent_iff_riemannHypothesis hm).1
    intro q
    exact (summable_gaussHodgeMassCurrent_iff_centeredRate_eq_zero hm q).2
      ((summable_gammaSixSuspensionDeterminantPrimeCurrent_iff_centeredRate_eq_zero
        hm q).1 (h q))
  · intro hRH q
    apply (summable_gammaSixSuspensionDeterminantPrimeCurrent_iff_centeredRate_eq_zero
      hm q).2
    apply (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

/-- One positive full-divisor trace of raw, derivative-free source suspension curvature. -/
def gammaSixSuspensionDeterminantPrimeSourceResolventTrace
    (m : ℕ) (X : ℝ) (p : Nat.Primes) : ℝ :=
  ∑' q : XiZeroCopy,
    gammaSixSuspensionDeterminantPrimeCurrent m q p *
      (xiResolventPoint X q).re

theorem summable_gammaSixSuspensionDeterminantCurrent_mul_resolvent_re
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 ≤ X) :
    Summable (fun q : XiZeroCopy =>
      gammaSixSuspensionDeterminantPrimeCurrent m q p *
        (xiResolventPoint X q).re) := by
  apply Summable.of_nonneg_of_le
    (fun q => mul_nonneg
      (gammaSixSuspensionDeterminantPrimeCurrent_nonneg hm q p)
      (xiResolventPoint_re_pos hX q).le)
    (fun q => ?_)
    (summable_gaussHodgeMassCurrent_mul_norm_resolventPoint hm p hX)
  calc
    gammaSixSuspensionDeterminantPrimeCurrent m q p *
          (xiResolventPoint X q).re ≤
        gaussHodgeMassCurrent m q p * (xiResolventPoint X q).re :=
      mul_le_mul_of_nonneg_right
        (gammaSixSuspensionDeterminantPrimeCurrent_le_gaussHodge hm q p)
        (xiResolventPoint_re_pos hX q).le
    _ ≤ gaussHodgeMassCurrent m q p * ‖xiResolventPoint X q‖ :=
      mul_le_mul_of_nonneg_left (Complex.re_le_norm _)
        (gaussHodgeMassCurrent_nonneg hm q p)

theorem gammaSixSuspensionDeterminantCurrent_mul_resolvent_re_le_sourceTrace
    {m : ℕ} (hm : 1 ≤ m) {X : ℝ} (hX : 0 ≤ X)
    (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixSuspensionDeterminantPrimeCurrent m q p *
        (xiResolventPoint X q).re ≤
      gammaSixSuspensionDeterminantPrimeSourceResolventTrace m X p := by
  exact (summable_gammaSixSuspensionDeterminantCurrent_mul_resolvent_re hm p hX).le_tsum
    q (fun r _ => mul_nonneg
      (gammaSixSuspensionDeterminantPrimeCurrent_nonneg hm r p)
      (xiResolventPoint_re_pos hX r).le)

/-- **Derivative-free Frankenstein endpoint.**  Prime summability of one literal source
suspension-determinant resolvent trace is equivalent to RH.  This is strictly closer to a source
estimate than the virial version: no differentiation or fitted divisor coefficient remains. -/
theorem summable_gammaSixSuspensionDeterminantPrimeSourceResolventTrace_iff_riemannHypothesis
    {m : ℕ} (hm : 1 ≤ m) {X : ℝ} (hX : 0 < X) :
    Summable (gammaSixSuspensionDeterminantPrimeSourceResolventTrace m X) ↔
      RiemannHypothesis := by
  constructor
  · intro hsource
    apply (forall_summable_gammaSixSuspensionDeterminantPrimeCurrent_iff_riemannHypothesis hm).1
    intro q
    have hweighted : Summable (fun p : Nat.Primes =>
        gammaSixSuspensionDeterminantPrimeCurrent m q p *
          (xiResolventPoint X q).re) := by
      apply Summable.of_nonneg_of_le
      · intro p
        exact mul_nonneg
          (gammaSixSuspensionDeterminantPrimeCurrent_nonneg hm q p)
          (xiResolventPoint_re_pos hX.le q).le
      · exact gammaSixSuspensionDeterminantCurrent_mul_resolvent_re_le_sourceTrace
          hm hX.le q
      · exact hsource
    exact (summable_mul_right_iff (xiResolventPoint_re_pos hX.le q).ne').1 hweighted
  · intro hRH
    have hzero : gammaSixSuspensionDeterminantPrimeSourceResolventTrace m X = 0 := by
      funext p
      change gammaSixSuspensionDeterminantPrimeSourceResolventTrace m X p = 0
      rw [gammaSixSuspensionDeterminantPrimeSourceResolventTrace]
      have hterm : (fun q : XiZeroCopy =>
          gammaSixSuspensionDeterminantPrimeCurrent m q p *
            (xiResolventPoint X q).re) = 0 := by
        funext q
        have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
          (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2
            (xi_divisor_support_re_eq_half_of_rh hRH q.1)
        rw [gammaSixSuspensionDeterminantPrimeCurrent,
          gaussGammaSixSuspensionTraceEnergy_eq_pairedBoundaryEnergy,
          gaussGammaSixPairedBoundaryEnergy_eq_splitEnergy,
          reciprocalCharacterSplitEnergy, hrate]
        simp
      rw [hterm]
      simp
    rw [hzero]
    exact summable_zero

end

end RHTower
