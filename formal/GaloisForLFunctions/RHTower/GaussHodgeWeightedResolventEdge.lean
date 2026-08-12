import GaloisForLFunctions.RHTower.GaussHodgeSeamEnergyBridge
import GaloisForLFunctions.RHTower.SourceHorizontalWoldResolventEdge
import GaloisForLFunctions.RHTower.XiSquaredCompleteMonotonicityFarRay

/-!
# Gauss--Hodge source pairing meets the Xi resolvent edge

This module replaces the nonlinear Wold selector by a literal labelled source pairing.  At every
Gauss depth and prime label, `gaussHodgeMassCurrent` pairs the two reflection-odd components of the
source-horizontal carrier before scalarization.  It is nonnegative, reflection-even, and strictly
positive exactly off the critical line.  Bounded normalization therefore preserves all divisor
copies, their multiplicities, the prime label, the Gauss depth, and both reflection orientations.

Weighted diagonal-edge oscillation then proves: at any fixed nonnegative resolvent shift, RH is
equivalent to nonnegativity of every full-divisor moment weighted by this source pairing.  This is
the reflection-doubled producer category forced by the single-holomorphic-profile no-go.
-/

open Complex

namespace RHTower

noncomputable section

/-- Bounded normalization of the labelled Gauss--Hodge source pairing. -/
def gaussHodgeNormalizedMassWeight (m : ℕ) (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  gaussHodgeMassCurrent m q p / (1 + gaussHodgeMassCurrent m q p)

theorem gaussHodgeNormalizedMassWeight_nonneg
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) (q : XiZeroCopy) :
    0 ≤ gaussHodgeNormalizedMassWeight m p q := by
  rw [gaussHodgeNormalizedMassWeight]
  exact div_nonneg (gaussHodgeMassCurrent_nonneg hm q p)
    (by linarith [gaussHodgeMassCurrent_nonneg hm q p])

theorem gaussHodgeNormalizedMassWeight_le_one
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) (q : XiZeroCopy) :
    gaussHodgeNormalizedMassWeight m p q ≤ 1 := by
  rw [gaussHodgeNormalizedMassWeight]
  have hden : 0 < 1 + gaussHodgeMassCurrent m q p := by
    linarith [gaussHodgeMassCurrent_nonneg hm q p]
  rw [div_le_one hden]
  linarith

theorem gaussHodgeNormalizedMassWeight_pos_iff
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) (q : XiZeroCopy) :
    0 < gaussHodgeNormalizedMassWeight m p q ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [gaussHodgeNormalizedMassWeight]
  have hden : 0 < 1 + gaussHodgeMassCurrent m q p := by
    linarith [gaussHodgeMassCurrent_nonneg hm q p]
  rw [div_pos_iff_of_pos_right hden]
  constructor
  · intro hpos hline
    rw [(gaussHodgeMassCurrent_eq_zero_iff hm q p).2 hline] at hpos
    exact lt_irrefl 0 hpos
  · intro hoff
    exact gaussHodgeMassCurrent_pos_of_offLine hm q hoff p

/-- Strict source-pairing weight is exactly nonvanishing of the reflected FE--Schwarz prime seam.
This identifies the coefficient with an existing two-orientation arithmetic source object, rather
than a divisor-selected sign. -/
theorem gaussHodgeNormalizedMassWeight_pos_iff_seamCharge_ne_zero
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) (q : XiZeroCopy) :
    0 < gaussHodgeNormalizedMassWeight m p q ↔
      orbitwiseNatPrimeSeamCharge (p : ℕ) (q.1 : ℂ) ≠ 0 := by
  rw [gaussHodgeNormalizedMassWeight_pos_iff hm p q]
  exact (orbitwiseNatSeamCharge_eq_zero_iff
    (q.1 : ℂ) p.prop.one_lt).not.symm

@[simp] theorem gaussHodgeNormalizedMassWeight_reflection
    (m : ℕ) (p : Nat.Primes) (q : XiZeroCopy) :
    gaussHodgeNormalizedMassWeight m p (xiZeroCopyLineConjEquiv q) =
      gaussHodgeNormalizedMassWeight m p q := by
  rw [gaussHodgeNormalizedMassWeight, gaussHodgeNormalizedMassWeight,
    gaussHodgeMassCurrent_reflection]

/-- Uniform divisor bound for a fixed labelled Gauss--Hodge current. -/
def gaussHodgeMassCurrentUniformBound (m : ℕ) (p : Nat.Primes) : ℝ :=
  (Real.log 2 / 2 * gaussChannelResidueCurrent m p *
      primeActivationOccupancyFisherDensity p) *
    ((2 * ((p : ℕ) : ℝ) ^ ((1 : ℝ) / 2) /
        Real.log ((p : ℕ) : ℝ)) * (2 * ((p : ℕ) : ℝ)))

theorem hodgeMassShape_centeredRate_le_uniformBound
    (q : XiZeroCopy) (p : Nat.Primes) :
    hodgeMassShape ((p : ℕ) : ℝ) (primeDepthBVWoldXiCenteredRate q.1) ≤
      (2 * ((p : ℕ) : ℝ) ^ ((1 : ℝ) / 2) /
          Real.log ((p : ℕ) : ℝ)) * (2 * ((p : ℕ) : ℝ)) := by
  let s : ℝ := ((p : ℕ) : ℝ)
  let t : ℝ := primeDepthBVWoldXiCenteredRate q.1
  have hs : 1 < s := by
    dsimp only [s]
    exact_mod_cast p.prop.one_lt
  have hs0 : 0 < s := lt_trans one_pos hs
  have ht : |t| ≤ 1 := by simpa only [t] using abs_centeredRate_le_one q
  have htUpper : t ≤ 1 := (abs_le.mp ht).2
  have hnegUpper : -t ≤ 1 := by linarith [(abs_le.mp ht).1]
  have hpow : s ^ t ≤ s := by
    have h := (Real.strictMono_rpow_of_base_gt_one hs).monotone htUpper
    simpa only [Real.rpow_one] using h
  have hpowNeg : s ^ (-t) ≤ s := by
    have h := (Real.strictMono_rpow_of_base_gt_one hs).monotone hnegUpper
    simpa only [Real.rpow_one] using h
  have hdefect : s ^ t + s ^ (-t) - 2 ≤ 2 * s := by
    linarith
  have hcoeff : 0 ≤ 2 * s ^ ((1 : ℝ) / 2) / Real.log s := by positivity
  have hshape := HTGeometry.shape_le_rpow_defect hs ht
  change t * (s ^ t - s ^ (-t)) ≤ _ at hshape
  change t * (s ^ t - s ^ (-t)) ≤ _
  exact hshape.trans (mul_le_mul_of_nonneg_left hdefect hcoeff)

/-- Fixed depth and prime labels make the literal, unnormalized source pairing uniformly bounded
over every Xi multiplicity copy.  The open critical strip supplies the compact horizontal window;
no bounded functional calculus is needed. -/
theorem gaussHodgeMassCurrent_le_uniformBound
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) (q : XiZeroCopy) :
    gaussHodgeMassCurrent m q p ≤ gaussHodgeMassCurrentUniformBound m p := by
  have hcoefficient : 0 ≤ Real.log 2 / 2 * gaussChannelResidueCurrent m p *
      primeActivationOccupancyFisherDensity p := by
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hcurrent := gaussChannelResidueCurrent_pos hm p
    have hdensity := primeActivationOccupancyFisherDensity_pos' p
    positivity
  rw [gaussHodgeMassCurrent_eq_boost_square,
    gaussHodgeMassCurrentUniformBound]
  exact mul_le_mul_of_nonneg_left
    (hodgeMassShape_centeredRate_le_uniformBound q p) hcoefficient

theorem gaussHodgeMassCurrentUniformBound_nonneg
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    0 ≤ gaussHodgeMassCurrentUniformBound m p := by
  rw [gaussHodgeMassCurrentUniformBound]
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcurrent := gaussChannelResidueCurrent_pos hm p
  have hdensity := primeActivationOccupancyFisherDensity_pos' p
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
  have hlogPrime : 0 < Real.log ((p : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  positivity

/-- Full-carrier diagonal resolvent moment with the labelled source-pairing coefficient. -/
def gaussHodgeWeightedResolventMoment
    (m : ℕ) (p : Nat.Primes) (n : ℕ) (X : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, (gaussHodgeNormalizedMassWeight m p q : ℂ) *
    xiResolventPoint X q ^ (n + 1)

def gaussHodgeOffCriticalWeightedResolventMoment
    (m : ℕ) (p : Nat.Primes) (n : ℕ) (X : ℝ) : ℂ :=
  ∑' q : XiOffCriticalCopy,
    (gaussHodgeNormalizedMassWeight m p q.1 : ℂ) *
      xiResolventPoint X q.1 ^ (n + 1)

theorem summable_gaussHodgeNormalizedMassWeight_mul_norm_resolventPoint
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 ≤ X) :
    Summable (fun q : XiZeroCopy =>
      gaussHodgeNormalizedMassWeight m p q * ‖xiResolventPoint X q‖) := by
  apply Summable.of_nonneg_of_le
    (fun q => mul_nonneg (gaussHodgeNormalizedMassWeight_nonneg hm p q)
      (norm_nonneg _)) ?_ (summable_norm_xiResolventPoint hX)
  intro q
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (gaussHodgeNormalizedMassWeight_le_one hm p q) (norm_nonneg _)

theorem summable_gaussHodgeNormalizedMassWeight_mul_norm_resolventPoint_pow
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    Summable (fun q : XiZeroCopy =>
      gaussHodgeNormalizedMassWeight m p q *
        ‖xiResolventPoint X q ^ (n + 1)‖) := by
  apply Summable.of_nonneg_of_le
    (fun q => mul_nonneg (gaussHodgeNormalizedMassWeight_nonneg hm p q)
      (norm_nonneg _)) ?_ (summable_norm_xiResolventPoint_pow hX n)
  intro q
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (gaussHodgeNormalizedMassWeight_le_one hm p q) (norm_nonneg _)

/-- Critical copies have exact zero source-pairing coefficient, so the full-carrier observable is
identical to its strictly positive off-critical restriction. -/
theorem gaussHodgeWeightedResolventMoment_eq_offCritical
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    gaussHodgeWeightedResolventMoment m p n X =
      gaussHodgeOffCriticalWeightedResolventMoment m p n X := by
  let f : XiZeroCopy → ℂ := fun q =>
    (gaussHodgeNormalizedMassWeight m p q : ℂ) *
      xiResolventPoint X q ^ (n + 1)
  have hsumNorm : Summable (fun q : XiZeroCopy => ‖f q‖) := by
    simpa [f, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gaussHodgeNormalizedMassWeight_nonneg hm p _)] using
      summable_gaussHodgeNormalizedMassWeight_mul_norm_resolventPoint_pow hm p hX n
  have hsum : Summable f := hsumNorm.of_norm
  let P : Set XiZeroCopy :=
    ({q | (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl P
  have hcomp : (∑' q : ↑Pᶜ, f q.1) = 0 := by
    have hfun : (fun q : ↑Pᶜ => f q.1) = fun _ => 0 := by
      funext q
      have hline : (q.1.1 : ℂ).re = 1 / 2 := by
        simpa [P] using q.2
      have hmass0 : gaussHodgeMassCurrent m q.1 p = 0 :=
        (gaussHodgeMassCurrent_eq_zero_iff hm q.1 p).2 hline
      simp [f, gaussHodgeNormalizedMassWeight, hmass0]
    rw [hfun, tsum_zero]
  rw [hcomp, add_zero] at hsplit
  rw [gaussHodgeWeightedResolventMoment,
    gaussHodgeOffCriticalWeightedResolventMoment]
  simpa only [f, P, Set.mem_setOf_eq, XiOffCriticalCopy] using hsplit.symm

/-- Source-pairing weighted edge collapse: all diagonal moment real parts cannot be nonnegative in
the presence of even one off-critical divisor copy. -/
theorem isEmpty_xiOffCriticalCopy_of_forall_gaussHodgeWeightedMoment_re_nonneg
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 ≤ X)
    (hmom : ∀ n : ℕ, 0 ≤ (gaussHodgeWeightedResolventMoment m p n X).re) :
    IsEmpty XiOffCriticalCopy := by
  constructor
  intro qa
  letI : Nonempty XiOffCriticalCopy := ⟨qa⟩
  obtain ⟨q, hqreal, _hqmax⟩ :=
    GaloisForLFunctions.HTGeometry.exists_positiveReal_maximal_of_forall_weightedPowerMoment_re_nonneg
      (fun q : XiOffCriticalCopy => xiResolventPoint X q.1)
      (fun q : XiOffCriticalCopy => gaussHodgeNormalizedMassWeight m p q.1)
      (fun q => xiResolventPoint_ne_zero hX q.1)
      (fun q => (gaussHodgeNormalizedMassWeight_pos_iff hm p q.1).2 (by
        simpa only [XiOffCriticalCopy, Set.mem_compl_iff, Set.mem_setOf_eq] using q.2))
      (fun {r} hr => by
        have hpre := Set.Finite.preimage
          (f := fun q : XiOffCriticalCopy => q.1)
          Subtype.val_injective.injOn
          (finite_setOf_le_norm_xiResolventPoint hX hr)
        simpa only [Set.preimage_setOf_eq] using hpre)
      ((summable_gaussHodgeNormalizedMassWeight_mul_norm_resolventPoint hm p hX).subtype _)
      (fun n =>
        (summable_gaussHodgeNormalizedMassWeight_mul_norm_resolventPoint_pow
          hm p hX n).subtype _)
      (fun n => by
        have h := hmom n
        rw [gaussHodgeWeightedResolventMoment_eq_offCritical hm p hX n] at h
        simpa only [gaussHodgeOffCriticalWeightedResolventMoment] using h)
  have hline : (q.1.1 : ℂ).re = 1 / 2 :=
    xiZeroCopy_re_eq_half_of_xiResolventPoint_eq_norm q.1 hqreal
  exact q.2 hline

/-- Full-carrier, prime-labelled Gauss--Hodge weighted moment positivity forces RH. -/
theorem riemannHypothesis_of_forall_gaussHodgeWeightedResolventMoment_re_nonneg
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 ≤ X)
    (hmom : ∀ n : ℕ, 0 ≤ (gaussHodgeWeightedResolventMoment m p n X).re) :
    RiemannHypothesis := by
  have hempty :=
    isEmpty_xiOffCriticalCopy_of_forall_gaussHodgeWeightedMoment_re_nonneg hm p hX hmom
  have hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
    intro q
    by_contra hq
    exact hempty.false ⟨q, hq⟩
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  refine ⟨(q.1 : ℂ).im, ?_⟩
  apply Complex.ext
  · simp [xiSpectralPoint]
  · simp [xiSpectralPoint, hline q]

/-- **Prime-labelled Frankenstein endpoint.**  At every Gauss depth, every prime label, and every
nonnegative resolvent shift, RH is equivalent to nonnegativity of all full-divisor diagonal
moments weighted by the bounded, reflection-doubled Gauss--Hodge source pairing. -/
theorem forall_gaussHodgeWeightedResolventMoment_re_nonneg_iff_riemannHypothesis
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 ≤ X) :
    (∀ n : ℕ, 0 ≤ (gaussHodgeWeightedResolventMoment m p n X).re) ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_forall_gaussHodgeWeightedResolventMoment_re_nonneg hm p hX
  · intro hRH n
    rw [gaussHodgeWeightedResolventMoment]
    have hfun : (fun q : XiZeroCopy =>
        (gaussHodgeNormalizedMassWeight m p q : ℂ) *
          xiResolventPoint X q ^ (n + 1)) = fun _ => 0 := by
      funext q
      have hline := xi_divisor_support_re_eq_half_of_rh hRH q.1
      have hmass0 := (gaussHodgeMassCurrent_eq_zero_iff hm q p).2 hline
      simp [gaussHodgeNormalizedMassWeight, hmass0]
    rw [hfun, tsum_zero]
    exact le_rfl

/-! ## Literal pre-scalarization source current -/

/-- Full-carrier resolvent moments weighted by the literal Gauss--Hodge current, with no bounded
normalization or spectral selector. -/
def gaussHodgeSourceResolventMoment
    (m : ℕ) (p : Nat.Primes) (n : ℕ) (X : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, (gaussHodgeMassCurrent m q p : ℂ) *
    xiResolventPoint X q ^ (n + 1)

def gaussHodgeOffCriticalSourceResolventMoment
    (m : ℕ) (p : Nat.Primes) (n : ℕ) (X : ℝ) : ℂ :=
  ∑' q : XiOffCriticalCopy, (gaussHodgeMassCurrent m q.1 p : ℂ) *
    xiResolventPoint X q.1 ^ (n + 1)

theorem summable_gaussHodgeMassCurrent_mul_norm_resolventPoint
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 ≤ X) :
    Summable (fun q : XiZeroCopy =>
      gaussHodgeMassCurrent m q p * ‖xiResolventPoint X q‖) := by
  apply Summable.of_nonneg_of_le
    (fun q => mul_nonneg (gaussHodgeMassCurrent_nonneg hm q p) (norm_nonneg _))
    (fun q => mul_le_mul_of_nonneg_right
      (gaussHodgeMassCurrent_le_uniformBound hm p q) (norm_nonneg _))
    ((summable_norm_xiResolventPoint hX).mul_left
      (gaussHodgeMassCurrentUniformBound m p))

theorem summable_gaussHodgeMassCurrent_mul_norm_resolventPoint_pow
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    Summable (fun q : XiZeroCopy =>
      gaussHodgeMassCurrent m q p * ‖xiResolventPoint X q ^ (n + 1)‖) := by
  apply Summable.of_nonneg_of_le
    (fun q => mul_nonneg (gaussHodgeMassCurrent_nonneg hm q p) (norm_nonneg _))
    (fun q => mul_le_mul_of_nonneg_right
      (gaussHodgeMassCurrent_le_uniformBound hm p q) (norm_nonneg _))
    ((summable_norm_xiResolventPoint_pow hX n).mul_left
      (gaussHodgeMassCurrentUniformBound m p))

/-- The literal source-weighted resolvent tower differentiates termwise on the positive shift
ray. The Gauss--Hodge coefficient is shift-independent and uniformly bounded on the divisor. -/
theorem hasDerivAt_gaussHodgeSourceResolventMoment
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    HasDerivAt (fun Y : ℝ => gaussHodgeSourceResolventMoment m p n Y)
      (-((n : ℂ) + 1) * gaussHodgeSourceResolventMoment m p (n + 1) X) X := by
  let B := gaussHodgeMassCurrentUniformBound m p
  have hu : Summable (fun q : XiZeroCopy =>
      B * ((n : ℝ) + 1) * ‖xiZeroCopyReciprocalSquare q‖ ^ (n + 2)) := by
    have h := (summable_xiZeroCopyReciprocalSquare_pow (n + 1)).norm
    simp only [norm_pow] at h
    exact h.mul_left (B * ((n : ℝ) + 1))
  have hderiv : ∀ q : XiZeroCopy, ∀ Y ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun T : ℝ =>
        (gaussHodgeMassCurrent m q p : ℂ) * xiResolventPoint T q ^ (n + 1))
        (-((n : ℂ) + 1) * (gaussHodgeMassCurrent m q p : ℂ) *
          xiResolventPoint Y q ^ (n + 2)) Y := by
    intro q Y hY
    have hbase := hasDerivAt_xiShiftedReciprocalSquare_pow hY q n
    have heq : (fun T : ℝ => xiShiftedReciprocalSquare T q ^ (n + 1)) =ᶠ[nhds Y]
        (fun T : ℝ => xiResolventPoint T q ^ (n + 1)) := by
      filter_upwards [Ioi_mem_nhds hY] with T hT
      rw [xiShiftedReciprocalSquare_eq_xiResolventPoint hT.le]
    have hres : HasDerivAt (fun T : ℝ => xiResolventPoint T q ^ (n + 1))
        (-((n : ℂ) + 1) * xiResolventPoint Y q ^ (n + 2)) Y := by
      rw [← xiShiftedReciprocalSquare_eq_xiResolventPoint hY.le]
      exact hbase.congr_of_eventuallyEq heq.symm
    have hscaled := hres.const_mul (gaussHodgeMassCurrent m q p : ℂ)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hbound : ∀ q : XiZeroCopy, ∀ Y ∈ Set.Ioi (0 : ℝ),
      ‖-((n : ℂ) + 1) * (gaussHodgeMassCurrent m q p : ℂ) *
          xiResolventPoint Y q ^ (n + 2)‖ ≤
        B * ((n : ℝ) + 1) * ‖xiZeroCopyReciprocalSquare q‖ ^ (n + 2) := by
    intro q Y hY
    have hmass0 := gaussHodgeMassCurrent_nonneg hm q p
    have hmass := gaussHodgeMassCurrent_le_uniformBound hm p q
    have hres := norm_xiShiftedReciprocalSquare_le hY.le q
    have hcast : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
        Complex.norm_natCast]
      push_cast
      ring
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hmass0, norm_pow, hcast]
    rw [← xiShiftedReciprocalSquare_eq_xiResolventPoint hY.le]
    change gaussHodgeMassCurrent m q p ≤ B at hmass
    have hcoef : ((n : ℝ) + 1) * gaussHodgeMassCurrent m q p ≤
        B * ((n : ℝ) + 1) := by
      calc
        ((n : ℝ) + 1) * gaussHodgeMassCurrent m q p ≤
            ((n : ℝ) + 1) * B :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
        _ = B * ((n : ℝ) + 1) := by ring
    calc
      ((n : ℝ) + 1) * gaussHodgeMassCurrent m q p *
          ‖xiShiftedReciprocalSquare Y q‖ ^ (n + 2) ≤
          B * ((n : ℝ) + 1) *
            ‖xiShiftedReciprocalSquare Y q‖ ^ (n + 2) :=
        mul_le_mul_of_nonneg_right hcoef (pow_nonneg (norm_nonneg _) _)
      _ ≤ B * ((n : ℝ) + 1) *
          ‖xiZeroCopyReciprocalSquare q‖ ^ (n + 2) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hres _)
          (mul_nonneg (gaussHodgeMassCurrentUniformBound_nonneg hm p) (by positivity))
  have hsumNorm : Summable (fun q : XiZeroCopy =>
      ‖(gaussHodgeMassCurrent m q p : ℂ) *
        xiResolventPoint X q ^ (n + 1)‖) := by
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gaussHodgeMassCurrent_nonneg hm _ p)] using
      summable_gaussHodgeMassCurrent_mul_norm_resolventPoint_pow hm p hX.le n
  have hsum0 : Summable (fun q : XiZeroCopy =>
      (gaussHodgeMassCurrent m q p : ℂ) *
        xiResolventPoint X q ^ (n + 1)) := hsumNorm.of_norm
  have hmain := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi
    hderiv hbound (Set.mem_Ioi.mpr hX) hsum0 (Set.mem_Ioi.mpr hX)
  simpa only [gaussHodgeSourceResolventMoment, Nat.add_assoc, Nat.reduceAdd,
    mul_assoc, tsum_mul_left] using hmain

theorem hasDerivAt_re_gaussHodgeSourceResolventMoment
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    HasDerivAt (fun Y : ℝ => (gaussHodgeSourceResolventMoment m p n Y).re)
      (-((n : ℝ) + 1) * (gaussHodgeSourceResolventMoment m p (n + 1) X).re) X := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt X
    (hasDerivAt_gaussHodgeSourceResolventMoment hm p hX n)
  have hval : Complex.reCLM
      (-((n : ℂ) + 1) * gaussHodgeSourceResolventMoment m p (n + 1) X) =
      -((n : ℝ) + 1) * (gaussHodgeSourceResolventMoment m p (n + 1) X).re := by
    simp [Complex.mul_re]
  rw [hval] at h
  exact h

/-- Single Hodge-weighted resolvent field whose derivative jet is the full source-moment tower. -/
def gaussHodgeSourceResolventField (m : ℕ) (p : Nat.Primes) (X : ℝ) : ℝ :=
  (gaussHodgeSourceResolventMoment m p 0 X).re

/-- Every source moment is one alternating derivative of a single literal paired resolvent field. -/
theorem iteratedDeriv_gaussHodgeSourceResolventField
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) (n : ℕ) :
    ∀ {X : ℝ}, 0 < X →
      iteratedDeriv n (gaussHodgeSourceResolventField m p) X =
        (-1 : ℝ) ^ n * (n.factorial : ℝ) *
          (gaussHodgeSourceResolventMoment m p n X).re := by
  induction n with
  | zero =>
      intro X _
      simp [gaussHodgeSourceResolventField]
  | succ n ih =>
      intro X hX
      have heq : iteratedDeriv n (gaussHodgeSourceResolventField m p) =ᶠ[nhds X]
          (fun Y : ℝ => (-1 : ℝ) ^ n * (n.factorial : ℝ) *
            (gaussHodgeSourceResolventMoment m p n Y).re) := by
        filter_upwards [Ioi_mem_nhds hX] with Y hY using ih hY
      rw [iteratedDeriv_succ, heq.deriv_eq]
      have hd := (hasDerivAt_re_gaussHodgeSourceResolventMoment hm p hX n).const_mul
        ((-1 : ℝ) ^ n * (n.factorial : ℝ))
      rw [hd.deriv]
      push_cast [Nat.factorial_succ]
      ring

/-- Alternating derivative positivity of the single Hodge field is exactly positivity of the
corresponding literal source moment. -/
theorem alternating_iteratedDeriv_gaussHodgeSourceResolventField_nonneg_iff
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    0 ≤ (-1 : ℝ) ^ n *
        iteratedDeriv n (gaussHodgeSourceResolventField m p) X ↔
      0 ≤ (gaussHodgeSourceResolventMoment m p n X).re := by
  rw [iteratedDeriv_gaussHodgeSourceResolventField hm p n hX]
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [show (-1 : ℝ) ^ n *
      ((-1 : ℝ) ^ n * (n.factorial : ℝ) *
        (gaussHodgeSourceResolventMoment m p n X).re) =
      ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
        ((n.factorial : ℝ) *
          (gaussHodgeSourceResolventMoment m p n X).re) by ring,
    hsign, one_mul]
  constructor <;> intro h
  · nlinarith [show (0 : ℝ) < n.factorial by positivity]
  · exact mul_nonneg (by positivity) h

/-- Literal source moments equal their strictly positive restriction only because the source
pairing itself vanishes on critical copies.  No post hoc support indicator occurs in the full
observable. -/
theorem gaussHodgeSourceResolventMoment_eq_offCritical
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    gaussHodgeSourceResolventMoment m p n X =
      gaussHodgeOffCriticalSourceResolventMoment m p n X := by
  let f : XiZeroCopy → ℂ := fun q =>
    (gaussHodgeMassCurrent m q p : ℂ) * xiResolventPoint X q ^ (n + 1)
  have hsumNorm : Summable (fun q : XiZeroCopy => ‖f q‖) := by
    simpa [f, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gaussHodgeMassCurrent_nonneg hm _ p)] using
      summable_gaussHodgeMassCurrent_mul_norm_resolventPoint_pow hm p hX n
  have hsum : Summable f := hsumNorm.of_norm
  let P : Set XiZeroCopy :=
    ({q | (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl P
  have hcomp : (∑' q : ↑Pᶜ, f q.1) = 0 := by
    have hfun : (fun q : ↑Pᶜ => f q.1) = fun _ => 0 := by
      funext q
      have hline : (q.1.1 : ℂ).re = 1 / 2 := by
        simpa [P] using q.2
      have hmass0 : gaussHodgeMassCurrent m q.1 p = 0 :=
        (gaussHodgeMassCurrent_eq_zero_iff hm q.1 p).2 hline
      simp [f, hmass0]
    rw [hfun, tsum_zero]
  rw [hcomp, add_zero] at hsplit
  rw [gaussHodgeSourceResolventMoment,
    gaussHodgeOffCriticalSourceResolventMoment]
  simpa only [f, P, XiOffCriticalCopy] using hsplit.symm

theorem isEmpty_xiOffCriticalCopy_of_forall_gaussHodgeSourceMoment_re_nonneg
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 ≤ X)
    (hmom : ∀ n : ℕ, 0 ≤ (gaussHodgeSourceResolventMoment m p n X).re) :
    IsEmpty XiOffCriticalCopy := by
  constructor
  intro qa
  letI : Nonempty XiOffCriticalCopy := ⟨qa⟩
  obtain ⟨q, hqreal, _hqmax⟩ :=
    GaloisForLFunctions.HTGeometry.exists_positiveReal_maximal_of_forall_weightedPowerMoment_re_nonneg
      (fun q : XiOffCriticalCopy => xiResolventPoint X q.1)
      (fun q : XiOffCriticalCopy => gaussHodgeMassCurrent m q.1 p)
      (fun q => xiResolventPoint_ne_zero hX q.1)
      (fun q => gaussHodgeMassCurrent_pos_of_offLine hm q.1 (by
        simpa only [XiOffCriticalCopy, Set.mem_compl_iff, Set.mem_setOf_eq] using q.2) p)
      (fun {r} hr => by
        have hpre := Set.Finite.preimage
          (f := fun q : XiOffCriticalCopy => q.1)
          Subtype.val_injective.injOn
          (finite_setOf_le_norm_xiResolventPoint hX hr)
        simpa only [Set.preimage_setOf_eq] using hpre)
      ((summable_gaussHodgeMassCurrent_mul_norm_resolventPoint hm p hX).subtype _)
      (fun n =>
        (summable_gaussHodgeMassCurrent_mul_norm_resolventPoint_pow hm p hX n).subtype _)
      (fun n => by
        have h := hmom n
        rw [gaussHodgeSourceResolventMoment_eq_offCritical hm p hX n] at h
        simpa only [gaussHodgeOffCriticalSourceResolventMoment] using h)
  have hline : (q.1.1 : ℂ).re = 1 / 2 :=
    xiZeroCopy_re_eq_half_of_xiResolventPoint_eq_norm q.1 hqreal
  exact q.2 hline

theorem riemannHypothesis_of_forall_gaussHodgeSourceResolventMoment_re_nonneg
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 ≤ X)
    (hmom : ∀ n : ℕ, 0 ≤ (gaussHodgeSourceResolventMoment m p n X).re) :
    RiemannHypothesis := by
  have hempty :=
    isEmpty_xiOffCriticalCopy_of_forall_gaussHodgeSourceMoment_re_nonneg hm p hX hmom
  have hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
    intro q
    by_contra hq
    exact hempty.false ⟨q, hq⟩
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  refine ⟨(q.1 : ℂ).im, ?_⟩
  apply Complex.ext
  · simp [xiSpectralPoint]
  · simp [xiSpectralPoint, hline q]

/-- Under RH the literal source-weighted moment vanishes: the Gauss--Hodge current kills every
critical-line divisor copy before the resolvent is read. -/
theorem gaussHodgeSourceResolventMoment_eq_zero_of_rh
    (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) (n : ℕ) (X : ℝ) :
    gaussHodgeSourceResolventMoment m p n X = 0 := by
  rw [gaussHodgeSourceResolventMoment]
  have hfun : (fun q : XiZeroCopy =>
      (gaussHodgeMassCurrent m q p : ℂ) *
        xiResolventPoint X q ^ (n + 1)) = fun _ => 0 := by
    funext q
    have hline := xi_divisor_support_re_eq_half_of_rh hRH q.1
    have hmass0 : gaussHodgeMassCurrent m q p = 0 :=
      (gaussHodgeMassCurrent_eq_zero_iff hm q p).2 hline
    simp [hmass0]
  rw [hfun, tsum_zero]

/-- The literal source current is nonnegative throughout the unconditional Xi resolvent sector:
all orders through eighteen at every positive shift, and every order on the quadratic far ray. -/
theorem gaussHodgeSourceResolventMoment_re_nonneg_of_le_or_far
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {n : ℕ} {X : ℝ} (hX : 0 < X)
    (hsector : n ≤ 18 ∨ ((n : ℝ) + 1) ^ 2 ≤ X) :
    0 ≤ (gaussHodgeSourceResolventMoment m p n X).re := by
  have hsumNorm : Summable (fun q : XiZeroCopy =>
      ‖(gaussHodgeMassCurrent m q p : ℂ) *
        xiResolventPoint X q ^ (n + 1)‖) := by
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gaussHodgeMassCurrent_nonneg hm _ p)] using
      summable_gaussHodgeMassCurrent_mul_norm_resolventPoint_pow hm p hX.le n
  have hsum : Summable (fun q : XiZeroCopy =>
      (gaussHodgeMassCurrent m q p : ℂ) *
        xiResolventPoint X q ^ (n + 1)) := hsumNorm.of_norm
  rw [gaussHodgeSourceResolventMoment, Complex.re_tsum hsum]
  apply tsum_nonneg
  intro q
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_nonneg (gaussHodgeMassCurrent_nonneg hm q p)
  rcases hsector with hn | hfar
  · rw [← xiShiftedReciprocalSquare_eq_xiResolventPoint hX.le]
    exact (re_xiShiftedReciprocalSquare_pow_pos_of_le_nineteen hX q (by omega)).le
  · exact (xiResolventPoint_pow_re_pos le_rfl (le_trans (by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]) hfar) q).le

/-- Off RH the same safe-sector source moment is strictly positive: one off-line divisor copy has
strictly positive Gauss--Hodge mass and every resolvent atom has positive real part. -/
theorem gaussHodgeSourceResolventMoment_re_pos_of_not_rh_of_le_or_far
    (hnot : ¬ RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes)
    {n : ℕ} {X : ℝ} (hX : 0 < X)
    (hsector : n ≤ 18 ∨ ((n : ℝ) + 1) ^ 2 ≤ X) :
    0 < (gaussHodgeSourceResolventMoment m p n X).re := by
  have hsumNorm : Summable (fun q : XiZeroCopy =>
      ‖(gaussHodgeMassCurrent m q p : ℂ) *
        xiResolventPoint X q ^ (n + 1)‖) := by
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gaussHodgeMassCurrent_nonneg hm _ p)] using
      summable_gaussHodgeMassCurrent_mul_norm_resolventPoint_pow hm p hX.le n
  have hsum : Summable (fun q : XiZeroCopy =>
      (gaussHodgeMassCurrent m q p : ℂ) *
        xiResolventPoint X q ^ (n + 1)) := hsumNorm.of_norm
  have hre : Summable (fun q : XiZeroCopy =>
      ((gaussHodgeMassCurrent m q p : ℂ) *
        xiResolventPoint X q ^ (n + 1)).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  have hatom : ∀ q : XiZeroCopy, 0 < (xiResolventPoint X q ^ (n + 1)).re := by
    intro q
    rcases hsector with hn | hfar
    · rw [← xiShiftedReciprocalSquare_eq_xiResolventPoint hX.le]
      exact re_xiShiftedReciprocalSquare_pow_pos_of_le_nineteen hX q (by omega)
    · exact xiResolventPoint_pow_re_pos le_rfl (le_trans (by
        nlinarith [Nat.cast_nonneg (α := ℝ) n]) hfar) q
  have hnonneg : ∀ q : XiZeroCopy,
      0 ≤ ((gaussHodgeMassCurrent m q p : ℂ) *
        xiResolventPoint X q ^ (n + 1)).re := by
    intro q
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (gaussHodgeMassCurrent_nonneg hm q p) (hatom q).le
  have hoff : ∃ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 := by
    by_contra hnone
    apply hnot
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hline : (q.1 : ℂ).re = 1 / 2 := by
      by_contra hne
      exact hnone ⟨q, hne⟩
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [xiSpectralPoint]
    · simp [xiSpectralPoint, hline]
  obtain ⟨q₀, hq₀⟩ := hoff
  rw [gaussHodgeSourceResolventMoment, Complex.re_tsum hsum]
  apply hre.tsum_pos hnonneg q₀
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (gaussHodgeMassCurrent_pos_of_offLine hm q₀ hq₀ p) (hatom q₀)

/-- **Safe-sector dichotomy.** In the coefficient-faithful Gauss--Hodge source carrier, strict
positivity of any low-order or far-ray resolvent moment is exactly failure of RH. -/
theorem gaussHodgeSourceResolventMoment_re_pos_iff_not_rh_of_le_or_far
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {n : ℕ} {X : ℝ} (hX : 0 < X)
    (hsector : n ≤ 18 ∨ ((n : ℝ) + 1) ^ 2 ≤ X) :
    0 < (gaussHodgeSourceResolventMoment m p n X).re ↔ ¬ RiemannHypothesis := by
  constructor
  · intro hpos hRH
    rw [gaussHodgeSourceResolventMoment_eq_zero_of_rh hRH hm] at hpos
    exact lt_irrefl 0 hpos
  · intro hnot
    exact gaussHodgeSourceResolventMoment_re_pos_of_not_rh_of_le_or_far
      hnot hm p hX hsector

/-- **Literal source-pairing Frankenstein endpoint.**  For every fixed Gauss depth and prime
label, the unnormalized pre-scalarization source current is already a legal coefficient for the
resolvent edge.  At every nonnegative shift, nonnegative real parts of all such moments are exactly
RH. -/
theorem forall_gaussHodgeSourceResolventMoment_re_nonneg_iff_riemannHypothesis
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 ≤ X) :
    (∀ n : ℕ, 0 ≤ (gaussHodgeSourceResolventMoment m p n X).re) ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_forall_gaussHodgeSourceResolventMoment_re_nonneg hm p hX
  · intro hRH n
    rw [gaussHodgeSourceResolventMoment]
    have hfun : (fun q : XiZeroCopy =>
        (gaussHodgeMassCurrent m q p : ℂ) *
          xiResolventPoint X q ^ (n + 1)) = fun _ => 0 := by
      funext q
      have hline := xi_divisor_support_re_eq_half_of_rh hRH q.1
      have hmass0 := (gaussHodgeMassCurrent_eq_zero_iff hm q p).2 hline
      simp [hmass0]
    rw [hfun, tsum_zero]
    exact le_rfl

/-- **One-field Frankenstein endpoint.** Complete monotonicity at any one positive shift of the
single literal Gauss--Hodge resolvent field is equivalent to RH. The formerly separate moment
signs are one derivative jet, matching the compact Markov/Thorin and shifted-Xi routes. -/
theorem forall_alternating_iteratedDeriv_gaussHodgeSourceResolventField_nonneg_iff_rh
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 < X) :
    (∀ n : ℕ, 0 ≤ (-1 : ℝ) ^ n *
      iteratedDeriv n (gaussHodgeSourceResolventField m p) X) ↔
      RiemannHypothesis := by
  rw [← forall_gaussHodgeSourceResolventMoment_re_nonneg_iff_riemannHypothesis
    hm p hX.le]
  exact forall_congr' fun n =>
    alternating_iteratedDeriv_gaussHodgeSourceResolventField_nonneg_iff hm p hX n

/-- **Exact obstruction wedge.** If RH fails, then at every positive shift and for every fixed
Gauss depth and prime label, a literal source-weighted resolvent moment is negative. Every such
witness has order at least nineteen and lies strictly below its quadratic far-ray threshold. -/
theorem exists_gaussHodgeSourceResolventMoment_re_neg_in_wedge_of_not_rh
    (hnot : ¬ RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes)
    {X : ℝ} (hX : 0 < X) :
    ∃ n : ℕ, 19 ≤ n ∧ X < ((n : ℝ) + 1) ^ 2 ∧
      (gaussHodgeSourceResolventMoment m p n X).re < 0 := by
  have hnotall : ¬ ∀ n : ℕ,
      0 ≤ (gaussHodgeSourceResolventMoment m p n X).re := by
    intro hall
    exact hnot ((forall_gaussHodgeSourceResolventMoment_re_nonneg_iff_riemannHypothesis
      hm p hX.le).1 hall)
  simp only [not_forall, not_le] at hnotall
  obtain ⟨n, hneg⟩ := hnotall
  have hn : 19 ≤ n := by
    by_contra hn
    have hsafe := gaussHodgeSourceResolventMoment_re_nonneg_of_le_or_far
      hm p hX (Or.inl (by omega : n ≤ 18))
    linarith
  have hfar : X < ((n : ℝ) + 1) ^ 2 := by
    by_contra hfar
    have hsafe := gaussHodgeSourceResolventMoment_re_nonneg_of_le_or_far
      hm p hX (Or.inr (le_of_not_gt hfar))
    linarith
  exact ⟨n, hn, hfar, hneg⟩

/-- Failure of RH is exactly existence of a negative literal source moment inside the critical
wedge; no low-order or far-ray moment can be a negative witness. -/
theorem exists_gaussHodgeSourceResolventMoment_re_neg_in_wedge_iff_not_rh
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 < X) :
    (∃ n : ℕ, 19 ≤ n ∧ X < ((n : ℝ) + 1) ^ 2 ∧
      (gaussHodgeSourceResolventMoment m p n X).re < 0) ↔
      ¬ RiemannHypothesis := by
  constructor
  · rintro ⟨n, _hn, _hfar, hneg⟩ hRH
    rw [gaussHodgeSourceResolventMoment_eq_zero_of_rh hRH hm] at hneg
    exact lt_irrefl 0 hneg
  · exact fun hnot =>
      exists_gaussHodgeSourceResolventMoment_re_neg_in_wedge_of_not_rh
        hnot hm p hX

/-- **Critical-wedge Frankenstein endpoint.** RH is equivalent to source-moment positivity only
where neither fixed low-order positivity nor the quadratic far-ray cone applies. The producer no
longer owes any sign theorem outside `19 ≤ n` and `X < (n+1)²`. -/
theorem forall_gaussHodgeSourceResolventMoment_re_nonneg_in_wedge_iff_rh
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 < X) :
    (∀ n : ℕ, 19 ≤ n → X < ((n : ℝ) + 1) ^ 2 →
      0 ≤ (gaussHodgeSourceResolventMoment m p n X).re) ↔
      RiemannHypothesis := by
  constructor
  · intro hwedge
    by_contra hnot
    obtain ⟨n, hn, hfar, hneg⟩ :=
      exists_gaussHodgeSourceResolventMoment_re_neg_in_wedge_of_not_rh
        hnot hm p hX
    exact (not_lt_of_ge (hwedge n hn hfar)) hneg
  · intro hRH n _hn _hfar
    rw [gaussHodgeSourceResolventMoment_eq_zero_of_rh hRH hm]
    exact le_rfl

/-- Final reduced producer contract: only the high-order, low-shift derivative wedge of one
source field remains. All complementary derivatives already have unconditional sign. -/
theorem forall_alternating_iteratedDeriv_gaussHodgeSourceResolventField_nonneg_in_wedge_iff_rh
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {X : ℝ} (hX : 0 < X) :
    (∀ n : ℕ, 19 ≤ n → X < ((n : ℝ) + 1) ^ 2 →
      0 ≤ (-1 : ℝ) ^ n *
        iteratedDeriv n (gaussHodgeSourceResolventField m p) X) ↔
      RiemannHypothesis := by
  rw [← forall_gaussHodgeSourceResolventMoment_re_nonneg_in_wedge_iff_rh hm p hX]
  constructor
  · intro h n hn hfar
    exact (alternating_iteratedDeriv_gaussHodgeSourceResolventField_nonneg_iff
      hm p hX n).1 (h n hn hfar)
  · intro h n hn hfar
    exact (alternating_iteratedDeriv_gaussHodgeSourceResolventField_nonneg_iff
      hm p hX n).2 (h n hn hfar)

end

end RHTower
