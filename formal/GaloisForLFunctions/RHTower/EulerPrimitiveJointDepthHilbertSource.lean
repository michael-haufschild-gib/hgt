import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedExteriorSource
import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestXiTraceTransport
import GaloisForLFunctions.RHTower.VonMangoldtGammaBoundaryDisplacementThreshold
import GaloisForLFunctions.RHTower.VonMangoldtLogMomentHankel
import GaloisForLFunctions.RHTower.XiPrimeTwoEulerHurwitzMonodromyCalibration

/-!
# Joint prime-power Hilbert source after primitive promotion

The squarefree common reporter deletes every valuation-depth coordinate.
This module constructs the required upstream replacement: the literal
primitive-promoted Euler amplitude on the full `(prime, valuation)` index.

For positive displacement `u` it is a genuine `ell^(2 : ℕ)` vector.  Its energy
threshold is sharp: summability holds exactly for `u > 0`.  Thus the family
is a moving noncompact source approaching the critical boundary, while every
finite-displacement vector retains every prime-power depth before any scalar
trace.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology

namespace RHTower

noncomputable section

private theorem log_prime_le_log_xiGammaEulerValuationNat
    (pe : Nat.Primes × ℕ) :
    Real.log (pe.1 : ℝ) ≤
      Real.log (xiGammaEulerValuationNat pe : ℝ) := by
  have hpLog : 0 ≤ Real.log (pe.1 : ℝ) :=
    (Real.log_pos (by exact_mod_cast pe.1.property.one_lt)).le
  have hheight :=
    xiGammaEulerBoundaryHalfHeight_eq_half_log_valuation pe.1 pe.2
  rw [xiGammaEulerBoundaryHalfHeight] at hheight
  have hdepth : (1 : ℝ) ≤ (pe.2 : ℝ) + 1 := by
    have he : (0 : ℝ) ≤ (pe.2 : ℝ) := by positivity
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hdepth hpLog]

/-- Positive displacement makes the complete primitive-promoted
prime/valuation amplitude square-summable. -/
theorem summable_sq_xiGammaEulerPrimitiveBoundaryAmplitude_of_pos
    {u : ℝ} (hu : 0 < u) :
    Summable (fun pe : Nat.Primes × ℕ =>
      xiGammaEulerPrimitiveBoundaryAmplitude u pe ^ 2) := by
  have huHalf : 0 < u / 2 := by linarith
  have hradial : Summable (fun pe : Nat.Primes × ℕ =>
      Complex.normSq (xiGammaEulerHeightBoundaryFeature (u / 2) 0 pe)) := by
    have hs := summable_normSq_xiGammaEulerRadialSection
      (s := ((u / 4 : ℝ) : ℂ)) (by simp; linarith)
    have hdamp :
        xiPrimeTwoEulerRadialDamping ((u / 4 : ℝ) : ℂ) = u / 2 := by
      simp only [xiPrimeTwoEulerRadialDamping, Complex.ofReal_re]
      ring
    have hphase :
        xiPrimeTwoEulerHeightPhase ((u / 4 : ℝ) : ℂ) = 0 := by
      simp [xiPrimeTwoEulerHeightPhase]
    simpa only [hdamp, hphase] using hs
  refine Summable.of_nonneg_of_le (fun pe => sq_nonneg _)
    (fun pe => ?_) (hradial.mul_left (1 / (u / 2)))
  let L := Real.log (xiGammaEulerValuationNat pe : ℝ)
  let A := Real.log (pe.1 : ℝ)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact (Real.log_pos
      (by exact_mod_cast pe.1.property.one_lt)).le
  have hn : (0 : ℝ) < xiGammaEulerValuationNat pe := by
    exact_mod_cast pow_pos pe.1.property.pos (pe.2 + 1)
  have hL : 0 ≤ L := by
    dsimp only [L]
    have hnOne : 1 ≤ xiGammaEulerValuationNat pe := by
      unfold xiGammaEulerValuationNat
      exact Nat.one_le_iff_ne_zero.mpr
        (pow_ne_zero _ pe.1.property.ne_zero)
    exact Real.log_nonneg (by exact_mod_cast hnOne)
  have hAL : A ≤ L := by
    simpa only [A, L] using
      log_prime_le_log_xiGammaEulerValuationNat pe
  have hmoment :=
    pow_mul_exp_neg_le_factorial_div_pow'
      (c := u / 2) huHalf hL 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at hmoment
  have hfactor : A * Real.exp (-(u / 2 * L)) ≤ 1 / (u / 2) := by
    exact (mul_le_mul_of_nonneg_right hAL
      (Real.exp_pos _).le).trans hmoment
  have hbase :
      0 ≤ A / (xiGammaEulerValuationNat pe : ℝ) *
        Real.exp (-(u / 2 * L)) := by positivity
  have hexp :
      Real.exp (-u * L) =
        Real.exp (-(u / 2 * L)) *
          Real.exp (-(u / 2 * L)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [xiGammaEulerPrimitiveBoundaryAmplitude_sq,
    normSq_xiGammaEulerHeightBoundaryFeature]
  change
    A ^ 2 / (xiGammaEulerValuationNat pe : ℝ) * Real.exp (-u * L) ≤
      1 / (u / 2) *
        (A / (xiGammaEulerValuationNat pe : ℝ) *
          Real.exp (-(u / 2) * L))
  rw [hexp]
  calc
    A ^ 2 / (xiGammaEulerValuationNat pe : ℝ) *
          (Real.exp (-(u / 2 * L)) * Real.exp (-(u / 2 * L))) =
        (A / (xiGammaEulerValuationNat pe : ℝ) *
          Real.exp (-(u / 2 * L))) *
            (A * Real.exp (-(u / 2 * L))) := by ring
    _ ≤ (A / (xiGammaEulerValuationNat pe : ℝ) *
          Real.exp (-(u / 2 * L))) * (1 / (u / 2)) :=
      mul_le_mul_of_nonneg_left hfactor hbase
    _ = _ := by ring

/-- At depth zero, primitive promotion is exactly multiplication of the
renormalized Gamma boundary energy by one prime logarithm. -/
theorem xiGammaEulerPrimitiveBoundaryAmplitude_depthZero_sq_eq
    (u : ℝ) (p : Nat.Primes) :
    xiGammaEulerPrimitiveBoundaryAmplitude u (p, 0) ^ 2 =
      Real.log (p : ℝ) *
        vonMangoldtGammaRenormalizedBoundaryCoordinate u p ^ 2 := by
  have hnonneg :
      0 ≤ ArithmeticFunction.vonMangoldt p / (p : ℝ) *
        Real.exp (-u * Real.log (p : ℝ)) := by positivity
  rw [xiGammaEulerPrimitiveBoundaryAmplitude_sq,
    vonMangoldtGammaRenormalizedBoundaryCoordinate_eq p.property.two_le,
    Real.sq_sqrt hnonneg,
    ArithmeticFunction.vonMangoldt_apply_prime p.property]
  simp only [xiGammaEulerValuationNat, zero_add, pow_one]
  ring

/-- **Sharp primitive-source chamber.**  The complete joint-depth source is
Hilbert exactly at positive displacement.  Nonpositive displacement already
diverges on its depth-zero prime face. -/
theorem summable_sq_xiGammaEulerPrimitiveBoundaryAmplitude_iff
    (u : ℝ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      xiGammaEulerPrimitiveBoundaryAmplitude u pe ^ 2) ↔
      0 < u := by
  constructor
  · intro hsum
    have hdepthZero : Summable (fun p : Nat.Primes =>
        xiGammaEulerPrimitiveBoundaryAmplitude u (p, 0) ^ 2) :=
      hsum.comp_injective fun p q h => by
        exact congrArg Prod.fst h
    have hscaled := hdepthZero.mul_left (1 / Real.log 2)
    have hunpromoted : Summable (fun p : Nat.Primes =>
        vonMangoldtGammaRenormalizedBoundaryCoordinate u p ^ 2) := by
      refine Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_) hscaled
      rw [xiGammaEulerPrimitiveBoundaryAmplitude_depthZero_sq_eq]
      have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hlogle : Real.log 2 ≤ Real.log (p : ℝ) :=
        Real.strictMonoOn_log.monotoneOn (by norm_num)
          (by
            show (0 : ℝ) < (p : ℝ)
            exact_mod_cast p.property.pos)
          (by exact_mod_cast p.property.two_le)
      have hfactor : 1 ≤ (1 / Real.log 2) * Real.log (p : ℝ) := by
        have hdiv : 1 ≤ Real.log (p : ℝ) / Real.log 2 :=
          (le_div_iff₀ hlog2).2 (by simpa only [one_mul] using hlogle)
        simpa [div_eq_mul_inv, mul_comm] using hdiv
      calc
        vonMangoldtGammaRenormalizedBoundaryCoordinate u p ^ 2 =
            1 * vonMangoldtGammaRenormalizedBoundaryCoordinate u p ^ 2 := by ring
        _ ≤ ((1 / Real.log 2) * Real.log (p : ℝ)) *
              vonMangoldtGammaRenormalizedBoundaryCoordinate u p ^ 2 :=
          mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)
        _ = 1 / Real.log 2 *
              (Real.log (p : ℝ) *
                vonMangoldtGammaRenormalizedBoundaryCoordinate u p ^ 2) := by ring
    exact
      (summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_iff u).1
        hunpromoted
  · exact summable_sq_xiGammaEulerPrimitiveBoundaryAmplitude_of_pos

/-- Complex Hilbert lift of the literal promoted joint-depth source. -/
def xiGammaEulerPrimitiveBoundarySourceLp
    (u : ℝ) (hu : 0 < u) :
    lp (fun _ : Nat.Primes × ℕ => ℂ) 2 :=
  ⟨fun pe => (xiGammaEulerPrimitiveBoundaryAmplitude u pe : ℂ),
    HilbertSchmidt.memℓp_of_sq <| by
      simpa [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (xiGammaEulerPrimitiveBoundaryAmplitude_pos u _)] using
        summable_sq_xiGammaEulerPrimitiveBoundaryAmplitude_of_pos hu⟩

@[simp]
theorem xiGammaEulerPrimitiveBoundarySourceLp_apply
    (u : ℝ) (hu : 0 < u) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveBoundarySourceLp u hu pe =
      (xiGammaEulerPrimitiveBoundaryAmplitude u pe : ℂ) :=
  rfl

/-- Every prime-power coordinate survives in the positive chamber. -/
theorem xiGammaEulerPrimitiveBoundarySourceLp_apply_ne_zero
    (u : ℝ) (hu : 0 < u) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveBoundarySourceLp u hu pe ≠ 0 := by
  rw [xiGammaEulerPrimitiveBoundarySourceLp_apply]
  exact Complex.ofReal_ne_zero.mpr
    (xiGammaEulerPrimitiveBoundaryAmplitude_pos u pe).ne'

/-! ## Reciprocal-promotion co-source and exact Xi landing -/

/-- Co-source which cancels exactly one primitive promotion only at the
final Hilbert pairing.  Prime and valuation labels remain separate in both
vectors. -/
def xiGammaEulerPrimitiveDescentTestAmplitude
    (u : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  (xiGammaEulerPrimitivePromotion pe)⁻¹ *
    xiGammaEulerBoundaryRealAmplitude u pe

theorem xiGammaEulerPrimitiveDescentTestAmplitude_sq
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveDescentTestAmplitude u pe ^ 2 =
      (1 / Real.log (pe.1 : ℝ)) *
        xiGammaEulerBoundaryRealAmplitude u pe ^ 2 := by
  have hlog : 0 ≤ Real.log (pe.1 : ℝ) :=
    (Real.log_pos (by exact_mod_cast pe.1.property.one_lt)).le
  rw [xiGammaEulerPrimitiveDescentTestAmplitude, mul_pow,
    inv_pow, xiGammaEulerPrimitivePromotion, Real.sq_sqrt hlog]
  ring

theorem summable_sq_xiGammaEulerPrimitiveDescentTestAmplitude_of_pos
    {u : ℝ} (hu : 0 < u) :
    Summable (fun pe : Nat.Primes × ℕ =>
      xiGammaEulerPrimitiveDescentTestAmplitude u pe ^ 2) := by
  have hboundary : Summable (fun pe : Nat.Primes × ℕ =>
      xiGammaEulerBoundaryRealAmplitude u pe ^ 2) := by
    have hs := summable_normSq_xiGammaEulerRadialSection
      (s := ((u / 2 : ℝ) : ℂ)) (by simp; linarith)
    have hdamp :
        xiPrimeTwoEulerRadialDamping ((u / 2 : ℝ) : ℂ) = u := by
      simp only [xiPrimeTwoEulerRadialDamping, Complex.ofReal_re]
      ring
    have hphase :
        xiPrimeTwoEulerHeightPhase ((u / 2 : ℝ) : ℂ) = 0 := by
      simp [xiPrimeTwoEulerHeightPhase]
    rw [show (fun pe : Nat.Primes × ℕ =>
        xiGammaEulerBoundaryRealAmplitude u pe ^ 2) =
      fun pe => Complex.normSq
        (xiGammaEulerHeightBoundaryFeature u 0 pe) by
      funext pe
      rw [xiGammaEulerHeightBoundaryFeature_zero_eq_realAmplitude,
        Complex.normSq_ofReal]
      simp only [pow_two]]
    simpa only [hdamp, hphase] using hs
  refine Summable.of_nonneg_of_le (fun pe => sq_nonneg _)
    (fun pe => ?_) (hboundary.mul_left (1 / Real.log 2))
  rw [xiGammaEulerPrimitiveDescentTestAmplitude_sq]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp0 : (0 : ℝ) < (pe.1 : ℝ) := by
    exact_mod_cast pe.1.property.pos
  have hlogle : Real.log 2 ≤ Real.log (pe.1 : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hp0
      (by exact_mod_cast pe.1.property.two_le)
  have hinv : 1 / Real.log (pe.1 : ℝ) ≤ 1 / Real.log 2 :=
    one_div_le_one_div_of_le hlog2 hlogle
  exact mul_le_mul_of_nonneg_right hinv (sq_nonneg _)

theorem xiGammaEulerPrimitiveDescentTestAmplitude_pos
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    0 < xiGammaEulerPrimitiveDescentTestAmplitude u pe := by
  exact mul_pos
    (inv_pos.mpr (Real.sqrt_pos.2
      (Real.log_pos (by exact_mod_cast pe.1.property.one_lt))))
    (xiGammaEulerBoundaryRealAmplitude_pos u pe)

/-- The reciprocal-promotion test is itself a joint-depth Hilbert vector. -/
def xiGammaEulerPrimitiveDescentTestLp
    (u : ℝ) (hu : 0 < u) :
    lp (fun _ : Nat.Primes × ℕ => ℂ) 2 :=
  ⟨fun pe => (xiGammaEulerPrimitiveDescentTestAmplitude u pe : ℂ),
    HilbertSchmidt.memℓp_of_sq <| by
      simpa [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (xiGammaEulerPrimitiveDescentTestAmplitude_pos u _)] using
        summable_sq_xiGammaEulerPrimitiveDescentTestAmplitude_of_pos hu⟩

@[simp]
theorem xiGammaEulerPrimitiveDescentTestLp_apply
    (u : ℝ) (hu : 0 < u) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveDescentTestLp u hu pe =
      (xiGammaEulerPrimitiveDescentTestAmplitude u pe : ℂ) :=
  rfl

theorem xiGammaEulerPrimitiveBoundaryAmplitude_mul_descentTest
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveBoundaryAmplitude u pe *
        xiGammaEulerPrimitiveDescentTestAmplitude u pe =
      eulerPrimeCurrentMass (1 + u) (xiGammaEulerValuationNat pe) := by
  have hpromotion : xiGammaEulerPrimitivePromotion pe ≠ 0 :=
    (Real.sqrt_pos.2
      (Real.log_pos (by exact_mod_cast pe.1.property.one_lt))).ne'
  have hn : (0 : ℝ) < xiGammaEulerValuationNat pe := by
    exact_mod_cast pow_pos pe.1.property.pos (pe.2 + 1)
  rw [xiGammaEulerPrimitiveBoundaryAmplitude,
    xiGammaEulerPrimitiveDescentTestAmplitude]
  have hcancel :
      xiGammaEulerPrimitivePromotion pe *
          xiGammaEulerBoundaryRealAmplitude u pe *
        ((xiGammaEulerPrimitivePromotion pe)⁻¹ *
          xiGammaEulerBoundaryRealAmplitude u pe) =
        xiGammaEulerBoundaryRealAmplitude u pe ^ 2 := by
    field_simp [hpromotion]
  rw [hcancel, xiGammaEulerBoundaryRealAmplitude_sq,
    eulerPrimeCurrentMass]
  have hvonMangoldt :
      ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat pe) =
        Real.log (pe.1 : ℝ) := by
    simpa only [xiGammaEulerValuationNat] using
      vonMangoldt_prime_pow_succ_eq_log pe
  rw [hvonMangoldt]
  have hrpow :
      (xiGammaEulerValuationNat pe : ℝ) ^ (-(1 + u)) =
        (xiGammaEulerValuationNat pe : ℝ)⁻¹ *
          Real.exp (-u * Real.log (xiGammaEulerValuationNat pe : ℝ)) := by
    rw [Real.rpow_def_of_pos hn]
    rw [show Real.log (xiGammaEulerValuationNat pe : ℝ) * -(1 + u) =
        -Real.log (xiGammaEulerValuationNat pe : ℝ) +
          (-u * Real.log (xiGammaEulerValuationNat pe : ℝ)) by ring,
      Real.exp_add, Real.exp_neg, Real.exp_log hn]
  rw [hrpow]
  ring

private theorem xiGammaEulerValuationNat_injective_jointDepth :
    Function.Injective xiGammaEulerValuationNat := by
  rintro ⟨p, e⟩ ⟨q, f⟩ h
  have hpq : (p : ℕ) = (q : ℕ) :=
    eq_of_prime_pow_eq p.property.prime q.property.prime (by omega) h
  have hpq' : p = q := Subtype.ext hpq
  subst q
  have hef : e + 1 = f + 1 :=
    (Nat.pow_right_injective p.property.two_le) h
  congr
  omega

/-- The joint-depth source/co-source pairing is exactly the full normalized
von Mangoldt prime-power flux before Gamma completion. -/
theorem inner_xiGammaEulerPrimitiveDescentTest_source_eq_primeCurrentTotal
    (u : ℝ) (hu : 0 < u) :
    inner ℂ (xiGammaEulerPrimitiveDescentTestLp u hu)
        (xiGammaEulerPrimitiveBoundarySourceLp u hu) =
      (eulerPrimeCurrentTotal (1 + u) : ℂ) := by
  have hsigma : 1 < 1 + u := by linarith
  have hmassReal := summable_eulerPrimeCurrentMass hsigma
  have hmass : Summable (fun n : ℕ =>
      (eulerPrimeCurrentMass (1 + u) n : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      hmassReal.map Complex.ofRealCLM Complex.ofRealCLM.continuous
  have hsupport : Function.support (fun n : ℕ =>
      (eulerPrimeCurrentMass (1 + u) n : ℂ)) ⊆
        {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hpow
    apply hn
    simp [eulerPrimeCurrentMass,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow]
  have hreindex :=
    tsum_eq_tsum_primes_of_support_subset_prime_powers hmass hsupport
  rw [lp.inner_eq_tsum]
  calc
    (∑' pe : Nat.Primes × ℕ,
        inner ℂ
          (xiGammaEulerPrimitiveDescentTestLp u hu pe)
          (xiGammaEulerPrimitiveBoundarySourceLp u hu pe)) =
        ∑' pe : Nat.Primes × ℕ,
          (eulerPrimeCurrentMass (1 + u)
            (xiGammaEulerValuationNat pe) : ℂ) := by
      apply tsum_congr
      intro pe
      rw [xiGammaEulerPrimitiveDescentTestLp_apply,
        xiGammaEulerPrimitiveBoundarySourceLp_apply, RCLike.inner_apply]
      simp only [Complex.conj_ofReal]
      exact_mod_cast
        xiGammaEulerPrimitiveBoundaryAmplitude_mul_descentTest u pe
    _ = ∑' p : Nat.Primes, ∑' e : ℕ,
          (eulerPrimeCurrentMass (1 + u) (p ^ (e + 1)) : ℂ) := by
      have hpair : Summable (fun pe : Nat.Primes × ℕ =>
          (eulerPrimeCurrentMass (1 + u)
            (xiGammaEulerValuationNat pe) : ℂ)) := by
        exact hmass.comp_injective
          xiGammaEulerValuationNat_injective_jointDepth
      simpa only [xiGammaEulerValuationNat] using hpair.tsum_prod
    _ = ∑' n : ℕ, (eulerPrimeCurrentMass (1 + u) n : ℂ) :=
      hreindex.symm
    _ = (eulerPrimeCurrentTotal (1 + u) : ℂ) := by
      have hmap := Complex.ofRealCLM.map_tsum hmassReal
      simpa only [eulerPrimeCurrentTotal, Complex.ofRealCLM_apply] using hmap.symm

/-- Gamma completion of the literal joint-depth Hilbert pairing. -/
def xiGammaEulerPrimitiveJointDepthCompletedXiLanding
    (u : ℝ) (hu : 0 < u) : ℂ :=
  -I *
    (inner ℂ (xiGammaEulerPrimitiveDescentTestLp u hu)
        (xiGammaEulerPrimitiveBoundarySourceLp u hu) -
      logDeriv archFactor ((1 + u : ℝ) : ℂ))

/-- **Unconditional primitive source-to-Xi landing.**  For every positive
displacement, the full joint prime-power Hilbert source lands exactly in the
continued completed Xi trace.  Primitive promotion is cancelled only by the
explicit co-source at the final pairing; no squarefree or divisor
scalarization occurs earlier. -/
theorem xiGammaEulerPrimitiveJointDepthCompletedXiLanding_eq
    (u : ℝ) (hu : 0 < u) :
    xiGammaEulerPrimitiveJointDepthCompletedXiLanding u hu =
      continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate ((1 + u : ℝ) : ℂ)) := by
  rw [xiGammaEulerPrimitiveJointDepthCompletedXiLanding,
    inner_xiGammaEulerPrimitiveDescentTest_source_eq_primeCurrentTotal,
    ofReal_eulerPrimeCurrentTotal_eq (by linarith : 1 < 1 + u),
    continuedPrimeArchSourceRelativeTrace,
    xiWardCenteredCoordinate_source]

end

end RHTower
