import GaloisForLFunctions.RHTower.JointAncestryActualThetaGradeNormEscape
import GaloisForLFunctions.HTGeometry.ContinuousL2MultiplicationDisjointness

/-!
# JAS critical singleton prime-multiplication escape

Prime multiplication cannot preserve any one-singleton line in critical prime-Poisson `L²`.
Multiplication adds the inserted prime to the finite character exponent, while the exact
singleton--compound pairing is the inserted prime's Poisson parameter. Both vectors have unit
norm, but that parameter has strict subunit norm, so the compound cannot be a scalar multiple of
the singleton.

Thus injective grade separation repairs the critical Bessel wall but not source-algebra
invariance. Any `C(PrimeTorus)`-source-linear JAS carrier containing a singleton must retain its
higher compound character orbit. This rules out singleton-only completion at the source-linearity
gate before the Xi reflection-sewing endpoint.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- The critical prime-Poisson `L²` class of an arbitrary finite prime character. -/
def criticalPrimeCharacterL2 (t : ℝ) (n : Nat.Primes →₀ ℤ) :
    PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num) :=
  ContinuousMap.toLp 2
    (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)) ℂ
    (infiniteTorusFourier n)

/-- Every finite prime character is a unit vector in critical prime-Poisson `L²`. -/
theorem norm_criticalPrimeCharacterL2 (t : ℝ) (n : Nat.Primes →₀ ℤ) :
    ‖criticalPrimeCharacterL2 t n‖ = 1 := by
  have hsq : ‖criticalPrimeCharacterL2 t n‖ ^ 2 = 1 := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    have hcoe : ((criticalPrimeCharacterL2 t n :
        PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num)) : PrimeTorus → ℂ) =ᵐ[
          primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)]
        fun x => infiniteTorusFourier n x := by
      simpa only [criticalPrimeCharacterL2] using
        ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
          (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num))
          (infiniteTorusFourier n)
    calc
      (∫ x, ‖((criticalPrimeCharacterL2 t n :
          PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num)) : PrimeTorus → ℂ) x‖ ^ 2
          ∂primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)) =
          ∫ _x : PrimeTorus, (1 : ℝ)
            ∂primePoissonMeasure (1 / 2 : ℝ) t (by norm_num) := by
        refine integral_congr_ae ?_
        filter_upwards [hcoe] with x hx
        rw [hx]
        have hnorm : ‖infiniteTorusFourier n x‖ = 1 := by
          classical
          simp only [infiniteTorusFourier, ContinuousMap.coe_mk, Finsupp.prod, norm_prod]
          exact Finset.prod_eq_one fun i _ => Circle.norm_coe _
        rw [hnorm]
        norm_num
      _ = 1 := by simp
  nlinarith [norm_nonneg (criticalPrimeCharacterL2 t n)]

/-- Product of singleton characters at `p` and `q` in critical prime-Poisson `L²`. -/
def criticalPrimeCompoundCharacterL2 (t : ℝ) (p q : Nat.Primes) :
    PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num) :=
  criticalPrimeCharacterL2 t (Finsupp.single p 1 + Finsupp.single q 1)

/-- The earlier singleton definition is the one-coordinate case of the finite-character class. -/
theorem criticalPrimeSingletonCharacterL2_eq_character
    (t : ℝ) (p : Nat.Primes) :
    criticalPrimeSingletonCharacterL2 t p =
      criticalPrimeCharacterL2 t (Finsupp.single p 1) := rfl

/-- Every two-prime compound character remains a unit vector. -/
theorem norm_criticalPrimeCompoundCharacterL2 (t : ℝ) (p q : Nat.Primes) :
    ‖criticalPrimeCompoundCharacterL2 t p q‖ = 1 := by
  exact norm_criticalPrimeCharacterL2 t _

/-- The exact singleton--compound pairing is the inserted-prime Poisson parameter. -/
theorem inner_criticalPrimeSingleton_compound
    (t : ℝ) (p q : Nat.Primes) :
    inner ℂ (criticalPrimeSingletonCharacterL2 t p)
        (criticalPrimeCompoundCharacterL2 t p q) =
      primePoissonParameterValue (1 / 2 : ℝ) t q := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x, inner ℂ (((criticalPrimeSingletonCharacterL2 t p :
        PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num)) : PrimeTorus → ℂ) x)
        (((criticalPrimeCompoundCharacterL2 t p q :
          PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num)) : PrimeTorus → ℂ) x)
        ∂primePoissonMeasure (1 / 2 : ℝ) t (by norm_num)) =
        ∫ x, infiniteTorusFourier (Finsupp.single q 1) x
          ∂primePoissonMeasure (1 / 2 : ℝ) t (by norm_num) := by
      refine integral_congr_ae ?_
      filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
          (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num))
          (infiniteTorusFourier (Finsupp.single p 1)),
        ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
          (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num))
          (infiniteTorusFourier (Finsupp.single p 1 + Finsupp.single q 1))]
        with x hxp hxpq
      rw [show (((criticalPrimeSingletonCharacterL2 t p :
          PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num)) : PrimeTorus → ℂ) x) =
          infiniteTorusFourier (Finsupp.single p 1) x by
            simpa only [criticalPrimeSingletonCharacterL2] using hxp]
      rw [show (((criticalPrimeCompoundCharacterL2 t p q :
          PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num)) : PrimeTorus → ℂ) x) =
          infiniteTorusFourier (Finsupp.single p 1 + Finsupp.single q 1) x by
            simpa only [criticalPrimeCompoundCharacterL2, criticalPrimeCharacterL2] using hxpq]
      rw [infiniteTorusFourier_add]
      simp only [RCLike.inner_apply]
      have hunit : infiniteTorusFourier (Finsupp.single p 1) x *
          (starRingEnd ℂ) (infiniteTorusFourier (Finsupp.single p 1) x) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        norm_cast
        simp [infiniteTorusFourier]
      calc
        infiniteTorusFourier (Finsupp.single p 1) x *
              infiniteTorusFourier (Finsupp.single q 1) x *
                (starRingEnd ℂ) (infiniteTorusFourier (Finsupp.single p 1) x) =
            infiniteTorusFourier (Finsupp.single q 1) x *
              (infiniteTorusFourier (Finsupp.single p 1) x *
                (starRingEnd ℂ) (infiniteTorusFourier (Finsupp.single p 1) x)) := by
          ring
        _ = infiniteTorusFourier (Finsupp.single q 1) x := by rw [hunit, mul_one]
    _ = primePoissonParameterValue (1 / 2 : ℝ) t q := by
      rw [integral_infiniteTorusFourier_primePoissonMeasure]
      simp [circlePoissonFourierMoment]

/-- Prime-coordinate multiplication sends a singleton to its literal compound character. -/
theorem continuousL2Mul_singleton_eq_compound
    (t : ℝ) (p q : Nat.Primes) :
    continuousL2Mul (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num))
        (infiniteTorusFourier (Finsupp.single q 1))
        (criticalPrimeSingletonCharacterL2 t p) =
      criticalPrimeCompoundCharacterL2 t p q := by
  rw [criticalPrimeSingletonCharacterL2, criticalPrimeCompoundCharacterL2,
    criticalPrimeCharacterL2, continuousL2Mul_apply_toLp]
  congr 1
  ext x
  exact (infiniteTorusFourier_add (Finsupp.single q 1)
    (Finsupp.single p 1) x).symm.trans (by rw [add_comm])

/-- A compound character never lies in its parent singleton line. -/
theorem criticalPrimeCompoundCharacterL2_not_mem_singletonSpan
    (t : ℝ) (p q : Nat.Primes) :
    criticalPrimeCompoundCharacterL2 t p q ∉
      (ℂ ∙ criticalPrimeSingletonCharacterL2 t p) := by
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hnormc : ‖c‖ = 1 := by
    have hnorm := congrArg norm hc
    rw [norm_smul, norm_criticalPrimeSingletonCharacterL2,
      norm_criticalPrimeCompoundCharacterL2, mul_one] at hnorm
    exact hnorm
  have hcparam : c = primePoissonParameterValue (1 / 2 : ℝ) t q := by
    have hinner := congrArg
      (fun y : PrimePoissonL2 (1 / 2 : ℝ) t (by norm_num) =>
        inner ℂ (criticalPrimeSingletonCharacterL2 t p) y) hc
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K,
      norm_criticalPrimeSingletonCharacterL2, inner_criticalPrimeSingleton_compound] at hinner
    simpa using hinner
  have hlt : ‖primePoissonParameterValue (1 / 2 : ℝ) t q‖ < 1 := by
    rw [← coe_primePoissonParameter (1 / 2 : ℝ) t (by norm_num) q]
    simpa only [mem_ball_zero_iff] using
      (primePoissonParameter (1 / 2 : ℝ) t (by norm_num) q).property
  rw [← hcparam, hnormc] at hlt
  exact lt_irrefl 1 hlt

/-- Closed source-algebra obstruction: every singleton line fails invariance under every prime
coordinate multiplier. -/
theorem not_invariant_singletonSpan_under_primeCoordinate
    (t : ℝ) (p q : Nat.Primes) :
    ¬ ∀ u ∈ (ℂ ∙ criticalPrimeSingletonCharacterL2 t p),
      continuousL2Mul (primePoissonMeasure (1 / 2 : ℝ) t _)
          (infiniteTorusFourier (Finsupp.single q 1)) u ∈
        (ℂ ∙ criticalPrimeSingletonCharacterL2 t p) := by
  intro hinvariant
  have hsingle : criticalPrimeSingletonCharacterL2 t p ∈
      (ℂ ∙ criticalPrimeSingletonCharacterL2 t p) :=
    Submodule.mem_span_singleton_self _
  have hout := hinvariant _ hsingle
  rw [continuousL2Mul_singleton_eq_compound] at hout
  exact criticalPrimeCompoundCharacterL2_not_mem_singletonSpan t p q
    hout

end

end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Actual completed-theta weight at `p` carried by the compound prime character `p + q` in the
same canonical grade as the original singleton. -/
def jointAncestryCriticalPrimeActualThetaCompoundPacket
    (t : ℝ) (p q : Nat.Primes) :
    L2Amplification ℕ (JASCriticalPrimePoissonL2 t) :=
  l2Single (natEquivPrimes.symm p)
    ((‖jointAncestryCompletedThetaGradeL2 (natEquivPrimes.symm p)‖ : ℂ) •
      criticalPrimeCompoundCharacterL2 t p q)

/-- Coordinatewise prime multiplication sends the literal actual-theta singleton packet to its
compound packet without changing its completed-theta coefficient or grade. -/
theorem l2Amplification_primeCoordinate_actualThetaPacket
    (t : ℝ) (p q : Nat.Primes) :
    l2Amplification
        (continuousL2Mul (primePoissonMeasure (1 / 2 : ℝ) t (by norm_num))
          (infiniteTorusFourier (Finsupp.single q 1)))
        (jointAncestryCriticalPrimeActualThetaInjectiveGradePacket t p) =
      jointAncestryCriticalPrimeActualThetaCompoundPacket t p q := by
  rw [jointAncestryCriticalPrimeActualThetaInjectiveGradePacket,
    jointAncestryCriticalPrimeActualThetaCompoundPacket, l2Amplification_single, map_smul,
    continuousL2Mul_singleton_eq_compound]

/-- The actual completed-theta compound packet lies outside the line of its parent actual-theta
singleton packet. The nonzero physical theta coefficient cannot hide the Poisson obstruction. -/
theorem jointAncestryCriticalPrimeActualThetaCompoundPacket_not_mem_singletonSpan
    (t : ℝ) (p q : Nat.Primes) :
    jointAncestryCriticalPrimeActualThetaCompoundPacket t p q ∉
      (ℂ ∙ jointAncestryCriticalPrimeActualThetaInjectiveGradePacket t p) := by
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  let w : ℂ :=
    (‖jointAncestryCompletedThetaGradeL2 (natEquivPrimes.symm p)‖ : ℂ)
  have hcoord := congrArg
    (l2Coordinate (H₁ := JASCriticalPrimePoissonL2 t) (natEquivPrimes.symm p)) hc
  simp only [map_smul, jointAncestryCriticalPrimeActualThetaInjectiveGradePacket,
    jointAncestryCriticalPrimeActualThetaCompoundPacket, l2Coordinate_single_same] at hcoord
  have hw : w ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr
        (jointAncestryCompletedThetaGradeL2_ne_zero (natEquivPrimes.symm p)))
  have hbase : c • criticalPrimeSingletonCharacterL2 t p =
      criticalPrimeCompoundCharacterL2 t p q := by
    have hscaled := congrArg
      (fun u : JASCriticalPrimePoissonL2 t => w⁻¹ • u) hcoord
    have hleft : w⁻¹ * c * w = c := by
      calc
        w⁻¹ * c * w = c * (w⁻¹ * w) := by ring
        _ = c := by rw [inv_mul_cancel₀ hw, mul_one]
    have hleft' : w⁻¹ * (c * w) = c := by rw [← mul_assoc, hleft]
    simpa only [w, smul_smul, hleft', inv_mul_cancel₀ hw, one_smul] using hscaled
  apply criticalPrimeCompoundCharacterL2_not_mem_singletonSpan t p q
  exact Submodule.mem_span_singleton.mpr ⟨c, hbase⟩

/-- RH-route consequence: the literal actual-theta singleton line is never invariant under a
prime-coordinate action in the countably amplified critical prime-Poisson representation. -/
theorem not_invariant_actualThetaSingletonSpan_under_primeCoordinate
    (t : ℝ) (p q : Nat.Primes) :
    ¬ ∀ u ∈ (ℂ ∙ jointAncestryCriticalPrimeActualThetaInjectiveGradePacket t p),
      l2Amplification
          (continuousL2Mul (primePoissonMeasure (1 / 2 : ℝ) t _)
            (infiniteTorusFourier (Finsupp.single q 1))) u ∈
        (ℂ ∙ jointAncestryCriticalPrimeActualThetaInjectiveGradePacket t p) := by
  intro hinvariant
  have hpacket : jointAncestryCriticalPrimeActualThetaInjectiveGradePacket t p ∈
      (ℂ ∙ jointAncestryCriticalPrimeActualThetaInjectiveGradePacket t p) :=
    Submodule.mem_span_singleton_self _
  have hout := hinvariant _ hpacket
  rw [l2Amplification_primeCoordinate_actualThetaPacket] at hout
  exact jointAncestryCriticalPrimeActualThetaCompoundPacket_not_mem_singletonSpan t p q hout

end

end RHTower
