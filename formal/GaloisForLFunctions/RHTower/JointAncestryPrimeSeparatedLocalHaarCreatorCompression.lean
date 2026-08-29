import GaloisForLFunctions.RHTower.JointAncestryHilbertMultiplicityHaarVacuumSuperselection
import GaloisForLFunctions.RHTower.JointAncestryActualThetaClosedUnboundedGradeSynthesis
import GaloisForLFunctions.HTGeometry.CirclePoissonProductEquivalence
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace NNReal

noncomputable section

def jasZeroCirclePoissonParameter : CirclePoissonParameter :=
  ⟨0, by simp⟩

@[simp] theorem coe_jasZeroCirclePoissonParameter :
    (jasZeroCirclePoissonParameter : ℂ) = 0 := rfl

def jasPrimePoissonLocalHaarParameter
    (sigma t : ℝ) (hsigma : 0 < sigma) (p q : Nat.Primes) :
    CirclePoissonParameter :=
  if q = p then jasZeroCirclePoissonParameter
  else primePoissonParameter sigma t hsigma q

@[simp] theorem jasPrimePoissonLocalHaarParameter_self
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) :
    jasPrimePoissonLocalHaarParameter sigma t hsigma p p =
      jasZeroCirclePoissonParameter := by
  simp [jasPrimePoissonLocalHaarParameter]

theorem jasPrimePoissonLocalHaarParameter_of_ne
    (sigma t : ℝ) (hsigma : 0 < sigma) {p q : Nat.Primes} (hqp : q ≠ p) :
    jasPrimePoissonLocalHaarParameter sigma t hsigma p q =
      primePoissonParameter sigma t hsigma q := by
  simp [jasPrimePoissonLocalHaarParameter, hqp]

def jasPrimePoissonLocalHaarMeasure
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) : Measure PrimeTorus :=
  torusPoissonMeasure (jasPrimePoissonLocalHaarParameter sigma t hsigma p)

instance isProbabilityMeasure_jasPrimePoissonLocalHaarMeasure
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) :
    IsProbabilityMeasure (jasPrimePoissonLocalHaarMeasure sigma t hsigma p) := by
  unfold jasPrimePoissonLocalHaarMeasure
  infer_instance

theorem tendsto_jasPrimePoissonLocalHaarParameter_natEquivPrimes_zero
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) :
    Tendsto (fun n =>
      ((jasPrimePoissonLocalHaarParameter sigma t hsigma p (natEquivPrimes n) :
        CirclePoissonParameter) : ℂ)) atTop (𝓝 0) := by
  apply (tendsto_primePoissonParameter_natEquivPrimes_zero sigma t hsigma).congr'
  filter_upwards [eventually_ge_atTop (natEquivPrimes.symm p + 1)] with n hn
  have hnindex : n ≠ natEquivPrimes.symm p := by omega
  have hnp : natEquivPrimes n ≠ p := by
    intro h
    apply hnindex
    simpa using congrArg natEquivPrimes.symm h
  rw [jasPrimePoissonLocalHaarParameter_of_ne sigma t hsigma hnp]

theorem summable_primePoissonParameter_sub_localHaarParameter_normSq
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) :
    Summable (fun q : Nat.Primes =>
      ‖(primePoissonParameter sigma t hsigma q : ℂ) -
        (jasPrimePoissonLocalHaarParameter sigma t hsigma p q : ℂ)‖ ^ 2) := by
  apply summable_of_ne_finset_zero (s := {p})
  intro q hq
  have hqp : q ≠ p := by simpa using hq
  rw [jasPrimePoissonLocalHaarParameter_of_ne sigma t hsigma hqp]
  simp

theorem primePoissonMeasure_mutuallyAbsolutelyContinuous_localHaar
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) :
    (primePoissonMeasure sigma t hsigma ≪
        jasPrimePoissonLocalHaarMeasure sigma t hsigma p) ∧
      (jasPrimePoissonLocalHaarMeasure sigma t hsigma p ≪
        primePoissonMeasure sigma t hsigma) := by
  rw [primePoissonMeasure, jasPrimePoissonLocalHaarMeasure]
  exact (torusPoissonMeasure_mutuallyAbsolutelyContinuous_iff_summable_normSq
    (primePoissonParameter sigma t hsigma)
    (jasPrimePoissonLocalHaarParameter sigma t hsigma p)
    (tendsto_primePoissonParameter_natEquivPrimes_zero sigma t hsigma)
    (tendsto_jasPrimePoissonLocalHaarParameter_natEquivPrimes_zero sigma t hsigma p)).2
      (summable_primePoissonParameter_sub_localHaarParameter_normSq sigma t hsigma p)

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

def probabilityL2Vacuum (μ : Measure X) [IsProbabilityMeasure μ] : Lp ℂ 2 μ :=
  ContinuousMap.toLp 2 μ ℂ (1 : C(X, ℂ))

theorem norm_probabilityL2Vacuum (μ : Measure X) [IsProbabilityMeasure μ] :
    ‖probabilityL2Vacuum μ‖ = 1 := by
  have hsq : ‖probabilityL2Vacuum μ‖ ^ 2 = 1 := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    have hcoe : (((probabilityL2Vacuum μ : Lp ℂ 2 μ) : X → ℂ)) =ᵐ[μ]
        fun _ => (1 : ℂ) := by
      filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) μ
        (1 : C(X, ℂ))] with x hx
      simpa [probabilityL2Vacuum] using hx
    calc
      (∫ x, ‖((probabilityL2Vacuum μ : Lp ℂ 2 μ) : X → ℂ) x‖ ^ 2 ∂μ) =
          ∫ _x : X, (1 : ℝ) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hcoe] with x hx
        rw [hx]
        norm_num
      _ = 1 := by simp
  nlinarith [norm_nonneg (probabilityL2Vacuum μ)]

theorem inner_probabilityL2Vacuum_continuousL2Mul
    (μ : Measure X) [IsProbabilityMeasure μ] (f : C(X, ℂ)) :
    inner ℂ (probabilityL2Vacuum μ)
        (continuousL2Mul μ f (probabilityL2Vacuum μ)) =
      ∫ x, f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousL2Mul_coeFn μ f (probabilityL2Vacuum μ),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) μ (1 : C(X, ℂ))]
      with x hmul hone
  rw [hmul]
  change inner ℂ (((probabilityL2Vacuum μ : Lp ℂ 2 μ) : X → ℂ) x)
      (f x * (((probabilityL2Vacuum μ : Lp ℂ 2 μ) : X → ℂ) x)) = f x
  rw [show (((probabilityL2Vacuum μ : Lp ℂ 2 μ) : X → ℂ) x) = 1 by
    simpa [probabilityL2Vacuum] using hone]
  simp

/-- A positive-density presentation transports the constant target vacuum back to the source
multiplication representation. -/
theorem exists_unitVector_inner_continuousL2Mul_eq_integral_of_withDensity_eq
    (ν : Measure X) [IsProbabilityMeasure ν]
    (w : X → ℝ) (hw : Measurable w) (hpos : ∀ x, 0 < w x)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hmeasure : ν.withDensity (realDensity w) = μ) :
    ∃ v : Lp ℂ 2 μ, ‖v‖ = 1 ∧ ∀ f : C(X, ℂ),
      inner ℂ v (continuousL2Mul μ f v) = ∫ x, f x ∂ν := by
  subst μ
  let U := weightedDensityUnitary (μ := ν) w hw hpos
  let v : WeightedL2 (μ := ν) w := U.symm (probabilityL2Vacuum ν)
  refine ⟨v, ?_, ?_⟩
  · change ‖U.symm (probabilityL2Vacuum ν)‖ = 1
    rw [U.symm.norm_map, norm_probabilityL2Vacuum]
  · intro f
    rw [← U.inner_map_map]
    change inner ℂ (U v)
      (U (continuousL2Mul (ν.withDensity (realDensity w)) f v)) = _
    rw [weightedDensityUnitary_continuousL2Mul]
    have hUv : U v = probabilityL2Vacuum ν := by simp [v]
    rw [hUv]
    exact inner_probabilityL2Vacuum_continuousL2Mul ν f

/-- Equivalent probability measures admit a normalized source vector whose every continuous
multiplier coefficient is integration against the target measure. -/
theorem exists_unitVector_inner_continuousL2Mul_eq_integral_of_mutuallyAbsolutelyContinuous
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    ∃ v : Lp ℂ 2 μ, ‖v‖ = 1 ∧ ∀ f : C(X, ℂ),
      inner ℂ v (continuousL2Mul μ f v) = ∫ x, f x ∂ν := by
  let w : X → ℝ := repairedRnDensity μ ν
  have hw : Measurable w := measurable_repairedRnDensity μ ν
  have hpos : ∀ x, 0 < w x := repairedRnDensity_pos μ ν
  have hmeasure : ν.withDensity (realDensity w) = μ :=
    withDensity_repairedRnDensity_eq μ ν hμν hνμ
  exact exists_unitVector_inner_continuousL2Mul_eq_integral_of_withDensity_eq
    ν w hw hpos μ hmeasure

theorem exists_jasPrimePoissonLocalHaarVacuum
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) :
    ∃ v : Lp ℂ 2 (primePoissonMeasure sigma t hsigma), ‖v‖ = 1 ∧
      ∀ f : C(PrimeTorus, ℂ),
        inner ℂ v (continuousL2Mul (primePoissonMeasure sigma t hsigma) f v) =
          ∫ x, f x ∂jasPrimePoissonLocalHaarMeasure sigma t hsigma p := by
  have hmac := primePoissonMeasure_mutuallyAbsolutelyContinuous_localHaar
    sigma t hsigma p
  exact exists_unitVector_inner_continuousL2Mul_eq_integral_of_mutuallyAbsolutelyContinuous
    (primePoissonMeasure sigma t hsigma)
    (jasPrimePoissonLocalHaarMeasure sigma t hsigma p) hmac.1 hmac.2

def jasPrimePoissonLocalHaarVacuum
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) :
    Lp ℂ 2 (primePoissonMeasure sigma t hsigma) :=
  Classical.choose (exists_jasPrimePoissonLocalHaarVacuum sigma t hsigma p)

theorem norm_jasPrimePoissonLocalHaarVacuum
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) :
    ‖jasPrimePoissonLocalHaarVacuum sigma t hsigma p‖ = 1 :=
  (Classical.choose_spec
    (exists_jasPrimePoissonLocalHaarVacuum sigma t hsigma p)).1

theorem inner_jasPrimePoissonLocalHaarVacuum_continuousL2Mul
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes)
    (f : C(PrimeTorus, ℂ)) :
    inner ℂ (jasPrimePoissonLocalHaarVacuum sigma t hsigma p)
        (continuousL2Mul (primePoissonMeasure sigma t hsigma) f
          (jasPrimePoissonLocalHaarVacuum sigma t hsigma p)) =
      ∫ x, f x ∂jasPrimePoissonLocalHaarMeasure sigma t hsigma p :=
  (Classical.choose_spec
    (exists_jasPrimePoissonLocalHaarVacuum sigma t hsigma p)).2 f

theorem circlePoissonFourierMoment_jasZero (q : ℤ) :
    circlePoissonFourierMoment jasZeroCirclePoissonParameter q =
      if q = 0 then 1 else 0 := by
  cases q with
  | ofNat n =>
      cases n with
      | zero => simp [circlePoissonFourierMoment]
      | succ n =>
          rw [if_neg (by
            intro h
            have hn : n + 1 = 0 := Int.ofNat.inj h
            omega : (Int.ofNat (n + 1)) ≠ 0)]
          simp [circlePoissonFourierMoment]
  | negSucc n => simp [circlePoissonFourierMoment]

theorem integral_infiniteTorusFourier_jasPrimePoissonLocalHaarMeasure_single
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) (q : ℤ) :
    (∫ x, infiniteTorusFourier (Finsupp.single p q) x
        ∂jasPrimePoissonLocalHaarMeasure sigma t hsigma p) =
      if q = 0 then 1 else 0 := by
  rw [jasPrimePoissonLocalHaarMeasure,
    integral_infiniteTorusFourier_torusPoissonMeasure]
  by_cases hq : q = 0
  · subst q
    simp
  · simp [Finsupp.prod, hq, circlePoissonFourierMoment_jasZero]

theorem star_infiniteTorusFourier {I : Type*} (n : I →₀ ℤ) :
    star (infiniteTorusFourier n) = infiniteTorusFourier (-n) := by
  ext x
  exact (infiniteTorusFourier_neg n x).symm

theorem continuousL2Mul_infiniteTorusFourier_add_apply
    {I : Type*} [Countable I] (μ : Measure (I → UnitAddCircle)) [IsFiniteMeasure μ]
    (m n : I →₀ ℤ) (v : Lp ℂ 2 μ) :
    continuousL2Mul μ (infiniteTorusFourier m)
        (continuousL2Mul μ (infiniteTorusFourier n) v) =
      continuousL2Mul μ (infiniteTorusFourier (m + n)) v := by
  apply Lp.ext
  filter_upwards [
    continuousL2Mul_coeFn μ (infiniteTorusFourier m)
      (continuousL2Mul μ (infiniteTorusFourier n) v),
    continuousL2Mul_coeFn μ (infiniteTorusFourier n) v,
    continuousL2Mul_coeFn μ (infiniteTorusFourier (m + n)) v]
      with x hleft hn hright
  rw [hleft, hn, hright, infiniteTorusFourier_add]
  ring

def jasPrimePoissonLocalHaarPowerVector
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) (q : ℤ) :
    Lp ℂ 2 (primePoissonMeasure sigma t hsigma) :=
  continuousL2Mul (primePoissonMeasure sigma t hsigma)
    (infiniteTorusFourier (Finsupp.single p q))
    (jasPrimePoissonLocalHaarVacuum sigma t hsigma p)

theorem inner_jasPrimePoissonLocalHaarVacuum_powerVector
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) (q : ℤ) :
    inner ℂ (jasPrimePoissonLocalHaarVacuum sigma t hsigma p)
        (jasPrimePoissonLocalHaarPowerVector sigma t hsigma p q) =
      if q = 0 then 1 else 0 := by
  rw [jasPrimePoissonLocalHaarPowerVector,
    inner_jasPrimePoissonLocalHaarVacuum_continuousL2Mul]
  exact integral_infiniteTorusFourier_jasPrimePoissonLocalHaarMeasure_single
    sigma t hsigma p q

theorem continuousL2Mul_jasPrimePoissonLocalHaarPowerVector
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) (m n : ℤ) :
    continuousL2Mul (primePoissonMeasure sigma t hsigma)
        (infiniteTorusFourier (Finsupp.single p m))
        (jasPrimePoissonLocalHaarPowerVector sigma t hsigma p n) =
      jasPrimePoissonLocalHaarPowerVector sigma t hsigma p (m + n) := by
  rw [jasPrimePoissonLocalHaarPowerVector,
    continuousL2Mul_infiniteTorusFourier_add_apply]
  congr 2
  rw [Finsupp.single_add]

theorem inner_jasPrimePoissonLocalHaarPowerVector
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) (m n : ℤ) :
    inner ℂ (jasPrimePoissonLocalHaarPowerVector sigma t hsigma p m)
        (jasPrimePoissonLocalHaarPowerVector sigma t hsigma p n) =
      if m = n then 1 else 0 := by
  let μ := primePoissonMeasure sigma t hsigma
  let v := jasPrimePoissonLocalHaarVacuum sigma t hsigma p
  let A := continuousL2Mul μ (infiniteTorusFourier (Finsupp.single p m))
  calc
    inner ℂ (jasPrimePoissonLocalHaarPowerVector sigma t hsigma p m)
        (jasPrimePoissonLocalHaarPowerVector sigma t hsigma p n) =
        inner ℂ (A v)
          (jasPrimePoissonLocalHaarPowerVector sigma t hsigma p n) := by rfl
    _ = inner ℂ v
        (A.adjoint (jasPrimePoissonLocalHaarPowerVector sigma t hsigma p n)) :=
      (A.adjoint_inner_right v
        (jasPrimePoissonLocalHaarPowerVector sigma t hsigma p n)).symm
    _ = inner ℂ v
        (jasPrimePoissonLocalHaarPowerVector sigma t hsigma p (-m + n)) := by
      change inner ℂ v
        ((continuousL2Mul μ (infiniteTorusFourier (Finsupp.single p m))).adjoint
          (jasPrimePoissonLocalHaarPowerVector sigma t hsigma p n)) = _
      rw [adjoint_continuousL2Mul, star_infiniteTorusFourier]
      rw [show -(Finsupp.single p m) = Finsupp.single p (-m) by simp]
      change inner ℂ v
        (continuousL2Mul μ
          (infiniteTorusFourier (Finsupp.single p (-m)))
          (jasPrimePoissonLocalHaarPowerVector sigma t hsigma p n)) = _
      rw [continuousL2Mul_jasPrimePoissonLocalHaarPowerVector]
    _ = if m = n then 1 else 0 := by
      rw [inner_jasPrimePoissonLocalHaarVacuum_powerVector]
      by_cases hmn : m = n
      · subst n
        simp
      · rw [if_neg (by omega), if_neg hmn]

def jasPrimePoissonLocalHaarBooleanVector
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) (i : Fin 2) :
    Lp ℂ 2 (primePoissonMeasure sigma t hsigma) :=
  jasPrimePoissonLocalHaarPowerVector sigma t hsigma p (i : ℕ)

/-- The local-Haar vacuum and its positive prime-coordinate image are orthonormal. -/
theorem orthonormal_jasPrimePoissonLocalHaarBooleanVector
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) :
    Orthonormal ℂ (jasPrimePoissonLocalHaarBooleanVector sigma t hsigma p) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [jasPrimePoissonLocalHaarBooleanVector]
  rw [inner_jasPrimePoissonLocalHaarPowerVector]
  by_cases hij : i = j
  · subst j
    simp
  · have hval : (i.val : ℤ) ≠ (j.val : ℤ) := by
      intro h
      apply hij
      apply Fin.ext
      exact Int.ofNat.inj h
    rw [if_neg hval, if_neg hij]

/-- Compression of the positive prime coordinate to the local two-frame is exactly the Boolean
creator matrix. -/
theorem jasPrimePoissonLocalHaar_positiveCompression
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) (i j : Fin 2) :
    inner ℂ (jasPrimePoissonLocalHaarBooleanVector sigma t hsigma p i)
        (continuousL2Mul (primePoissonMeasure sigma t hsigma)
          (infiniteTorusFourier (Finsupp.single p 1))
          (jasPrimePoissonLocalHaarBooleanVector sigma t hsigma p j)) =
      if i = 1 ∧ j = 0 then 1 else 0 := by
  simp only [jasPrimePoissonLocalHaarBooleanVector]
  rw [continuousL2Mul_jasPrimePoissonLocalHaarPowerVector,
    inner_jasPrimePoissonLocalHaarPowerVector]
  fin_cases i <;> fin_cases j <;> norm_num

/-- Compression of the inverse prime coordinate is exactly the adjoint Boolean annihilator
matrix. -/
theorem jasPrimePoissonLocalHaar_negativeCompression
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) (i j : Fin 2) :
    inner ℂ (jasPrimePoissonLocalHaarBooleanVector sigma t hsigma p i)
        (continuousL2Mul (primePoissonMeasure sigma t hsigma)
          (infiniteTorusFourier (Finsupp.single p (-1)))
          (jasPrimePoissonLocalHaarBooleanVector sigma t hsigma p j)) =
      if i = 0 ∧ j = 1 then 1 else 0 := by
  simp only [jasPrimePoissonLocalHaarBooleanVector]
  rw [continuousL2Mul_jasPrimePoissonLocalHaarPowerVector,
    inner_jasPrimePoissonLocalHaarPowerVector]
  fin_cases i <;> fin_cases j <;> norm_num

/-- Each prime's local-Haar Boolean pair occupies its own canonical amplification grade. -/
def jasPrimeSeparatedLocalHaarBooleanPacket
    (sigma t : ℝ) (hsigma : 0 < sigma) (a : Nat.Primes × Fin 2) :
    L2Amplification ℕ (Lp ℂ 2 (primePoissonMeasure sigma t hsigma)) :=
  l2Single (natEquivPrimes.symm a.1)
    (jasPrimePoissonLocalHaarBooleanVector sigma t hsigma a.1 a.2)

/-- The simultaneous all-prime Boolean packet is orthonormal: local Haarization separates the
two states inside each prime block, and canonical grades separate distinct primes. -/
theorem orthonormal_jasPrimeSeparatedLocalHaarBooleanPacket
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    Orthonormal ℂ (jasPrimeSeparatedLocalHaarBooleanPacket sigma t hsigma) := by
  rw [orthonormal_iff_ite]
  rintro ⟨p, i⟩ ⟨q, j⟩
  by_cases hpq : p = q
  · subst q
    rw [jasPrimeSeparatedLocalHaarBooleanPacket,
      jasPrimeSeparatedLocalHaarBooleanPacket, l2Single_apply,
      lp.inner_single_left]
    simp only [l2Single_apply, lp.single_apply,
      jasPrimePoissonLocalHaarBooleanVector]
    rw [Pi.single_eq_same]
    rw [inner_jasPrimePoissonLocalHaarPowerVector]
    by_cases hij : i = j
    · subst j
      simp
    · have hval : ((i : ℕ) : ℤ) ≠ ((j : ℕ) : ℤ) := by
        intro h
        apply hij
        apply Fin.ext
        exact Int.ofNat.inj h
      simp [hij, hval]
  · have hgrade : natEquivPrimes.symm p ≠ natEquivPrimes.symm q := by
      exact fun h => hpq (natEquivPrimes.symm.injective h)
    simp [jasPrimeSeparatedLocalHaarBooleanPacket, l2Single_apply,
      lp.inner_single_left, lp.single_apply, hpq, hgrade]

/-- Isometric synthesis of all prime-separated local-Haar Boolean source states. -/
def jasPrimeSeparatedLocalHaarBooleanSynthesis
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    HTGeometry.IndexedEllTwo (Nat.Primes × Fin 2) →L[ℂ]
      L2Amplification ℕ (Lp ℂ 2 (primePoissonMeasure sigma t hsigma)) :=
  (orthonormal_jasPrimeSeparatedLocalHaarBooleanPacket sigma t hsigma).orthogonalFamily
    |>.linearIsometry.toContinuousLinearMap

/-- Synthesis sends each coordinate basis vector to its corresponding prime/Boolean packet. -/
theorem jasPrimeSeparatedLocalHaarBooleanSynthesis_coordinateBasis
    (sigma t : ℝ) (hsigma : 0 < sigma) (a : Nat.Primes × Fin 2) :
    jasPrimeSeparatedLocalHaarBooleanSynthesis sigma t hsigma
        (HTGeometry.ellTwoCoordinateBasis (Nat.Primes × Fin 2) a) =
      jasPrimeSeparatedLocalHaarBooleanPacket sigma t hsigma a := by
  rw [jasPrimeSeparatedLocalHaarBooleanSynthesis,
    HTGeometry.ellTwoCoordinateBasis_apply]
  change
    (orthonormal_jasPrimeSeparatedLocalHaarBooleanPacket sigma t hsigma).orthogonalFamily.linearIsometry
      (lp.single 2 a 1) = _
  rw [OrthogonalFamily.linearIsometry_apply_single]
  simp [LinearIsometry.toSpanSingleton_apply]

/-- The global positive-coordinate compression is block diagonal, with one Boolean creator block
at every prime and no cross-prime matrix coefficients. -/
theorem jasPrimeSeparatedLocalHaar_positiveCompression
    (sigma t : ℝ) (hsigma : 0 < sigma)
    (p q : Nat.Primes) (i j : Fin 2) :
    inner ℂ (jasPrimeSeparatedLocalHaarBooleanPacket sigma t hsigma (p, i))
        (l2Amplification
          (continuousL2Mul (primePoissonMeasure sigma t hsigma)
            (infiniteTorusFourier (Finsupp.single q 1)))
          (jasPrimeSeparatedLocalHaarBooleanPacket sigma t hsigma (q, j))) =
      if p = q ∧ i = 1 ∧ j = 0 then 1 else 0 := by
  rw [jasPrimeSeparatedLocalHaarBooleanPacket,
    jasPrimeSeparatedLocalHaarBooleanPacket, l2Amplification_single,
    l2Single_apply, lp.inner_single_left]
  by_cases hpq : p = q
  · subst q
    simp only [l2Single_apply, lp.single_apply]
    simpa using jasPrimePoissonLocalHaar_positiveCompression sigma t hsigma p i j
  · have hgrade : natEquivPrimes.symm p ≠ natEquivPrimes.symm q := by
      exact fun h => hpq (natEquivPrimes.symm.injective h)
    simp [lp.single_apply, hpq, hgrade]

/-- The global inverse-coordinate compression is block diagonal, with the adjoint Boolean
annihilator block at every prime and no cross-prime matrix coefficients. -/
theorem jasPrimeSeparatedLocalHaar_negativeCompression
    (sigma t : ℝ) (hsigma : 0 < sigma)
    (p q : Nat.Primes) (i j : Fin 2) :
    inner ℂ (jasPrimeSeparatedLocalHaarBooleanPacket sigma t hsigma (p, i))
        (l2Amplification
          (continuousL2Mul (primePoissonMeasure sigma t hsigma)
            (infiniteTorusFourier (Finsupp.single q (-1))))
          (jasPrimeSeparatedLocalHaarBooleanPacket sigma t hsigma (q, j))) =
      if p = q ∧ i = 0 ∧ j = 1 then 1 else 0 := by
  rw [jasPrimeSeparatedLocalHaarBooleanPacket,
    jasPrimeSeparatedLocalHaarBooleanPacket, l2Amplification_single,
    l2Single_apply, lp.inner_single_left]
  by_cases hpq : p = q
  · subst q
    simp only [l2Single_apply, lp.single_apply]
    simpa using jasPrimePoissonLocalHaar_negativeCompression sigma t hsigma p i j
  · have hgrade : natEquivPrimes.symm p ≠ natEquivPrimes.symm q := by
      exact fun h => hpq (natEquivPrimes.symm.injective h)
    simp [lp.single_apply, hpq, hgrade]

end


end GaloisForLFunctions.HTGeometry
