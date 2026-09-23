import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberGlobalReflection
import GaloisForLFunctions.HTGeometry.SmoothNumbers

/-!
# The canonical theta packet defines an infinite-rank reflection functional

The positive square-index atoms give the arithmetic coordinates of the theta source.  On the
closed upper half-plane their value and spectral-derivative coordinates are both absolutely
summable.  This module packages exactly that source-selected completion and proves that its
oriented quadratic synthesis is the full canonical density current, hence also the absolutely
convergent product-fibre current.

At the archimedean fixed point `z = 0`, every positive product fibre has strictly positive current.
Consequently the completed current has genuinely infinite arithmetic support: it cannot factor
through any finite square-index, product-fibre, or prime-power window.  This is compatible with the
finite valuation freeness theorem, but it does not assign the upper-half-plane sign required for
RH.  The missing datum is an infinite-support reflection polarization, not another finite packet
identity.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The complete finite-support prime-valuation vector carried by one positive square index. -/
def thetaSquareIndexValuationVector (n : ℕ) : Nat.Primes →₀ ℕ :=
  GaloisForLFunctions.primeExponentVector (n + 1)

/-- Unique factorization makes the square-index labelling by valuation vectors faithful. -/
theorem thetaSquareIndexValuationVector_injective :
    Function.Injective thetaSquareIndexValuationVector := by
  intro m n hmn
  change GaloisForLFunctions.primeExponentVector (m + 1) =
    GaloisForLFunctions.primeExponentVector (n + 1) at hmn
  have hprod := congrArg GaloisForLFunctions.primeProduct hmn
  rw [GaloisForLFunctions.primeProduct_primeExponentVector (by omega),
    GaloisForLFunctions.primeProduct_primeExponentVector (by omega)] at hprod
  omega

/-- The archimedean logarithmic displacement is exactly the prime-valuation pairing. -/
theorem thetaSquareIndex_log_eq_valuationPairing (n : ℕ) :
    Real.log (n + 1 : ℝ) =
      (thetaSquareIndexValuationVector n).sum fun p k =>
        (k : ℝ) * Real.log (p : ℕ) := by
  simpa [thetaSquareIndexValuationVector] using
    (GaloisForLFunctions.log_nat_eq_sum_factorization (n := n + 1) (by omega))

/-- The distinguished valuation coordinate used to witness unbounded prime-power depth. -/
def thetaPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- The completed square-index packet reaches every depth on the two-adic valuation ray. -/
theorem thetaSquareIndexValuationVector_two_pow (N : ℕ) :
    thetaSquareIndexValuationVector (2 ^ (N + 1) - 1) thetaPrimeTwo = N + 1 := by
  have hpow : 0 < 2 ^ (N + 1) := pow_pos (by norm_num) _
  have hadd : 2 ^ (N + 1) - 1 + 1 = 2 ^ (N + 1) :=
    Nat.sub_add_cancel hpow
  rw [thetaSquareIndexValuationVector,
    GaloisForLFunctions.primeExponentVector_apply,
    hadd]
  simpa [thetaPrimeTwo] using
    (Nat.factorization_pow_self (n := N + 1) Nat.prime_two)

/-- No bounded prime-power depth contains the completed valuation packet. -/
theorem thetaSquareIndexValuationVector_unboundedDepth (N : ℕ) :
    ∃ n : ℕ, N < thetaSquareIndexValuationVector n thetaPrimeTwo := by
  refine ⟨2 ^ (N + 1) - 1, ?_⟩
  rw [thetaSquareIndexValuationVector_two_pow]
  omega

/-- Raw value and spectral-derivative coordinates over all positive square indices. -/
abbrev ThetaCompletedValuationRaw := (ℕ → ℂ) × (ℕ → ℂ)

/-- The source-selected completion on which both canonical arithmetic syntheses converge. -/
def thetaCompletedValuationDomain : Submodule ℂ ThetaCompletedValuationRaw where
  carrier := {a | Summable a.1 ∧ Summable a.2}
  zero_mem' := by exact ⟨summable_zero, summable_zero⟩
  add_mem' := by
    intro a b ha hb
    exact ⟨by simpa [Pi.add_def] using ha.1.add hb.1,
      by simpa [Pi.add_def] using ha.2.add hb.2⟩
  smul_mem' := by
    intro c a ha
    refine ⟨?_, ?_⟩
    · have h : Summable (fun i => c * a.1 i) := ha.1.mul_left c
      simpa [Pi.smul_def, smul_eq_mul] using h
    · have h : Summable (fun i => c * a.2 i) := ha.2.mul_left c
      simpa [Pi.smul_def, smul_eq_mul] using h

/-- Infinite value synthesis on the completed valuation domain. -/
def thetaCompletedValuationValue : thetaCompletedValuationDomain →ₗ[ℂ] ℂ where
  toFun a := ∑' n : ℕ, a.1.1 n
  map_add' a b := by
    simpa using a.2.1.tsum_add b.2.1
  map_smul' c a := by
    simpa using a.2.1.tsum_mul_left c

/-- Infinite spectral-derivative synthesis on the completed valuation domain. -/
def thetaCompletedValuationDerivative : thetaCompletedValuationDomain →ₗ[ℂ] ℂ where
  toFun a := ∑' n : ℕ, a.1.2 n
  map_add' a b := by
    simpa using a.2.2.tsum_add b.2.2
  map_smul' c a := by
    simpa using a.2.2.tsum_mul_left c

/-- The literal canonical theta value/derivative tomography at a spectral point. -/
def thetaCanonicalCompletedValuationRaw (z : ℂ) : ThetaCompletedValuationRaw :=
  (fun n : ℕ => thetaCuspTailSecondDensityAtomPhase (n + 1) z,
    fun n : ℕ => thetaCuspTailSecondDensityAtomPhaseDerivative (n + 1) z)

/-- The canonical tomography belongs to the completed domain on the closed upper half-plane. -/
theorem thetaCanonicalCompletedValuationRaw_mem
    {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCanonicalCompletedValuationRaw z ∈ thetaCompletedValuationDomain := by
  exact ⟨summable_thetaCuspTailSecondDensityAtomPhase hz,
    summable_thetaCuspTailSecondDensityAtomPhaseDerivative hz⟩

/-- The canonical completed valuation vector. -/
def thetaCanonicalCompletedValuation
    (z : ℂ) (hz : 0 ≤ z.im) : thetaCompletedValuationDomain :=
  ⟨thetaCanonicalCompletedValuationRaw z,
    thetaCanonicalCompletedValuationRaw_mem hz⟩

/-- Value synthesis of the completed tomography is the full one-sided density phase. -/
theorem thetaCompletedValuationValue_canonical
    {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCompletedValuationValue (thetaCanonicalCompletedValuation z hz) =
      thetaCuspTailSecondDensityPhaseValue z := by
  exact tsum_thetaCuspTailSecondDensityAtomPhase_eq_full hz

/-- Derivative synthesis of the completed tomography is the full phase derivative. -/
theorem thetaCompletedValuationDerivative_canonical
    {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCompletedValuationDerivative (thetaCanonicalCompletedValuation z hz) =
      thetaCuspTailSecondDensityPhaseDerivative z := by
  exact tsum_thetaCuspTailSecondDensityAtomPhaseDerivative_eq_full hz

/-- The oriented Hermitian reflection functional on the completed valuation tomography. -/
def thetaCompletedValuationReflectionCurrent
    (a : thetaCompletedValuationDomain) : ℝ :=
  (thetaCompletedValuationDerivative a *
    (starRingEnd ℂ) (thetaCompletedValuationValue a)).im

/-- The completed reflection functional is exactly the full canonical density current. -/
theorem thetaCompletedValuationReflectionCurrent_canonical
    {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCompletedValuationReflectionCurrent
        (thetaCanonicalCompletedValuation z hz) =
      (thetaCuspTailSecondDensityPhaseDerivative z *
        (starRingEnd ℂ) (thetaCuspTailSecondDensityPhaseValue z)).im := by
  rw [thetaCompletedValuationReflectionCurrent,
    thetaCompletedValuationDerivative_canonical hz,
    thetaCompletedValuationValue_canonical hz]

/-- The same functional is the absolutely convergent sum of all product-fibre currents. -/
theorem thetaCompletedValuationReflectionCurrent_canonical_eq_productFibres
    {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCompletedValuationReflectionCurrent
        (thetaCanonicalCompletedValuation z hz) =
      ∑' k : ℕ, thetaProductFiberActualPhaseCurrent k z := by
  rw [thetaCompletedValuationReflectionCurrent_canonical hz,
    thetaCuspTailSecondDensityPhase_current_eq_tsum_productFiberActualPhaseCurrent hz]

/-- Archimedean reflection reads the even boundary channel of the infinite value synthesis. -/
theorem thetaCompletedValuationValue_canonical_boundary_reflection
    (t : ℝ) :
    (t ^ (2 : ℕ) + 1 / 4) *
        (thetaCompletedValuationValue
          (thetaCanonicalCompletedValuation (t : ℂ) (by simp))).re =
      1 / 4 + 2 * t ^ (2 : ℕ) * (XiC (t : ℂ)).re := by
  rw [thetaCompletedValuationValue_canonical (by simp)]
  exact thetaCuspTailSecondDensityPhaseValue_re_ofReal_crossed t

/-! ## Strict infinite support at the archimedean fixed point -/

/-- Every raw moment of every positive square-index density atom is strictly positive. -/
theorem thetaCuspTailSecondDensityAtomMoment_pos
    {n : ℕ} (hn : 0 < n) (m : ℕ) :
    0 < thetaCuspTailSecondDensityAtomMoment n m := by
  rw [thetaCuspTailSecondDensityAtomMoment]
  let f : ℝ → ℝ := fun x => x ^ m * thetaCuspTailSecondDensityAtom n x
  have hfcont : Continuous f := by
    dsimp [f]
    exact (continuous_id.pow _).mul
      (continuous_const.mul (continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspPolynomialAtom
          (thetaCuspTailDerivativePolynomial 2) n x).continuousAt))
  have hfint : IntegrableOn f (Ioi 0) := by
    simpa only [f] using
      integrableOn_pow_mul_thetaCuspTailSecondDensityAtom m hn
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le _)
      (thetaCuspTailSecondDensityAtom_pos hn hx.le).le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
  have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
    hfcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  change f 1 ≠ 0
  dsimp [f]
  positivity [thetaCuspTailSecondDensityAtom_pos hn (x := 1) (by norm_num)]

/-- At `z=0`, an atom value is its positive mass. -/
theorem thetaCuspTailSecondDensityAtomPhase_zero (n : ℕ) :
    thetaCuspTailSecondDensityAtomPhase (n + 1) 0 =
      (thetaCuspTailSecondDensityAtomMoment (n + 1) 0 : ℂ) := by
  unfold thetaCuspTailSecondDensityAtomPhase spectralTranslationPhase
  simp only [mul_zero, Complex.exp_zero, mul_one]
  simpa only [pow_zero, mul_one] using
    integral_thetaCuspTailSecondDensityAtom_mul_complexPower n 0

/-- At `z=0`, an atom derivative is `i` times its positive first moment. -/
theorem thetaCuspTailSecondDensityAtomPhaseDerivative_zero (n : ℕ) :
    thetaCuspTailSecondDensityAtomPhaseDerivative (n + 1) 0 =
      I * (thetaCuspTailSecondDensityAtomMoment (n + 1) 1 : ℂ) := by
  unfold thetaCuspTailSecondDensityAtomPhaseDerivative spectralTranslationPhase
  simp only [mul_zero, Complex.exp_zero, mul_one]
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) * ((x : ℂ) * I)) =
      fun x : ℝ => I *
        ((thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) * (x : ℂ) ^ (1 : ℕ)) by
    funext x
    simp only [pow_one]
    ring]
  rw [MeasureTheory.integral_const_mul,
    integral_thetaCuspTailSecondDensityAtom_mul_complexPower]

/-- Every value coordinate of the canonical tomography is nonzero at the reflection fixed point. -/
theorem thetaCanonicalCompletedValuationRaw_value_zero_ne
    (n : ℕ) :
    (thetaCanonicalCompletedValuationRaw 0).1 n ≠ 0 := by
  simp only [thetaCanonicalCompletedValuationRaw, thetaCuspTailSecondDensityAtomPhase_zero]
  exact Complex.ofReal_ne_zero.mpr
    (thetaCuspTailSecondDensityAtomMoment_pos (Nat.succ_pos n) 0).ne'

/-- No finite square-index window carries the canonical completed value synthesis. -/
theorem thetaCanonicalCompletedValuationRaw_value_zero_infiniteSupport :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (thetaCanonicalCompletedValuationRaw 0).1 n ≠ 0 := by
  intro N
  exact ⟨N, le_rfl, thetaCanonicalCompletedValuationRaw_value_zero_ne N⟩

/-- Exact positive-moment formula for one product-fibre current at `z=0`. -/
theorem thetaProductFiberActualPhaseCurrent_zero (k : ℕ) :
    thetaProductFiberActualPhaseCurrent k 0 =
      ∑ q ∈ thetaPositiveFactorPairs k,
        thetaCuspTailSecondDensityAtomMoment (q.1 + 1) 1 *
          thetaCuspTailSecondDensityAtomMoment (q.2 + 1) 0 := by
  unfold thetaProductFiberActualPhaseCurrent
  apply Finset.sum_congr rfl
  intro q _hq
  rw [thetaCuspTailSecondDensityAtomPhaseDerivative_zero,
    thetaCuspTailSecondDensityAtomPhase_zero]
  simp

/-- Every positive product fibre contributes strictly at the archimedean fixed point. -/
theorem thetaProductFiberActualPhaseCurrent_zero_pos
    {k : ℕ} (hk : 0 < k) :
    0 < thetaProductFiberActualPhaseCurrent k 0 := by
  rw [thetaProductFiberActualPhaseCurrent_zero]
  apply Finset.sum_pos
  · intro q _hq
    exact mul_pos
      (thetaCuspTailSecondDensityAtomMoment_pos (Nat.succ_pos q.1) 1)
      (thetaCuspTailSecondDensityAtomMoment_pos (Nat.succ_pos q.2) 0)
  · refine ⟨(0, k - 1), ?_⟩
    simp [thetaPositiveFactorPairs, hk, Nat.sub_lt hk, Nat.sub_add_cancel hk]

/-- The completed product-fibre reflection current has genuinely infinite arithmetic support. -/
theorem thetaProductFiberActualPhaseCurrent_zero_infiniteSupport :
    ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧
      thetaProductFiberActualPhaseCurrent k 0 ≠ 0 := by
  intro N
  refine ⟨N + 1, by omega, ?_⟩
  exact (thetaProductFiberActualPhaseCurrent_zero_pos (by omega)).ne'

end

end RHTower
