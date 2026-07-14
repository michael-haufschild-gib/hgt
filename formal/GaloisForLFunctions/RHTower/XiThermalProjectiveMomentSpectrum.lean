import GaloisForLFunctions.RHTower.XiOffLineQuartetThermalOrientationBound
import GaloisForLFunctions.RHTower.XiProjectiveReflectionSourceTemperatureSpectrum

/-!
# Faithful thermal projective moments and the fixed-window abscissa

The unconditional reciprocal-square thermal mass is strictly positive on every multiplicity copy
of the Xi divisor.  Use that mass as a faithful vacuum weight, but use the projective/Born
reflection displacement as the static observable.  The resulting positive moments retain the
exact horizontal support radius: a scale `alpha` bounds every Xi zero precisely when every moment
is bounded by the zeroth source mass times `alpha^m`.

Every finite truncation is an explicit finite KMS/Wightman moment system, and the pointwise limit
remains in the closed trace--Hankel cone.  Thus the fixed-window prime--Gamma abscissa is read by a
thermodynamic moment-growth law rather than by a height-damped quadratic energy.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The faithful thermal moment of the projective reflection displacement. -/
def xiThermalProjectiveMoment (m : ℕ) : ℝ :=
  ∑' q : XiZeroCopy, xiThermalNode q *
    xiEndpointProjectiveReflectionDisplacement q ^ m

/-- The corresponding finite multiplicity-exact thermal truncation. -/
def xiThermalProjectiveTruncation (N m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N,
    xiThermalNode (xiThermalEnumeration j) *
      xiEndpointProjectiveReflectionDisplacement (xiThermalEnumeration j) ^ m

theorem xiEndpointProjectiveReflectionDisplacement_nonneg (q : XiZeroCopy) :
    0 ≤ xiEndpointProjectiveReflectionDisplacement q := by
  rw [xiEndpointProjectiveReflectionDisplacement_eq_abs]
  exact abs_nonneg _

theorem xiEndpointProjectiveReflectionDisplacement_lt_half (q : XiZeroCopy) :
    xiEndpointProjectiveReflectionDisplacement q < 1 / 2 := by
  rw [xiEndpointProjectiveReflectionDisplacement_eq_abs]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  rw [abs_lt]
  constructor <;> linarith

theorem xiEndpointProjectiveReflectionDisplacement_le_one (q : XiZeroCopy) :
    xiEndpointProjectiveReflectionDisplacement q ≤ 1 := by
  linarith [xiEndpointProjectiveReflectionDisplacement_lt_half q]

/-- Every faithful projective thermal moment is absolutely summable. -/
theorem summable_xiThermalProjectiveMoment (m : ℕ) :
    Summable (fun q : XiZeroCopy => xiThermalNode q *
      xiEndpointProjectiveReflectionDisplacement q ^ m) := by
  have hmass : Summable (fun q : XiZeroCopy => xiThermalNode q) := by
    simpa using summable_xiThermalNode_pow 0
  refine Summable.of_nonneg_of_le
    (fun q => mul_nonneg (xiThermalNode_pos q).le
      (pow_nonneg (xiEndpointProjectiveReflectionDisplacement_nonneg q) _))
    (fun q => ?_) hmass
  exact mul_le_of_le_one_right (xiThermalNode_pos q).le
    (pow_le_one₀ (xiEndpointProjectiveReflectionDisplacement_nonneg q)
      (xiEndpointProjectiveReflectionDisplacement_le_one q))

theorem xiThermalProjectiveMoment_nonneg (m : ℕ) :
    0 ≤ xiThermalProjectiveMoment m := by
  exact tsum_nonneg fun q => mul_nonneg (xiThermalNode_pos q).le
    (pow_nonneg (xiEndpointProjectiveReflectionDisplacement_nonneg q) _)

/-- The zeroth faithful orientation mass is exactly the unconditional prime--Gamma source mass. -/
theorem xiThermalProjectiveMoment_zero_eq_source :
    xiThermalProjectiveMoment 0 = normalizedPrimeArchMoment 0 := by
  rw [xiThermalProjectiveMoment]
  simp only [pow_zero, mul_one]
  simpa only [xiThermalPositiveMoment, zero_add, pow_one] using
    xiThermalPositiveMoment_zero_eq_source

/-- The faithful cold partition value of the projective reflection observable at integer inverse
temperature `k`. -/
def xiThermalProjectiveColdPartition (k : ℕ) : ℝ :=
  ∑' q : XiZeroCopy, xiThermalNode q *
    Real.exp ((k : ℝ) * xiEndpointProjectiveReflectionDisplacement q)

/-- The finite-system cold partition value. -/
def xiThermalProjectiveColdTruncation (N k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N,
    xiThermalNode (xiThermalEnumeration j) *
      Real.exp ((k : ℝ) *
        xiEndpointProjectiveReflectionDisplacement (xiThermalEnumeration j))

/-- Every cold partition value is absolutely summable; the open critical strip gives the
uniform atomwise majorant `exp (k/2)`. -/
theorem summable_xiThermalProjectiveColdPartition (k : ℕ) :
    Summable (fun q : XiZeroCopy => xiThermalNode q *
      Real.exp ((k : ℝ) * xiEndpointProjectiveReflectionDisplacement q)) := by
  have hmass : Summable (fun q : XiZeroCopy => xiThermalNode q) := by
    simpa using summable_xiThermalNode_pow 0
  have hscaled : Summable (fun q : XiZeroCopy =>
      xiThermalNode q * Real.exp ((k : ℝ) * (1 / 2 : ℝ))) :=
    hmass.mul_right _
  refine Summable.of_nonneg_of_le
    (fun q => mul_nonneg (xiThermalNode_pos q).le (Real.exp_pos _).le)
    (fun q => mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left
          (xiEndpointProjectiveReflectionDisplacement_lt_half q).le
          (Nat.cast_nonneg k)))
      (xiThermalNode_pos q).le)
    hscaled

theorem xiThermalProjectiveColdPartition_nonneg (k : ℕ) :
    0 ≤ xiThermalProjectiveColdPartition k := by
  exact tsum_nonneg fun q =>
    mul_nonneg (xiThermalNode_pos q).le (Real.exp_pos _).le

/-- At zero inverse temperature the cold partition value is exactly the source mass. -/
theorem xiThermalProjectiveColdPartition_zero_eq_source :
    xiThermalProjectiveColdPartition 0 = normalizedPrimeArchMoment 0 := by
  rw [xiThermalProjectiveColdPartition]
  simp only [Nat.cast_zero, zero_mul, Real.exp_zero, mul_one]
  simpa only [xiThermalPositiveMoment, zero_add, pow_one] using
    xiThermalPositiveMoment_zero_eq_source

set_option maxHeartbeats 500000 in
/-- The fixed enumeration sums every cold partition value. -/
theorem hasSum_xiThermalEnumeration_projectiveColdPartition (k : ℕ) :
    HasSum (fun j : ℕ =>
      xiThermalNode (xiThermalEnumeration j) *
        Real.exp ((k : ℝ) *
          xiEndpointProjectiveReflectionDisplacement (xiThermalEnumeration j)))
      (xiThermalProjectiveColdPartition k) := by
  let e : ℕ ≃ XiZeroCopy :=
    Equiv.ofBijective xiThermalEnumeration xiThermalEnumeration_bijective
  have hsum : HasSum (fun q : XiZeroCopy => xiThermalNode q *
      Real.exp ((k : ℝ) * xiEndpointProjectiveReflectionDisplacement q))
      (xiThermalProjectiveColdPartition k) := by
    simpa [xiThermalProjectiveColdPartition] using
      (summable_xiThermalProjectiveColdPartition k).hasSum
  have hsumNat : HasSum
      (fun j : ℕ => xiThermalNode (e j) *
        Real.exp ((k : ℝ) * xiEndpointProjectiveReflectionDisplacement (e j)))
      (xiThermalProjectiveColdPartition k) := e.hasSum_iff.mpr hsum
  simpa [e] using hsumNat

/-- Growing finite systems converge pointwise to the complete cold partition function. -/
theorem tendsto_xiThermalProjectiveColdTruncation :
    Tendsto xiThermalProjectiveColdTruncation atTop
      (nhds xiThermalProjectiveColdPartition) := by
  apply tendsto_pi_nhds.mpr
  intro k
  have ht :=
    (hasSum_xiThermalEnumeration_projectiveColdPartition k).tendsto_sum_nat
  simpa only [xiThermalProjectiveColdTruncation] using ht

/-- Every finite cold system is dominated by the complete positive partition value. -/
theorem xiThermalProjectiveColdTruncation_le_partition (N k : ℕ) :
    xiThermalProjectiveColdTruncation N k ≤
      xiThermalProjectiveColdPartition k := by
  rw [xiThermalProjectiveColdTruncation]
  have hsum := hasSum_xiThermalEnumeration_projectiveColdPartition k
  calc
    ∑ j ∈ Finset.range N,
        xiThermalNode (xiThermalEnumeration j) *
          Real.exp ((k : ℝ) *
            xiEndpointProjectiveReflectionDisplacement (xiThermalEnumeration j))
      ≤ ∑' j : ℕ,
          xiThermalNode (xiThermalEnumeration j) *
            Real.exp ((k : ℝ) *
              xiEndpointProjectiveReflectionDisplacement (xiThermalEnumeration j)) :=
        hsum.summable.sum_le_tsum (Finset.range N) (fun j _ =>
          mul_nonneg (xiThermalNode_pos _).le (Real.exp_pos _).le)
    _ = xiThermalProjectiveColdPartition k := hsum.tsum_eq

set_option maxHeartbeats 500000 in
/-- The fixed enumeration sums every faithful projective moment. -/
theorem hasSum_xiThermalEnumeration_projectiveMoment (m : ℕ) :
    HasSum (fun j : ℕ =>
      xiThermalNode (xiThermalEnumeration j) *
      xiEndpointProjectiveReflectionDisplacement (xiThermalEnumeration j) ^ m)
      (xiThermalProjectiveMoment m) := by
  let e : ℕ ≃ XiZeroCopy :=
    Equiv.ofBijective xiThermalEnumeration xiThermalEnumeration_bijective
  have hsum : HasSum (fun q : XiZeroCopy => xiThermalNode q *
      xiEndpointProjectiveReflectionDisplacement q ^ m)
      (xiThermalProjectiveMoment m) := by
    simpa [xiThermalProjectiveMoment] using
      (summable_xiThermalProjectiveMoment m).hasSum
  have hsumNat : HasSum
      (fun j : ℕ => xiThermalNode (e j) *
        xiEndpointProjectiveReflectionDisplacement (e j) ^ m)
      (xiThermalProjectiveMoment m) := e.hasSum_iff.mpr hsum
  simpa [e] using hsumNat

/-- The growing finite systems converge pointwise to the faithful projective moment tower. -/
theorem tendsto_xiThermalProjectiveTruncation :
    Tendsto xiThermalProjectiveTruncation atTop
      (nhds xiThermalProjectiveMoment) := by
  apply tendsto_pi_nhds.mpr
  intro m
  have ht := (hasSum_xiThermalEnumeration_projectiveMoment m).tendsto_sum_nat
  simpa only [xiThermalProjectiveTruncation] using ht

/-- Every finite faithful projective truncation is canonical finite KMS/Wightman data. -/
theorem finiteKMSWightmanMomentSequence_xiThermalProjectiveTruncation (N : ℕ) :
    FiniteKMSWightmanMomentSequence (xiThermalProjectiveTruncation N) := by
  let mass : Fin N → ℝ := fun i => xiThermalNode (xiThermalEnumeration i)
  let node : Fin N → ℝ := fun i =>
    xiEndpointProjectiveReflectionDisplacement (xiThermalEnumeration i)
  refine ⟨N, 0, HTGeometry.finiteAtomicThermalEnergy node,
    HTGeometry.finiteAtomicKMSAmplitude mass, ?_⟩
  funext m
  rw [HTGeometry.thermalEvenGapMoment_finiteAtomicKMS mass node
    (fun _ => (xiThermalNode_pos _).le)
    (fun _ => xiEndpointProjectiveReflectionDisplacement_nonneg _)]
  exact (Fin.sum_univ_eq_sum_range
    (fun j : ℕ => xiThermalNode (xiThermalEnumeration j) *
      xiEndpointProjectiveReflectionDisplacement (xiThermalEnumeration j) ^ m) N).symm

/-- The complete faithful projective moment tower lies in the closed trace--Hankel cone. -/
theorem sequenceTraceHankelNonnegative_xiThermalProjectiveMoment :
    SequenceTraceHankelNonnegative xiThermalProjectiveMoment := by
  exact sequenceTraceHankelNonnegative_of_finiteThermalKrylov_tendsto
    xiThermalProjectiveTruncation xiThermalProjectiveMoment
    (fun N => finiteKMSWightmanMomentSequence_finiteThermalKrylov
      (finiteKMSWightmanMomentSequence_xiThermalProjectiveTruncation N))
    tendsto_xiThermalProjectiveTruncation

/-- A global Xi half-plane bound gives the sharp source-normalized projective moment bounds. -/
theorem xiThermalProjectiveMoment_le_source_mul_pow_of_halfPlaneBound
    {alpha : ℝ} (_halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha)
    (m : ℕ) :
    xiThermalProjectiveMoment m ≤ normalizedPrimeArchMoment 0 * alpha ^ m := by
  have hmass : Summable (fun q : XiZeroCopy => xiThermalNode q) := by
    simpa using summable_xiThermalNode_pow 0
  have hscaled : Summable (fun q : XiZeroCopy => xiThermalNode q * alpha ^ m) :=
    hmass.mul_right (alpha ^ m)
  have hle := (summable_xiThermalProjectiveMoment m).tsum_le_tsum
    (fun q => by
      have hd : xiEndpointProjectiveReflectionDisplacement q ≤ alpha := by
        rw [xiEndpointProjectiveReflectionDisplacement_eq_abs]
        exact abs_xiZero_re_sub_half_le_of_halfPlaneBound hzeros q
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀
          (xiEndpointProjectiveReflectionDisplacement_nonneg q) hd m)
        (xiThermalNode_pos q).le)
    hscaled
  calc
    xiThermalProjectiveMoment m ≤
        ∑' q : XiZeroCopy, xiThermalNode q * alpha ^ m := by
      simpa only [xiThermalProjectiveMoment] using hle
    _ = (∑' q : XiZeroCopy, xiThermalNode q) * alpha ^ m := tsum_mul_right
    _ = normalizedPrimeArchMoment 0 * alpha ^ m := by
      congr 1
      simpa only [xiThermalPositiveMoment, zero_add, pow_one] using
        xiThermalPositiveMoment_zero_eq_source

/-- Faithfulness of the thermal mass makes the complete geometric moment bounds recover the
pointwise Xi half-plane bound. -/
theorem xiZeroHalfPlaneBound_of_forall_thermalProjectiveMoment_le
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hmom : ∀ m : ℕ,
      xiThermalProjectiveMoment m ≤ normalizedPrimeArchMoment 0 * alpha ^ m) :
    XiZeroHalfPlaneBound alpha := by
  intro rho hzero
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hmult : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (support : ℂ)) := by
    have hpos := xi_divisor_pos_on_support support
    omega
  let q : XiZeroCopy := ⟨support, ⟨0, hmult⟩⟩
  have hpoint : xiEndpointProjectiveReflectionDisplacement q ≤ alpha := by
    by_contra hnot
    have hdgt : alpha < xiEndpointProjectiveReflectionDisplacement q :=
      lt_of_not_ge hnot
    have hwpos : 0 < xiThermalNode q := xiThermalNode_pos q
    by_cases halpha0 : alpha = 0
    · subst alpha
      have hterm := (summable_xiThermalProjectiveMoment 1).le_tsum q
        (fun r _ => mul_nonneg (xiThermalNode_pos r).le
          (pow_nonneg (xiEndpointProjectiveReflectionDisplacement_nonneg r) _))
      have hupper := hmom 1
      simp only [pow_one, mul_zero] at hupper
      have hdpos : 0 < xiEndpointProjectiveReflectionDisplacement q := by linarith
      have hprod : 0 < xiThermalNode q *
          xiEndpointProjectiveReflectionDisplacement q ^ 1 := by positivity
      rw [← xiThermalProjectiveMoment] at hterm
      linarith
    · have halphaPos : 0 < alpha := lt_of_le_of_ne halpha (Ne.symm halpha0)
      let r : ℝ := xiEndpointProjectiveReflectionDisplacement q / alpha
      have hr : 1 < r := by
        dsimp only [r]
        exact (lt_div_iff₀ halphaPos).2 (by simpa using hdgt)
      have hev := (tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop
        (normalizedPrimeArchMoment 0 / xiThermalNode q)
      obtain ⟨M, hM⟩ := eventually_atTop.mp hev
      have hlarge := hM M le_rfl
      have hterm := (summable_xiThermalProjectiveMoment M).le_tsum q
        (fun s _ => mul_nonneg (xiThermalNode_pos s).le
          (pow_nonneg (xiEndpointProjectiveReflectionDisplacement_nonneg s) _))
      have hupper := hmom M
      rw [← xiThermalProjectiveMoment] at hterm
      have hscalePos : 0 < xiThermalNode q * alpha ^ M := by positivity
      have hlargeMul := mul_lt_mul_of_pos_right hlarge hscalePos
      have hleft :
          (normalizedPrimeArchMoment 0 / xiThermalNode q) *
              (xiThermalNode q * alpha ^ M) =
            normalizedPrimeArchMoment 0 * alpha ^ M := by
        field_simp [ne_of_gt hwpos]
      have hright :
          r ^ M * (xiThermalNode q * alpha ^ M) =
            xiThermalNode q *
              xiEndpointProjectiveReflectionDisplacement q ^ M := by
        dsimp only [r]
        rw [div_pow]
        field_simp [ne_of_gt halphaPos]
      rw [hleft, hright] at hlargeMul
      linarith
  rw [xiEndpointProjectiveReflectionDisplacement_eq_abs] at hpoint
  dsimp only [q, support] at hpoint
  rw [abs_le] at hpoint
  linarith

/-- **Faithful thermal support law.**  The source-normalized projective moment envelope is exactly
the Xi half-plane width. -/
theorem xiZeroHalfPlaneBound_iff_forall_thermalProjectiveMoment_le
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    XiZeroHalfPlaneBound alpha ↔
      ∀ m : ℕ, xiThermalProjectiveMoment m ≤
        normalizedPrimeArchMoment 0 * alpha ^ m := by
  constructor
  · exact fun hzeros m =>
      xiThermalProjectiveMoment_le_source_mul_pow_of_halfPlaneBound
        halpha hzeros m
  · exact xiZeroHalfPlaneBound_of_forall_thermalProjectiveMoment_le halpha

/-- **Fixed-window thermal moment abscissa spectrum.**  At every nonnegative transverse scale,
the prime--Gamma negative-source abscissa bound is exactly the source-normalized growth bound for
all faithful projective moments. -/
theorem primeGamma_abscissa_le_iff_forall_thermalProjectiveMoment_le
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) ≤
          ((1 + alpha : ℝ) : EReal) ↔
      ∀ m : ℕ, xiThermalProjectiveMoment m ≤
        normalizedPrimeArchMoment 0 * alpha ^ m := by
  exact (primeGamma_abscissa_le_iff_projectiveReflectionRadius_le
      hL halpha hN).trans
    ((xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le halpha).symm.trans
      (xiZeroHalfPlaneBound_iff_forall_thermalProjectiveMoment_le halpha))

/-- An eventual geometric envelope for the faithful thermal moments already forces the pointwise
Xi half-plane bound.  The constant may be arbitrary: strict excess of one displacement over
`alpha` would make its positive atomic contribution outrun that constant geometrically. -/
theorem xiZeroHalfPlaneBound_of_eventually_thermalProjectiveMoment_le
    {alpha C : ℝ} (halpha : 0 < alpha)
    (hmom : ∀ᶠ m : ℕ in atTop,
      xiThermalProjectiveMoment m ≤ C * alpha ^ m) :
    XiZeroHalfPlaneBound alpha := by
  intro rho hzero
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hmult : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (support : ℂ)) := by
    have hpos := xi_divisor_pos_on_support support
    omega
  let q : XiZeroCopy := ⟨support, ⟨0, hmult⟩⟩
  have hpoint : xiEndpointProjectiveReflectionDisplacement q ≤ alpha := by
    by_contra hnot
    have hdgt : alpha < xiEndpointProjectiveReflectionDisplacement q :=
      lt_of_not_ge hnot
    have hwpos : 0 < xiThermalNode q := xiThermalNode_pos q
    let r : ℝ := xiEndpointProjectiveReflectionDisplacement q / alpha
    have hr : 1 < r := by
      dsimp only [r]
      exact (lt_div_iff₀ halpha).2 (by simpa using hdgt)
    have hlargeEvent := (tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop
      (C / xiThermalNode q)
    obtain ⟨Mmom, hMmom⟩ := eventually_atTop.mp hmom
    obtain ⟨Mlarge, hMlarge⟩ := eventually_atTop.mp hlargeEvent
    let M := max Mmom Mlarge
    have hupper := hMmom M (le_max_left _ _)
    have hlarge := hMlarge M (le_max_right _ _)
    have hterm := (summable_xiThermalProjectiveMoment M).le_tsum q
      (fun s _ => mul_nonneg (xiThermalNode_pos s).le
        (pow_nonneg (xiEndpointProjectiveReflectionDisplacement_nonneg s) _))
    rw [← xiThermalProjectiveMoment] at hterm
    have hscalePos : 0 < xiThermalNode q * alpha ^ M := by positivity
    have hlargeMul := mul_lt_mul_of_pos_right hlarge hscalePos
    have hleft :
        (C / xiThermalNode q) * (xiThermalNode q * alpha ^ M) =
          C * alpha ^ M := by
      field_simp [ne_of_gt hwpos]
    have hright :
        r ^ M * (xiThermalNode q * alpha ^ M) =
          xiThermalNode q *
            xiEndpointProjectiveReflectionDisplacement q ^ M := by
      dsimp only [r]
      rw [div_pow]
      field_simp [ne_of_gt halpha]
    rw [hleft, hright] at hlargeMul
    linarith
  rw [xiEndpointProjectiveReflectionDisplacement_eq_abs] at hpoint
  dsimp only [q, support] at hpoint
  rw [abs_le] at hpoint
  linarith

/-- **Cofinal thermal support law.**  At every positive scale, a half-plane bound is equivalent
to any eventual geometric envelope for the faithful projective moments.  No exact finite moment
or prescribed envelope constant is required. -/
theorem xiZeroHalfPlaneBound_iff_exists_eventually_thermalProjectiveMoment_le
    {alpha : ℝ} (halpha : 0 < alpha) :
    XiZeroHalfPlaneBound alpha ↔
      ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
        xiThermalProjectiveMoment m ≤ C * alpha ^ m := by
  constructor
  · intro hzeros
    refine ⟨normalizedPrimeArchMoment 0, ?_⟩
    exact Filter.Eventually.of_forall fun m =>
      xiThermalProjectiveMoment_le_source_mul_pow_of_halfPlaneBound
        halpha.le hzeros m
  · rintro ⟨C, hC⟩
    exact xiZeroHalfPlaneBound_of_eventually_thermalProjectiveMoment_le halpha hC

/-- The scale-resolved fixed-window abscissa is equivalently an eventual high-order thermal
moment-growth bound with an arbitrary finite prefactor. -/
theorem primeGamma_abscissa_le_iff_exists_eventually_thermalProjectiveMoment_le
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 < alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) ≤
          ((1 + alpha : ℝ) : EReal) ↔
      ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
        xiThermalProjectiveMoment m ≤ C * alpha ^ m := by
  exact (primeGamma_abscissa_le_iff_projectiveReflectionRadius_le
      hL halpha.le hN).trans
    ((xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le halpha.le).symm.trans
      (xiZeroHalfPlaneBound_iff_exists_eventually_thermalProjectiveMoment_le halpha))

/-- **Cofinal high-moment RH criterion.**  RH requires no exact thermal/source equality in this
chart: it is equivalent to eventual geometric decay of the faithful projective moments at every
positive rate. -/
theorem riemannHypothesis_iff_forall_pos_exists_eventually_thermalProjectiveMoment_le :
    RiemannHypothesis ↔
      ∀ alpha : ℝ, 0 < alpha →
        ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
          xiThermalProjectiveMoment m ≤ C * alpha ^ m := by
  constructor
  · intro hRH alpha halpha
    apply (xiZeroHalfPlaneBound_iff_exists_eventually_thermalProjectiveMoment_le
      halpha).mp
    intro rho hzero
    rw [xi_zero_re_eq_half_of_RH hRH hzero]
    linarith
  · intro hcofinal
    rw [rh_iff_xi_ne_zero_right]
    intro rho hrho hzero
    have hrhoHalf : 1 / 2 < rho.re := mem_rightHalf.mp hrho
    let alpha : ℝ := (rho.re - 1 / 2) / 2
    have halpha : 0 < alpha := by
      dsimp only [alpha]
      linarith
    obtain ⟨C, hC⟩ := hcofinal alpha halpha
    have hzeros := xiZeroHalfPlaneBound_of_eventually_thermalProjectiveMoment_le
      halpha hC
    have hbound := hzeros rho hzero
    dsimp only [alpha] at hbound
    linarith

/-- **Direct RH-target discharge interface.**  The exact Gamma-free negative-abscissa inequality
is equivalent to the cofinal high-order decay of one faithful static thermal observable.  This
replaces exact second-moment source saturation by eventual estimates with arbitrary constants. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_cofinal_thermalProjectiveMoments
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
        ((1 : ℝ) : EReal) ↔
      ∀ alpha : ℝ, 0 < alpha →
        ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
          xiThermalProjectiveMoment m ≤ C * alpha ^ m := by
  exact
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
      hL hN).symm.trans
        riemannHypothesis_iff_forall_pos_exists_eventually_thermalProjectiveMoment_le

/-- A Xi half-plane bound gives the sharp source-normalized cold-partition envelope. -/
theorem xiThermalProjectiveColdPartition_le_source_exp_of_halfPlaneBound
    {alpha : ℝ} (_halpha : 0 ≤ alpha) (hzeros : XiZeroHalfPlaneBound alpha)
    (k : ℕ) :
    xiThermalProjectiveColdPartition k ≤
      normalizedPrimeArchMoment 0 * Real.exp ((k : ℝ) * alpha) := by
  have hmass : Summable (fun q : XiZeroCopy => xiThermalNode q) := by
    simpa using summable_xiThermalNode_pow 0
  have hscaled : Summable (fun q : XiZeroCopy =>
      xiThermalNode q * Real.exp ((k : ℝ) * alpha)) := hmass.mul_right _
  have hle := (summable_xiThermalProjectiveColdPartition k).tsum_le_tsum
    (fun q => by
      have hd : xiEndpointProjectiveReflectionDisplacement q ≤ alpha := by
        rw [xiEndpointProjectiveReflectionDisplacement_eq_abs]
        exact abs_xiZero_re_sub_half_le_of_halfPlaneBound hzeros q
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg k)))
        (xiThermalNode_pos q).le)
    hscaled
  calc
    xiThermalProjectiveColdPartition k ≤
        ∑' q : XiZeroCopy,
          xiThermalNode q * Real.exp ((k : ℝ) * alpha) := by
      simpa only [xiThermalProjectiveColdPartition] using hle
    _ = (∑' q : XiZeroCopy, xiThermalNode q) *
        Real.exp ((k : ℝ) * alpha) := tsum_mul_right
    _ = normalizedPrimeArchMoment 0 * Real.exp ((k : ℝ) * alpha) := by
      congr 1
      simpa only [xiThermalPositiveMoment, zero_add, pow_one] using
        xiThermalPositiveMoment_zero_eq_source

/-- Any eventual exponential envelope for the cold partition function forces the Xi half-plane
bound at the same exponent.  One atom outside the bound would dominate every fixed prefactor. -/
theorem xiZeroHalfPlaneBound_of_eventually_thermalProjectiveColdPartition_le
    {alpha C : ℝ} (_halpha : 0 ≤ alpha)
    (hcold : ∀ᶠ k : ℕ in atTop,
      xiThermalProjectiveColdPartition k ≤
        C * Real.exp ((k : ℝ) * alpha)) :
    XiZeroHalfPlaneBound alpha := by
  intro rho hzero
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hmult : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (support : ℂ)) := by
    have hpos := xi_divisor_pos_on_support support
    omega
  let q : XiZeroCopy := ⟨support, ⟨0, hmult⟩⟩
  have hpoint : xiEndpointProjectiveReflectionDisplacement q ≤ alpha := by
    by_contra hnot
    have hdgt : alpha < xiEndpointProjectiveReflectionDisplacement q :=
      lt_of_not_ge hnot
    have hwpos : 0 < xiThermalNode q := xiThermalNode_pos q
    let r : ℝ := Real.exp
      (xiEndpointProjectiveReflectionDisplacement q - alpha)
    have hr : 1 < r := by
      dsimp only [r]
      exact Real.one_lt_exp_iff.mpr (sub_pos.mpr hdgt)
    have hlargeEvent := (tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop
      (C / xiThermalNode q)
    obtain ⟨Mcold, hMcold⟩ := eventually_atTop.mp hcold
    obtain ⟨Mlarge, hMlarge⟩ := eventually_atTop.mp hlargeEvent
    let M := max Mcold Mlarge
    have hupper := hMcold M (le_max_left _ _)
    have hlarge := hMlarge M (le_max_right _ _)
    have hterm := (summable_xiThermalProjectiveColdPartition M).le_tsum q
      (fun s _ => mul_nonneg (xiThermalNode_pos s).le (Real.exp_pos _).le)
    rw [← xiThermalProjectiveColdPartition] at hterm
    have hscalePos : 0 < xiThermalNode q *
        Real.exp ((M : ℝ) * alpha) := by positivity
    have hlargeMul := mul_lt_mul_of_pos_right hlarge hscalePos
    have hleft :
        (C / xiThermalNode q) *
            (xiThermalNode q * Real.exp ((M : ℝ) * alpha)) =
          C * Real.exp ((M : ℝ) * alpha) := by
      field_simp [ne_of_gt hwpos]
    have hright :
        r ^ M * (xiThermalNode q * Real.exp ((M : ℝ) * alpha)) =
          xiThermalNode q * Real.exp
            ((M : ℝ) * xiEndpointProjectiveReflectionDisplacement q) := by
      dsimp only [r]
      rw [← Real.exp_nat_mul]
      calc
        Real.exp
              ((M : ℝ) *
                (xiEndpointProjectiveReflectionDisplacement q - alpha)) *
            (xiThermalNode q * Real.exp ((M : ℝ) * alpha)) =
            xiThermalNode q *
              (Real.exp
                  ((M : ℝ) *
                    (xiEndpointProjectiveReflectionDisplacement q - alpha)) *
                Real.exp ((M : ℝ) * alpha)) := by ring
        _ = xiThermalNode q * Real.exp
            (((M : ℝ) *
                (xiEndpointProjectiveReflectionDisplacement q - alpha)) +
              (M : ℝ) * alpha) := by rw [Real.exp_add]
        _ = xiThermalNode q * Real.exp
            ((M : ℝ) * xiEndpointProjectiveReflectionDisplacement q) := by
          congr 2
          ring
    rw [hleft, hright] at hlargeMul
    linarith
  rw [xiEndpointProjectiveReflectionDisplacement_eq_abs] at hpoint
  dsimp only [q, support] at hpoint
  rw [abs_le] at hpoint
  linarith

/-- **Cold free-energy support law.**  At every nonnegative scale, the Xi half-plane bound is
equivalent to an eventual cold-partition envelope with an arbitrary finite prefactor. -/
theorem xiZeroHalfPlaneBound_iff_exists_eventually_thermalProjectiveColdPartition_le
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    XiZeroHalfPlaneBound alpha ↔
      ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
        xiThermalProjectiveColdPartition k ≤
          C * Real.exp ((k : ℝ) * alpha) := by
  constructor
  · intro hzeros
    refine ⟨normalizedPrimeArchMoment 0, ?_⟩
    exact Filter.Eventually.of_forall fun k =>
      xiThermalProjectiveColdPartition_le_source_exp_of_halfPlaneBound
        halpha hzeros k
  · rintro ⟨C, hC⟩
    exact xiZeroHalfPlaneBound_of_eventually_thermalProjectiveColdPartition_le
      halpha hC

/-- **Bounded cold-partition RH criterion.**  RH is equivalent to eventual boundedness of one
positive faithful zero-temperature partition function. -/
theorem riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveColdPartition :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
        xiThermalProjectiveColdPartition k ≤ C := by
  constructor
  · intro hRH
    refine ⟨normalizedPrimeArchMoment 0, Filter.Eventually.of_forall fun k => ?_⟩
    have hzeros : XiZeroHalfPlaneBound 0 := by
      intro rho hzero
      rw [xi_zero_re_eq_half_of_RH hRH hzero]
      norm_num
    have hbound :=
      xiThermalProjectiveColdPartition_le_source_exp_of_halfPlaneBound
        (le_refl 0) hzeros k
    simpa using hbound
  · rintro ⟨C, hC⟩
    have hColdScaled : ∀ᶠ k : ℕ in atTop,
        xiThermalProjectiveColdPartition k ≤
          C * Real.exp ((k : ℝ) * 0) := by
      simpa using hC
    have hzeros :=
      xiZeroHalfPlaneBound_of_eventually_thermalProjectiveColdPartition_le
        (le_refl 0) hColdScaled
    rw [rh_iff_xi_ne_zero_right]
    intro rho hrho hzero
    have hbound := hzeros rho hzero
    have hright : 1 / 2 < rho.re := mem_rightHalf.mp hrho
    linarith

/-- **Exact Gamma-free target as bounded cold free energy.**  The open RH inequality for the
fixed-window negative source is discharged by proving eventual boundedness of the faithful cold
partition function—no exact source-moment identity remains in the hypothesis. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_eventually_bounded_coldPartition
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
        ((1 : ℝ) : EReal) ↔
      ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
        xiThermalProjectiveColdPartition k ≤ C := by
  exact
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
      hL hN).symm.trans
        riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveColdPartition

/-- **Exact finite thermodynamic RH law.**  RH is equivalent to one bound on all sufficiently
large finite thermal systems at every sufficiently cold integer temperature.  The forward
direction uses positivity of finite truncations; the reverse direction passes each eventual
finite-system bound through the pointwise thermodynamic limit. -/
theorem riemannHypothesis_iff_exists_eventually_cold_eventually_thermodynamic_bound :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        xiThermalProjectiveColdTruncation N k ≤ C := by
  constructor
  · intro hRH
    obtain ⟨C, hC⟩ :=
      riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveColdPartition.mp
        hRH
    refine ⟨C, ?_⟩
    filter_upwards [hC] with k hk
    exact Filter.Eventually.of_forall fun N =>
      (xiThermalProjectiveColdTruncation_le_partition N k).trans hk
  · rintro ⟨C, hC⟩
    apply
      riemannHypothesis_iff_exists_eventually_bounded_thermalProjectiveColdPartition.mpr
    refine ⟨C, ?_⟩
    filter_upwards [hC] with k hk
    have ht := (tendsto_pi_nhds.mp
      tendsto_xiThermalProjectiveColdTruncation) k
    exact le_of_tendsto ht hk

/-- The exact Gamma-free negative source abscissa target is equivalent to the same uniform
finite-system cold bound. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_eventually_cold_eventually_thermodynamic_bound
    {L : ℝ} (hL : 0 < L) {N₀ : ℕ}
    (hN₀ : ∀ n : ℕ, N₀ ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N₀) ≤
        ((1 : ℝ) : EReal) ↔
      ∃ C : ℝ, ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        xiThermalProjectiveColdTruncation N k ≤ C := by
  exact
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
      hL hN₀).symm.trans
        riemannHypothesis_iff_exists_eventually_cold_eventually_thermodynamic_bound

/-- The first faithful projective moment vanishes exactly on the RH fibre. -/
theorem xiThermalProjectiveMoment_one_eq_zero_iff_rh :
    xiThermalProjectiveMoment 1 = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hterm := (summable_xiThermalProjectiveMoment 1).le_tsum q
      (fun r _ => mul_nonneg (xiThermalNode_pos r).le
        (pow_nonneg (xiEndpointProjectiveReflectionDisplacement_nonneg r) _))
    rw [← xiThermalProjectiveMoment, hzero] at hterm
    have hd : xiEndpointProjectiveReflectionDisplacement q = 0 := by
      have hprod : xiThermalNode q *
          xiEndpointProjectiveReflectionDisplacement q = 0 := by
        simpa only [pow_one] using le_antisymm hterm
          (mul_nonneg (xiThermalNode_pos q).le
            (pow_nonneg (xiEndpointProjectiveReflectionDisplacement_nonneg q) 1))
      exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (xiThermalNode_pos q))
    rw [xiEndpointProjectiveReflectionDisplacement_eq_abs, abs_eq_zero] at hd
    have hre : (q.1 : ℂ).re = 1 / 2 := by linarith
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simp [xiSpectralPoint, hre]
  · intro hRH
    rw [xiThermalProjectiveMoment]
    have hfun : (fun q : XiZeroCopy => xiThermalNode q *
        xiEndpointProjectiveReflectionDisplacement q ^ 1) = 0 := by
      funext q
      have hre := xi_zero_re_eq_half_of_RH hRH
        (xi_eq_zero_of_mem_divisor_support q.1)
      rw [xiEndpointProjectiveReflectionDisplacement_eq_abs, hre]
      norm_num
    rw [hfun]
    exact tsum_zero

/-- Since the first faithful projective moment is nonnegative, its reverse inequality is already
the exact RH endpoint. -/
theorem xiThermalProjectiveMoment_one_le_zero_iff_rh :
    xiThermalProjectiveMoment 1 ≤ 0 ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact xiThermalProjectiveMoment_one_eq_zero_iff_rh.mp
      (le_antisymm h (xiThermalProjectiveMoment_nonneg 1))
  · intro hRH
    rw [xiThermalProjectiveMoment_one_eq_zero_iff_rh.mpr hRH]

end

end RHTower
