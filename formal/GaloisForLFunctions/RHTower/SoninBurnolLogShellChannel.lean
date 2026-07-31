import GaloisForLFunctions.RHTower.SoninBurnolConductorConcrete
import GaloisForLFunctions.RHTower.SoninEulerCrossShellOverlap
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry

/-!
# A concrete logarithmic position channel for the Burnol conductor

The Burnol conductor layer is stated for an abstract bounded position channel `M` subject to
`[M, A_a] = 0`.  This file supplies a genuine channel with that property, adapted to the geometric
shell tower the Sonin construction already uses.

Physical cutoffs commute with each other, so any finite real combination of them is a bounded
self-adjoint position channel commuting with every cutoff.  Taking the combination whose value on
the shell between `rᵏa` and `rᵏ⁺¹a` is `log(rᵏa)` produces a step approximation of the logarithmic
position multiplier, bounded by construction and exactly logarithmic on the tower.  Its conductor
`H = M + JMJ` is therefore a concrete operator, and the abstract Burnol cancellation identities
become statements about it.

The channel acts on the shell unit vector of its own layer by the scalar `log(rᵏa)`, so it is not
the zero operator: the interface is inhabited, not merely consistent.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Set
open ContinuousLinearMap
open scoped ENNReal

/-- Scalars pull out of a left product of operators on the even carrier. -/
private theorem smul_mul_even (c : ℂ) (X Y : evenSubspace →L[ℂ] evenSubspace) :
    (c • X) * Y = c • (X * Y) := by
  ext x
  simp

/-- Scalars pull out of a right product of operators on the even carrier. -/
private theorem mul_smul_even (c : ℂ) (X Y : evenSubspace →L[ℂ] evenSubspace) :
    X * (c • Y) = c • (X * Y) := by
  ext x
  simp

/-! ## Physical cutoffs commute -/

/-- Two physical cutoffs commute: their product is the cutoff at the smaller radius either way. -/
theorem evenIndicatorCutoff_comm (s t : ℝ) :
    evenIndicatorCutoff s * evenIndicatorCutoff t =
      evenIndicatorCutoff t * evenIndicatorCutoff s := by
  rw [evenIndicatorCutoff_mul_min, evenIndicatorCutoff_mul_min, min_comm]

/-- The commutator of two physical cutoffs vanishes. -/
theorem ccmCommutator_evenIndicatorCutoff (s t : ℝ) :
    ccmCommutator (evenIndicatorCutoff s) (evenIndicatorCutoff t) = 0 := by
  rw [ccmCommutator, evenIndicatorCutoff_comm, sub_self]

/-! ## The geometric shell tower -/

/-- Radius of the `k`-th step of the geometric shell tower above the base aperture. -/
def logShellRadius (a r : ℝ) (k : ℕ) : ℝ := r ^ k * a

theorem logShellRadius_pos {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (k : ℕ) :
    0 < logShellRadius a r k :=
  mul_pos (pow_pos (zero_lt_one.trans hr) k) ha

theorem logShellRadius_mono {a r : ℝ} (ha : 0 < a) (hr : 1 < r) {j k : ℕ} (hjk : j ≤ k) :
    logShellRadius a r j ≤ logShellRadius a r k :=
  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr.le hjk) ha.le

theorem logShellRadius_lt_succ {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (k : ℕ) :
    logShellRadius a r k < logShellRadius a r (k + 1) := by
  have hbase : 0 < r ^ k * a := logShellRadius_pos ha hr k
  have hstep : r ^ k * a < r ^ (k + 1) * a := by
    rw [pow_succ]
    nlinarith [pow_pos (zero_lt_one.trans hr) k]
  simpa only [logShellRadius] using hstep

/-! ## The logarithmic shell channel -/

/-- Step approximation of the logarithmic position multiplier on the geometric shell tower: on the
layer between `rᵏa` and `rᵏ⁺¹a` it is multiplication by `log(rᵏa)`. -/
def evenLogShellChannel (a r : ℝ) (n : ℕ) : evenSubspace →L[ℂ] evenSubspace :=
  ∑ k ∈ Finset.range n,
    ((Real.log (logShellRadius a r k) : ℝ) : ℂ) •
      (evenIndicatorCutoff (logShellRadius a r (k + 1)) -
        evenIndicatorCutoff (logShellRadius a r k))

/-- The logarithmic shell channel commutes with every physical cutoff. -/
theorem evenLogShellChannel_comm_evenIndicatorCutoff (a r c : ℝ) (n : ℕ) :
    evenLogShellChannel a r n * evenIndicatorCutoff c =
      evenIndicatorCutoff c * evenLogShellChannel a r n := by
  unfold evenLogShellChannel
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_even, mul_smul_even, sub_mul, mul_sub,
    evenIndicatorCutoff_comm (logShellRadius a r (k + 1)) c,
    evenIndicatorCutoff_comm (logShellRadius a r k) c]

/-- **Concrete Burnol position hypothesis.**  The logarithmic shell channel discharges the
commuting-channel hypothesis of the Burnol conductor layer. -/
theorem ccmCommutator_evenLogShellChannel_evenIndicatorCutoff (a r c : ℝ) (n : ℕ) :
    ccmCommutator (evenLogShellChannel a r n) (evenIndicatorCutoff c) = 0 := by
  rw [ccmCommutator, evenLogShellChannel_comm_evenIndicatorCutoff, sub_self]

/-- The adjoint of a finite sum of operators on the even carrier is the sum of the adjoints. -/
theorem adjoint_sum_even {ι : Type*} (s : Finset ι)
    (f : ι → evenSubspace →L[ℂ] evenSubspace) :
    ContinuousLinearMap.adjoint (∑ i ∈ s, f i) =
      ∑ i ∈ s, ContinuousLinearMap.adjoint (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, map_add, ih]

/-- The logarithmic shell channel is self-adjoint: its coefficients are real and physical cutoffs
are self-adjoint. -/
theorem adjoint_evenLogShellChannel (a r : ℝ) (n : ℕ) :
    ContinuousLinearMap.adjoint (evenLogShellChannel a r n) =
      evenLogShellChannel a r n := by
  classical
  unfold evenLogShellChannel
  rw [adjoint_sum_even]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ, map_sub,
    adjoint_evenIndicatorCutoff, adjoint_evenIndicatorCutoff]
  congr 1
  simp

/-! ## The concrete conductor -/

/-- Burnol conductor of the logarithmic shell channel under cosine-Fourier reflection. -/
def soninBurnolLogShellConductor (a r : ℝ) (n : ℕ) : evenSubspace →L[ℂ] evenSubspace :=
  burnolConductor (evenLogShellChannel a r n) evenFourierTransform

/-- The concrete conductor commutes with the reflection that defines it. -/
theorem ccmCommutator_soninBurnolLogShellConductor_evenFourierTransform
    (a r : ℝ) (n : ℕ) :
    ccmCommutator (soninBurnolLogShellConductor a r n) evenFourierTransform = 0 :=
  ccmCommutator_burnolConductor_evenFourierTransform (evenLogShellChannel a r n)

/-- **Concrete Burnol cancellation.**  The Fourier-edge commutator of the logarithmic shell
channel is the cosine-Fourier reflection of the physical conductor edge — an identity between
explicitly constructed operators, with no abstract channel left. -/
theorem ccmCommutator_evenLogShellChannel_evenFourierCutoff
    (a r c : ℝ) (n : ℕ) :
    ccmCommutator (evenLogShellChannel a r n) (evenFourierCutoff c) =
      evenFourierTransform *
        ccmCommutator (soninBurnolLogShellConductor a r n)
          (evenIndicatorCutoff c) * evenFourierTransform :=
  ccmCommutator_evenFourierCutoff_eq_reflectedConductorEdge c
    (evenLogShellChannel a r n)
    (ccmCommutator_evenLogShellChannel_evenIndicatorCutoff a r c n)

/-! ## Cutoffs on normalized indicators -/

/-- A physical cutoff fixes a normalized indicator supported inside its window. -/
theorem indicatorCutoff_normalizedIndicator_of_subset
    (c s : Set ℝ) (hc : MeasurableSet c) (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) (hsub : s ⊆ c) :
    indicatorCutoff c hc (normalizedIndicator s hs hfin) =
      normalizedIndicator s hs hfin := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae c hc (normalizedIndicator s hs hfin),
    normalizedIndicator_ae s hs hfin] with x hcut hnorm
  rw [hcut]
  by_cases hx : x ∈ c
  · rw [Set.indicator_of_mem hx]
  · have hxs : x ∉ s := fun h => hx (hsub h)
    rw [Set.indicator_of_notMem hx, hnorm, Set.indicator_of_notMem hxs, mul_zero]

/-- A physical cutoff annihilates a normalized indicator supported outside its window. -/
theorem indicatorCutoff_normalizedIndicator_of_disjoint
    (c s : Set ℝ) (hc : MeasurableSet c) (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) (hdisj : Disjoint c s) :
    indicatorCutoff c hc (normalizedIndicator s hs hfin) = 0 := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae c hc (normalizedIndicator s hs hfin),
    normalizedIndicator_ae s hs hfin,
    Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hcut hnorm hzero
  rw [hcut, hzero]
  by_cases hx : x ∈ c
  · have hxs : x ∉ s := Set.disjoint_left.mp hdisj hx
    rw [Set.indicator_of_mem hx, hnorm, Set.indicator_of_notMem hxs, mul_zero]
    rfl
  · rw [Set.indicator_of_notMem hx]
    rfl

/-! ## Shell units of the tower -/

/-- Unit vector supported strictly inside the `k`-th layer of the geometric shell tower. -/
def logShellUnit (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (k : ℕ) : evenSubspace :=
  evenShellVectorEven (logShellRadius a r k) (logShellRadius a r (k + 1))
    (logShellRadius_lt_succ ha hr k) 0

theorem norm_logShellUnit (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (k : ℕ) :
    ‖logShellUnit a r ha hr k‖ = 1 :=
  (evenShellVectorEven_orthonormal (logShellRadius a r k)
    (logShellRadius a r (k + 1)) (logShellRadius_pos ha hr k)
    (logShellRadius_lt_succ ha hr k)).norm_eq_one 0

theorem logShellUnit_ne_zero (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (k : ℕ) :
    logShellUnit a r ha hr k ≠ 0 := by
  intro h
  have hnorm := norm_logShellUnit a r ha hr k
  rw [h, norm_zero] at hnorm
  exact zero_ne_one hnorm

/-- A cutoff above the layer fixes the layer unit vector. -/
theorem evenIndicatorCutoff_logShellUnit_of_le
    (a r c : ℝ) (ha : 0 < a) (hr : 1 < r) (k : ℕ)
    (hc : logShellRadius a r (k + 1) ≤ c) :
    evenIndicatorCutoff c (logShellUnit a r ha hr k) = logShellUnit a r ha hr k := by
  apply Subtype.ext
  rw [coe_evenIndicatorCutoff_apply]
  have hsub : evenShellCell (logShellRadius a r k) (logShellRadius a r (k + 1)) 0 ⊆
      centralInterval c := by
    intro x hx
    have hIcc := evenShellCell_subset_Icc (logShellRadius_lt_succ ha hr k) 0 hx
    exact ⟨by linarith [hIcc.1], hIcc.2.trans hc⟩
  exact indicatorCutoff_normalizedIndicator_of_subset _ _ _ _ _ hsub

/-- A cutoff below the layer annihilates the layer unit vector. -/
theorem evenIndicatorCutoff_logShellUnit_of_ge
    (a r c : ℝ) (ha : 0 < a) (hr : 1 < r) (k : ℕ)
    (hc : c ≤ logShellRadius a r k) :
    evenIndicatorCutoff c (logShellUnit a r ha hr k) = 0 := by
  apply Subtype.ext
  rw [coe_evenIndicatorCutoff_apply]
  have hdisj : Disjoint (centralInterval c)
      (evenShellCell (logShellRadius a r k) (logShellRadius a r (k + 1)) 0) := by
    rw [Set.disjoint_left]
    intro x hxc hxs
    have hxabs : |x| ≤ c := abs_le.mpr hxc
    have hlow : logShellRadius a r k < |x| :=
      (lt_shellLeft (logShellRadius_lt_succ ha hr k) 0).trans hxs.1
    linarith
  exact indicatorCutoff_normalizedIndicator_of_disjoint _ _ _ _ _ hdisj

/-- **Logarithmic eigen-action.**  The channel multiplies the unit vector of the `k`-th layer by
`log(rᵏa)`: it really is the logarithm of the position on the tower. -/
theorem evenLogShellChannel_apply_logShellUnit
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n k : ℕ) (hk : k < n) :
    evenLogShellChannel a r n (logShellUnit a r ha hr k) =
      ((Real.log (logShellRadius a r k) : ℝ) : ℂ) • logShellUnit a r ha hr k := by
  classical
  unfold evenLogShellChannel
  rw [ContinuousLinearMap.sum_apply]
  rw [Finset.sum_eq_single k]
  · rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      evenIndicatorCutoff_logShellUnit_of_le a r _ ha hr k le_rfl,
      evenIndicatorCutoff_logShellUnit_of_ge a r _ ha hr k le_rfl, sub_zero]
  · intro j _ hjk
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · have h₁ : logShellRadius a r (j + 1) ≤ logShellRadius a r k :=
        logShellRadius_mono ha hr hlt
      have h₂ : logShellRadius a r j ≤ logShellRadius a r k :=
        logShellRadius_mono ha hr (Nat.le_of_lt (Nat.lt_of_succ_le (Nat.succ_le_of_lt hlt)))
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        evenIndicatorCutoff_logShellUnit_of_ge a r _ ha hr k h₁,
        evenIndicatorCutoff_logShellUnit_of_ge a r _ ha hr k h₂, sub_zero, smul_zero]
    · have h₁ : logShellRadius a r (k + 1) ≤ logShellRadius a r j :=
        logShellRadius_mono ha hr hgt
      have h₂ : logShellRadius a r (k + 1) ≤ logShellRadius a r (j + 1) :=
        logShellRadius_mono ha hr (Nat.succ_le_succ hgt.le)
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        evenIndicatorCutoff_logShellUnit_of_le a r _ ha hr k h₂,
        evenIndicatorCutoff_logShellUnit_of_le a r _ ha hr k h₁, sub_self, smul_zero]
  · intro hkn
    exact absurd (Finset.mem_range.mpr hk) hkn

/-- **Nonvacuity of the Burnol channel interface.**  The logarithmic shell channel is not the zero
operator whenever its first layer sits off the unit radius, so the concrete conductor is a genuine
object and every abstract Burnol cancellation identity has a nontrivial instance. -/
theorem evenLogShellChannel_ne_zero
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n : ℕ) (hn : 0 < n)
    (hlog : Real.log a ≠ 0) :
    evenLogShellChannel a r n ≠ 0 := by
  intro hzero
  have hrad : logShellRadius a r 0 = a := by
    simp [logShellRadius]
  have haction := evenLogShellChannel_apply_logShellUnit a r ha hr n 0 hn
  rw [hzero] at haction
  rw [hrad] at haction
  have hsmul : ((Real.log a : ℝ) : ℂ) • logShellUnit a r ha hr 0 = 0 :=
    haction.symm
  rcases smul_eq_zero.mp hsmul with hc | hv
  · exact hlog (by exact_mod_cast hc)
  · exact logShellUnit_ne_zero a r ha hr 0 hv

end RHTower
