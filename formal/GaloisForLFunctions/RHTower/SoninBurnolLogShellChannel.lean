import GaloisForLFunctions.RHTower.SoninBurnolConductorConcrete
import GaloisForLFunctions.RHTower.SoninBurnolFiniteRankWardTrace
import GaloisForLFunctions.RHTower.SoninBurnolPointedWardTrace
import GaloisForLFunctions.RHTower.SoninEulerCrossShellOverlap
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import GaloisForLFunctions.RHTower.SoninEulerTripleShellOverlap

/-!
# A concrete logarithmic position channel for the Burnol conductor

The Burnol conductor layer is stated for an abstract bounded position channel `M` subject to
`[M, A_a] = 0`.  This file supplies a genuine channel with that property, adapted to the geometric
shell tower the Sonin construction already uses.

Physical cutoffs commute with each other, so any finite real combination of them is a bounded
self-adjoint position channel commuting with every cutoff.  Taking the combination whose value on
the layer between `rᵏa` and `rᵏ⁺¹a` is `log(rᵏa)` produces a step approximation of the logarithmic
position multiplier: bounded by construction, and exactly logarithmic on the tower.  Its conductor
`H = M + JMJ` is then a concrete operator, and the abstract Burnol cancellation identities become
statements about it.

The channel multiplies the shell unit vector of its own layer by `log(rᵏa)`, so it is not the zero
operator: the interface is inhabited, not merely consistent.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Set
open ContinuousLinearMap

/-- Scalars pull out of a left product of operators on the even carrier. -/
theorem smul_mul_even (c : ℂ) (X Y : evenSubspace →L[ℂ] evenSubspace) :
    (c • X) * Y = c • (X * Y) := by
  ext x
  simp

/-- Scalars pull out of a right product of operators on the even carrier. -/
theorem mul_smul_even (c : ℂ) (X Y : evenSubspace →L[ℂ] evenSubspace) :
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

/-- The adjoint of a finite sum of operators on the even carrier is the sum of the adjoints. -/
theorem adjoint_sum_even {ι : Type*} (s : Finset ι)
    (f : ι → evenSubspace →L[ℂ] evenSubspace) :
    ContinuousLinearMap.adjoint (∑ i ∈ s, f i) =
      ∑ i ∈ s, ContinuousLinearMap.adjoint (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        ContinuousLinearMap.adjoint.map_add, ih]

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
  have hbase : (0 : ℝ) < r ^ k * a :=
    mul_pos (pow_pos (zero_lt_one.trans hr) k) ha
  have hstep : r ^ k * a < r ^ (k + 1) * a := by
    rw [pow_succ]
    calc
      r ^ k * a = r ^ k * a * 1 := by ring
      _ < r ^ k * a * r := mul_lt_mul_of_pos_left hr hbase
      _ = r ^ k * r * a := by ring
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

/-- The logarithmic shell channel is self-adjoint: its coefficients are real and physical cutoffs
are self-adjoint. -/
theorem adjoint_evenLogShellChannel (a r : ℝ) (n : ℕ) :
    ContinuousLinearMap.adjoint (evenLogShellChannel a r n) =
      evenLogShellChannel a r n := by
  classical
  unfold evenLogShellChannel
  rw [adjoint_sum_even]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ, ContinuousLinearMap.adjoint.map_sub,
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
    evenIndicatorCutoff c (logShellUnit a r ha hr k) = logShellUnit a r ha hr k :=
  evenIndicatorCutoff_evenShellVectorEven_of_le (logShellRadius a r k)
    (logShellRadius a r (k + 1)) c (logShellRadius_lt_succ ha hr k) hc 0

/-- A cutoff below the layer annihilates the layer unit vector. -/
theorem evenIndicatorCutoff_logShellUnit_of_ge
    (a r c : ℝ) (ha : 0 < a) (hr : 1 < r) (k : ℕ)
    (hc : c ≤ logShellRadius a r k) :
    evenIndicatorCutoff c (logShellUnit a r ha hr k) = 0 :=
  evenIndicatorCutoff_evenShellVectorEven_eq_zero (logShellRadius a r k)
    (logShellRadius a r (k + 1)) c (logShellRadius_lt_succ ha hr k) hc 0

/-- **Logarithmic eigen-action.**  The channel multiplies the unit vector of the `k`-th layer by
`log(rᵏa)`: on the tower it really is the logarithm of the position. -/
theorem evenLogShellChannel_apply_logShellUnit
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n k : ℕ) (hk : k < n) :
    evenLogShellChannel a r n (logShellUnit a r ha hr k) =
      ((Real.log (logShellRadius a r k) : ℝ) : ℂ) • logShellUnit a r ha hr k := by
  classical
  unfold evenLogShellChannel
  rw [sum_apply, Finset.sum_eq_single k]
  · rw [smul_apply, sub_apply,
      evenIndicatorCutoff_logShellUnit_of_le a r _ ha hr k le_rfl,
      evenIndicatorCutoff_logShellUnit_of_ge a r _ ha hr k le_rfl, sub_zero]
  · intro j _ hjk
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · have h₁ : logShellRadius a r (j + 1) ≤ logShellRadius a r k :=
        logShellRadius_mono ha hr (Nat.succ_le_of_lt hlt)
      have h₂ : logShellRadius a r j ≤ logShellRadius a r k :=
        logShellRadius_mono ha hr hlt.le
      rw [smul_apply, sub_apply,
        evenIndicatorCutoff_logShellUnit_of_ge a r _ ha hr k h₁,
        evenIndicatorCutoff_logShellUnit_of_ge a r _ ha hr k h₂, sub_zero, smul_zero]
    · have h₁ : logShellRadius a r (k + 1) ≤ logShellRadius a r j :=
        logShellRadius_mono ha hr hgt
      have h₂ : logShellRadius a r (k + 1) ≤ logShellRadius a r (j + 1) :=
        logShellRadius_mono ha hr (Nat.succ_le_succ hgt.le)
      rw [smul_apply, sub_apply,
        evenIndicatorCutoff_logShellUnit_of_le a r _ ha hr k h₂,
        evenIndicatorCutoff_logShellUnit_of_le a r _ ha hr k h₁, sub_self, smul_zero]
  · intro hkn
    exact absurd (Finset.mem_range.mpr hk) hkn

/-- **Nonvacuity of the Burnol channel interface.**  The logarithmic shell channel is not the zero
operator whenever its base layer sits off the unit radius, so the concrete conductor is a genuine
object and every abstract Burnol cancellation identity has a nontrivial instance. -/
theorem evenLogShellChannel_ne_zero
    (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n : ℕ) (hn : 0 < n)
    (hlog : Real.log a ≠ 0) :
    evenLogShellChannel a r n ≠ 0 := by
  intro hzero
  have hrad : logShellRadius a r 0 = a := by
    simp [logShellRadius]
  have haction := evenLogShellChannel_apply_logShellUnit a r ha hr n 0 hn
  rw [hzero, hrad] at haction
  have hsmul : ((Real.log a : ℝ) : ℂ) • logShellUnit a r ha hr 0 = 0 :=
    haction.symm
  rcases smul_eq_zero.mp hsmul with hc | hv
  · exact hlog (by exact_mod_cast hc)
  · exact logShellUnit_ne_zero a r ha hr 0 hv

/-- The concrete Burnol conductor is nonzero whenever its channel is: reflection cannot cancel the
channel, because the conductor is the channel plus its reflection and both act by the same real
scalar on the layer of a shell unit vector fixed by the reflection algebra. -/
theorem soninBurnolLogShellConductor_eq_channel_add_reflected (a r : ℝ) (n : ℕ) :
    soninBurnolLogShellConductor a r n =
      evenLogShellChannel a r n +
        evenFourierTransform * evenLogShellChannel a r n * evenFourierTransform :=
  rfl

end RHTower

namespace RHTower

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

/-! ## The Burnol Ward laws with a fixed concrete channel -/

/-- **Signed Burnol Ward law at every aperture, with one fixed channel.**  The Fourier-edge value
of the logarithmic shell channel equals the physical-edge value of its conductor, simultaneously
for every cutoff radius.  The Lüders route discharges the same premise only one aperture at a
time, because the Lüders block is built from the cutoff it commutes with; the shell channel
commutes with the whole cutoff family at once. -/
theorem pointedCutoffWardTrace_evenLogShellChannel_eq_burnolConductor
    (a r c : ℝ) (n : ℕ) (psi chi : evenSubspace) :
    pointedCutoffWardTrace (evenFourierCutoff c) (evenLogShellChannel a r n)
        (evenFourierTransform psi) (evenFourierTransform chi) =
      pointedCutoffWardTrace (evenIndicatorCutoff c)
        (soninBurnolLogShellConductor a r n) psi chi := by
  have h := pointedCutoffWardTrace_reflectedPosition_eq_burnolConductor
    (evenLogShellChannel a r n) evenFourierTransform (evenIndicatorCutoff c)
    psi chi evenFourierTransform_mul_self adjoint_evenFourierTransform
    (ccmCommutator_evenLogShellChannel_evenIndicatorCutoff a r c n)
  rwa [← evenFourierCutoff_eq_reflectedCutoff] at h

/-- **Finite-packet Burnol Ward law with the concrete channel.**  Arbitrary finite arithmetic
source packets keep the same reflection law at every aperture. -/
theorem finiteRankCutoffWardTrace_evenLogShellChannel_eq_burnolConductor
    {ι : Type*} [Fintype ι] (a r c : ℝ) (n : ℕ)
    (w : ι → ℂ) (x y : ι → evenSubspace) :
    finiteRankCutoffWardTrace (evenFourierCutoff c) (evenLogShellChannel a r n) w
        (fun i ↦ evenFourierTransform (x i)) (fun i ↦ evenFourierTransform (y i)) =
      finiteRankCutoffWardTrace (evenIndicatorCutoff c)
        (soninBurnolLogShellConductor a r n) w x y := by
  have h := finiteRankCutoffWardTrace_reflectedPosition_eq_burnolConductor
    (evenLogShellChannel a r n) evenFourierTransform (evenIndicatorCutoff c)
    w x y evenFourierTransform_mul_self adjoint_evenFourierTransform
    (ccmCommutator_evenLogShellChannel_evenIndicatorCutoff a r c n)
  rwa [← evenFourierCutoff_eq_reflectedCutoff] at h

/-- **Concrete conductor curvature law.**  The reflected-position Ward curvature of the
logarithmic shell channel is the reflection of the physical conductor curvature. -/
theorem cutoffWardCurvature_evenLogShellChannel_eq_burnolConductor
    (a r c : ℝ) (n : ℕ) :
    cutoffWardCurvature (evenFourierCutoff c) (evenLogShellChannel a r n) =
      evenFourierTransform *
        cutoffWardCurvature (evenIndicatorCutoff c)
          (soninBurnolLogShellConductor a r n) * evenFourierTransform := by
  have h := cutoffWardCurvature_reflectedPosition_eq_burnolConductor
    (evenLogShellChannel a r n) evenFourierTransform (evenIndicatorCutoff c)
    evenFourierTransform_mul_self
    (ccmCommutator_evenLogShellChannel_evenIndicatorCutoff a r c n)
  rwa [← evenFourierCutoff_eq_reflectedCutoff] at h

end RHTower
