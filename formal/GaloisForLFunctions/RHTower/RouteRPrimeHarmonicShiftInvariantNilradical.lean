import GaloisForLFunctions.RHTower.RouteRPrimeHarmonicSummableCorona
import GaloisForLFunctions.HTGeometry.DifferenceSigmaSimple

open GaloisForLFunctions.HTGeometry
open scoped BoundedContinuousFunction BigOperators

namespace RHTower

noncomputable section

/-- Delete the head of a bounded tail. -/
def routeRBoundedTailShiftHom :
    RouteRBoundedTraceSequence →+* RouteRBoundedTraceSequence where
  toFun a := a.compContinuous
    ⟨Nat.succ, continuous_of_discreteTopology⟩
  map_one' := by ext n; rfl
  map_mul' a b := by ext n; rfl
  map_zero' := by ext n; rfl
  map_add' a b := by ext n; rfl

@[simp] theorem routeRBoundedTailShiftHom_apply
    (a : RouteRBoundedTraceSequence) (n : ℕ) :
    routeRBoundedTailShiftHom a n = a (n + 1) := rfl

/-- Duplicate the head.  This supplies representatives for inverse cofinal shift. -/
def routeRBoundedTailDuplicateHead
    (a : RouteRBoundedTraceSequence) : RouteRBoundedTraceSequence :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun n : ℕ => a n.pred) continuous_of_discreteTopology ‖a‖
      (fun n => a.norm_coe_le_norm n.pred)

@[simp] theorem routeRBoundedTailDuplicateHead_apply
    (a : RouteRBoundedTraceSequence) (n : ℕ) :
    routeRBoundedTailDuplicateHead a n = a n.pred := rfl

theorem routeRBoundedTailShiftHom_mem_summableIdeal
    {a : RouteRBoundedTraceSequence}
    (ha : a ∈ routeRSummableBoundedTailIdeal) :
    routeRBoundedTailShiftHom a ∈ routeRSummableBoundedTailIdeal := by
  change Summable (fun n => ‖a n‖) at ha
  change Summable (fun n => ‖a (n + 1)‖)
  exact (summable_nat_add_iff 1).2 ha

/-- Cofinal shift on bounded tails modulo absolutely summable changes. -/
def routeRSummableHadamardShiftHom :
    RouteRSummableHadamardCorona →+* RouteRSummableHadamardCorona :=
  Ideal.Quotient.lift routeRSummableBoundedTailIdeal
    ((Ideal.Quotient.mk routeRSummableBoundedTailIdeal).comp
      routeRBoundedTailShiftHom)
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      (routeRBoundedTailShiftHom_mem_summableIdeal ha))

@[simp] theorem routeRSummableHadamardShiftHom_mk
    (a : RouteRBoundedTraceSequence) :
    routeRSummableHadamardShiftHom
        (Ideal.Quotient.mk routeRSummableBoundedTailIdeal a) =
      Ideal.Quotient.mk routeRSummableBoundedTailIdeal
        (routeRBoundedTailShiftHom a) := by
  simp [routeRSummableHadamardShiftHom]

theorem routeRBoundedTailShift_duplicateHead
    (a : RouteRBoundedTraceSequence) :
    routeRBoundedTailShiftHom (routeRBoundedTailDuplicateHead a) = a := by
  ext n
  simp

/-- Cofinal deletion is an automorphism after absolutely summable tails are erased. -/
def routeRSummableHadamardShiftEquiv :
    RouteRSummableHadamardCorona ≃+* RouteRSummableHadamardCorona :=
  RingEquiv.ofBijective routeRSummableHadamardShiftHom
    ⟨by
      intro x y h
      induction x using Quotient.inductionOn' with
      | _ a =>
        induction y using Quotient.inductionOn' with
        | _ b =>
          change routeRSummableHadamardShiftHom
              (Ideal.Quotient.mk routeRSummableBoundedTailIdeal a) =
            routeRSummableHadamardShiftHom
              (Ideal.Quotient.mk routeRSummableBoundedTailIdeal b) at h
          rw [routeRSummableHadamardShiftHom_mk,
            routeRSummableHadamardShiftHom_mk] at h
          change Ideal.Quotient.mk routeRSummableBoundedTailIdeal a =
            Ideal.Quotient.mk routeRSummableBoundedTailIdeal b
          apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
          change Summable (fun n => ‖a n - b n‖)
          apply (summable_nat_add_iff 1).1
          have hmem : routeRBoundedTailShiftHom a -
              routeRBoundedTailShiftHom b ∈ routeRSummableBoundedTailIdeal :=
            (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 (by
              exact h)
          change Summable (fun n =>
            ‖routeRBoundedTailShiftHom a n -
              routeRBoundedTailShiftHom b n‖) at hmem
          simpa using hmem,
      by
        intro y
        induction y using Quotient.inductionOn' with
        | _ a =>
          change ∃ x, routeRSummableHadamardShiftHom x =
            Ideal.Quotient.mk routeRSummableBoundedTailIdeal a
          refine ⟨Ideal.Quotient.mk routeRSummableBoundedTailIdeal
              (routeRBoundedTailDuplicateHead a), ?_⟩
          rw [routeRSummableHadamardShiftHom_mk,
            routeRBoundedTailShift_duplicateHead]⟩

/-- Successive differences of the enumerated prime reciprocals have finite total variation. -/
theorem summable_norm_routeRPrimeHarmonicTraceSequence_shift_sub :
    Summable (fun n =>
      ‖routeRPrimeHarmonicTraceSequence (n + 1) -
        routeRPrimeHarmonicTraceSequence n‖) := by
  let q : ℕ → ℝ := fun n => ((nthPrimeSubtype n : ℕ) : ℝ)⁻¹
  have hnonneg : ∀ n, 0 ≤ q n - q (n + 1) := by
    intro n
    dsimp [q]
    apply sub_nonneg.mpr
    apply inv_anti₀ (nthPrimeSubtype_pos n)
    exact_mod_cast nthPrimeSubtype_strictMono.monotone (Nat.le_succ n)
  have hsum : Summable (fun n => q n - q (n + 1)) := by
    apply summable_of_sum_range_le hnonneg
    intro N
    rw [Finset.sum_range_sub']
    exact sub_le_self _ (by positivity)
  refine hsum.congr fun n => ?_
  have heq (k : ℕ) : routeRPrimeHarmonicTraceSequence k = (q k : ℂ) := by
    simp [routeRPrimeHarmonicTraceSequence, q, nthPrimeEquiv,
      Complex.ofReal_inv]
  rw [heq n, heq (n + 1), ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (hnonneg n)]

/-- Prime-harmonic defect is stationary under cofinal prime-tail translation. -/
theorem routeRPrimeHarmonicSummableHadamardClass_shift_fixed :
    routeRSummableHadamardShiftEquiv
        (routeRSummableHadamardClass
          routeRPrimeHarmonicBoundedTraceSequence) =
      routeRSummableHadamardClass
        routeRPrimeHarmonicBoundedTraceSequence := by
  change routeRSummableHadamardShiftHom
      (Ideal.Quotient.mk routeRSummableBoundedTailIdeal
        routeRPrimeHarmonicBoundedTraceSequence) =
    Ideal.Quotient.mk routeRSummableBoundedTailIdeal
      routeRPrimeHarmonicBoundedTraceSequence
  rw [routeRSummableHadamardShiftHom_mk]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
  change Summable (fun n =>
    ‖routeRPrimeHarmonicTraceSequence (n + 1) -
      routeRPrimeHarmonicTraceSequence n‖)
  exact summable_norm_routeRPrimeHarmonicTraceSequence_shift_sub

/-- The stationary harmonic defect makes the summable corona dynamically non-simple. -/
theorem not_isSigmaSimple_routeRSummableHadamardShift :
    ¬ IsSigmaSimple routeRSummableHadamardShiftEquiv := by
  intro hsigma
  let h := routeRSummableHadamardClass
    routeRPrimeHarmonicBoundedTraceSequence
  have hhne : h ≠ 0 := routeRPrimeHarmonicSummableHadamardClass_ne_zero
  letI : Nontrivial RouteRSummableHadamardCorona :=
    ⟨⟨h, 0, hhne⟩⟩
  have hred : IsReduced RouteRSummableHadamardCorona :=
    isReduced_of_isSigmaSimple hsigma
  exact hhne ((show IsNilpotent h from
    ⟨2, routeRPrimeHarmonicSummableHadamardClass_sq_zero⟩).eq_zero)

end

end RHTower
