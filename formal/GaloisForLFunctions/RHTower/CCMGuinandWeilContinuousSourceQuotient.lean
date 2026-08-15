/-
# Continuous Guinand--Weil source quotient

The physical event horizon is the compact interval `[0,1]`.  A continuous source is represented by
a continuous linear functional on `C([0,1], R)`, which includes finite Borel measures by
integration and signed finite measures by linear combination.  The full finite source observer
reads the weighted-horizon, sine, and weighted-cosine coordinate functions from this functional.

For every such source, not only for finite atomic packets, this file proves that the `2N+1`
coordinates vanish exactly when the entire finite CCM divided-difference packet vanishes.  It also
constructs the integration functional of a finite measure and proves that finite atomic functionals
specialize exactly to the earlier atomic observer and event-packet matrix.  Thus continuous pole and
archimedean measures belong to the same exact source quotient; their arithmetic identification and
canonical pre-quotient transport remain separate tasks.
-/
import GaloisForLFunctions.RHTower.CCMGuinandWeilPositiveSourceNonselection
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

noncomputable section

open scoped BigOperators

namespace RHTower

open Matrix MeasureTheory Set

/-- Compact physical horizon for the finite Guinand--Weil event dictionary. -/
abbrev CCMGuinandWeilHorizon := Set.Icc (0 : ℝ) 1

/-- Source-native continuous dual. Finite signed Borel measures act here by integration. -/
abbrev CCMGuinandWeilContinuousSource := C(CCMGuinandWeilHorizon, ℝ) →L[ℝ] ℝ

/-- Central weighted-horizon coordinate function. -/
def ccmGuinandWeilHorizonCoordinate : C(CCMGuinandWeilHorizon, ℝ) :=
  ⟨fun omega => omega.1, continuous_subtype_val⟩

/-- Sine coordinate function at an integral Fourier mode. -/
def ccmGuinandWeilSineCoordinate (n : ℤ) : C(CCMGuinandWeilHorizon, ℝ) := by
  refine ⟨fun omega => Real.sin (2 * Real.pi * omega.1 * (n : ℝ)), ?_⟩
  fun_prop

/-- Weighted-cosine coordinate function at an integral Fourier mode. -/
def ccmGuinandWeilWeightedCosineCoordinate (n : ℤ) :
    C(CCMGuinandWeilHorizon, ℝ) := by
  refine ⟨fun omega => omega.1 * Real.cos (2 * Real.pi * omega.1 * (n : ℝ)), ?_⟩
  fun_prop

@[simp] theorem ccmGuinandWeilSineCoordinate_zero :
    ccmGuinandWeilSineCoordinate 0 = 0 := by
  ext omega
  simp [ccmGuinandWeilSineCoordinate]

@[simp] theorem ccmGuinandWeilWeightedCosineCoordinate_zero :
    ccmGuinandWeilWeightedCosineCoordinate 0 = ccmGuinandWeilHorizonCoordinate := by
  ext omega
  simp [ccmGuinandWeilWeightedCosineCoordinate, ccmGuinandWeilHorizonCoordinate]

/-- The exact `2N+1` reporter applied to an arbitrary continuous source functional. -/
def ccmGuinandWeilContinuousSourceCoordinateObserver (N : ℕ)
    (source : CCMGuinandWeilContinuousSource) : CCMGuinandWeilSourceCoordinates N :=
  (source ccmGuinandWeilHorizonCoordinate,
    (fun k => source
      (ccmGuinandWeilSineCoordinate ((Fin.succ k).val : ℤ))),
    fun k => source
      (ccmGuinandWeilWeightedCosineCoordinate ((Fin.succ k).val : ℤ)))

/-- Odd source value obtained from a continuous source functional. -/
def ccmGuinandWeilContinuousSourceValue
    (source : CCMGuinandWeilContinuousSource) (n : ℤ) : ℝ :=
  source (ccmGuinandWeilSineCoordinate n) / Real.pi

/-- Diagonal source value obtained from a continuous source functional. -/
def ccmGuinandWeilContinuousDiagonalValue
    (source : CCMGuinandWeilContinuousSource) (n : ℤ) : ℝ :=
  2 * source (ccmGuinandWeilWeightedCosineCoordinate n)

/-- Whole finite CCM matrix produced by an arbitrary continuous source functional. -/
def ccmGuinandWeilContinuousSourcePacketMatrix (N : ℕ)
    (source : CCMGuinandWeilContinuousSource) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  ccmDividedDifferenceMatrix
    (fun j : Fin (N + 1) => (j.val : ℝ))
    (fun j => ccmGuinandWeilContinuousSourceValue source (j.val : ℤ))
    (fun j => ccmGuinandWeilContinuousDiagonalValue source (j.val : ℤ))

/-- Vanishing of all continuous-source coordinates forces every entry of the whole finite packet
to vanish. -/
theorem ccmGuinandWeilContinuousSourceCoordinateObserver_zero_implies_packet_zero
    {N : ℕ} (source : CCMGuinandWeilContinuousSource)
    (hobserver : ccmGuinandWeilContinuousSourceCoordinateObserver N source = 0) :
    ccmGuinandWeilContinuousSourcePacketMatrix N source = 0 := by
  have hcentral : source ccmGuinandWeilHorizonCoordinate = 0 := by
    have h := congrArg Prod.fst hobserver
    simpa [ccmGuinandWeilContinuousSourceCoordinateObserver] using h
  have hsine : ∀ k : Fin N,
      source (ccmGuinandWeilSineCoordinate ((Fin.succ k).val : ℤ)) = 0 := by
    intro k
    have h := congr_fun (congrArg (fun x => x.2.1) hobserver) k
    simpa [ccmGuinandWeilContinuousSourceCoordinateObserver] using h
  have hcosine : ∀ k : Fin N,
      source (ccmGuinandWeilWeightedCosineCoordinate ((Fin.succ k).val : ℤ)) = 0 := by
    intro k
    have h := congr_fun (congrArg (fun x => x.2.2) hobserver) k
    simpa [ccmGuinandWeilContinuousSourceCoordinateObserver] using h
  have hsource : ∀ j : Fin (N + 1),
      source (ccmGuinandWeilSineCoordinate (j.val : ℤ)) = 0 := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · exact hsine k
  have hdiagonal : ∀ j : Fin (N + 1),
      source (ccmGuinandWeilWeightedCosineCoordinate (j.val : ℤ)) = 0 := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa using hcentral
    · exact hcosine k
  ext i j
  by_cases hij : i = j
  · subst j
    simp [ccmGuinandWeilContinuousSourcePacketMatrix, ccmDividedDifferenceMatrix,
      ccmGuinandWeilContinuousDiagonalValue, hdiagonal]
  · simp [ccmGuinandWeilContinuousSourcePacketMatrix, ccmDividedDifferenceMatrix, hij,
      ccmGuinandWeilContinuousSourceValue, hsource]

/-- Conversely, zero edge and diagonal entries recover all `2N+1` continuous-source coordinates. -/
theorem ccmGuinandWeilContinuousSourcePacketMatrix_zero_implies_observer_zero
    {N : ℕ} (source : CCMGuinandWeilContinuousSource)
    (hpacket : ccmGuinandWeilContinuousSourcePacketMatrix N source = 0) :
    ccmGuinandWeilContinuousSourceCoordinateObserver N source = 0 := by
  apply Prod.ext
  · have h := congr_fun (congr_fun hpacket 0) 0
    change ccmGuinandWeilContinuousSourcePacketMatrix N source 0 0 = 0 at h
    simp [ccmGuinandWeilContinuousSourcePacketMatrix, ccmDividedDifferenceMatrix,
      ccmGuinandWeilContinuousDiagonalValue] at h
    simpa [ccmGuinandWeilContinuousSourceCoordinateObserver] using h
  · apply Prod.ext
    · apply _root_.funext
      intro k
      have h := congr_fun (congr_fun hpacket (Fin.succ k)) 0
      change ccmGuinandWeilContinuousSourcePacketMatrix N source (Fin.succ k) 0 = 0 at h
      rw [ccmGuinandWeilContinuousSourcePacketMatrix] at h
      simp only [ccmDividedDifferenceMatrix, Fin.succ_ne_zero, if_false,
        ccmGuinandWeilContinuousSourceValue, Fin.val_zero,
        ccmGuinandWeilSineCoordinate_zero, map_zero, zero_div, sub_zero,
        Nat.cast_zero] at h
      have hdenom : (((Fin.succ k).val : ℕ) : ℝ) ≠ 0 := by
        simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
        positivity
      have hinner := (div_eq_zero_iff.mp h).resolve_right hdenom
      have hnumerator :=
        (div_eq_zero_iff.mp hinner).resolve_right Real.pi_ne_zero
      simpa [ccmGuinandWeilContinuousSourceCoordinateObserver] using hnumerator
    · apply _root_.funext
      intro k
      have h := congr_fun (congr_fun hpacket (Fin.succ k)) (Fin.succ k)
      change ccmGuinandWeilContinuousSourcePacketMatrix N source
        (Fin.succ k) (Fin.succ k) = 0 at h
      simp [ccmGuinandWeilContinuousSourcePacketMatrix, ccmDividedDifferenceMatrix,
        ccmGuinandWeilContinuousDiagonalValue] at h
      simpa [ccmGuinandWeilContinuousSourceCoordinateObserver] using h

/-- **Exact continuous source quotient.** For every continuous source functional, its full finite
coordinate vector vanishes exactly when its whole CCM packet does. -/
theorem ccmGuinandWeilContinuousSourceCoordinateObserver_zero_iff_packet_zero
    {N : ℕ} (source : CCMGuinandWeilContinuousSource) :
    ccmGuinandWeilContinuousSourceCoordinateObserver N source = 0 ↔
      ccmGuinandWeilContinuousSourcePacketMatrix N source = 0 :=
  ⟨ccmGuinandWeilContinuousSourceCoordinateObserver_zero_implies_packet_zero source,
    ccmGuinandWeilContinuousSourcePacketMatrix_zero_implies_observer_zero source⟩

/-- Integration embeds every finite Borel measure on the physical horizon into the continuous
source dual. -/
def ccmGuinandWeilFiniteMeasureSourceFunctional
    (mu : Measure CCMGuinandWeilHorizon) [IsFiniteMeasure mu] :
    CCMGuinandWeilContinuousSource :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ omega, f omega ∂mu
      map_add' := by
        intro f g
        change (∫ omega, f omega + g omega ∂mu) =
          (∫ omega, f omega ∂mu) + ∫ omega, g omega ∂mu
        rw [integral_add]
        · exact (ContinuousMap.equivBoundedOfCompact CCMGuinandWeilHorizon ℝ f).integrable mu
        · exact (ContinuousMap.equivBoundedOfCompact CCMGuinandWeilHorizon ℝ g).integrable mu
      map_smul' := by
        intro c f
        simpa using integral_smul c (fun omega => f omega) }
    (mu.real Set.univ)
    (fun f => by
      have hbound := norm_integral_le_of_norm_le_const (μ := mu) (C := ‖f‖)
        (Filter.Eventually.of_forall fun omega => f.norm_coe_le_norm omega)
      simpa [mul_comm] using hbound)

@[simp] theorem ccmGuinandWeilFiniteMeasureSourceFunctional_apply
    (mu : Measure CCMGuinandWeilHorizon) [IsFiniteMeasure mu]
    (f : C(CCMGuinandWeilHorizon, ℝ)) :
    ccmGuinandWeilFiniteMeasureSourceFunctional mu f =
      ∫ omega, f omega ∂mu := rfl

/-- On a finite measure, the abstract reporter is literally Groskin's moment vector. -/
theorem ccmGuinandWeilFiniteMeasureSourceCoordinateObserver_eq
    (N : ℕ) (mu : Measure CCMGuinandWeilHorizon) [IsFiniteMeasure mu] :
    ccmGuinandWeilContinuousSourceCoordinateObserver N
        (ccmGuinandWeilFiniteMeasureSourceFunctional mu) =
      (∫ omega, (omega.1 : ℝ) ∂mu,
        (fun k => ∫ omega,
          Real.sin (2 * Real.pi * omega.1 * (((Fin.succ k).val : ℕ) : ℝ)) ∂mu),
        fun k => ∫ omega,
          omega.1 * Real.cos
            (2 * Real.pi * omega.1 * (((Fin.succ k).val : ℕ) : ℝ)) ∂mu) := by
  rfl

/-- Finite atomic source as a continuous functional, using evaluation on the physical horizon. -/
def ccmGuinandWeilAtomicSourceFunctional {R : ℕ}
    (weight : Fin R → ℝ) (horizon : Fin R → CCMGuinandWeilHorizon) :
    CCMGuinandWeilContinuousSource :=
  ∑ i, weight i • ContinuousMap.evalCLM ℝ (horizon i)

@[simp] theorem ccmGuinandWeilAtomicSourceFunctional_apply {R : ℕ}
    (weight : Fin R → ℝ) (horizon : Fin R → CCMGuinandWeilHorizon)
    (f : C(CCMGuinandWeilHorizon, ℝ)) :
    ccmGuinandWeilAtomicSourceFunctional weight horizon f =
      ∑ i, weight i * f (horizon i) := by
  simp [ccmGuinandWeilAtomicSourceFunctional]

/-- The continuous observer specializes exactly to the earlier finite atomic observer. -/
theorem ccmGuinandWeilAtomicSourceCoordinateObserver_eq {N R : ℕ}
    (weight : Fin R → ℝ) (horizon : Fin R → CCMGuinandWeilHorizon) :
    ccmGuinandWeilContinuousSourceCoordinateObserver N
        (ccmGuinandWeilAtomicSourceFunctional weight horizon) =
      ccmGuinandWeilFiniteSourceCoordinateObserver (N := N)
        (fun i => (horizon i).1) weight := by
  apply Prod.ext
  · simp [ccmGuinandWeilContinuousSourceCoordinateObserver,
      ccmGuinandWeilHorizonCoordinate,
      ccmGuinandWeilFiniteSourceCoordinateObserver]
  · apply Prod.ext <;> apply _root_.funext <;> intro k
    · simp [ccmGuinandWeilContinuousSourceCoordinateObserver,
        ccmGuinandWeilSineCoordinate,
        ccmGuinandWeilFiniteSourceCoordinateObserver, Fin.val_succ]
      apply Finset.sum_congr rfl
      intro i _
      ring_nf
    · simp [ccmGuinandWeilContinuousSourceCoordinateObserver,
        ccmGuinandWeilWeightedCosineCoordinate,
        ccmGuinandWeilFiniteSourceCoordinateObserver, Fin.val_succ]
      apply Finset.sum_congr rfl
      intro i _
      ring_nf

/-- Atomic continuous-source values are the weighted sums of literal event-source values. -/
theorem ccmGuinandWeilAtomicSourceValue_eq {R : ℕ}
    (weight : Fin R → ℝ) (horizon : Fin R → CCMGuinandWeilHorizon) (n : ℤ) :
    ccmGuinandWeilContinuousSourceValue
        (ccmGuinandWeilAtomicSourceFunctional weight horizon) n =
      ∑ i, weight i * ccmGuinandWeilEventSource (horizon i).1 n := by
  simp [ccmGuinandWeilContinuousSourceValue, ccmGuinandWeilSineCoordinate,
    ccmGuinandWeilEventSource]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Atomic continuous-source diagonals are weighted sums of literal event diagonals. -/
theorem ccmGuinandWeilAtomicDiagonalValue_eq {R : ℕ}
    (weight : Fin R → ℝ) (horizon : Fin R → CCMGuinandWeilHorizon) (n : ℤ) :
    ccmGuinandWeilContinuousDiagonalValue
        (ccmGuinandWeilAtomicSourceFunctional weight horizon) n =
      ∑ i, weight i * ccmGuinandWeilEventDiagonal (horizon i).1 n := by
  simp [ccmGuinandWeilContinuousDiagonalValue,
    ccmGuinandWeilWeightedCosineCoordinate,
    ccmGuinandWeilEventDiagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The whole continuous-source packet specializes exactly to the earlier finite atomic event
packet, not merely to an equal coordinate vector. -/
theorem ccmGuinandWeilAtomicSourcePacketMatrix_eq {N R : ℕ}
    (weight : Fin R → ℝ) (horizon : Fin R → CCMGuinandWeilHorizon) :
    ccmGuinandWeilContinuousSourcePacketMatrix N
        (ccmGuinandWeilAtomicSourceFunctional weight horizon) =
      ccmGuinandWeilFiniteEventPacketMatrix (N := N) weight
        (fun i => (horizon i).1) := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [ccmGuinandWeilContinuousSourcePacketMatrix]
    simp only [ccmDividedDifferenceMatrix]
    rw [ccmGuinandWeilAtomicDiagonalValue_eq]
    rw [ccmGuinandWeilFiniteEventPacketMatrix, Matrix.sum_apply]
    simp [ccmGuinandWeilEventMatrix, ccmDividedDifferenceMatrix]
  · rw [ccmGuinandWeilContinuousSourcePacketMatrix]
    simp only [ccmDividedDifferenceMatrix, hij, if_false]
    rw [ccmGuinandWeilAtomicSourceValue_eq, ccmGuinandWeilAtomicSourceValue_eq]
    rw [ccmGuinandWeilFiniteEventPacketMatrix, Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul,
      ccmGuinandWeilEventMatrix, ccmDividedDifferenceMatrix, hij, if_false]
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    push_cast
    ring

end RHTower
