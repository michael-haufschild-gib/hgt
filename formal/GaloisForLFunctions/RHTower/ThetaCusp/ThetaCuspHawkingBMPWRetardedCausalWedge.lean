import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularCausalPeierlsPairing

/-!
# PW-B literal retarded response: finite-time causal wedge

The original two-event CTP is the skew pairing of two retarded full-circle
responses. The physical onset and both direct/image gates force each response
to have compact radial support at every finite receiver time. This removes a
spatial-infinity face from a finite-time Green-current construction. The
remaining top-time cap, native bulk, and optical extinction are not asserted.
-/

open MeasureTheory Set
namespace RHTower.D4BMFullAngularCausalPeierls
open D4BMJointSource D4BMFullAngularReconstruction D4BMModularCore
open D4BMLiteralCyclicPeierls
noncomputable section
set_option autoImplicit false

private theorem retarded_density_zero_wedge (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (τ x X k : ℝ) (p : Event)
    (hp : 0 < p.1 ∧ p.2 < 0) (hx : x < -τ) :
    angularDirichletKernel q branch (τ-p.1) x p.2 X k *
      timeReducedCoefficient (physicalRate q b) a p.1 p.2 = 0 := by
  by_cases hs : p.1+p.2 < 0
  · rw [timeReducedCoefficient_zero_before_onset _ _ _ _ hs, mul_zero]
  · have hs' : 0 ≤ p.1+p.2 := le_of_not_gt hs
    have hd : ¬ |x-p.2| ≤ τ-p.1 := by
      intro h
      have hlow := (abs_le.mp h).1
      linarith
    have hi : ¬ |x+p.2| ≤ τ-p.1 := by
      intro h
      have hlow := (abs_le.mp h).1
      linarith
    simp [angularDirichletKernel, hd, hi]

theorem fullRetardedResponse_zero_outside_wedge (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (τ x X k : ℝ) (hx : x < -τ) :
    fullRetardedResponse q branch b a τ x X k = 0 := by
  have he1 : ∀ᵐ p : Event ∂eventMeasure, 0 < p.1 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((isOpen_lt continuous_const continuous_fst).measurableSet :
        MeasurableSet {p : Event | 0 < p.1})).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ae_of_all _ (fun _ => ht)
  have he2 : ∀ᵐ p : Event ∂eventMeasure, p.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((isOpen_lt continuous_snd continuous_const).measurableSet :
        MeasurableSet {p : Event | p.2 < 0})).mpr
    exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Iio)
  unfold fullRetardedResponse
  apply integral_eq_zero_of_ae
  filter_upwards [he1, he2] with p hp1 hp2
  change angularDirichletKernel q branch (τ-p.1) x p.2 X k *
    timeReducedCoefficient (physicalRate q b) a p.1 p.2 = 0
  exact retarded_density_zero_wedge q branch b a τ x X k p ⟨hp1,hp2⟩ hx

private theorem retarded_inner (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) (r : Event) :
    (∫ p, fullSourcePairDensity q branch b c a d X k (p,r) ∂eventMeasure) =
      fullRetardedResponse q branch b a r.1 r.2 X k *
        timeReducedCoefficient (physicalRate q c) d r.1 r.2 := by
  rw [fullRetardedResponse, ← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by
    change timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      angularDirichletKernel q branch (r.1-p.1) p.2 r.2 X k *
        timeReducedCoefficient (physicalRate q c) d r.1 r.2 =
      (angularDirichletKernel q branch (r.1-p.1) r.2 p.2 X k *
        timeReducedCoefficient (physicalRate q b) a p.1 p.2) *
        timeReducedCoefficient (physicalRate q c) d r.1 r.2
    rw [angularDirichletKernel_cyclic q branch (r.1-p.1) p.2 r.2 X k]
    ring)

theorem fullCausalSourcePair_eq_retarded_skew (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    fullCausalSourcePair q branch b c a d X k =
      (∫ p : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
          fullRetardedResponse q branch c d p.1 p.2 X k ∂eventMeasure) -
        ∫ p : Event, timeReducedCoefficient (physicalRate q c) d p.1 p.2 *
          fullRetardedResponse q branch b a p.1 p.2 X k ∂eventMeasure := by
  rw [fullCausalSourcePair_decomposition]
  rw [integral_prod_symm _ (fullSourcePairDensity_integrable q branch c b d a X k),
    integral_prod_symm _ (fullSourcePairDensity_integrable q branch b c a d X k)]
  simp only [retarded_inner]
  congr 1 <;> apply integral_congr_ae <;>
    exact ae_of_all _ (fun p => by ring)

private theorem kernel_negative (q : XiZeroCopy) (branch : Bool)
    (h x y X k : ℝ) (hh : h < 0) :
    angularDirichletKernel q branch h x y X k = 0 := by
  have h1 : ¬ |x-y| ≤ h := not_le.mpr ((abs_nonneg _).trans_lt' hh)
  have h2 : ¬ |x+y| ≤ h := not_le.mpr ((abs_nonneg _).trans_lt' hh)
  simp [angularDirichletKernel, h1, h2]

theorem fullRetardedResponse_zero_nonpositive_time (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (τ x X k : ℝ) (hτ : τ ≤ 0) :
    fullRetardedResponse q branch b a τ x X k = 0 := by
  have he : ∀ᵐ p : Event ∂eventMeasure, 0 < p.1 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((isOpen_lt continuous_const continuous_fst).measurableSet :
        MeasurableSet {p : Event | 0 < p.1})).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ae_of_all _ (fun _ => ht)
  unfold fullRetardedResponse
  apply integral_eq_zero_of_ae
  filter_upwards [he] with p hp
  change angularDirichletKernel q branch (τ-p.1) x p.2 X k *
    timeReducedCoefficient (physicalRate q b) a p.1 p.2 = 0
  rw [kernel_negative q branch _ _ _ _ _ (by linarith), zero_mul]

theorem angularDirichletKernel_zero_wall (q : XiZeroCopy)
    (branch : Bool) (h y X k : ℝ) :
    angularDirichletKernel q branch h 0 y X k = 0 := by
  simp [angularDirichletKernel, D4BMCausalKernel.invariant, Real.cosh_neg]

theorem fullRetardedResponse_zero_wall (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (τ X k : ℝ) :
    fullRetardedResponse q branch b a τ 0 X k = 0 := by
  unfold fullRetardedResponse
  apply integral_eq_zero_of_ae
  exact ae_of_all _ (fun p => by
    change angularDirichletKernel q branch (τ-p.1) 0 p.2 X k *
      timeReducedCoefficient (physicalRate q b) a p.1 p.2 = 0
    rw [angularDirichletKernel_zero_wall, zero_mul])

/-- Zero extension of the literal retarded response to the radial real line. -/
def physicalRetardedSlice (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (τ X k : ℝ) (x : ℝ) : ℂ :=
  if x < 0 then fullRetardedResponse q branch b a τ x X k else 0

/-- At every finite receiver time, the physical retarded response has no radial
tail: its support lies in the causal triangle `-max τ 0 ≤ x ≤ 0`. -/
theorem physicalRetardedSlice_compact (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (τ X k : ℝ) :
    HasCompactSupport (physicalRetardedSlice q branch b a τ X k) := by
  apply HasCompactSupport.intro (K := Icc (-max τ 0) 0) isCompact_Icc
  intro x hx
  by_cases hx0 : x < 0
  · have hleft : x < -max τ 0 := lt_of_not_ge (fun h => hx ⟨h, hx0.le⟩)
    by_cases hτ : τ ≤ 0
    · rw [physicalRetardedSlice, if_pos hx0,
        fullRetardedResponse_zero_nonpositive_time q branch b a τ x X k hτ]
    · have ht : 0 < τ := lt_of_not_ge hτ
      have hmax : max τ 0 = τ := max_eq_left ht.le
      rw [hmax] at hleft
      rw [physicalRetardedSlice, if_pos hx0,
        fullRetardedResponse_zero_outside_wedge q branch b a τ x X k hleft]
  · simp [physicalRetardedSlice, hx0]

end
end RHTower.D4BMFullAngularCausalPeierls
