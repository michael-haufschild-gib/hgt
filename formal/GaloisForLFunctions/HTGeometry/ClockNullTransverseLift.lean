import GaloisForLFunctions.HTGeometry.ClockTrivariateC1
import GaloisForLFunctions.HTGeometry.ClockSlabProbe

/-!
# Fields depending on the two null coordinates and one transverse coordinate

A field on Minkowski space of dimension `n + 3` that depends on `ξ = x⁰ + x¹`, `η = x⁰ - x¹` and on
the single transverse coordinate `x²` has

`□ u = -2 (∂η∂ξ u + ∂ξ∂η u) + ∂₂∂₂ u`,

since the two pure null terms cancel between the timelike and the first spacelike direction exactly
as on a slab, the transverse coordinate `x²` contributes its own second derivative, and the
remaining directions contribute nothing.

So a field solving the characteristic equation `∂ξ∂η u = (∂₂∂₂ u + V u)/4` is a clock probe for the
potential `V`, and the potential may now depend on all three coordinates. This is the geometric half
of the statement; the analytic half is the solvability of that characteristic equation.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {n : ℕ}

/-! ## The three distinguished coordinate directions -/

theorem nullTrans_val_two (n : ℕ) : ((2 : Fin (n + 3)) : ℕ) = 2 := by
  simp [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]

theorem nullTrans_zero_ne_one (n : ℕ) : (0 : Fin (n + 3)) ≠ 1 := by
  refine Fin.ne_of_val_ne ?_
  simp

theorem nullTrans_zero_ne_two (n : ℕ) : (0 : Fin (n + 3)) ≠ 2 := by
  refine Fin.ne_of_val_ne ?_
  rw [Fin.val_zero, nullTrans_val_two]
  omega

theorem nullTrans_one_ne_two (n : ℕ) : (1 : Fin (n + 3)) ≠ 2 := by
  refine Fin.ne_of_val_ne ?_
  rw [Fin.val_one, nullTrans_val_two]
  omega

/-- The two null coordinates and the transverse coordinate of an event. -/
noncomputable def nullTransCLM (n : ℕ) : (Fin (n + 3) → ℝ) →L[ℝ] ((ℝ × ℝ) × ℝ) :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 3) => ℝ) 0
      + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 3) => ℝ) 1).prod
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 3) => ℝ) 0
      - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 3) => ℝ) 1)).prod
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 3) => ℝ) 2)

theorem nullTransCLM_apply (x : Fin (n + 3) → ℝ) :
    nullTransCLM n x = (((x 0 + x 1, x 0 - x 1), x 2) : (ℝ × ℝ) × ℝ) := rfl

/-- The field obtained from a function of the two null coordinates and one transverse one. -/
noncomputable def nullTransLift (u : ℝ → ℝ → ℝ → ℝ) (n : ℕ) : (Fin (n + 3) → ℝ) → ℝ :=
  fun x => u (x 0 + x 1) (x 0 - x 1) (x 2)

theorem nullTransLift_eq_comp (u : ℝ → ℝ → ℝ → ℝ) (n : ℕ) :
    nullTransLift u n = uncurry3 u ∘ nullTransCLM n := rfl

/-- The events whose null and transverse coordinates lie in a given set. -/
def nullTransBox (Ω : Set ((ℝ × ℝ) × ℝ)) (n : ℕ) : Set (Fin (n + 3) → ℝ) :=
  nullTransCLM n ⁻¹' Ω

theorem mem_nullTransBox {Ω : Set ((ℝ × ℝ) × ℝ)} {x : Fin (n + 3) → ℝ} :
    x ∈ nullTransBox Ω n ↔ nullTransCLM n x ∈ Ω := Iff.rfl

theorem isOpen_nullTransBox {Ω : Set ((ℝ × ℝ) × ℝ)} (hΩ : IsOpen Ω) (n : ℕ) :
    IsOpen (nullTransBox Ω n) :=
  hΩ.preimage (nullTransCLM n).continuous

/-! ## The chain rule through the null and transverse projections -/

variable {u A B C : ℝ → ℝ → ℝ → ℝ} {Ω : Set ((ℝ × ℝ) × ℝ)}

theorem hasFDerivAt_nullTransLift (h : IsC1On3 u A B C Ω) {x : Fin (n + 3) → ℝ}
    (hx : nullTransCLM n x ∈ Ω) :
    HasFDerivAt (nullTransLift u n)
      (((pairToCLM (A (x 0 + x 1) (x 0 - x 1) (x 2)) (B (x 0 + x 1) (x 0 - x 1) (x 2))).coprod
        (toCLM (C (x 0 + x 1) (x 0 - x 1) (x 2)))).comp (nullTransCLM n)) x :=
  (hasFDerivAt_uncurry3 h hx).comp x (nullTransCLM n).hasFDerivAt

theorem differentiableAt_nullTransLift (h : IsC1On3 u A B C Ω) {x : Fin (n + 3) → ℝ}
    (hx : nullTransCLM n x ∈ Ω) : DifferentiableAt ℝ (nullTransLift u n) x :=
  (hasFDerivAt_nullTransLift h hx).differentiableAt

theorem coordPartial_nullTransLift_zero (h : IsC1On3 u A B C Ω) {x : Fin (n + 3) → ℝ}
    (hx : nullTransCLM n x ∈ Ω) :
    coordPartial 0 (nullTransLift u n) x
      = A (x 0 + x 1) (x 0 - x 1) (x 2) + B (x 0 + x 1) (x 0 - x 1) (x 2) := by
  rw [coordPartial, (hasFDerivAt_nullTransLift h hx).fderiv]
  simp [nullTransCLM_apply, pairToCLM_apply, toCLM_apply, (nullTrans_zero_ne_one n).symm,
    (nullTrans_zero_ne_two n).symm]

theorem coordPartial_nullTransLift_one (h : IsC1On3 u A B C Ω) {x : Fin (n + 3) → ℝ}
    (hx : nullTransCLM n x ∈ Ω) :
    coordPartial 1 (nullTransLift u n) x
      = A (x 0 + x 1) (x 0 - x 1) (x 2) - B (x 0 + x 1) (x 0 - x 1) (x 2) := by
  rw [coordPartial, (hasFDerivAt_nullTransLift h hx).fderiv]
  simp [nullTransCLM_apply, pairToCLM_apply, toCLM_apply, nullTrans_zero_ne_one n,
    (nullTrans_one_ne_two n).symm]
  ring

theorem coordPartial_nullTransLift_two (h : IsC1On3 u A B C Ω) {x : Fin (n + 3) → ℝ}
    (hx : nullTransCLM n x ∈ Ω) :
    coordPartial 2 (nullTransLift u n) x = C (x 0 + x 1) (x 0 - x 1) (x 2) := by
  rw [coordPartial, (hasFDerivAt_nullTransLift h hx).fderiv]
  simp [nullTransCLM_apply, pairToCLM_apply, toCLM_apply, nullTrans_zero_ne_two n,
    nullTrans_one_ne_two n]

theorem coordPartial_nullTransLift_transverse (h : IsC1On3 u A B C Ω) {x : Fin (n + 3) → ℝ}
    (hx : nullTransCLM n x ∈ Ω) {i : Fin (n + 3)} (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2) :
    coordPartial i (nullTransLift u n) x = 0 := by
  rw [coordPartial, (hasFDerivAt_nullTransLift h hx).fderiv]
  simp [nullTransCLM_apply, pairToCLM_apply, toCLM_apply, Ne.symm h0, Ne.symm h1, Ne.symm h2]

/-! ## Second derivatives -/

theorem eventuallyEq_coordPartial_nullTransLift_zero (h : IsC1On3 u A B C Ω)
    {x : Fin (n + 3) → ℝ} (hx : nullTransCLM n x ∈ Ω) :
    coordPartial 0 (nullTransLift u n)
      =ᶠ[nhds x] nullTransLift (fun s t w => A s t w + B s t w) n :=
  Filter.eventually_of_mem ((isOpen_nullTransBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_nullTransLift_zero h hy

theorem eventuallyEq_coordPartial_nullTransLift_one (h : IsC1On3 u A B C Ω)
    {x : Fin (n + 3) → ℝ} (hx : nullTransCLM n x ∈ Ω) :
    coordPartial 1 (nullTransLift u n)
      =ᶠ[nhds x] nullTransLift (fun s t w => A s t w - B s t w) n :=
  Filter.eventually_of_mem ((isOpen_nullTransBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_nullTransLift_one h hy

theorem eventuallyEq_coordPartial_nullTransLift_two (h : IsC1On3 u A B C Ω)
    {x : Fin (n + 3) → ℝ} (hx : nullTransCLM n x ∈ Ω) :
    coordPartial 2 (nullTransLift u n) =ᶠ[nhds x] nullTransLift C n :=
  Filter.eventually_of_mem ((isOpen_nullTransBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_nullTransLift_two h hy

theorem eventuallyEq_coordPartial_nullTransLift_transverse (h : IsC1On3 u A B C Ω)
    {x : Fin (n + 3) → ℝ} (hx : nullTransCLM n x ∈ Ω) {i : Fin (n + 3)} (h0 : i ≠ 0)
    (h1 : i ≠ 1) (h2 : i ≠ 2) :
    coordPartial i (nullTransLift u n) =ᶠ[nhds x] fun _ => (0 : ℝ) :=
  Filter.eventually_of_mem ((isOpen_nullTransBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_nullTransLift_transverse h hy h0 h1 h2

variable {Aa Ab Ac Ba Bb Bc Ca Cb Cc : ℝ → ℝ → ℝ → ℝ}

/-- **Every chart partial derivative of the lift is differentiable.** -/
theorem differentiableAt_coordPartial_nullTransLift (h : IsC1On3 u A B C Ω)
    (hA : IsC1On3 A Aa Ab Ac Ω) (hB : IsC1On3 B Ba Bb Bc Ω) (hC : IsC1On3 C Ca Cb Cc Ω)
    {x : Fin (n + 3) → ℝ} (hx : nullTransCLM n x ∈ Ω) (i : Fin (n + 3)) :
    DifferentiableAt ℝ (coordPartial i (nullTransLift u n)) x := by
  by_cases h0 : i = 0
  · subst h0
    exact (differentiableAt_nullTransLift (hA.add hB) hx).congr_of_eventuallyEq
      (eventuallyEq_coordPartial_nullTransLift_zero h hx)
  · by_cases h1 : i = 1
    · subst h1
      exact (differentiableAt_nullTransLift (hA.sub hB) hx).congr_of_eventuallyEq
        (eventuallyEq_coordPartial_nullTransLift_one h hx)
    · by_cases h2 : i = 2
      · subst h2
        exact (differentiableAt_nullTransLift hC hx).congr_of_eventuallyEq
          (eventuallyEq_coordPartial_nullTransLift_two h hx)
      · exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
          (eventuallyEq_coordPartial_nullTransLift_transverse h hx h0 h1 h2)

/-- **The d'Alembertian of a field of the null and one transverse coordinate.** -/
theorem dalembert_nullTransLift (h : IsC1On3 u A B C Ω) (hA : IsC1On3 A Aa Ab Ac Ω)
    (hB : IsC1On3 B Ba Bb Bc Ω) (hC : IsC1On3 C Ca Cb Cc Ω) {x : Fin (n + 3) → ℝ}
    (hx : nullTransCLM n x ∈ Ω) :
    (SmoothPseudoMetric.ofSignature (slabEps (n + 1)) (slabEps_ne_zero (n + 1))).chart.dalembert
        (nullTransLift u n) x
      = -2 * (Ab (x 0 + x 1) (x 0 - x 1) (x 2) + Ba (x 0 + x 1) (x 0 - x 1) (x 2))
        + Cc (x 0 + x 1) (x 0 - x 1) (x 2) := by
  have hdiff : ∀ i, DifferentiableAt ℝ (coordPartial i (nullTransLift u n)) x :=
    fun i => differentiableAt_coordPartial_nullTransLift h hA hB hC hx i
  rw [ofSignature_dalembert_of_differentiableAt (slabEps (n + 1)) (slabEps_ne_zero (n + 1)) hdiff]
  have hzero : coordPartial 0 (coordPartial 0 (nullTransLift u n)) x
      = (Aa (x 0 + x 1) (x 0 - x 1) (x 2) + Ba (x 0 + x 1) (x 0 - x 1) (x 2))
        + (Ab (x 0 + x 1) (x 0 - x 1) (x 2) + Bb (x 0 + x 1) (x 0 - x 1) (x 2)) := by
    rw [coordPartial_congr (eventuallyEq_coordPartial_nullTransLift_zero h hx) 0,
      coordPartial_nullTransLift_zero (hA.add hB) hx]
  have hone : coordPartial 1 (coordPartial 1 (nullTransLift u n)) x
      = (Aa (x 0 + x 1) (x 0 - x 1) (x 2) - Ba (x 0 + x 1) (x 0 - x 1) (x 2))
        - (Ab (x 0 + x 1) (x 0 - x 1) (x 2) - Bb (x 0 + x 1) (x 0 - x 1) (x 2)) := by
    rw [coordPartial_congr (eventuallyEq_coordPartial_nullTransLift_one h hx) 1,
      coordPartial_nullTransLift_one (hA.sub hB) hx]
  have htwo : coordPartial 2 (coordPartial 2 (nullTransLift u n)) x
      = Cc (x 0 + x 1) (x 0 - x 1) (x 2) := by
    rw [coordPartial_congr (eventuallyEq_coordPartial_nullTransLift_two h hx) 2,
      coordPartial_nullTransLift_two hC hx]
  have htrans : ∀ i : Fin (n + 3), i ≠ 0 → i ≠ 1 → i ≠ 2 →
      coordPartial i (coordPartial i (nullTransLift u n)) x = 0 := by
    intro i h0 h1 h2
    rw [coordPartial_congr (eventuallyEq_coordPartial_nullTransLift_transverse h hx h0 h1 h2) i,
      coordPartial_const]
  have hsplit : ∑ i : Fin (n + 3), (slabEps (n + 1) i)⁻¹
        * coordPartial i (coordPartial i (nullTransLift u n)) x
      = (slabEps (n + 1) 0)⁻¹ * coordPartial 0 (coordPartial 0 (nullTransLift u n)) x
        + (slabEps (n + 1) 1)⁻¹ * coordPartial 1 (coordPartial 1 (nullTransLift u n)) x
        + (slabEps (n + 1) 2)⁻¹ * coordPartial 2 (coordPartial 2 (nullTransLift u n)) x := by
    rw [← Finset.sum_subset
      (Finset.subset_univ ({0, 1, 2} : Finset (Fin (n + 3))))]
    · rw [Finset.sum_insert (by
        simp [nullTrans_zero_ne_one n, nullTrans_zero_ne_two n]),
        Finset.sum_insert (by simp [nullTrans_one_ne_two n]), Finset.sum_singleton, add_assoc]
    · intro i _ hi
      have h0 : i ≠ 0 := fun hc => hi (by simp [hc])
      have h1 : i ≠ 1 := fun hc => hi (by simp [hc])
      have h2 : i ≠ 2 := fun hc => hi (by simp [hc])
      rw [htrans i h0 h1 h2, mul_zero]
  rw [hsplit, hzero, hone, htwo, slabEps_zero (n + 1),
    slabEps_of_ne (n + 1) (Ne.symm (nullTrans_zero_ne_one n)),
    slabEps_of_ne (n + 1) (Ne.symm (nullTrans_zero_ne_two n))]
  ring

/-! ## The characteristic form of the probe equation -/

/-- **A field of the null and one transverse coordinate solving the characteristic equation is a
clock probe.** -/
theorem solvesPotentialWaveAt_nullTransLift {v : ℝ → ℝ → ℝ → ℝ} (h : IsC1On3 u A B C Ω)
    (hA : IsC1On3 A Aa Ab Ac Ω) (hB : IsC1On3 B Ba Bb Bc Ω) (hC : IsC1On3 C Ca Cb Cc Ω)
    {x : Fin (n + 3) → ℝ} (hx : nullTransCLM n x ∈ Ω)
    (hchar : Ab (x 0 + x 1) (x 0 - x 1) (x 2) + Ba (x 0 + x 1) (x 0 - x 1) (x 2)
      = (Cc (x 0 + x 1) (x 0 - x 1) (x 2)
        + v (x 0 + x 1) (x 0 - x 1) (x 2) * u (x 0 + x 1) (x 0 - x 1) (x 2)) / 2) :
    SolvesPotentialWaveAt
      (SmoothPseudoMetric.ofSignature (slabEps (n + 1)) (slabEps_ne_zero (n + 1))).chart.dalembert
      (nullTransLift v n) (nullTransLift u n) x := by
  show (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
      (slabEps_ne_zero (n + 1))).chart.dalembert (nullTransLift u n) x
      + nullTransLift v n x * nullTransLift u n x = 0
  rw [dalembert_nullTransLift h hA hB hC hx, hchar]
  show -2 * ((Cc (x 0 + x 1) (x 0 - x 1) (x 2)
      + v (x 0 + x 1) (x 0 - x 1) (x 2) * u (x 0 + x 1) (x 0 - x 1) (x 2)) / 2)
      + Cc (x 0 + x 1) (x 0 - x 1) (x 2)
      + v (x 0 + x 1) (x 0 - x 1) (x 2) * u (x 0 + x 1) (x 0 - x 1) (x 2) = 0
  ring

/-- **The same, throughout a region on which the characteristic equation holds.** -/
theorem solvesPotentialWaveOn_nullTransLift {v : ℝ → ℝ → ℝ → ℝ} (h : IsC1On3 u A B C Ω)
    (hA : IsC1On3 A Aa Ab Ac Ω) (hB : IsC1On3 B Ba Bb Bc Ω) (hC : IsC1On3 C Ca Cb Cc Ω)
    {W : Set (Fin (n + 3) → ℝ)} (hW : W ⊆ nullTransBox Ω n)
    (hchar : ∀ y ∈ W, Ab (y 0 + y 1) (y 0 - y 1) (y 2) + Ba (y 0 + y 1) (y 0 - y 1) (y 2)
      = (Cc (y 0 + y 1) (y 0 - y 1) (y 2)
        + v (y 0 + y 1) (y 0 - y 1) (y 2) * u (y 0 + y 1) (y 0 - y 1) (y 2)) / 2) :
    SolvesPotentialWaveOn
      (SmoothPseudoMetric.ofSignature (slabEps (n + 1)) (slabEps_ne_zero (n + 1))).chart.dalembert
      (nullTransLift v n) (nullTransLift u n) W :=
  fun y hy => solvesPotentialWaveAt_nullTransLift h hA hB hC (hW hy) (hchar y hy)

end GaloisForLFunctions.HTGeometry
