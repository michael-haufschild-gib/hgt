import GaloisForLFunctions.HTGeometry.ClockNullMultiLift

/-!
# The d'Alembertian of a field of the null and finitely many transverse coordinates

Each chart partial derivative of the lift is again a lift, of the corresponding partial derivative of
the datum, so the second derivatives are read off the first ones. The two null directions cancel in
the null combination exactly as on a slab, each transverse direction contributes its own second
derivative, and the remaining directions contribute nothing:

`□ u = -2 (∂η∂ξ u + ∂ξ∂η u) + ∑ᵢ ∂ᵢ∂ᵢ u`.

A field solving the characteristic equation `∂ξ∂η u = (∑ᵢ ∂ᵢ²u + V u)/4` is therefore a clock probe
for the potential `V`, with `V` depending on the two null coordinates and on all the transverse ones.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {k n : ℕ} {u A B : ℝ → ℝ → (Fin k → ℝ) → ℝ} {C : Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ}
  {Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))}

/-! ## The chart partial derivatives as lifts -/

theorem eventuallyEq_coordPartial_nullMultiLift_zero (h : IsC1OnMulti u A B C Ω)
    {x : Fin (k + n + 2) → ℝ} (hx : nullMultiCLM k n x ∈ Ω) :
    coordPartial 0 (nullMultiLift u n)
      =ᶠ[nhds x] nullMultiLift (fun s t y => A s t y + B s t y) n :=
  Filter.eventually_of_mem ((isOpen_nullMultiBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_nullMultiLift_zero h hy

theorem eventuallyEq_coordPartial_nullMultiLift_one (h : IsC1OnMulti u A B C Ω)
    {x : Fin (k + n + 2) → ℝ} (hx : nullMultiCLM k n x ∈ Ω) :
    coordPartial 1 (nullMultiLift u n)
      =ᶠ[nhds x] nullMultiLift (fun s t y => A s t y - B s t y) n :=
  Filter.eventually_of_mem ((isOpen_nullMultiBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_nullMultiLift_one h hy

theorem eventuallyEq_coordPartial_nullMultiLift_trans (h : IsC1OnMulti u A B C Ω)
    {x : Fin (k + n + 2) → ℝ} (hx : nullMultiCLM k n x ∈ Ω) (i : Fin k) :
    coordPartial (transIdx k n i) (nullMultiLift u n) =ᶠ[nhds x] nullMultiLift (C i) n :=
  Filter.eventually_of_mem ((isOpen_nullMultiBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_nullMultiLift_trans h hy i

theorem eventuallyEq_coordPartial_nullMultiLift_other (h : IsC1OnMulti u A B C Ω)
    {x : Fin (k + n + 2) → ℝ} (hx : nullMultiCLM k n x ∈ Ω) {j : Fin (k + n + 2)}
    (h0 : j ≠ 0) (h1 : j ≠ 1) (ht : ∀ i : Fin k, j ≠ transIdx k n i) :
    coordPartial j (nullMultiLift u n) =ᶠ[nhds x] fun _ => (0 : ℝ) :=
  Filter.eventually_of_mem ((isOpen_nullMultiBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_nullMultiLift_other h hy h0 h1 ht

variable {Aa Ab Ba Bb : ℝ → ℝ → (Fin k → ℝ) → ℝ}
  {Ac Bc Ca Cb : Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ}
  {Cc : Fin k → Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ}

/-- **Every chart partial derivative of the lift is differentiable.** -/
theorem differentiableAt_coordPartial_nullMultiLift (h : IsC1OnMulti u A B C Ω)
    (hA : IsC1OnMulti A Aa Ab Ac Ω) (hB : IsC1OnMulti B Ba Bb Bc Ω)
    (hC : ∀ i : Fin k, IsC1OnMulti (C i) (Ca i) (Cb i) (Cc i) Ω)
    {x : Fin (k + n + 2) → ℝ} (hx : nullMultiCLM k n x ∈ Ω) (j : Fin (k + n + 2)) :
    DifferentiableAt ℝ (coordPartial j (nullMultiLift u n)) x := by
  classical
  by_cases h0 : j = 0
  · subst h0
    exact (differentiableAt_nullMultiLift (hA.add hB) hx).congr_of_eventuallyEq
      (eventuallyEq_coordPartial_nullMultiLift_zero h hx)
  · by_cases h1 : j = 1
    · subst h1
      exact (differentiableAt_nullMultiLift (hA.sub hB) hx).congr_of_eventuallyEq
        (eventuallyEq_coordPartial_nullMultiLift_one h hx)
    · by_cases ht : ∃ i : Fin k, j = transIdx k n i
      · obtain ⟨i, hi⟩ := ht
        subst hi
        exact (differentiableAt_nullMultiLift (hC i) hx).congr_of_eventuallyEq
          (eventuallyEq_coordPartial_nullMultiLift_trans h hx i)
      · exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
          (eventuallyEq_coordPartial_nullMultiLift_other h hx h0 h1
            fun i hc => ht ⟨i, hc⟩)

/-! ## The sum over the chart directions -/

/-- The distinguished chart directions: the two null ones and the transverse ones. -/
noncomputable def nullMultiIdx (k n : ℕ) : Finset (Fin (k + n + 2)) :=
  insert 0 (insert 1 (Finset.univ.image (transIdx k n)))

theorem mem_nullMultiIdx_iff {j : Fin (k + n + 2)} :
    j ∈ nullMultiIdx k n ↔ j = 0 ∨ j = 1 ∨ ∃ i : Fin k, j = transIdx k n i := by
  classical
  simp [nullMultiIdx, Finset.mem_insert, Finset.mem_image, eq_comm]

/-- **The sum of a family over the chart directions**, when the undistinguished directions
contribute nothing. -/
theorem sum_over_nullMultiIdx {F : Fin (k + n + 2) → ℝ}
    (hF : ∀ j : Fin (k + n + 2), j ≠ 0 → j ≠ 1 → (∀ i : Fin k, j ≠ transIdx k n i) → F j = 0) :
    ∑ j : Fin (k + n + 2), F j = F 0 + F 1 + ∑ i : Fin k, F (transIdx k n i) := by
  classical
  have hsub : nullMultiIdx k n ⊆ Finset.univ := Finset.subset_univ _
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin (k + n + 2))), j ∉ nullMultiIdx k n → F j = 0 := by
    intro j _ hj
    have h0 : j ≠ 0 := fun hc => hj (mem_nullMultiIdx_iff.mpr (Or.inl hc))
    have h1 : j ≠ 1 := fun hc => hj (mem_nullMultiIdx_iff.mpr (Or.inr (Or.inl hc)))
    have ht : ∀ i : Fin k, j ≠ transIdx k n i := fun i hc =>
      hj (mem_nullMultiIdx_iff.mpr (Or.inr (Or.inr ⟨i, hc⟩)))
    exact hF j h0 h1 ht
  rw [← Finset.sum_subset hsub hzero, nullMultiIdx]
  have h0notin : (0 : Fin (k + n + 2)) ∉ insert 1 (Finset.univ.image (transIdx k n)) := by
    intro hc
    rcases Finset.mem_insert.mp hc with h | h
    · exact nullMulti_zero_ne_one k n h
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact transIdx_ne_zero (n := n) i hi
  have h1notin : (1 : Fin (k + n + 2)) ∉ Finset.univ.image (transIdx k n) := by
    intro hc
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hc
    exact transIdx_ne_one (n := n) i hi
  rw [Finset.sum_insert h0notin, Finset.sum_insert h1notin,
    Finset.sum_image fun i _ j _ hij => transIdx_injective hij]
  ring

/-! ## The d'Alembertian -/

/-- **The d'Alembertian of a field of the null and finitely many transverse coordinates.** -/
theorem dalembert_nullMultiLift (h : IsC1OnMulti u A B C Ω)
    (hA : IsC1OnMulti A Aa Ab Ac Ω) (hB : IsC1OnMulti B Ba Bb Bc Ω)
    (hC : ∀ i : Fin k, IsC1OnMulti (C i) (Ca i) (Cb i) (Cc i) Ω)
    {x : Fin (k + n + 2) → ℝ} (hx : nullMultiCLM k n x ∈ Ω) :
    (SmoothPseudoMetric.ofSignature (slabEps (k + n)) (slabEps_ne_zero (k + n))).chart.dalembert
        (nullMultiLift u n) x
      = -2 * (Ab (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
          + Ba (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i)))
        + ∑ i : Fin k, Cc i i (x 0 + x 1) (x 0 - x 1) (fun i' => x (transIdx k n i')) := by
  classical
  have hdiff : ∀ j, DifferentiableAt ℝ (coordPartial j (nullMultiLift u n)) x :=
    fun j => differentiableAt_coordPartial_nullMultiLift h hA hB hC hx j
  rw [ofSignature_dalembert_of_differentiableAt (slabEps (k + n)) (slabEps_ne_zero (k + n)) hdiff]
  have hzero : coordPartial 0 (coordPartial 0 (nullMultiLift u n)) x
      = (Aa (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
          + Ba (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i)))
        + (Ab (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
          + Bb (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))) := by
    rw [coordPartial_congr (eventuallyEq_coordPartial_nullMultiLift_zero h hx) 0,
      coordPartial_nullMultiLift_zero (hA.add hB) hx]
  have hone : coordPartial 1 (coordPartial 1 (nullMultiLift u n)) x
      = (Aa (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
          - Ba (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i)))
        - (Ab (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
          - Bb (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))) := by
    rw [coordPartial_congr (eventuallyEq_coordPartial_nullMultiLift_one h hx) 1,
      coordPartial_nullMultiLift_one (hA.sub hB) hx]
  have htrans : ∀ i : Fin k,
      coordPartial (transIdx k n i) (coordPartial (transIdx k n i) (nullMultiLift u n)) x
        = Cc i i (x 0 + x 1) (x 0 - x 1) (fun i' => x (transIdx k n i')) := by
    intro i
    rw [coordPartial_congr (eventuallyEq_coordPartial_nullMultiLift_trans h hx i)
      (transIdx k n i), coordPartial_nullMultiLift_trans (hC i) hx i]
  have hother : ∀ j : Fin (k + n + 2), j ≠ 0 → j ≠ 1 → (∀ i : Fin k, j ≠ transIdx k n i) →
      (slabEps (k + n) j)⁻¹ * coordPartial j (coordPartial j (nullMultiLift u n)) x = 0 := by
    intro j h0 h1 ht
    rw [coordPartial_congr (eventuallyEq_coordPartial_nullMultiLift_other h hx h0 h1 ht) j,
      coordPartial_const, mul_zero]
  rw [sum_over_nullMultiIdx hother, hzero, hone, slabEps_zero (k + n),
    slabEps_of_ne (k + n) (Ne.symm (nullMulti_zero_ne_one k n))]
  have hsum : ∑ i : Fin k, (slabEps (k + n) (transIdx k n i))⁻¹
        * coordPartial (transIdx k n i) (coordPartial (transIdx k n i) (nullMultiLift u n)) x
      = ∑ i : Fin k, Cc i i (x 0 + x 1) (x 0 - x 1) (fun i' => x (transIdx k n i')) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [slabEps_of_ne (k + n) (transIdx_ne_zero (n := n) i), htrans i]
    ring
  rw [hsum]
  ring

/-! ## The characteristic form of the probe equation -/

/-- **A field of the null and finitely many transverse coordinates solving the characteristic
equation is a clock probe.** -/
theorem solvesPotentialWaveAt_nullMultiLift {v : ℝ → ℝ → (Fin k → ℝ) → ℝ}
    (h : IsC1OnMulti u A B C Ω) (hA : IsC1OnMulti A Aa Ab Ac Ω) (hB : IsC1OnMulti B Ba Bb Bc Ω)
    (hC : ∀ i : Fin k, IsC1OnMulti (C i) (Ca i) (Cb i) (Cc i) Ω)
    {x : Fin (k + n + 2) → ℝ} (hx : nullMultiCLM k n x ∈ Ω)
    (hchar : Ab (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
        + Ba (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
      = ((∑ i : Fin k, Cc i i (x 0 + x 1) (x 0 - x 1) (fun i' => x (transIdx k n i')))
        + v (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
          * u (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))) / 2) :
    SolvesPotentialWaveAt
      (SmoothPseudoMetric.ofSignature (slabEps (k + n)) (slabEps_ne_zero (k + n))).chart.dalembert
      (nullMultiLift v n) (nullMultiLift u n) x := by
  show (SmoothPseudoMetric.ofSignature (slabEps (k + n))
      (slabEps_ne_zero (k + n))).chart.dalembert (nullMultiLift u n) x
      + nullMultiLift v n x * nullMultiLift u n x = 0
  rw [dalembert_nullMultiLift h hA hB hC hx, hchar]
  show -2 * (((∑ i : Fin k, Cc i i (x 0 + x 1) (x 0 - x 1) (fun i' => x (transIdx k n i')))
        + v (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
          * u (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))) / 2)
      + (∑ i : Fin k, Cc i i (x 0 + x 1) (x 0 - x 1) (fun i' => x (transIdx k n i')))
      + v (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
        * u (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i)) = 0
  ring

/-- **The same, throughout a region on which the characteristic equation holds.** -/
theorem solvesPotentialWaveOn_nullMultiLift {v : ℝ → ℝ → (Fin k → ℝ) → ℝ}
    (h : IsC1OnMulti u A B C Ω) (hA : IsC1OnMulti A Aa Ab Ac Ω) (hB : IsC1OnMulti B Ba Bb Bc Ω)
    (hC : ∀ i : Fin k, IsC1OnMulti (C i) (Ca i) (Cb i) (Cc i) Ω)
    {W : Set (Fin (k + n + 2) → ℝ)} (hW : W ⊆ nullMultiBox Ω n)
    (hchar : ∀ y ∈ W, Ab (y 0 + y 1) (y 0 - y 1) (fun i => y (transIdx k n i))
        + Ba (y 0 + y 1) (y 0 - y 1) (fun i => y (transIdx k n i))
      = ((∑ i : Fin k, Cc i i (y 0 + y 1) (y 0 - y 1) (fun i' => y (transIdx k n i')))
        + v (y 0 + y 1) (y 0 - y 1) (fun i => y (transIdx k n i))
          * u (y 0 + y 1) (y 0 - y 1) (fun i => y (transIdx k n i))) / 2) :
    SolvesPotentialWaveOn
      (SmoothPseudoMetric.ofSignature (slabEps (k + n)) (slabEps_ne_zero (k + n))).chart.dalembert
      (nullMultiLift v n) (nullMultiLift u n) W :=
  fun y hy => solvesPotentialWaveAt_nullMultiLift h hA hB hC (hW hy) (hchar y hy)

end GaloisForLFunctions.HTGeometry
