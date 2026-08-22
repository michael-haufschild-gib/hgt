import GaloisForLFunctions.HTGeometry.ClockNullTransverseLift

/-!
# Fields coupling two transverse coordinates

A field of the two null coordinates and of the *diagonal* `(x² + x³)/√2` couples two transverse
directions: it is constant along one direction of the transverse plane and varies along the other,
so it is a function of two transverse coordinates which is not a sum of one-variable profiles.

The scaling by `√2` is what keeps the equation unchanged. Each of `x²` and `x³` contributes half of
the transverse second derivative, so the two together contribute exactly one:

`□ u = -2 (∂η∂ξ u + ∂ξ∂η u) + ∂w∂w u`,

the same formula as for a single transverse coordinate. A field solving the characteristic clock
equation is therefore a clock probe here too, for a potential depending on the same diagonal.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {n : ℕ}

/-! ## The four distinguished coordinate directions -/

theorem diagTrans_val_two (n : ℕ) : ((2 : Fin (n + 4)) : ℕ) = 2 := by
  simp [Nat.mod_eq_of_lt (show 2 < n + 4 by omega)]

theorem diagTrans_val_three (n : ℕ) : ((3 : Fin (n + 4)) : ℕ) = 3 := by
  simp [Nat.mod_eq_of_lt (show 3 < n + 4 by omega)]

theorem diagTrans_zero_ne_one (n : ℕ) : (0 : Fin (n + 4)) ≠ 1 := by
  refine Fin.ne_of_val_ne ?_
  simp

theorem diagTrans_zero_ne_two (n : ℕ) : (0 : Fin (n + 4)) ≠ 2 := by
  refine Fin.ne_of_val_ne ?_
  rw [Fin.val_zero, diagTrans_val_two]
  omega

theorem diagTrans_zero_ne_three (n : ℕ) : (0 : Fin (n + 4)) ≠ 3 := by
  refine Fin.ne_of_val_ne ?_
  rw [Fin.val_zero, diagTrans_val_three]
  omega

theorem diagTrans_one_ne_two (n : ℕ) : (1 : Fin (n + 4)) ≠ 2 := by
  refine Fin.ne_of_val_ne ?_
  rw [Fin.val_one, diagTrans_val_two]
  omega

theorem diagTrans_one_ne_three (n : ℕ) : (1 : Fin (n + 4)) ≠ 3 := by
  refine Fin.ne_of_val_ne ?_
  rw [Fin.val_one, diagTrans_val_three]
  omega

theorem diagTrans_two_ne_three (n : ℕ) : (2 : Fin (n + 4)) ≠ 3 := by
  refine Fin.ne_of_val_ne ?_
  rw [diagTrans_val_two, diagTrans_val_three]
  omega

/-! ## Scalar multiples of a three-variable datum -/

theorem IsC1On3.const_mul {u A B C : ℝ → ℝ → ℝ → ℝ} {Ω : Set ((ℝ × ℝ) × ℝ)}
    (h : IsC1On3 u A B C Ω) (c : ℝ) :
    IsC1On3 (fun s t w => c * u s t w) (fun s t w => c * A s t w) (fun s t w => c * B s t w)
      (fun s t w => c * C s t w) Ω where
  isOpen := h.isOpen
  hasDerivFst := fun q hq => (h.hasDerivFst q hq).const_mul c
  hasDerivSnd := fun q hq => (h.hasDerivSnd q hq).const_mul c
  hasDerivThd := fun q hq => (h.hasDerivThd q hq).const_mul c
  contFst := continuous_const.mul h.contFst
  contSnd := continuous_const.mul h.contSnd
  contThd := continuous_const.mul h.contThd

/-! ## The diagonal lift -/

/-- The half of the diagonal scaling. -/
noncomputable def diagUnitScale : ℝ := (Real.sqrt 2)⁻¹

theorem diagUnitScale_sq : diagUnitScale * diagUnitScale = 1 / 2 := by
  rw [diagUnitScale, ← mul_inv]
  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The two null coordinates and the transverse diagonal of an event. -/
noncomputable def diagCLM (n : ℕ) : (Fin (n + 4) → ℝ) →L[ℝ] ((ℝ × ℝ) × ℝ) :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 4) => ℝ) 0
      + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 4) => ℝ) 1).prod
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 4) => ℝ) 0
      - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 4) => ℝ) 1)).prod
    (diagUnitScale • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 4) => ℝ) 2
      + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 4) => ℝ) 3))

private theorem diagCLM_apply (x : Fin (n + 4) → ℝ) :
    diagCLM n x = (((x 0 + x 1, x 0 - x 1), diagUnitScale * (x 2 + x 3)) : (ℝ × ℝ) × ℝ) := rfl

/-- The field obtained from a function of the two null coordinates and the transverse diagonal. -/
noncomputable def diagTransLift (u : ℝ → ℝ → ℝ → ℝ) (n : ℕ) : (Fin (n + 4) → ℝ) → ℝ :=
  fun x => u (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))

theorem diagTransLift_eq_comp (u : ℝ → ℝ → ℝ → ℝ) (n : ℕ) :
    diagTransLift u n = uncurry3 u ∘ diagCLM n := rfl

/-- The events whose null and diagonal coordinates lie in a given set. -/
def diagTransBox (Ω : Set ((ℝ × ℝ) × ℝ)) (n : ℕ) : Set (Fin (n + 4) → ℝ) :=
  diagCLM n ⁻¹' Ω

theorem mem_diagTransBox {Ω : Set ((ℝ × ℝ) × ℝ)} {x : Fin (n + 4) → ℝ} :
    x ∈ diagTransBox Ω n ↔ diagCLM n x ∈ Ω := Iff.rfl

theorem isOpen_diagTransBox {Ω : Set ((ℝ × ℝ) × ℝ)} (hΩ : IsOpen Ω) (n : ℕ) :
    IsOpen (diagTransBox Ω n) :=
  hΩ.preimage (diagCLM n).continuous

/-! ## The chain rule through the diagonal projection -/

variable {u A B C : ℝ → ℝ → ℝ → ℝ} {Ω : Set ((ℝ × ℝ) × ℝ)}

theorem hasFDerivAt_diagTransLift (h : IsC1On3 u A B C Ω) {x : Fin (n + 4) → ℝ}
    (hx : diagCLM n x ∈ Ω) :
    HasFDerivAt (diagTransLift u n)
      (((pairToCLM (A (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3)))
          (B (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3)))).coprod
        (toCLM (C (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))))).comp (diagCLM n)) x :=
  (hasFDerivAt_uncurry3 h hx).comp x (diagCLM n).hasFDerivAt

theorem differentiableAt_diagTransLift (h : IsC1On3 u A B C Ω) {x : Fin (n + 4) → ℝ}
    (hx : diagCLM n x ∈ Ω) : DifferentiableAt ℝ (diagTransLift u n) x :=
  (hasFDerivAt_diagTransLift h hx).differentiableAt

theorem coordPartial_diagTransLift_zero (h : IsC1On3 u A B C Ω) {x : Fin (n + 4) → ℝ}
    (hx : diagCLM n x ∈ Ω) :
    coordPartial 0 (diagTransLift u n) x
      = A (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
        + B (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3)) := by
  rw [coordPartial, (hasFDerivAt_diagTransLift h hx).fderiv]
  simp [diagCLM_apply, pairToCLM_apply, toCLM_apply, (diagTrans_zero_ne_one n).symm,
    (diagTrans_zero_ne_two n).symm, (diagTrans_zero_ne_three n).symm]

theorem coordPartial_diagTransLift_one (h : IsC1On3 u A B C Ω) {x : Fin (n + 4) → ℝ}
    (hx : diagCLM n x ∈ Ω) :
    coordPartial 1 (diagTransLift u n) x
      = A (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
        - B (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3)) := by
  rw [coordPartial, (hasFDerivAt_diagTransLift h hx).fderiv]
  simp [diagCLM_apply, pairToCLM_apply, toCLM_apply, diagTrans_zero_ne_one n,
    (diagTrans_one_ne_two n).symm, (diagTrans_one_ne_three n).symm]
  ring

theorem coordPartial_diagTransLift_two (h : IsC1On3 u A B C Ω) {x : Fin (n + 4) → ℝ}
    (hx : diagCLM n x ∈ Ω) :
    coordPartial 2 (diagTransLift u n) x
      = diagUnitScale * C (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3)) := by
  rw [coordPartial, (hasFDerivAt_diagTransLift h hx).fderiv]
  simp [diagCLM_apply, pairToCLM_apply, toCLM_apply, diagTrans_zero_ne_two n,
    diagTrans_one_ne_two n, (diagTrans_two_ne_three n).symm]

theorem coordPartial_diagTransLift_three (h : IsC1On3 u A B C Ω) {x : Fin (n + 4) → ℝ}
    (hx : diagCLM n x ∈ Ω) :
    coordPartial 3 (diagTransLift u n) x
      = diagUnitScale * C (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3)) := by
  rw [coordPartial, (hasFDerivAt_diagTransLift h hx).fderiv]
  simp [diagCLM_apply, pairToCLM_apply, toCLM_apply, diagTrans_zero_ne_three n,
    diagTrans_one_ne_three n, diagTrans_two_ne_three n]

theorem coordPartial_diagTransLift_transverse (h : IsC1On3 u A B C Ω) {x : Fin (n + 4) → ℝ}
    (hx : diagCLM n x ∈ Ω) {i : Fin (n + 4)} (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2)
    (h3 : i ≠ 3) : coordPartial i (diagTransLift u n) x = 0 := by
  rw [coordPartial, (hasFDerivAt_diagTransLift h hx).fderiv]
  simp [diagCLM_apply, pairToCLM_apply, toCLM_apply, Ne.symm h0, Ne.symm h1, Ne.symm h2,
    Ne.symm h3]

/-! ## Second derivatives -/

theorem sum_of_transverse_zero₄ {f : Fin (n + 4) → ℝ}
    (hz : ∀ i : Fin (n + 4), i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 3 → f i = 0) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [← Finset.sum_subset (Finset.subset_univ ({0, 1, 2, 3} : Finset (Fin (n + 4))))]
  · rw [Finset.sum_insert (by
        simp [diagTrans_zero_ne_one n, diagTrans_zero_ne_two n, diagTrans_zero_ne_three n]),
      Finset.sum_insert (by simp [diagTrans_one_ne_two n, diagTrans_one_ne_three n]),
      Finset.sum_insert (by simp [diagTrans_two_ne_three n]), Finset.sum_singleton]
    ring
  · intro i _ hi
    exact hz i (fun hc => hi (by simp [hc])) (fun hc => hi (by simp [hc]))
      (fun hc => hi (by simp [hc])) (fun hc => hi (by simp [hc]))

theorem eventuallyEq_coordPartial_diagTransLift_zero (h : IsC1On3 u A B C Ω)
    {x : Fin (n + 4) → ℝ} (hx : diagCLM n x ∈ Ω) :
    coordPartial 0 (diagTransLift u n)
      =ᶠ[nhds x] diagTransLift (fun s t w => A s t w + B s t w) n :=
  Filter.eventually_of_mem ((isOpen_diagTransBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_diagTransLift_zero h hy

theorem eventuallyEq_coordPartial_diagTransLift_one (h : IsC1On3 u A B C Ω)
    {x : Fin (n + 4) → ℝ} (hx : diagCLM n x ∈ Ω) :
    coordPartial 1 (diagTransLift u n)
      =ᶠ[nhds x] diagTransLift (fun s t w => A s t w - B s t w) n :=
  Filter.eventually_of_mem ((isOpen_diagTransBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_diagTransLift_one h hy

theorem eventuallyEq_coordPartial_diagTransLift_two (h : IsC1On3 u A B C Ω)
    {x : Fin (n + 4) → ℝ} (hx : diagCLM n x ∈ Ω) :
    coordPartial 2 (diagTransLift u n)
      =ᶠ[nhds x] diagTransLift (fun s t w => diagUnitScale * C s t w) n :=
  Filter.eventually_of_mem ((isOpen_diagTransBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_diagTransLift_two h hy

theorem eventuallyEq_coordPartial_diagTransLift_three (h : IsC1On3 u A B C Ω)
    {x : Fin (n + 4) → ℝ} (hx : diagCLM n x ∈ Ω) :
    coordPartial 3 (diagTransLift u n)
      =ᶠ[nhds x] diagTransLift (fun s t w => diagUnitScale * C s t w) n :=
  Filter.eventually_of_mem ((isOpen_diagTransBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_diagTransLift_three h hy

theorem eventuallyEq_coordPartial_diagTransLift_transverse (h : IsC1On3 u A B C Ω)
    {x : Fin (n + 4) → ℝ} (hx : diagCLM n x ∈ Ω) {i : Fin (n + 4)} (h0 : i ≠ 0)
    (h1 : i ≠ 1) (h2 : i ≠ 2) (h3 : i ≠ 3) :
    coordPartial i (diagTransLift u n) =ᶠ[nhds x] fun _ => (0 : ℝ) :=
  Filter.eventually_of_mem ((isOpen_diagTransBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_diagTransLift_transverse h hy h0 h1 h2 h3

variable {Aa Ab Ac Ba Bb Bc Ca Cb Cc : ℝ → ℝ → ℝ → ℝ}

/-- **Every chart partial derivative of the diagonal lift is differentiable.** -/
theorem differentiableAt_coordPartial_diagTransLift (h : IsC1On3 u A B C Ω)
    (hA : IsC1On3 A Aa Ab Ac Ω) (hB : IsC1On3 B Ba Bb Bc Ω) (hC : IsC1On3 C Ca Cb Cc Ω)
    {x : Fin (n + 4) → ℝ} (hx : diagCLM n x ∈ Ω) (i : Fin (n + 4)) :
    DifferentiableAt ℝ (coordPartial i (diagTransLift u n)) x := by
  by_cases h0 : i = 0
  · subst h0
    exact (differentiableAt_diagTransLift (hA.add hB) hx).congr_of_eventuallyEq
      (eventuallyEq_coordPartial_diagTransLift_zero h hx)
  · by_cases h1 : i = 1
    · subst h1
      exact (differentiableAt_diagTransLift (hA.sub hB) hx).congr_of_eventuallyEq
        (eventuallyEq_coordPartial_diagTransLift_one h hx)
    · by_cases h2 : i = 2
      · subst h2
        exact (differentiableAt_diagTransLift (hC.const_mul diagUnitScale) hx).congr_of_eventuallyEq
          (eventuallyEq_coordPartial_diagTransLift_two h hx)
      · by_cases h3 : i = 3
        · subst h3
          exact (differentiableAt_diagTransLift (hC.const_mul diagUnitScale) hx).congr_of_eventuallyEq
            (eventuallyEq_coordPartial_diagTransLift_three h hx)
        · exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
            (eventuallyEq_coordPartial_diagTransLift_transverse h hx h0 h1 h2 h3)

/-- **The d'Alembertian of a field of the null coordinates and the transverse diagonal**, which is
the same as for a single transverse coordinate: the two diagonal directions contribute a half
each. -/
theorem dalembert_diagTransLift (h : IsC1On3 u A B C Ω) (hA : IsC1On3 A Aa Ab Ac Ω)
    (hB : IsC1On3 B Ba Bb Bc Ω) (hC : IsC1On3 C Ca Cb Cc Ω) {x : Fin (n + 4) → ℝ}
    (hx : diagCLM n x ∈ Ω) :
    (SmoothPseudoMetric.ofSignature (slabEps (n + 2)) (slabEps_ne_zero (n + 2))).chart.dalembert
        (diagTransLift u n) x
      = -2 * (Ab (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
          + Ba (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3)))
        + Cc (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3)) := by
  have hdiff : ∀ i, DifferentiableAt ℝ (coordPartial i (diagTransLift u n)) x :=
    fun i => differentiableAt_coordPartial_diagTransLift h hA hB hC hx i
  rw [ofSignature_dalembert_of_differentiableAt (slabEps (n + 2)) (slabEps_ne_zero (n + 2)) hdiff]
  have hzero : coordPartial 0 (coordPartial 0 (diagTransLift u n)) x
      = (Aa (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
          + Ba (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3)))
        + (Ab (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
          + Bb (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))) := by
    rw [coordPartial_congr (eventuallyEq_coordPartial_diagTransLift_zero h hx) 0,
      coordPartial_diagTransLift_zero (hA.add hB) hx]
  have hone : coordPartial 1 (coordPartial 1 (diagTransLift u n)) x
      = (Aa (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
          - Ba (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3)))
        - (Ab (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
          - Bb (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))) := by
    rw [coordPartial_congr (eventuallyEq_coordPartial_diagTransLift_one h hx) 1,
      coordPartial_diagTransLift_one (hA.sub hB) hx]
  have htwo : coordPartial 2 (coordPartial 2 (diagTransLift u n)) x
      = 1 / 2 * Cc (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3)) := by
    rw [coordPartial_congr (eventuallyEq_coordPartial_diagTransLift_two h hx) 2,
      coordPartial_diagTransLift_two (hC.const_mul diagUnitScale) hx, ← mul_assoc, diagUnitScale_sq]
  have hthree : coordPartial 3 (coordPartial 3 (diagTransLift u n)) x
      = 1 / 2 * Cc (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3)) := by
    rw [coordPartial_congr (eventuallyEq_coordPartial_diagTransLift_three h hx) 3,
      coordPartial_diagTransLift_three (hC.const_mul diagUnitScale) hx, ← mul_assoc, diagUnitScale_sq]
  have htrans : ∀ i : Fin (n + 4), i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 3 →
      (slabEps (n + 2) i)⁻¹ * coordPartial i (coordPartial i (diagTransLift u n)) x = 0 := by
    intro i h0 h1 h2 h3
    rw [coordPartial_congr (eventuallyEq_coordPartial_diagTransLift_transverse h hx h0 h1 h2 h3) i,
      coordPartial_const, mul_zero]
  rw [sum_of_transverse_zero₄ htrans, hzero, hone, htwo, hthree, slabEps_zero,
    slabEps_of_ne (n + 2) (Ne.symm (diagTrans_zero_ne_one n)),
    slabEps_of_ne (n + 2) (Ne.symm (diagTrans_zero_ne_two n)),
    slabEps_of_ne (n + 2) (Ne.symm (diagTrans_zero_ne_three n))]
  ring

/-- **A field of the null coordinates and the transverse diagonal solving the characteristic
equation is a clock probe.** -/
theorem solvesPotentialWaveAt_diagTransLift {v : ℝ → ℝ → ℝ → ℝ} (h : IsC1On3 u A B C Ω)
    (hA : IsC1On3 A Aa Ab Ac Ω) (hB : IsC1On3 B Ba Bb Bc Ω) (hC : IsC1On3 C Ca Cb Cc Ω)
    {x : Fin (n + 4) → ℝ} (hx : diagCLM n x ∈ Ω)
    (hchar : Ab (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
        + Ba (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
      = (Cc (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
        + v (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
          * u (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))) / 2) :
    SolvesPotentialWaveAt
      (SmoothPseudoMetric.ofSignature (slabEps (n + 2)) (slabEps_ne_zero (n + 2))).chart.dalembert
      (diagTransLift v n) (diagTransLift u n) x := by
  show (SmoothPseudoMetric.ofSignature (slabEps (n + 2))
      (slabEps_ne_zero (n + 2))).chart.dalembert (diagTransLift u n) x
      + diagTransLift v n x * diagTransLift u n x = 0
  rw [dalembert_diagTransLift h hA hB hC hx, hchar]
  show -2 * ((Cc (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
      + v (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
        * u (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))) / 2)
      + Cc (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
      + v (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3))
        * u (x 0 + x 1) (x 0 - x 1) (diagUnitScale * (x 2 + x 3)) = 0
  ring

/-- **The same, throughout a region on which the characteristic equation holds.** -/
theorem solvesPotentialWaveOn_diagTransLift {v : ℝ → ℝ → ℝ → ℝ} (h : IsC1On3 u A B C Ω)
    (hA : IsC1On3 A Aa Ab Ac Ω) (hB : IsC1On3 B Ba Bb Bc Ω) (hC : IsC1On3 C Ca Cb Cc Ω)
    {W : Set (Fin (n + 4) → ℝ)} (hW : W ⊆ diagTransBox Ω n)
    (hchar : ∀ y ∈ W, Ab (y 0 + y 1) (y 0 - y 1) (diagUnitScale * (y 2 + y 3))
        + Ba (y 0 + y 1) (y 0 - y 1) (diagUnitScale * (y 2 + y 3))
      = (Cc (y 0 + y 1) (y 0 - y 1) (diagUnitScale * (y 2 + y 3))
        + v (y 0 + y 1) (y 0 - y 1) (diagUnitScale * (y 2 + y 3))
          * u (y 0 + y 1) (y 0 - y 1) (diagUnitScale * (y 2 + y 3))) / 2) :
    SolvesPotentialWaveOn
      (SmoothPseudoMetric.ofSignature (slabEps (n + 2)) (slabEps_ne_zero (n + 2))).chart.dalembert
      (diagTransLift v n) (diagTransLift u n) W :=
  fun y hy => solvesPotentialWaveAt_diagTransLift h hA hB hC (hW hy) (hchar y hy)

end GaloisForLFunctions.HTGeometry
