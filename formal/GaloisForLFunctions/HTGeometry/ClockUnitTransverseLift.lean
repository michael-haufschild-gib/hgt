import GaloisForLFunctions.HTGeometry.ClockDiagonalTransverseLift

/-!
# Fields coupling the transverse coordinates along one direction

The diagonal of the previous chapter is one direction of the transverse plane; nothing distinguishes
it. This file replaces it by an arbitrary unit direction `c` of the transverse space, in any number
of transverse dimensions: the field is a function of the two null coordinates and of the single
combination `∑ᵢ cᵢ xⁱ`.

The d'Alembertian is again unchanged. Each transverse direction contributes `cᵢ²` of the transverse
second derivative, and the direction being a unit vector means those contributions sum to exactly
one:

`□ u = -2 (∂η∂ξ u + ∂ξ∂η u) + ∂w∂w u`.

So a field solving the characteristic clock equation is a clock probe for any potential depending on
the same combination — a genuinely coupled dependence on all the transverse coordinates at once.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {n : ℕ}

/-- A unit direction of the transverse space: a vector orthogonal to the two null directions and of
unit length. -/
structure UnitDirection (n : ℕ) (c : Fin (n + 2) → ℝ) : Prop where
  nullFst : c 0 = 0
  nullSnd : c 1 = 0
  normOne : ∑ i, c i ^ (2 : ℕ) = 1

/-- The two null coordinates and the transverse combination of an event. -/
noncomputable def unitCLM (n : ℕ) (c : Fin (n + 2) → ℝ) :
    (Fin (n + 2) → ℝ) →L[ℝ] ((ℝ × ℝ) × ℝ) :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 2) => ℝ) 0
      + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 2) => ℝ) 1).prod
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 2) => ℝ) 0
      - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 2) => ℝ) 1)).prod
    (∑ i, c i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 2) => ℝ) i)

theorem unitCLM_apply (c : Fin (n + 2) → ℝ) (x : Fin (n + 2) → ℝ) :
    unitCLM n c x = (((x 0 + x 1, x 0 - x 1), ∑ i, c i * x i) : (ℝ × ℝ) × ℝ) := by
  refine Prod.ext rfl ?_
  show (∑ i, c i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 2) => ℝ) i) x
      = ∑ i, c i * x i
  rw [sum_apply]
  rfl

/-- The field obtained from a function of the two null coordinates and one transverse
combination. -/
noncomputable def unitTransLift (u : ℝ → ℝ → ℝ → ℝ) (c : Fin (n + 2) → ℝ) :
    (Fin (n + 2) → ℝ) → ℝ :=
  fun x => u (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)

theorem unitTransLift_eq_comp (u : ℝ → ℝ → ℝ → ℝ) (c : Fin (n + 2) → ℝ) :
    unitTransLift u c = uncurry3 u ∘ unitCLM n c := by
  funext x
  rw [Function.comp_apply, unitCLM_apply]
  rfl

/-- The events whose null and transverse combination lie in a given set. -/
def unitTransBox (Ω : Set ((ℝ × ℝ) × ℝ)) (c : Fin (n + 2) → ℝ) : Set (Fin (n + 2) → ℝ) :=
  unitCLM n c ⁻¹' Ω

theorem mem_unitTransBox {Ω : Set ((ℝ × ℝ) × ℝ)} {c x : Fin (n + 2) → ℝ} :
    x ∈ unitTransBox Ω c ↔ unitCLM n c x ∈ Ω := Iff.rfl

theorem isOpen_unitTransBox {Ω : Set ((ℝ × ℝ) × ℝ)} (hΩ : IsOpen Ω) (c : Fin (n + 2) → ℝ) :
    IsOpen (unitTransBox Ω c) :=
  hΩ.preimage (unitCLM n c).continuous

/-- The transverse combination of a coordinate direction is the corresponding component. -/
theorem sum_smul_single (c : Fin (n + 2) → ℝ) (j : Fin (n + 2)) :
    ∑ i, c i * (Pi.single j (1 : ℝ) : Fin (n + 2) → ℝ) i = c j := by
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, mul_one]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-! ## The chain rule through the transverse combination -/

variable {u A B C : ℝ → ℝ → ℝ → ℝ} {Ω : Set ((ℝ × ℝ) × ℝ)}

theorem hasFDerivAt_unitTransLift (h : IsC1On3 u A B C Ω) {c : Fin (n + 2) → ℝ}
    {x : Fin (n + 2) → ℝ} (hx : unitCLM n c x ∈ Ω) :
    HasFDerivAt (unitTransLift u c)
      (((pairToCLM (A (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i))
          (B (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i))).coprod
        (toCLM (C (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)))).comp (unitCLM n c)) x := by
  rw [unitTransLift_eq_comp]
  have hq : uncurry3 u = uncurry3 u := rfl
  have hbase := hasFDerivAt_uncurry3 h hx
  have hcomp := hbase.comp x (unitCLM n c).hasFDerivAt
  have hpt : unitCLM n c x = (((x 0 + x 1, x 0 - x 1), ∑ i, c i * x i) : (ℝ × ℝ) × ℝ) :=
    unitCLM_apply c x
  rw [hpt] at hcomp
  exact hcomp

theorem differentiableAt_unitTransLift (h : IsC1On3 u A B C Ω) {c : Fin (n + 2) → ℝ}
    {x : Fin (n + 2) → ℝ} (hx : unitCLM n c x ∈ Ω) :
    DifferentiableAt ℝ (unitTransLift u c) x :=
  (hasFDerivAt_unitTransLift h hx).differentiableAt

theorem coordPartial_unitTransLift_zero (h : IsC1On3 u A B C Ω) {c : Fin (n + 2) → ℝ}
    {x : Fin (n + 2) → ℝ} (hx : unitCLM n c x ∈ Ω) :
    coordPartial 0 (unitTransLift u c) x
      = A (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
        + B (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
        + c 0 * C (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i) := by
  rw [coordPartial, (hasFDerivAt_unitTransLift h hx).fderiv]
  show pairToCLM _ _ ((unitCLM n c) (Pi.single 0 1)).1
      + toCLM _ ((unitCLM n c) (Pi.single 0 1)).2 = _
  rw [unitCLM_apply, sum_smul_single]
  simp [pairToCLM_apply, toCLM_apply, (slab_zero_ne_one n).symm]

theorem coordPartial_unitTransLift_one (h : IsC1On3 u A B C Ω) {c : Fin (n + 2) → ℝ}
    {x : Fin (n + 2) → ℝ} (hx : unitCLM n c x ∈ Ω) :
    coordPartial 1 (unitTransLift u c) x
      = A (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
        - B (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
        + c 1 * C (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i) := by
  rw [coordPartial, (hasFDerivAt_unitTransLift h hx).fderiv]
  show pairToCLM _ _ ((unitCLM n c) (Pi.single 1 1)).1
      + toCLM _ ((unitCLM n c) (Pi.single 1 1)).2 = _
  rw [unitCLM_apply, sum_smul_single]
  simp [pairToCLM_apply, toCLM_apply, slab_zero_ne_one n]
  ring

theorem coordPartial_unitTransLift_transverse (h : IsC1On3 u A B C Ω) {c : Fin (n + 2) → ℝ}
    {x : Fin (n + 2) → ℝ} (hx : unitCLM n c x ∈ Ω) {j : Fin (n + 2)} (h0 : j ≠ 0)
    (h1 : j ≠ 1) :
    coordPartial j (unitTransLift u c) x
      = c j * C (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i) := by
  rw [coordPartial, (hasFDerivAt_unitTransLift h hx).fderiv]
  show pairToCLM _ _ ((unitCLM n c) (Pi.single j 1)).1
      + toCLM _ ((unitCLM n c) (Pi.single j 1)).2 = _
  rw [unitCLM_apply, sum_smul_single]
  simp [pairToCLM_apply, toCLM_apply, Ne.symm h0, Ne.symm h1]

/-! ## Second derivatives -/

theorem coordPartial_unitTransLift_zero' {c : Fin (n + 2) → ℝ} (hc : UnitDirection n c)
    (h : IsC1On3 u A B C Ω) {x : Fin (n + 2) → ℝ} (hx : unitCLM n c x ∈ Ω) :
    coordPartial 0 (unitTransLift u c) x
      = A (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
        + B (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i) := by
  rw [coordPartial_unitTransLift_zero h hx, hc.nullFst, zero_mul, add_zero]

theorem coordPartial_unitTransLift_one' {c : Fin (n + 2) → ℝ} (hc : UnitDirection n c)
    (h : IsC1On3 u A B C Ω) {x : Fin (n + 2) → ℝ} (hx : unitCLM n c x ∈ Ω) :
    coordPartial 1 (unitTransLift u c) x
      = A (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
        - B (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i) := by
  rw [coordPartial_unitTransLift_one h hx, hc.nullSnd, zero_mul, add_zero]

theorem eventuallyEq_coordPartial_unitTransLift_zero {c : Fin (n + 2) → ℝ}
    (hc : UnitDirection n c) (h : IsC1On3 u A B C Ω) {x : Fin (n + 2) → ℝ}
    (hx : unitCLM n c x ∈ Ω) :
    coordPartial 0 (unitTransLift u c)
      =ᶠ[nhds x] unitTransLift (fun s t w => A s t w + B s t w) c :=
  Filter.eventually_of_mem ((isOpen_unitTransBox h.isOpen c).mem_nhds hx)
    fun _ hy => coordPartial_unitTransLift_zero' hc h hy

theorem eventuallyEq_coordPartial_unitTransLift_one {c : Fin (n + 2) → ℝ}
    (hc : UnitDirection n c) (h : IsC1On3 u A B C Ω) {x : Fin (n + 2) → ℝ}
    (hx : unitCLM n c x ∈ Ω) :
    coordPartial 1 (unitTransLift u c)
      =ᶠ[nhds x] unitTransLift (fun s t w => A s t w - B s t w) c :=
  Filter.eventually_of_mem ((isOpen_unitTransBox h.isOpen c).mem_nhds hx)
    fun _ hy => coordPartial_unitTransLift_one' hc h hy

theorem eventuallyEq_coordPartial_unitTransLift_transverse {c : Fin (n + 2) → ℝ}
    (h : IsC1On3 u A B C Ω) {x : Fin (n + 2) → ℝ} (hx : unitCLM n c x ∈ Ω)
    {j : Fin (n + 2)} (h0 : j ≠ 0) (h1 : j ≠ 1) :
    coordPartial j (unitTransLift u c)
      =ᶠ[nhds x] unitTransLift (fun s t w => c j * C s t w) c :=
  Filter.eventually_of_mem ((isOpen_unitTransBox h.isOpen c).mem_nhds hx)
    fun _ hy => coordPartial_unitTransLift_transverse h hy h0 h1

variable {Aa Ab Ac Ba Bb Bc Ca Cb Cc : ℝ → ℝ → ℝ → ℝ}

/-- **Every chart partial derivative of the lift is differentiable.** -/
theorem differentiableAt_coordPartial_unitTransLift {c : Fin (n + 2) → ℝ}
    (hc : UnitDirection n c) (h : IsC1On3 u A B C Ω) (hA : IsC1On3 A Aa Ab Ac Ω)
    (hB : IsC1On3 B Ba Bb Bc Ω) (hC : IsC1On3 C Ca Cb Cc Ω) {x : Fin (n + 2) → ℝ}
    (hx : unitCLM n c x ∈ Ω) (j : Fin (n + 2)) :
    DifferentiableAt ℝ (coordPartial j (unitTransLift u c)) x := by
  by_cases h0 : j = 0
  · subst h0
    exact (differentiableAt_unitTransLift (hA.add hB) hx).congr_of_eventuallyEq
      (eventuallyEq_coordPartial_unitTransLift_zero hc h hx)
  · by_cases h1 : j = 1
    · subst h1
      exact (differentiableAt_unitTransLift (hA.sub hB) hx).congr_of_eventuallyEq
        (eventuallyEq_coordPartial_unitTransLift_one hc h hx)
    · exact (differentiableAt_unitTransLift (hC.const_mul (c j)) hx).congr_of_eventuallyEq
        (eventuallyEq_coordPartial_unitTransLift_transverse h hx h0 h1)

/-- **The d'Alembertian of a field of the null coordinates and one transverse combination**, which
is the same as for a single transverse coordinate: the transverse directions contribute the squares
of the components of a unit vector, and those sum to one. -/
theorem dalembert_unitTransLift {c : Fin (n + 2) → ℝ} (hc : UnitDirection n c)
    (h : IsC1On3 u A B C Ω) (hA : IsC1On3 A Aa Ab Ac Ω) (hB : IsC1On3 B Ba Bb Bc Ω)
    (hC : IsC1On3 C Ca Cb Cc Ω) {x : Fin (n + 2) → ℝ} (hx : unitCLM n c x ∈ Ω) :
    (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
        (unitTransLift u c) x
      = -2 * (Ab (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i)
          + Ba (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i))
        + Cc (x 0 + x 1) (x 0 - x 1) (∑ i, c i * x i) := by
  classical
  have hdiff : ∀ j, DifferentiableAt ℝ (coordPartial j (unitTransLift u c)) x :=
    fun j => differentiableAt_coordPartial_unitTransLift hc h hA hB hC hx j
  rw [ofSignature_dalembert_of_differentiableAt (slabEps n) (slabEps_ne_zero n) hdiff]
  set W : ℝ := ∑ i, c i * x i with hW
  have hzero : coordPartial 0 (coordPartial 0 (unitTransLift u c)) x
      = (Aa (x 0 + x 1) (x 0 - x 1) W + Ba (x 0 + x 1) (x 0 - x 1) W)
        + (Ab (x 0 + x 1) (x 0 - x 1) W + Bb (x 0 + x 1) (x 0 - x 1) W) := by
    rw [coordPartial_congr (eventuallyEq_coordPartial_unitTransLift_zero hc h hx) 0,
      coordPartial_unitTransLift_zero' hc (hA.add hB) hx]
  have hone : coordPartial 1 (coordPartial 1 (unitTransLift u c)) x
      = (Aa (x 0 + x 1) (x 0 - x 1) W - Ba (x 0 + x 1) (x 0 - x 1) W)
        - (Ab (x 0 + x 1) (x 0 - x 1) W - Bb (x 0 + x 1) (x 0 - x 1) W) := by
    rw [coordPartial_congr (eventuallyEq_coordPartial_unitTransLift_one hc h hx) 1,
      coordPartial_unitTransLift_one' hc (hA.sub hB) hx]
  have htrans : ∀ j ∈ (Finset.univ \ {0, 1} : Finset (Fin (n + 2))),
      (slabEps n j)⁻¹ * coordPartial j (coordPartial j (unitTransLift u c)) x
        = c j ^ (2 : ℕ) * Cc (x 0 + x 1) (x 0 - x 1) W := by
    intro j hj
    have h0 : j ≠ 0 := by
      intro hc0
      exact absurd (by simp [hc0] : j ∈ ({0, 1} : Finset (Fin (n + 2))))
        (Finset.mem_sdiff.mp hj).2
    have h1 : j ≠ 1 := by
      intro hc1
      exact absurd (by simp [hc1] : j ∈ ({0, 1} : Finset (Fin (n + 2))))
        (Finset.mem_sdiff.mp hj).2
    rw [coordPartial_congr (eventuallyEq_coordPartial_unitTransLift_transverse h hx h0 h1) j,
      coordPartial_unitTransLift_transverse (hC.const_mul (c j)) hx h0 h1,
      slabEps_of_ne n h0]
    ring
  have hsplit : ∑ j, (slabEps n j)⁻¹ * coordPartial j (coordPartial j (unitTransLift u c)) x
      = (∑ j ∈ (Finset.univ \ {0, 1} : Finset (Fin (n + 2))),
          c j ^ (2 : ℕ) * Cc (x 0 + x 1) (x 0 - x 1) W)
        + ((slabEps n 0)⁻¹ * coordPartial 0 (coordPartial 0 (unitTransLift u c)) x
          + (slabEps n 1)⁻¹ * coordPartial 1 (coordPartial 1 (unitTransLift u c)) x) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ ({0, 1} : Finset (Fin (n + 2))))]
    rw [Finset.sum_congr rfl htrans, Finset.sum_pair (slab_zero_ne_one n)]
  have hnorm : (∑ j ∈ (Finset.univ \ {0, 1} : Finset (Fin (n + 2))), c j ^ (2 : ℕ)) = 1 := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ ({0, 1} : Finset (Fin (n + 2)))),
      Finset.sum_pair (slab_zero_ne_one n), hc.nullFst, hc.nullSnd, hc.normOne]
    ring
  rw [hsplit, ← Finset.sum_mul, hnorm, hzero, hone, slabEps_zero,
    slabEps_of_ne n (Ne.symm (slab_zero_ne_one n))]
  ring

end GaloisForLFunctions.HTGeometry
