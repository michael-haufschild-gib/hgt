import GaloisForLFunctions.HTGeometry.ClockGoursatC2
import GaloisForLFunctions.HTGeometry.ClockProbeSeparablePotential

/-!
# Clock probes in every dimension for potentials supported on a null slab

The characteristic reduction that closes the two-dimensional inverse step is not confined to two
dimensions. On Minkowski space of any dimension `n + 2`, a field depending only on the two null
combinations `ξ = x⁰ + x¹` and `η = x⁰ - x¹` has

`□ u = -2 (∂η∂ξ u + ∂ξ∂η u)`,

because the transverse coordinates contribute nothing and the two pure terms cancel between the
timelike and the spacelike direction exactly as in two dimensions. So the Goursat solution, lifted
along the transverse directions, is a clock probe in dimension `n + 2` for every potential of the
same slab form.

That is a determined class in every dimension, obtained by solving rather than by an ansatz: the
probe is normalised to `1` at the prescribed event and nonvanishing on a neighbourhood, but it is
not globally nonvanishing, so it is not of Riccati type.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {n : ℕ}

/-! ## The Minkowski signature and the null projection -/

/-- Minkowski signature in dimension `n + 2`. -/
noncomputable def slabEps (n : ℕ) : Fin (n + 2) → ℝ := fun i => if i = 0 then -1 else 1

theorem slabEps_ne_zero (n : ℕ) : ∀ i, slabEps n i ≠ 0 := by
  intro i
  rw [slabEps]
  by_cases hi : i = 0
  · rw [if_pos hi]; norm_num
  · rw [if_neg hi]; norm_num

theorem slabEps_zero (n : ℕ) : slabEps n 0 = -1 := if_pos rfl

theorem slabEps_of_ne (n : ℕ) {i : Fin (n + 2)} (hi : i ≠ 0) : slabEps n i = 1 := if_neg hi

theorem slab_zero_ne_one (n : ℕ) : (0 : Fin (n + 2)) ≠ 1 := by
  refine Fin.ne_of_val_ne ?_
  rw [Fin.val_zero, Fin.val_one]
  omega

/-- The pair of null coordinates of an event, as a continuous linear map. -/
noncomputable def slabCLM (n : ℕ) : (Fin (n + 2) → ℝ) →L[ℝ] ℝ × ℝ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 2) => ℝ) 0
      + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 2) => ℝ) 1).prod
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 2) => ℝ) 0
      - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 2) => ℝ) 1))

theorem slabCLM_apply (x : Fin (n + 2) → ℝ) :
    slabCLM n x = ((x 0 + x 1, x 0 - x 1) : ℝ × ℝ) := rfl

/-- The field on the slab obtained from a bivariate function of the null coordinates. -/
noncomputable def slabLift (u : ℝ → ℝ → ℝ) (n : ℕ) : (Fin (n + 2) → ℝ) → ℝ :=
  fun x => u (x 0 + x 1) (x 0 - x 1)

theorem slabLift_eq_comp (u : ℝ → ℝ → ℝ) (n : ℕ) :
    slabLift u n = Function.uncurry u ∘ slabCLM n := rfl

/-! ## The chain rule through the null projection -/

variable {u A B : ℝ → ℝ → ℝ} {Ω : Set (ℝ × ℝ)}

theorem hasFDerivAt_slabLift (h : IsC1On u A B Ω) {x : Fin (n + 2) → ℝ}
    (hx : slabCLM n x ∈ Ω) :
    HasFDerivAt (slabLift u n)
      (((toCLM (A (x 0 + x 1) (x 0 - x 1))).coprod
        (toCLM (B (x 0 + x 1) (x 0 - x 1)))).comp (slabCLM n)) x :=
  (hasFDerivAt_uncurry_isC1On h hx).comp x (slabCLM n).hasFDerivAt

theorem differentiableAt_slabLift (h : IsC1On u A B Ω) {x : Fin (n + 2) → ℝ}
    (hx : slabCLM n x ∈ Ω) : DifferentiableAt ℝ (slabLift u n) x :=
  (hasFDerivAt_slabLift h hx).differentiableAt

theorem coordPartial_slabLift_zero (h : IsC1On u A B Ω) {x : Fin (n + 2) → ℝ}
    (hx : slabCLM n x ∈ Ω) :
    coordPartial 0 (slabLift u n) x
      = A (x 0 + x 1) (x 0 - x 1) + B (x 0 + x 1) (x 0 - x 1) := by
  rw [coordPartial, (hasFDerivAt_slabLift h hx).fderiv]
  simp [slabCLM_apply, toCLM_apply, (slab_zero_ne_one n).symm]

theorem coordPartial_slabLift_one (h : IsC1On u A B Ω) {x : Fin (n + 2) → ℝ}
    (hx : slabCLM n x ∈ Ω) :
    coordPartial 1 (slabLift u n) x
      = A (x 0 + x 1) (x 0 - x 1) - B (x 0 + x 1) (x 0 - x 1) := by
  rw [coordPartial, (hasFDerivAt_slabLift h hx).fderiv]
  simp [slabCLM_apply, toCLM_apply, slab_zero_ne_one n]
  ring

theorem coordPartial_slabLift_transverse (h : IsC1On u A B Ω) {x : Fin (n + 2) → ℝ}
    (hx : slabCLM n x ∈ Ω) {i : Fin (n + 2)} (h0 : i ≠ 0) (h1 : i ≠ 1) :
    coordPartial i (slabLift u n) x = 0 := by
  rw [coordPartial, (hasFDerivAt_slabLift h hx).fderiv]
  simp [slabCLM_apply, toCLM_apply, Ne.symm h0, Ne.symm h1]

/-! ## The slab is an open condition -/

/-- The events whose null coordinates lie in a planar set. -/
def slabBox (Ω : Set (ℝ × ℝ)) (n : ℕ) : Set (Fin (n + 2) → ℝ) := slabCLM n ⁻¹' Ω

theorem isOpen_slabBox (hΩ : IsOpen Ω) (n : ℕ) : IsOpen (slabBox Ω n) :=
  hΩ.preimage (slabCLM n).continuous

theorem mem_slabBox {x : Fin (n + 2) → ℝ} : x ∈ slabBox Ω n ↔ slabCLM n x ∈ Ω := Iff.rfl

/-! ## Second derivatives on the slab -/

variable {Aa Ab Ba Bb : ℝ → ℝ → ℝ}

/-- The sum of the two first derivatives is again continuously differentiable. -/
theorem IsC1On.add (hA : IsC1On A Aa Ab Ω) (hB : IsC1On B Ba Bb Ω) :
    IsC1On (fun s t => A s t + B s t) (fun s t => Aa s t + Ba s t)
      (fun s t => Ab s t + Bb s t) Ω where
  isOpen := hA.isOpen
  hasDerivFst := fun p hp => (hA.hasDerivFst p hp).add (hB.hasDerivFst p hp)
  hasDerivSnd := fun p hp => (hA.hasDerivSnd p hp).add (hB.hasDerivSnd p hp)
  contFst := hA.contFst.add hB.contFst
  contSnd := hA.contSnd.add hB.contSnd

theorem IsC1On.sub (hA : IsC1On A Aa Ab Ω) (hB : IsC1On B Ba Bb Ω) :
    IsC1On (fun s t => A s t - B s t) (fun s t => Aa s t - Ba s t)
      (fun s t => Ab s t - Bb s t) Ω where
  isOpen := hA.isOpen
  hasDerivFst := fun p hp => (hA.hasDerivFst p hp).sub (hB.hasDerivFst p hp)
  hasDerivSnd := fun p hp => (hA.hasDerivSnd p hp).sub (hB.hasDerivSnd p hp)
  contFst := hA.contFst.sub hB.contFst
  contSnd := hA.contSnd.sub hB.contSnd

theorem eventuallyEq_coordPartial_slabLift_zero (h : IsC1On u A B Ω) {x : Fin (n + 2) → ℝ}
    (hx : slabCLM n x ∈ Ω) :
    coordPartial 0 (slabLift u n) =ᶠ[nhds x] slabLift (fun s t => A s t + B s t) n :=
  Filter.eventually_of_mem ((isOpen_slabBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_slabLift_zero h hy

theorem eventuallyEq_coordPartial_slabLift_one (h : IsC1On u A B Ω) {x : Fin (n + 2) → ℝ}
    (hx : slabCLM n x ∈ Ω) :
    coordPartial 1 (slabLift u n) =ᶠ[nhds x] slabLift (fun s t => A s t - B s t) n :=
  Filter.eventually_of_mem ((isOpen_slabBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_slabLift_one h hy

theorem eventuallyEq_coordPartial_slabLift_transverse (h : IsC1On u A B Ω)
    {x : Fin (n + 2) → ℝ} (hx : slabCLM n x ∈ Ω) {i : Fin (n + 2)} (h0 : i ≠ 0) (h1 : i ≠ 1) :
    coordPartial i (slabLift u n) =ᶠ[nhds x] fun _ => (0 : ℝ) :=
  Filter.eventually_of_mem ((isOpen_slabBox h.isOpen n).mem_nhds hx)
    fun _ hy => coordPartial_slabLift_transverse h hy h0 h1

/-- **Every chart partial derivative of a slab lift is differentiable.** -/
theorem differentiableAt_coordPartial_slabLift (h : IsC1On u A B Ω) (hA : IsC1On A Aa Ab Ω)
    (hB : IsC1On B Ba Bb Ω) {x : Fin (n + 2) → ℝ} (hx : slabCLM n x ∈ Ω)
    (i : Fin (n + 2)) : DifferentiableAt ℝ (coordPartial i (slabLift u n)) x := by
  by_cases h0 : i = 0
  · subst h0
    exact (differentiableAt_slabLift (hA.add hB) hx).congr_of_eventuallyEq
      (eventuallyEq_coordPartial_slabLift_zero h hx)
  · by_cases h1 : i = 1
    · subst h1
      exact (differentiableAt_slabLift (hA.sub hB) hx).congr_of_eventuallyEq
        (eventuallyEq_coordPartial_slabLift_one h hx)
    · exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
        (eventuallyEq_coordPartial_slabLift_transverse h hx h0 h1)

/-- **The d'Alembertian of a slab lift is the two-dimensional characteristic operator.** -/
theorem dalembert_slabLift (h : IsC1On u A B Ω) (hA : IsC1On A Aa Ab Ω) (hB : IsC1On B Ba Bb Ω)
    {x : Fin (n + 2) → ℝ} (hx : slabCLM n x ∈ Ω) :
    (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.dalembert
        (slabLift u n) x
      = -2 * (Ab (x 0 + x 1) (x 0 - x 1) + Ba (x 0 + x 1) (x 0 - x 1)) := by
  have hdiff : ∀ i, DifferentiableAt ℝ (coordPartial i (slabLift u n)) x :=
    fun i => differentiableAt_coordPartial_slabLift h hA hB hx i
  rw [ofSignature_dalembert_of_differentiableAt (slabEps n) (slabEps_ne_zero n) hdiff]
  have hzero : coordPartial 0 (coordPartial 0 (slabLift u n)) x
      = (Aa (x 0 + x 1) (x 0 - x 1) + Ba (x 0 + x 1) (x 0 - x 1))
        + (Ab (x 0 + x 1) (x 0 - x 1) + Bb (x 0 + x 1) (x 0 - x 1)) := by
    rw [coordPartial_congr (eventuallyEq_coordPartial_slabLift_zero h hx) 0,
      coordPartial_slabLift_zero (hA.add hB) hx]
  have hone : coordPartial 1 (coordPartial 1 (slabLift u n)) x
      = (Aa (x 0 + x 1) (x 0 - x 1) - Ba (x 0 + x 1) (x 0 - x 1))
        - (Ab (x 0 + x 1) (x 0 - x 1) - Bb (x 0 + x 1) (x 0 - x 1)) := by
    rw [coordPartial_congr (eventuallyEq_coordPartial_slabLift_one h hx) 1,
      coordPartial_slabLift_one (hA.sub hB) hx]
  have htrans : ∀ i : Fin (n + 2), i ≠ 0 → i ≠ 1 →
      coordPartial i (coordPartial i (slabLift u n)) x = 0 := by
    intro i h0 h1
    rw [coordPartial_congr (eventuallyEq_coordPartial_slabLift_transverse h hx h0 h1) i,
      coordPartial_const]
  have hsplit : ∑ i : Fin (n + 2), (slabEps n i)⁻¹ * coordPartial i (coordPartial i
      (slabLift u n)) x
      = (slabEps n 0)⁻¹ * coordPartial 0 (coordPartial 0 (slabLift u n)) x
        + (slabEps n 1)⁻¹ * coordPartial 1 (coordPartial 1 (slabLift u n)) x := by
    rw [← Finset.sum_subset
      (Finset.subset_univ ({0, 1} : Finset (Fin (n + 2))))]
    · rw [Finset.sum_pair (slab_zero_ne_one n)]
    · intro i _ hi
      have h0 : i ≠ 0 := fun hc => hi (by simp [hc])
      have h1 : i ≠ 1 := fun hc => hi (by simp [hc])
      rw [htrans i h0 h1, mul_zero]
  rw [hsplit, hzero, hone, slabEps_zero, slabEps_of_ne n (Ne.symm (slab_zero_ne_one n))]
  ring

end GaloisForLFunctions.HTGeometry
