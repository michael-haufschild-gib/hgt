import GaloisForLFunctions.HTGeometry.ClockMultivariateC1
import GaloisForLFunctions.HTGeometry.ClockSlabProbe

/-!
# Fields depending on the two null coordinates and finitely many transverse ones

A field on Minkowski space of dimension `k + n + 2` that depends on `ξ = x⁰ + x¹`, `η = x⁰ - x¹` and
on the `k` transverse coordinates `x², …, x^{k+1}` has

`□ u = -2 (∂η∂ξ u + ∂ξ∂η u) + ∑ᵢ ∂ᵢ∂ᵢ u`,

since the two pure null terms cancel between the timelike and the first spacelike direction exactly
as on a slab, each transverse coordinate contributes its own second derivative, and the remaining
directions contribute nothing.

So a field solving the characteristic equation `∂ξ∂η u = (∑ᵢ ∂ᵢ²u + V u)/4` is a clock probe for the
potential `V`, and the potential may now depend on the two null coordinates and on arbitrarily many
transverse ones.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {k n : ℕ}

/-! ## The distinguished coordinate directions -/

/-- The ambient index of the `i`-th transverse coordinate. -/
def transIdx (k n : ℕ) (i : Fin k) : Fin (k + n + 2) := ⟨i.val + 2, by omega⟩

theorem transIdx_val (i : Fin k) : (transIdx k n i).val = i.val + 2 := rfl

theorem transIdx_ne_zero (i : Fin k) : transIdx k n i ≠ 0 := by
  refine Fin.ne_of_val_ne ?_
  rw [transIdx_val, Fin.val_zero]
  omega

theorem transIdx_ne_one (i : Fin k) : transIdx k n i ≠ 1 := by
  refine Fin.ne_of_val_ne ?_
  rw [transIdx_val, Fin.val_one]
  omega

theorem transIdx_injective : Function.Injective (transIdx k n) := by
  intro i j hij
  have hval : i.val + 2 = j.val + 2 := by
    have := congrArg Fin.val hij
    rwa [transIdx_val, transIdx_val] at this
  exact Fin.ext (by omega)

theorem nullMulti_zero_ne_one (k n : ℕ) : (0 : Fin (k + n + 2)) ≠ 1 := by
  refine Fin.ne_of_val_ne ?_
  rw [Fin.val_zero, Fin.val_one]
  omega

/-- The two null coordinates and the transverse coordinates of an event. -/
noncomputable def nullMultiCLM (k n : ℕ) :
    (Fin (k + n + 2) → ℝ) →L[ℝ] ((ℝ × ℝ) × (Fin k → ℝ)) :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + n + 2) => ℝ) 0
      + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + n + 2) => ℝ) 1).prod
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + n + 2) => ℝ) 0
      - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + n + 2) => ℝ) 1)).prod
    (ContinuousLinearMap.pi fun i : Fin k =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + n + 2) => ℝ) (transIdx k n i))

theorem nullMultiCLM_apply (x : Fin (k + n + 2) → ℝ) :
    nullMultiCLM k n x
      = (((x 0 + x 1, x 0 - x 1), fun i : Fin k => x (transIdx k n i)) :
        (ℝ × ℝ) × (Fin k → ℝ)) := rfl

/-- The field obtained from a function of the two null coordinates and the transverse ones. -/
noncomputable def nullMultiLift (u : ℝ → ℝ → (Fin k → ℝ) → ℝ) (n : ℕ) :
    (Fin (k + n + 2) → ℝ) → ℝ :=
  fun x => u (x 0 + x 1) (x 0 - x 1) fun i : Fin k => x (transIdx k n i)

theorem nullMultiLift_eq_comp (u : ℝ → ℝ → (Fin k → ℝ) → ℝ) (n : ℕ) :
    nullMultiLift u n = uncurryMulti u ∘ nullMultiCLM k n := rfl

/-- The events whose null and transverse coordinates lie in a given set. -/
def nullMultiBox (Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))) (n : ℕ) : Set (Fin (k + n + 2) → ℝ) :=
  nullMultiCLM k n ⁻¹' Ω

theorem mem_nullMultiBox {Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))} {x : Fin (k + n + 2) → ℝ} :
    x ∈ nullMultiBox Ω n ↔ nullMultiCLM k n x ∈ Ω := Iff.rfl

theorem isOpen_nullMultiBox {Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))} (hΩ : IsOpen Ω) (n : ℕ) :
    IsOpen (nullMultiBox (k := k) Ω n) :=
  hΩ.preimage (nullMultiCLM k n).continuous

/-! ## The coordinate directions in the chart -/

theorem nullMultiCLM_single_zero (k n : ℕ) :
    nullMultiCLM k n (Pi.single (0 : Fin (k + n + 2)) (1 : ℝ)) = (((1, 1), 0)) := by
  rw [nullMultiCLM_apply]
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · simp
  · simp
  · funext i
    simp [(transIdx_ne_zero (n := n) i)]

theorem nullMultiCLM_single_one (k n : ℕ) :
    nullMultiCLM k n (Pi.single (1 : Fin (k + n + 2)) (1 : ℝ)) = (((1, -1), 0)) := by
  rw [nullMultiCLM_apply]
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · simp
  · simp
  · funext i
    simp [(transIdx_ne_one (n := n) i)]

theorem nullMultiCLM_single_trans (k n : ℕ) (i : Fin k) :
    nullMultiCLM k n (Pi.single (transIdx k n i) (1 : ℝ))
      = (((0, 0), Pi.single i (1 : ℝ))) := by
  rw [nullMultiCLM_apply]
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · simp [(transIdx_ne_zero (n := n) i).symm, (transIdx_ne_one (n := n) i).symm]
  · simp [(transIdx_ne_zero (n := n) i).symm, (transIdx_ne_one (n := n) i).symm]
  · funext j
    by_cases hj : j = i
    · subst hj
      simp
    · have hne : transIdx k n j ≠ transIdx k n i := fun hc => hj (transIdx_injective hc)
      simp [hne, hj]

theorem nullMultiCLM_single_other (k n : ℕ) {j : Fin (k + n + 2)} (h0 : j ≠ 0) (h1 : j ≠ 1)
    (ht : ∀ i : Fin k, j ≠ transIdx k n i) :
    nullMultiCLM k n (Pi.single j (1 : ℝ)) = (((0, 0), 0)) := by
  rw [nullMultiCLM_apply]
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · simp [Ne.symm h0, Ne.symm h1]
  · simp [Ne.symm h0, Ne.symm h1]
  · funext i
    simp [Ne.symm (ht i)]

/-! ## The chain rule through the null and transverse projections -/

variable {u A B : ℝ → ℝ → (Fin k → ℝ) → ℝ} {C : Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ}
  {Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))}

theorem hasFDerivAt_nullMultiLift (h : IsC1OnMulti u A B C Ω) {x : Fin (k + n + 2) → ℝ}
    (hx : nullMultiCLM k n x ∈ Ω) :
    HasFDerivAt (nullMultiLift u n)
      (((pairToCLM (A (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))
          (B (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))).coprod
        (piToCLM fun i => C i (x 0 + x 1) (x 0 - x 1) fun i' => x (transIdx k n i'))).comp
        (nullMultiCLM k n)) x :=
  (hasFDerivAt_uncurryMulti h hx).comp x (nullMultiCLM k n).hasFDerivAt

theorem differentiableAt_nullMultiLift (h : IsC1OnMulti u A B C Ω) {x : Fin (k + n + 2) → ℝ}
    (hx : nullMultiCLM k n x ∈ Ω) : DifferentiableAt ℝ (nullMultiLift u n) x :=
  (hasFDerivAt_nullMultiLift h hx).differentiableAt

theorem coordPartial_nullMultiLift_zero (h : IsC1OnMulti u A B C Ω)
    {x : Fin (k + n + 2) → ℝ} (hx : nullMultiCLM k n x ∈ Ω) :
    coordPartial 0 (nullMultiLift u n) x
      = A (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
        + B (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i)) := by
  rw [coordPartial, (hasFDerivAt_nullMultiLift h hx).fderiv]
  show (pairToCLM (A (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))
        (B (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))).coprod
      (piToCLM fun i => C i (x 0 + x 1) (x 0 - x 1) fun i' => x (transIdx k n i'))
      (nullMultiCLM k n (Pi.single (0 : Fin (k + n + 2)) (1 : ℝ))) = _
  rw [nullMultiCLM_single_zero]
  show (pairToCLM (A (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))
        (B (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))) ((1 : ℝ), (1 : ℝ))
      + (piToCLM fun i => C i (x 0 + x 1) (x 0 - x 1) fun i' => x (transIdx k n i')) 0 = _
  rw [pairToCLM_apply, piToCLM_zero]
  ring

theorem coordPartial_nullMultiLift_one (h : IsC1OnMulti u A B C Ω)
    {x : Fin (k + n + 2) → ℝ} (hx : nullMultiCLM k n x ∈ Ω) :
    coordPartial 1 (nullMultiLift u n) x
      = A (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
        - B (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i)) := by
  rw [coordPartial, (hasFDerivAt_nullMultiLift h hx).fderiv]
  show (pairToCLM (A (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))
        (B (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))).coprod
      (piToCLM fun i => C i (x 0 + x 1) (x 0 - x 1) fun i' => x (transIdx k n i'))
      (nullMultiCLM k n (Pi.single (1 : Fin (k + n + 2)) (1 : ℝ))) = _
  rw [nullMultiCLM_single_one]
  show (pairToCLM (A (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))
        (B (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))) ((1 : ℝ), (-1 : ℝ))
      + (piToCLM fun i => C i (x 0 + x 1) (x 0 - x 1) fun i' => x (transIdx k n i')) 0 = _
  rw [pairToCLM_apply, piToCLM_zero]
  ring

theorem coordPartial_nullMultiLift_trans (h : IsC1OnMulti u A B C Ω)
    {x : Fin (k + n + 2) → ℝ} (hx : nullMultiCLM k n x ∈ Ω) (i : Fin k) :
    coordPartial (transIdx k n i) (nullMultiLift u n) x
      = C i (x 0 + x 1) (x 0 - x 1) (fun i' => x (transIdx k n i')) := by
  rw [coordPartial, (hasFDerivAt_nullMultiLift h hx).fderiv]
  show (pairToCLM (A (x 0 + x 1) (x 0 - x 1) fun i' => x (transIdx k n i'))
        (B (x 0 + x 1) (x 0 - x 1) fun i' => x (transIdx k n i'))).coprod
      (piToCLM fun i' => C i' (x 0 + x 1) (x 0 - x 1) fun i'' => x (transIdx k n i''))
      (nullMultiCLM k n (Pi.single (transIdx k n i) (1 : ℝ))) = _
  rw [nullMultiCLM_single_trans]
  show (pairToCLM (A (x 0 + x 1) (x 0 - x 1) fun i' => x (transIdx k n i'))
        (B (x 0 + x 1) (x 0 - x 1) fun i' => x (transIdx k n i'))) ((0 : ℝ), (0 : ℝ))
      + (piToCLM fun i' => C i' (x 0 + x 1) (x 0 - x 1) fun i'' => x (transIdx k n i''))
        (Pi.single i (1 : ℝ)) = _
  rw [pairToCLM_apply, piToCLM_single]
  ring

theorem coordPartial_nullMultiLift_other (h : IsC1OnMulti u A B C Ω)
    {x : Fin (k + n + 2) → ℝ} (hx : nullMultiCLM k n x ∈ Ω) {j : Fin (k + n + 2)}
    (h0 : j ≠ 0) (h1 : j ≠ 1) (ht : ∀ i : Fin k, j ≠ transIdx k n i) :
    coordPartial j (nullMultiLift u n) x = 0 := by
  rw [coordPartial, (hasFDerivAt_nullMultiLift h hx).fderiv]
  show (pairToCLM (A (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))
        (B (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))).coprod
      (piToCLM fun i => C i (x 0 + x 1) (x 0 - x 1) fun i' => x (transIdx k n i'))
      (nullMultiCLM k n (Pi.single j (1 : ℝ))) = _
  rw [nullMultiCLM_single_other k n h0 h1 ht]
  show (pairToCLM (A (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))
        (B (x 0 + x 1) (x 0 - x 1) fun i => x (transIdx k n i))) ((0 : ℝ), (0 : ℝ))
      + (piToCLM fun i => C i (x 0 + x 1) (x 0 - x 1) fun i' => x (transIdx k n i')) 0 = _
  rw [pairToCLM_apply, piToCLM_zero]
  ring

end GaloisForLFunctions.HTGeometry
