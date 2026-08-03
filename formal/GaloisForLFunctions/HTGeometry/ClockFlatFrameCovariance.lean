import GaloisForLFunctions.HTGeometry.ClockProbeFullySeparable

/-!
# Linear changes of frame for the flat clock calculus

All the flat constructions so far are tied to the coordinate frame. A linear change of frame given
by a family of covectors `n : ι → covectors`, `y ↦ (⟪n_k, y⟫)_k`, transports the d'Alembertian to the
constant-coefficient operator whose coefficients are the **metric pairings** of the frame covectors:

`□(u ∘ F) (x) = ∑_{k,l} ⟨n_k, n_l⟩_G · (∂_l ∂_k u)(F x)`.

The proof is the chain rule applied twice, at the regularity the Picard–Lindelöf probes have:
pointwise differentiability of `u` and of its first partial derivatives on an open set.

Two consequences are immediate from the formula. For a `G`-orthogonal frame the right-hand side is
diagonal, so every flat construction transports verbatim to that frame. For a **null** frame in two
dimensions the diagonal entries vanish and only the mixed derivative survives, which is the
characteristic form of the wave operator.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

variable {d : ℕ}

/-! ## The differential in coordinates -/

/-- **The differential is the coordinate expansion of the partial derivatives.** -/
theorem fderiv_apply_eq_sum (u : (Fin (d + 1) → ℝ) → ℝ) (x v : Fin (d + 1) → ℝ) :
    fderiv ℝ u x v = ∑ k, v k * coordPartial k u x := by
  classical
  have hv : (∑ k, Pi.single k (v k) : Fin (d + 1) → ℝ) = v := Finset.univ_sum_single v
  calc fderiv ℝ u x v = fderiv ℝ u x (∑ k, Pi.single k (v k)) := by rw [hv]
    _ = ∑ k, fderiv ℝ u x (Pi.single k (v k)) := by rw [map_sum]
    _ = ∑ k, v k * coordPartial k u x := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hs : (Pi.single k (v k) : Fin (d + 1) → ℝ)
            = v k • (Pi.single k (1 : ℝ) : Fin (d + 1) → ℝ) := by
          funext j
          simp [Pi.single_apply]
        rw [hs, map_smul, coordPartial]
        simp

/-! ## Linear frames -/

/-- The change of frame determined by a family of covectors. -/
noncomputable def frameMap (n : Fin (d + 1) → (Fin (d + 1) → ℝ)) :
    (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ) := fun y k => covectorPhase (n k) y

/-- The change of frame as a continuous linear map. -/
noncomputable def frameCLM (n : Fin (d + 1) → (Fin (d + 1) → ℝ)) :
    (Fin (d + 1) → ℝ) →L[ℝ] (Fin (d + 1) → ℝ) :=
  ContinuousLinearMap.pi fun k => covectorCLM (n k)

theorem frameCLM_coe (n : Fin (d + 1) → (Fin (d + 1) → ℝ)) :
    (⇑(frameCLM n)) = frameMap (d := d) n := by
  funext y k
  simp [frameCLM, frameMap]

theorem frameMap_single (n : Fin (d + 1) → (Fin (d + 1) → ℝ)) (i k : Fin (d + 1)) :
    frameMap n (Pi.single i (1 : ℝ)) k = n k i := covectorPhase_single (n k) i

theorem hasFDerivAt_frameMap (n : Fin (d + 1) → (Fin (d + 1) → ℝ)) (x : Fin (d + 1) → ℝ) :
    HasFDerivAt (frameMap (d := d) n) (frameCLM n) x := by
  rw [← frameCLM_coe n]
  exact (frameCLM n).hasFDerivAt

theorem continuous_frameMap (n : Fin (d + 1) → (Fin (d + 1) → ℝ)) :
    Continuous (frameMap (d := d) n) := by
  rw [← frameCLM_coe n]
  exact (frameCLM n).continuous

/-! ## The chain rule through a frame -/

/-- **First-order chain rule through a linear frame.** -/
theorem coordPartial_comp_frame (n : Fin (d + 1) → (Fin (d + 1) → ℝ))
    {u : (Fin (d + 1) → ℝ) → ℝ} {x : Fin (d + 1) → ℝ}
    (hu : DifferentiableAt ℝ u (frameMap n x)) (i : Fin (d + 1)) :
    coordPartial i (fun y => u (frameMap n y)) x
      = ∑ k, n k i * coordPartial k u (frameMap n x) := by
  have hcomp := hu.hasFDerivAt.comp x (hasFDerivAt_frameMap n x)
  have hEq : (u ∘ frameMap (d := d) n) = fun y => u (frameMap n y) := rfl
  rw [hEq] at hcomp
  rw [coordPartial, hcomp.fderiv, ContinuousLinearMap.comp_apply, frameCLM_coe,
    fderiv_apply_eq_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [frameMap_single]

theorem differentiableAt_comp_frame (n : Fin (d + 1) → (Fin (d + 1) → ℝ))
    {u : (Fin (d + 1) → ℝ) → ℝ} {x : Fin (d + 1) → ℝ}
    (hu : DifferentiableAt ℝ u (frameMap n x)) :
    DifferentiableAt ℝ (fun y => u (frameMap n y)) x :=
  (hu.hasFDerivAt.comp x (hasFDerivAt_frameMap n x)).differentiableAt

/-! ## Covariance of the flat d'Alembertian -/

/-- **The flat d'Alembertian in a linear frame.** Its coefficients are the metric pairings of the
frame covectors. -/
theorem dalembert_comp_frame (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    (n : Fin (d + 1) → (Fin (d + 1) → ℝ)) {u : (Fin (d + 1) → ℝ) → ℝ} {x : Fin (d + 1) → ℝ}
    {V : Set (Fin (d + 1) → ℝ)} (hV : IsOpen V) (hFx : frameMap n x ∈ V)
    (hu : ∀ z ∈ V, DifferentiableAt ℝ u z)
    (hu2 : ∀ k, ∀ z ∈ V, DifferentiableAt ℝ (coordPartial k u) z) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
        (fun y => u (frameMap n y)) x
      = ∑ k, ∑ l, covectorPairing eps (n k) (n l)
          * coordPartial l (coordPartial k u) (frameMap n x) := by
  classical
  have hWopen : IsOpen (frameMap (d := d) n ⁻¹' V) := hV.preimage (continuous_frameMap n)
  have hxW : x ∈ frameMap (d := d) n ⁻¹' V := hFx
  have hev : ∀ i : Fin (d + 1), coordPartial i (fun y => u (frameMap n y)) =ᶠ[nhds x]
      fun y => ∑ k, n k i * coordPartial k u (frameMap n y) := by
    intro i
    refine Filter.eventuallyEq_of_mem (hWopen.mem_nhds hxW) ?_
    intro y hy
    exact coordPartial_comp_frame n (hu _ hy) i
  have hsumdiff : ∀ i : Fin (d + 1),
      DifferentiableAt ℝ (fun y => ∑ k, n k i * coordPartial k u (frameMap n y)) x := by
    intro i
    exact DifferentiableAt.fun_sum fun k _ =>
      (differentiableAt_comp_frame n (hu2 k _ hFx)).const_mul (n k i)
  have hdiff : ∀ i : Fin (d + 1),
      DifferentiableAt ℝ (coordPartial i (fun y => u (frameMap n y))) x := by
    intro i
    rw [(hev i).differentiableAt_iff]
    exact hsumdiff i
  have hsecond : ∀ i : Fin (d + 1),
      coordPartial i (coordPartial i (fun y => u (frameMap n y))) x
        = ∑ k, n k i * ∑ l, n l i * coordPartial l (coordPartial k u) (frameMap n x) := by
    intro i
    rw [coordPartial_congr (hev i) i,
      coordPartial_sum (fun k _ => (differentiableAt_comp_frame n (hu2 k _ hFx)).const_mul (n k i))
        i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coordPartial_const_mul (differentiableAt_comp_frame n (hu2 k _ hFx)) (n k i) i,
      coordPartial_comp_frame n (hu2 k _ hFx) i]
  rw [ofSignature_dalembert_of_differentiableAt eps heps hdiff]
  have hstep : ∀ i : Fin (d + 1),
      (eps i)⁻¹ * coordPartial i (coordPartial i (fun y => u (frameMap n y))) x
        = ∑ k, ∑ l, (eps i)⁻¹ * (n k i * n l i)
            * coordPartial l (coordPartial k u) (frameMap n x) := by
    intro i
    rw [hsecond i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [covectorPairing, Finset.sum_mul]

/-! ## Orthogonal frames diagonalise the operator -/

/-- **In a `G`-orthogonal frame only the pure second derivatives survive.** -/
theorem dalembert_comp_orthogonal_frame (eps : Fin (d + 1) → ℝ) (heps : ∀ i, eps i ≠ 0)
    (n : Fin (d + 1) → (Fin (d + 1) → ℝ))
    (hortho : ∀ k l, k ≠ l → covectorPairing eps (n k) (n l) = 0)
    {u : (Fin (d + 1) → ℝ) → ℝ} {x : Fin (d + 1) → ℝ}
    {V : Set (Fin (d + 1) → ℝ)} (hV : IsOpen V) (hFx : frameMap n x ∈ V)
    (hu : ∀ z ∈ V, DifferentiableAt ℝ u z)
    (hu2 : ∀ k, ∀ z ∈ V, DifferentiableAt ℝ (coordPartial k u) z) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert
        (fun y => u (frameMap n y)) x
      = ∑ k, covectorNormConst eps (n k)
          * coordPartial k (coordPartial k u) (frameMap n x) := by
  rw [dalembert_comp_frame eps heps n hV hFx hu hu2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [covectorPairing_self]
  · intro l _ hl
    rw [hortho k l (Ne.symm hl), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

end GaloisForLFunctions.HTGeometry
