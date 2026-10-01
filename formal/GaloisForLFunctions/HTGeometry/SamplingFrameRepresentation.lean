import Mathlib

/-!
# Point evaluations through a weighted sampling frame

If a bounded operator `T : E → F` between real Hilbert spaces is bounded below, every bounded
functional on `E` factors through `T`: `φ(f) = ⟪β, T f⟫` (Lax–Milgram applied to the coercive form
`⟪T u, T v⟫`, then Riesz).

For a family of bounded functionals `ev_i` with weighted frame bounds
`A‖f‖² ≤ Σ w_i |ev_i f|² ≤ B‖f‖²`, this gives
`φ(f) = Σ β_i √w_i · ev_i f` with `β ∈ ℓ²`. Applied to point evaluations at a deleted node, it
produces linear relations `δ_{x₀} − Σ β_i √w_i δ_{λ_i}` that annihilate the whole space: the
mechanism behind supercritical-sampling abundance results (Kulikov–Nazarov–Sodin uniqueness
pairs, and the abundance of Dirichlet series sharing `ζ(s)³`'s functional equation).
-/

open InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-- A bounded-below operator represents every bounded functional: `φ f = ⟪β, T f⟫`. -/
theorem exists_sampling_representation {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] (T : E →L[ℝ] F) {c : ℝ}
    (hc : 0 < c) (hT : ∀ f : E, c * ‖f‖ ≤ ‖T f‖) (φ : E →L[ℝ] ℝ) :
    ∃ β : F, ∀ f : E, φ f = inner ℝ β (T f) := by
  set B : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ (E := F)).bilinearComp T T with hBdef
  have hB : ∀ u v : E, B u v = inner ℝ (T u) (T v) := fun u v => rfl
  have hcoer : IsCoercive B := by
    refine ⟨c ^ 2, by positivity, fun u => ?_⟩
    rw [hB, real_inner_self_eq_norm_sq]
    have h1 := hT u
    have h0 : 0 ≤ c * ‖u‖ := by positivity
    nlinarith [h1, h0]
  set J := hcoer.continuousLinearEquivOfBilin
  set k := (InnerProductSpace.toDual ℝ E).symm φ
  refine ⟨T (J.symm k), fun f => ?_⟩
  have h1 := hcoer.continuousLinearEquivOfBilin_apply (J.symm k) f
  rw [ContinuousLinearEquiv.apply_symm_apply, hB] at h1
  rw [← h1, InnerProductSpace.toDual_symm_apply]

/-- Weighted sampling-frame form: under `A‖f‖² ≤ Σ w_i (ev_i f)² ≤ B‖f‖²`, every bounded functional
is `Σ β_i √w_i ev_i` with square-summable `β`. -/
theorem exists_weighted_sampling_representation {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (ev : ι → E →L[ℝ] ℝ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {A B : ℝ} (hA : 0 < A) (hB0 : 0 ≤ B) (hsum : ∀ f : E, Summable fun i => w i * (ev i f) ^ 2)
    (hlow : ∀ f : E, A * ‖f‖ ^ 2 ≤ ∑' i, w i * (ev i f) ^ 2)
    (hup : ∀ f : E, ∑' i, w i * (ev i f) ^ 2 ≤ B * ‖f‖ ^ 2) (φ : E →L[ℝ] ℝ) :
    ∃ β : ι → ℝ, Summable (fun i => β i ^ 2) ∧
      ∀ f : E, φ f = ∑' i, β i * (Real.sqrt (w i) * ev i f) := by
  have h2 : (0 : ℝ) < ((2 : ENNReal)).toReal := by norm_num
  have hsq : ∀ (f : E) (i : ι), ‖Real.sqrt (w i) * ev i f‖ ^ ((2 : ENNReal)).toReal
      = w i * (ev i f) ^ 2 := by
    intro f i
    rw [show ((2 : ENNReal)).toReal = (2 : ℝ) by norm_num, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      mul_pow, Real.sq_sqrt (hw i)]
  have hmem : ∀ f : E, Memℓp (fun i => Real.sqrt (w i) * ev i f) 2 := by
    intro f
    rw [memℓp_gen_iff h2]
    simp_rw [hsq]
    exact hsum f
  let Tl : E →ₗ[ℝ] lp (fun _ : ι => ℝ) 2 :=
    { toFun := fun f => ⟨fun i => Real.sqrt (w i) * ev i f, hmem f⟩
      map_add' := fun f g => by
        apply Subtype.ext; funext i; simp [mul_add]
      map_smul' := fun r f => by
        apply Subtype.ext; funext i; simp; ring }
  have hnorm : ∀ f : E, ‖Tl f‖ ^ 2 = ∑' i, w i * (ev i f) ^ 2 := by
    intro f
    have := lp.norm_rpow_eq_tsum h2 (Tl f)
    rw [show ((2 : ENNReal)).toReal = (2 : ℝ) by norm_num, Real.rpow_two] at this
    rw [this]
    congr 1; funext i
    have := hsq f i
    rw [show ((2 : ENNReal)).toReal = (2 : ℝ) by norm_num] at this
    exact this
  let T : E →L[ℝ] lp (fun _ : ι => ℝ) 2 := Tl.mkContinuous (Real.sqrt B) (fun f => by
    have h := hnorm f
    have hb := hup f
    rw [← h] at hb
    have : ‖Tl f‖ ≤ Real.sqrt (B * ‖f‖ ^ 2) := Real.le_sqrt_of_sq_le hb
    rw [Real.sqrt_mul hB0, Real.sqrt_sq (norm_nonneg f)] at this
    exact this)
  have hTlow : ∀ f : E, Real.sqrt A * ‖f‖ ≤ ‖T f‖ := by
    intro f
    have h := hnorm f
    have hl := hlow f
    rw [← h] at hl
    have h3 : Real.sqrt (A * ‖f‖ ^ 2) ≤ Real.sqrt (‖Tl f‖ ^ 2) := Real.sqrt_le_sqrt hl
    rw [Real.sqrt_mul hA.le, Real.sqrt_sq (norm_nonneg f), Real.sqrt_sq (norm_nonneg _)] at h3
    exact h3
  obtain ⟨β, hβ⟩ := exists_sampling_representation T (Real.sqrt_pos.mpr hA) hTlow φ
  refine ⟨fun i => (β : ι → ℝ) i, ?_, fun f => ?_⟩
  · have := (lp.memℓp β)
    rw [memℓp_gen_iff h2] at this
    simpa [show ((2 : ENNReal)).toReal = (2 : ℝ) by norm_num, Real.rpow_two, sq_abs] using this
  · rw [hβ f, lp.inner_eq_tsum]
    congr 1; funext i
    simp [T, Tl, LinearMap.mkContinuous_apply]
    ring

end GaloisForLFunctions.HTGeometry
