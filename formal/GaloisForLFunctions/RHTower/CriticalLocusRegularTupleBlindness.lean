import GaloisForLFunctions.RHTower.CriticalLocusSingleTestBlindness
import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain

/-!
# Finite evaluation blindness for families with a regular support tuple

Let `F₁, …, F_k` be spectral tests holomorphic on the strip `|Re s − 1/2| < θ` and decaying in the
substrip `|Re s − 1/2| ≤ t*`, and write `u_i(β) = 2 Re F_i(1/2 + iβ)` for the line-pair value.  If
some support ordinates `α₁, …, α_k` of a configuration make the matrix `(u_i'(α_m))` invertible,
then for every sufficiently distant ordinate `γ₀` an off-line quadruple at `(γ₀, t*)` can be added
while sliding each `α_m` to `α_m + ε_m`, with every test value unchanged:

  `4 Re F_i(1/2 + t* + iγ₀) + Σ_m (u_i(α_m + ε_m) − u_i(α_m)) = 0`   for all `i`
  (`regularTuple_blindness`).

The slide map `ε ↦ (Σ_m (u_i(α_m + ε_m) − u_i(α_m)))_i` vanishes at `ε = 0` and has invertible
derivative there, so by the inverse function theorem its image is a neighbourhood of `0`; the
quadruple value tends to `0` as `γ₀ → ∞` and is eventually inside it.  A regular tuple exists as
soon as the derivatives `u_i'` are linearly independent on the support
(`supportIndependent_blindness`), so finitely many such spectral tests never separate an
RH configuration from one with an off-line quadruple of prescribed displacement.  The remaining
case of `Θ4` is a support lying in the common critical set of a nonzero combination of the tests.
-/

namespace RHTower

noncomputable section

open Complex Set Filter Topology

/-- The line-pair value `β ↦ 2 Re F(1/2 + iβ)` has a strict derivative everywhere. -/
theorem hasStrictDerivAt_pairValue (F : ℂ → ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hhol : DifferentiableOn ℂ F (criticalStrip θ)) (β : ℝ) :
    HasStrictDerivAt (pairValue F) (deriv (pairValue F) β) β := by
  have hmem : (1 / 2 + (β : ℂ) * I) ∈ criticalStrip θ := by simp [criticalStrip, hθ]
  have han : AnalyticAt ℂ F (1 / 2 + (β : ℂ) * I) :=
    hhol.analyticAt ((isOpen_criticalStrip θ).mem_nhds hmem)
  have haff : AnalyticAt ℂ (fun z : ℂ => 1 / 2 + z * I) (β : ℂ) :=
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hg : AnalyticAt ℂ (F ∘ fun z : ℂ => 1 / 2 + z * I) (β : ℂ) :=
    AnalyticAt.comp (g := F) (f := fun z : ℂ => 1 / 2 + z * I) han haff
  have h1 := hg.hasStrictDerivAt.real_of_complex
  have h2 := h1.const_mul 2
  have h3 : HasStrictDerivAt (pairValue F)
      (2 * (deriv (F ∘ fun z : ℂ => 1 / 2 + z * I) (β : ℂ)).re) β := h2
  rwa [h3.hasDerivAt.deriv]

/-- **Blindness with a regular support tuple.**  If `(u_i'(α_m))` is invertible, then for every
large `γ₀` there are slides `ε` with
`4 Re F_i(1/2 + t* + iγ₀) + Σ_m (u_i(α_m + ε_m) − u_i(α_m)) = 0` for every `i`. -/
theorem regularTuple_blindness {k : ℕ} (F : Fin k → ℂ → ℂ) {θ tstar : ℝ} (htpos : 0 < tstar)
    (hθ : tstar < θ) (hhol : ∀ i, DifferentiableOn ℂ (F i) (criticalStrip θ))
    (hdecay : ∀ i, ∀ ε > 0, ∃ T : ℝ, ∀ s : ℂ,
      |s.re - 1 / 2| ≤ tstar → T ≤ |s.im| → ‖F i s‖ ≤ ε)
    (α : Fin k → ℝ) (hα : IsUnit (Matrix.of fun i m => deriv (pairValue (F i)) (α m))) :
    ∀ᶠ γ₀ in atTop, ∃ ε : Fin k → ℝ, ∀ i,
      quadValue (F i) tstar γ₀ + ∑ m, (pairValue (F i) (α m + ε m) - pairValue (F i) (α m)) = 0 := by
  classical
  have hθ0 : 0 < θ := by linarith
  set M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i m => deriv (pairValue (F i)) (α m) with hM
  set f : (Fin k → ℝ) → (Fin k → ℝ) := fun ε i =>
    ∑ m, (pairValue (F i) (α m + ε m) - pairValue (F i) (α m)) with hf
  -- the strict derivative of each component
  have hcomp : ∀ i, HasStrictFDerivAt (fun ε : Fin k → ℝ => f ε i)
      (∑ m, deriv (pairValue (F i)) (α m) • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin k => ℝ) m) 0 := by
    intro i
    have e : (fun ε : Fin k → ℝ => f ε i)
        = ∑ m, fun ε : Fin k → ℝ => pairValue (F i) (α m + ε m) - pairValue (F i) (α m) := by
      funext ε
      simp [hf, Finset.sum_apply]
    rw [e]
    refine HasStrictFDerivAt.sum fun m _ => ?_
    have haff : HasStrictFDerivAt (fun ε : Fin k → ℝ => α m + ε m)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) m) 0 :=
      (hasStrictFDerivAt_apply m 0).const_add (α m)
    have hP : HasStrictDerivAt (pairValue (F i)) (deriv (pairValue (F i)) (α m))
        ((fun ε : Fin k → ℝ => α m + ε m) 0) := by
      simpa using hasStrictDerivAt_pairValue (F i) hθ0 (hhol i) (α m)
    exact (hP.comp_hasStrictFDerivAt (0 : Fin k → ℝ) haff).sub_const _
  have hL := hasStrictFDerivAt_pi.2 hcomp
  -- the derivative is the matrix `M`
  set L := ContinuousLinearMap.pi fun i => ∑ m, deriv (pairValue (F i)) (α m) •
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) m with hLdef
  have hLM : ⇑L = M.mulVec := by
    funext δ i
    simp [hLdef, hM, Matrix.mulVec, dotProduct, mul_comm]
  have hsurj : (L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    show Function.Surjective ⇑L
    rw [hLM]
    exact Matrix.mulVec_surjective_iff_isUnit.2 hα
  have hmap := hL.map_nhds_eq_of_surj hsurj
  have hf0 : f 0 = 0 := by
    funext i
    simp [hf]
  have hfun : (fun x : Fin k → ℝ => fun i => f x i) = f := rfl
  rw [hfun, hf0] at hmap
  have himg : f '' univ ∈ 𝓝 (0 : Fin k → ℝ) := by
    rw [← hmap]
    exact image_mem_map univ_mem
  -- the quadruple values tend to `0`
  have hq : Tendsto (fun γ : ℝ => fun i => -quadValue (F i) tstar γ) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro i
    have := (tendsto_quadValue_atTop (F i) (le_of_eq (abs_of_pos htpos)) (hdecay i)).neg
    simpa using this
  filter_upwards [hq himg] with γ hγ
  obtain ⟨ε, -, hε⟩ := hγ
  refine ⟨ε, fun i => ?_⟩
  have h := congrFun hε i
  simp only [hf] at h
  linarith

/-- **Blindness from linear independence on the support.**  If the derivatives `u_i'` of the
line-pair values are linearly independent on the support `S`, there are distinct support
ordinates `α₁, …, α_k ∈ S` with the conclusion of `regularTuple_blindness`. -/
theorem supportIndependent_blindness {k : ℕ} (F : Fin k → ℂ → ℂ) {θ tstar : ℝ} (htpos : 0 < tstar)
    (hθ : tstar < θ) (hhol : ∀ i, DifferentiableOn ℂ (F i) (criticalStrip θ))
    (hdecay : ∀ i, ∀ ε > 0, ∃ T : ℝ, ∀ s : ℂ,
      |s.re - 1 / 2| ≤ tstar → T ≤ |s.im| → ‖F i s‖ ≤ ε)
    (S : Set ℝ)
    (hind : LinearIndependent ℂ
      (fun i (a : S) => ((deriv (pairValue (F i)) (a : ℝ) : ℝ) : ℂ))) :
    ∃ α : Fin k → ℝ, (∀ m, α m ∈ S) ∧ Function.Injective α ∧
      ∀ᶠ γ₀ in atTop, ∃ ε : Fin k → ℝ, ∀ i,
        quadValue (F i) tstar γ₀ + ∑ m, (pairValue (F i) (α m + ε m) - pairValue (F i) (α m))
          = 0 := by
  classical
  obtain ⟨e, P, he, hP, hPe⟩ :=
    GaloisForLFunctions.HTGeometry.exists_injective_evaluation_minor_of_linearIndependent _ hind
  set α : Fin k → ℝ := fun m => (e m : ℝ) with hαdef
  refine ⟨α, fun m => (e m).2, fun a b hab => he (Subtype.ext hab), ?_⟩
  set M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i m => deriv (pairValue (F i)) (α m) with hM
  have hPM : P = (Complex.ofRealHom.mapMatrix M).transpose := by
    ext r s
    simp [hPe, hM, hαdef]
  have hdet : IsUnit M.det := by
    rw [hPM, Matrix.det_transpose, ← RingHom.map_det] at hP
    have hne : (Complex.ofRealHom M.det) ≠ 0 := hP.ne_zero
    have : M.det ≠ 0 := fun h => hne (by rw [h, map_zero])
    exact isUnit_iff_ne_zero.2 this
  exact regularTuple_blindness F htpos hθ hhol hdecay α ((Matrix.isUnit_iff_isUnit_det M).2 hdet)

end

end RHTower
