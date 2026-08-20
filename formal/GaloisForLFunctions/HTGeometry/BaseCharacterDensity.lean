/-
# Products of a base amplitude and a torus character are dense

On a compact base times a product torus, the functions `(x, t) ↦ g(x)·χ_k(t)` form a multiplicative,
self-adjoint, point-separating family, so by Stone--Weierstrass their linear span is dense in all
continuous complex functions.  Testing a family of probability measures against those products
therefore already tests it against every continuous function: this is the reduction the weak
convergence of joint angular-phase laws runs on.

Main results:
* `exists_mFourier_ne` — torus characters separate points.
* `baseCharProd`, `baseCharSubmonoid` — the multiplicative family of products.
* `dense_span_baseChar` — **its linear span is dense**.
* `exists_baseChar_approx` — the uniform approximation in usable form.
-/
import Mathlib
import GaloisForLFunctions.HTGeometry.CommutativeGeneration

open Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable {d : Type*} [Fintype d]

/-- **Torus characters separate points.** -/
theorem exists_mFourier_ne {x y : UnitAddTorus d} (hxy : x ≠ y) :
    ∃ k : d → ℤ, UnitAddTorus.mFourier k x ≠ UnitAddTorus.mFourier k y := by
  classical
  rw [Ne, funext_iff, not_forall] at hxy
  obtain ⟨i, hi⟩ := hxy
  refine ⟨Pi.single i 1, ?_⟩
  rw [UnitAddTorus.mFourier_single, UnitAddTorus.mFourier_single, fourier_one, fourier_one,
    Ne, Subtype.coe_inj]
  contrapose hi
  exact AddCircle.injective_toCircle one_ne_zero hi

/-- A product of a continuous base amplitude and a torus character. -/
def baseCharProd (g : C(X, ℂ)) (k : d → ℤ) : C(X × UnitAddTorus d, ℂ) :=
  (g.comp ContinuousMap.fst) * ((UnitAddTorus.mFourier k).comp ContinuousMap.snd)

omit [CompactSpace X] [T2Space X] in
@[simp] theorem baseCharProd_apply (g : C(X, ℂ)) (k : d → ℤ) (y : X × UnitAddTorus d) :
    baseCharProd g k y = g y.1 * UnitAddTorus.mFourier k y.2 := rfl

/-- The multiplicative family of base-times-character products. -/
def baseCharSubmonoid (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (d : Type*) [Fintype d] : Submonoid C(X × UnitAddTorus d, ℂ) where
  carrier := {F | ∃ (g : C(X, ℂ)) (k : d → ℤ), F = baseCharProd g k}
  one_mem' := by
    refine ⟨1, 0, ?_⟩
    ext y
    simp [UnitAddTorus.mFourier_zero]
  mul_mem' := by
    rintro _ _ ⟨g, k, rfl⟩ ⟨h, l, rfl⟩
    refine ⟨g * h, k + l, ?_⟩
    ext y
    simp [UnitAddTorus.mFourier_add]
    ring

theorem mem_baseCharSubmonoid (g : C(X, ℂ)) (k : d → ℤ) :
    baseCharProd g k ∈ baseCharSubmonoid X d := ⟨g, k, rfl⟩

omit [CompactSpace X] [T2Space X] in
theorem star_baseCharProd (g : C(X, ℂ)) (k : d → ℤ) :
    star (baseCharProd g k) = baseCharProd (star g) (-k) := by
  ext y
  simp [UnitAddTorus.mFourier_neg]

/-- **The linear span of base-times-character products is dense.** -/
theorem dense_span_baseChar (hsep : ∀ x y : X, x ≠ y → ∃ g : C(X, ℂ), g x ≠ g y) :
    Dense ((Submodule.span ℂ (baseCharSubmonoid X d : Set C(X × UnitAddTorus d, ℂ)) :
      Submodule ℂ C(X × UnitAddTorus d, ℂ)) : Set C(X × UnitAddTorus d, ℂ)) := by
  classical
  have hstar : ∀ F ∈ (baseCharSubmonoid X d : Set C(X × UnitAddTorus d, ℂ)),
      star F ∈ (baseCharSubmonoid X d : Set C(X × UnitAddTorus d, ℂ)) := by
    rintro _ ⟨g, k, rfl⟩
    exact ⟨star g, -k, star_baseCharProd g k⟩
  have hsepY : ∀ y z : X × UnitAddTorus d, y ≠ z →
      ∃ F ∈ (baseCharSubmonoid X d : Set C(X × UnitAddTorus d, ℂ)), F y ≠ F z := by
    intro y z hyz
    by_cases hx : y.1 = z.1
    · have ht : y.2 ≠ z.2 := by
        intro h
        exact hyz (Prod.ext hx h)
      obtain ⟨k, hk⟩ := exists_mFourier_ne ht
      refine ⟨baseCharProd 1 k, mem_baseCharSubmonoid 1 k, ?_⟩
      simpa using hk
    · obtain ⟨g, hg⟩ := hsep y.1 z.1 hx
      refine ⟨baseCharProd g 0, mem_baseCharSubmonoid g 0, ?_⟩
      simpa [UnitAddTorus.mFourier_zero] using hg
  have hgen := ShilovLocal.generates_of_separatesPoints
    (Y := X × UnitAddTorus d) (baseCharSubmonoid X d : Set C(X × UnitAddTorus d, ℂ))
    hstar hsepY
  have hspan : (Algebra.adjoin ℂ (baseCharSubmonoid X d : Set C(X × UnitAddTorus d, ℂ))).toSubmodule
      = Submodule.span ℂ (baseCharSubmonoid X d : Set C(X × UnitAddTorus d, ℂ)) := by
    rw [Algebra.adjoin_eq_span, Submonoid.closure_eq]
  have hcoe : ((Algebra.adjoin ℂ (baseCharSubmonoid X d : Set C(X × UnitAddTorus d, ℂ))) :
      Set C(X × UnitAddTorus d, ℂ))
      = ((Submodule.span ℂ (baseCharSubmonoid X d : Set C(X × UnitAddTorus d, ℂ))) :
        Set C(X × UnitAddTorus d, ℂ)) := by
    rw [← hspan]
    rfl
  have hdense : Dense ((Algebra.adjoin ℂ
      (baseCharSubmonoid X d : Set C(X × UnitAddTorus d, ℂ))) :
      Set C(X × UnitAddTorus d, ℂ)) := by
    rw [dense_iff_closure_eq]
    have := congrArg (fun A : Subalgebra ℂ C(X × UnitAddTorus d, ℂ) =>
      (A : Set C(X × UnitAddTorus d, ℂ))) hgen
    simpa [Subalgebra.topologicalClosure_coe] using this
  rwa [hcoe] at hdense

/-- The uniform approximation, in the form the measure argument uses. -/
theorem exists_baseChar_approx (hsep : ∀ x y : X, x ≠ y → ∃ g : C(X, ℂ), g x ≠ g y)
    (F : C(X × UnitAddTorus d, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (G : Fin n → C(X × UnitAddTorus d, ℂ)),
      (∀ i, ∃ (g : C(X, ℂ)) (k : d → ℤ), G i = baseCharProd g k) ∧
      ‖F - ∑ i, c i • G i‖ < ε := by
  classical
  obtain ⟨P, hP, hdist⟩ :=
    Metric.mem_closure_iff.1 ((dense_span_baseChar (d := d) hsep) F) ε hε
  obtain ⟨n, c, G, hG⟩ := Submodule.mem_span_set'.1 hP
  refine ⟨n, c, fun i => (G i : C(X × UnitAddTorus d, ℂ)), fun i => (G i).2, ?_⟩
  rw [hG, ← dist_eq_norm]
  exact hdist

/-! ## Transfer to weak convergence -/

section Measure

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

theorem integrable_continuousMap_prod (μ : Measure (X × UnitAddTorus d)) [IsFiniteMeasure μ]
    (F : C(X × UnitAddTorus d, ℂ)) : Integrable (fun y => F y) μ :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem norm_integral_sub_le_norm (μ : Measure (X × UnitAddTorus d)) [IsProbabilityMeasure μ]
    (F G : C(X × UnitAddTorus d, ℂ)) :
    ‖(∫ y, F y ∂μ) - ∫ y, G y ∂μ‖ ≤ ‖F - G‖ := by
  rw [← integral_sub (integrable_continuousMap_prod μ F) (integrable_continuousMap_prod μ G)]
  have hb : ∀ y, ‖F y - G y‖ ≤ ‖F - G‖ := by
    intro y
    have h := ContinuousMap.norm_coe_le_norm (F - G) y
    rwa [ContinuousMap.sub_apply] at h
  have hle := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun y => F y - G y) (C := ‖F - G‖) (Filter.Eventually.of_forall hb)
  simpa using hle

/-- **Weak convergence from the base-times-character tests.**  If a family of probability measures
on a compact base times a product torus converges against every product of a continuous base
amplitude and a torus character, it converges against every continuous function. -/
theorem tendsto_integral_of_baseChar {L : Type*} {l : Filter L}
    (hsep : ∀ x y : X, x ≠ y → ∃ g : C(X, ℂ), g x ≠ g y)
    (μ : L → Measure (X × UnitAddTorus d)) (ν : Measure (X × UnitAddTorus d))
    [hμ : ∀ a, IsProbabilityMeasure (μ a)] [IsProbabilityMeasure ν]
    (hgen : ∀ (g : C(X, ℂ)) (k : d → ℤ),
      Tendsto (fun a => ∫ y, baseCharProd g k y ∂(μ a)) l
        (nhds (∫ y, baseCharProd g k y ∂ν)))
    (F : C(X × UnitAddTorus d, ℂ)) :
    Tendsto (fun a => ∫ y, F y ∂(μ a)) l (nhds (∫ y, F y ∂ν)) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, c, G, hGmem, hGapp⟩ :=
    exists_baseChar_approx hsep F (show (0 : ℝ) < ε / 3 by linarith)
  obtain ⟨P, hPdef⟩ : ∃ P : C(X × UnitAddTorus d, ℂ), P = ∑ i, c i • G i := ⟨_, rfl⟩
  have hPint : ∀ ρ : Measure (X × UnitAddTorus d), IsProbabilityMeasure ρ →
      (∫ y, P y ∂ρ) = ∑ i, c i * ∫ y, G i y ∂ρ := by
    intro ρ hρ
    have happ : ∀ y, P y = ∑ i, c i * G i y := by
      intro y
      rw [hPdef]
      simp
    rw [integral_congr_ae (Filter.Eventually.of_forall happ)]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]
    · intro i _
      exact (integrable_continuousMap_prod ρ (G i)).const_mul (c i)
  have hPconv : Tendsto (fun a => ∫ y, P y ∂(μ a)) l (nhds (∫ y, P y ∂ν)) := by
    have hsum : Tendsto (fun a => ∑ i, c i * ∫ y, G i y ∂(μ a)) l
        (nhds (∑ i, c i * ∫ y, G i y ∂ν)) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      obtain ⟨g, k, hgk⟩ := hGmem i
      have h := hgen g k
      rw [← hgk] at h
      exact h.const_mul (c i)
    have hl : (fun a => ∫ y, P y ∂(μ a)) = fun a => ∑ i, c i * ∫ y, G i y ∂(μ a) :=
      funext fun a => hPint (μ a) (hμ a)
    rw [hl, hPint ν inferInstance]
    exact hsum
  have hFP : ‖F - P‖ < ε / 3 := by rw [hPdef]; exact hGapp
  rw [Metric.tendsto_nhds] at hPconv
  filter_upwards [hPconv (ε / 3) (by linarith)] with a ha
  have h1 : ‖(∫ y, F y ∂(μ a)) - ∫ y, P y ∂(μ a)‖ ≤ ‖F - P‖ :=
    norm_integral_sub_le_norm (μ a) F P
  have h2 : ‖(∫ y, F y ∂ν) - ∫ y, P y ∂ν‖ ≤ ‖F - P‖ :=
    norm_integral_sub_le_norm ν F P
  have h3 : ‖(∫ y, P y ∂(μ a)) - ∫ y, P y ∂ν‖ < ε / 3 := by
    have := ha
    rwa [dist_eq_norm] at this
  rw [dist_eq_norm]
  calc ‖(∫ y, F y ∂(μ a)) - ∫ y, F y ∂ν‖
      = ‖((∫ y, F y ∂(μ a)) - ∫ y, P y ∂(μ a))
        + ((∫ y, P y ∂(μ a)) - ∫ y, P y ∂ν)
        + ((∫ y, P y ∂ν) - ∫ y, F y ∂ν)‖ := by ring_nf
    _ ≤ ‖(∫ y, F y ∂(μ a)) - ∫ y, P y ∂(μ a)‖ + ‖(∫ y, P y ∂(μ a)) - ∫ y, P y ∂ν‖
        + ‖(∫ y, P y ∂ν) - ∫ y, F y ∂ν‖ := norm_add₃_le
    _ < ε := by
        have h2' : ‖(∫ y, P y ∂ν) - ∫ y, F y ∂ν‖ ≤ ‖F - P‖ := by
          rw [← norm_neg, neg_sub]
          exact h2
        linarith

end Measure

end

end GaloisForLFunctions.HTGeometry
