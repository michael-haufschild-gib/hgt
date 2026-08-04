import GaloisForLFunctions.HTGeometry.SmoothPeriodicCohomology
import GaloisForLFunctions.HTGeometry.PeriodicCohomologyRing

/-!
# The de Rham complex of a torus is a commutative differential graded algebra

The wedge product of two smooth periodic forms is smooth and periodic, because in coordinates it is
a finite sum of products of the coefficients times constant forms.  So the smooth periodic forms
carry a product, and it satisfies the axioms of a commutative differential graded algebra: it is
bilinear and associative, graded commutative, and the exterior derivative is a graded derivation for
it.

* `wedgeForm_contDiff` : the wedge of smooth forms is smooth.
* `smoothWedge` : the product on the smooth periodic forms.
* `smoothWedge_assoc`, `smoothWedge_comm`, `smoothExtDerivMap_smoothWedge` : the axioms of a
  commutative differential graded algebra.
-/

set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

namespace GaloisForLFunctions.HTGeometry

open exteriorPower Module
open scoped ContDiff

section SmoothWedge

variable {𝕜 : Type u} [RCLike 𝕜] {r a b n : ℕ}

/-- The coefficients of a smooth form are smooth. -/
theorem form_coeff_contDiff {v : PeriodicFormSpace 𝕜 r n} (hsm : ContDiff 𝕜 ∞ v)
    (S : Set.powersetCard (Fin r) n) : ContDiff 𝕜 ∞ fun x => v x (coordTuple 𝕜 S) :=
  (evalFormL (coordTuple 𝕜 S)).contDiff.comp hsm

/-- **The wedge product of two smooth forms is smooth.** -/
theorem wedgeForm_contDiff (h : a + b = n) {u : PeriodicFormSpace 𝕜 r a}
    {v : PeriodicFormSpace 𝕜 r b} (hu : ContDiff 𝕜 ∞ u) (hv : ContDiff 𝕜 ∞ v) :
    ContDiff 𝕜 ∞ fun y => wedgeForm h (u y) (v y) := by
  have hexp : (fun y => wedgeForm h (u y) (v y)) =
      fun y => ∑ S : Set.powersetCard (Fin r) a, ∑ T : Set.powersetCard (Fin r) b,
        (u y (coordTuple 𝕜 S) * v y (coordTuple 𝕜 T)) •
          constantFormOfExterior 𝕜 r n
            (exteriorMulOf h (coordExterior 𝕜 r a S) (coordExterior 𝕜 r b T)) := by
    funext y
    exact wedgeForm_expansion h (u y) (v y)
  rw [hexp]
  refine ContDiff.sum fun S _ => ContDiff.sum fun T _ => ?_
  exact ((form_coeff_contDiff hu S).mul (form_coeff_contDiff hv T)).smul contDiff_const

/-- The wedge product of two smooth periodic forms is a smooth periodic form. -/
theorem wedgeForm_mem_smoothPeriodicForms {p : 𝕜} (h : a + b = n)
    {u : PeriodicFormSpace 𝕜 r a} {v : PeriodicFormSpace 𝕜 r b}
    (hu : u ∈ smoothPeriodicForms p r a) (hv : v ∈ smoothPeriodicForms p r b) :
    (fun y => wedgeForm h (u y) (v y)) ∈ smoothPeriodicForms p r n :=
  ⟨wedgeForm_contDiff h hu.1 hv.1, fun l w => wedgeForm_periodic h hu.2 hv.2 l w⟩

/-- **The product of the de Rham complex of the torus.** -/
noncomputable def smoothWedge (p : 𝕜) (h : a + b = n) (u : smoothPeriodicForms p r a)
    (v : smoothPeriodicForms p r b) : smoothPeriodicForms p r n :=
  ⟨fun y => wedgeForm h ((u : PeriodicFormSpace 𝕜 r a) y) ((v : PeriodicFormSpace 𝕜 r b) y),
    wedgeForm_mem_smoothPeriodicForms h u.2 v.2⟩

@[simp]
theorem smoothWedge_coe (p : 𝕜) (h : a + b = n) (u : smoothPeriodicForms p r a)
    (v : smoothPeriodicForms p r b) :
    (smoothWedge p h u v : PeriodicFormSpace 𝕜 r n) =
      fun y => wedgeForm h ((u : PeriodicFormSpace 𝕜 r a) y)
        ((v : PeriodicFormSpace 𝕜 r b) y) := rfl

theorem smoothWedge_add_left (p : 𝕜) (h : a + b = n) (u u' : smoothPeriodicForms p r a)
    (v : smoothPeriodicForms p r b) :
    smoothWedge p h (u + u') v = smoothWedge p h u v + smoothWedge p h u' v := by
  refine Subtype.ext ?_
  funext y
  exact wedgeForm_add_left h _ _ _

theorem smoothWedge_add_right (p : 𝕜) (h : a + b = n) (u : smoothPeriodicForms p r a)
    (v v' : smoothPeriodicForms p r b) :
    smoothWedge p h u (v + v') = smoothWedge p h u v + smoothWedge p h u v' := by
  refine Subtype.ext ?_
  funext y
  exact wedgeForm_add_right h _ _ _

theorem smoothWedge_smul_left (p : 𝕜) (h : a + b = n) (c : 𝕜) (u : smoothPeriodicForms p r a)
    (v : smoothPeriodicForms p r b) :
    smoothWedge p h (c • u) v = c • smoothWedge p h u v := by
  refine Subtype.ext ?_
  funext y
  exact wedgeForm_smul_left h c _ _

theorem smoothWedge_smul_right (p : 𝕜) (h : a + b = n) (c : 𝕜) (u : smoothPeriodicForms p r a)
    (v : smoothPeriodicForms p r b) :
    smoothWedge p h u (c • v) = c • smoothWedge p h u v := by
  refine Subtype.ext ?_
  funext y
  exact wedgeForm_smul_right h c _ _

/-- **The product is associative.** -/
theorem smoothWedge_assoc {m m' k : ℕ} (p : 𝕜) (h₁ : a + b = m) (h₂ : m + k = n)
    (h₃ : b + k = m') (h₄ : a + m' = n) (u : smoothPeriodicForms p r a)
    (v : smoothPeriodicForms p r b) (w : smoothPeriodicForms p r k) :
    smoothWedge p h₂ (smoothWedge p h₁ u v) w = smoothWedge p h₄ u (smoothWedge p h₃ v w) := by
  refine Subtype.ext ?_
  funext y
  exact wedgeForm_assoc h₁ h₂ h₃ h₄ _ _ _

/-- **The product is graded commutative.** -/
theorem smoothWedge_comm (p : 𝕜) (h : a + b = n) (h' : b + a = n)
    (u : smoothPeriodicForms p r a) (v : smoothPeriodicForms p r b) :
    smoothWedge p h u v = ((-1 : 𝕜)) ^ (a * b) • smoothWedge p h' v u := by
  refine Subtype.ext ?_
  funext y
  exact wedgeForm_comm h h' _ _

/-- **The exterior derivative is a graded derivation for the wedge product**: the Leibniz rule on
the de Rham complex of the torus. -/
theorem smoothExtDerivMap_smoothWedge (p : 𝕜) (h : a + b = n)
    (u : smoothPeriodicForms p r a) (v : smoothPeriodicForms p r b) :
    smoothExtDerivMap p r n (smoothWedge p h u v) =
      smoothWedge p (by omega : a + 1 + b = n + 1) (smoothExtDerivMap p r a u) v +
        ((-1 : 𝕜)) ^ a •
          smoothWedge p (by omega : a + (b + 1) = n + 1) u (smoothExtDerivMap p r b v) := by
  refine Subtype.ext ?_
  funext y
  exact extDeriv_wedgeForm h (u.2.1.differentiable (by simp))
    (v.2.1.differentiable (by simp)) y

end SmoothWedge

end GaloisForLFunctions.HTGeometry
