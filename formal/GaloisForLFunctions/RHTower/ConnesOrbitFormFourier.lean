import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# The orbit form and the Fourier unitary

§VII Lemma 1 of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The inner product of the adele-class Hilbert space `L²(X_S)` is the orbit sum

  `⟪f₁, f₂⟫_X = ∑_{q ∈ O_S^*} ⟪f₁, U(q) f₂⟫_A`   (§VII (11)),

of the ambient `L²(A_S)` inner product over the `S`-unit group.  Lemma 1(b) says the Fourier
transform of the ambient space descends to a unitary of `L²(X_S)`.  Its whole mechanism is the
following elementary fact: an ambient isometry that intertwines the group action with the
inversion `q ↦ q^{-1}` preserves the orbit form, because inversion is a bijection of the group
and so only reindexes the sum.  Nothing about adeles, Haar measures or Bruhat–Schwartz spaces
enters; those only supply the ambient space, the action and the Fourier transform.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {G : Type*} [Group G]

/-- **§VII (11).**  The orbit form of a group action: the inner product of the quotient space. -/
def connesOrbitForm (U : G → E →ₗ[ℂ] E) (f g : E) : ℂ :=
  ∑' q : G, inner ℂ f (U q g)

/-- The summand of the orbit form is transported by an inner-product-preserving intertwiner. -/
theorem connes_orbitForm_term (U : G → E →ₗ[ℂ] E) (F : E →ₗ[ℂ] E)
    (hF : ∀ x y : E, inner ℂ (F x) (F y) = (inner ℂ x y : ℂ))
    (hcomm : ∀ (q : G) (x : E), F (U q x) = U q⁻¹ (F x)) (f g : E) (q : G) :
    (inner ℂ (F f) (U q (F g)) : ℂ) = inner ℂ f (U q⁻¹ g) := by
  have h := hcomm q⁻¹ g
  rw [inv_inv] at h
  rw [← h, hF]

/-- Summability of the orbit form is preserved by the intertwiner. -/
theorem connes_orbitForm_summable (U : G → E →ₗ[ℂ] E) (F : E →ₗ[ℂ] E)
    (hF : ∀ x y : E, inner ℂ (F x) (F y) = (inner ℂ x y : ℂ))
    (hcomm : ∀ (q : G) (x : E), F (U q x) = U q⁻¹ (F x)) (f g : E) :
    Summable (fun q : G => (inner ℂ (F f) (U q (F g)) : ℂ))
      ↔ Summable (fun q : G => (inner ℂ f (U q g) : ℂ)) := by
  have hcongr : (fun q : G => (inner ℂ (F f) (U q (F g)) : ℂ))
      = fun q : G => (inner ℂ f (U q⁻¹ g) : ℂ) :=
    funext fun q => connes_orbitForm_term U F hF hcomm f g q
  rw [hcongr]
  exact (Equiv.inv G).summable_iff (f := fun q : G => (inner ℂ f (U q g) : ℂ))

/-- **§VII Lemma 1(b), the mechanism.**  An ambient isometry intertwining the group action with
inversion preserves the orbit form; this is exactly what makes the Fourier transform descend to
a unitary of the quotient Hilbert space. -/
theorem connes_orbitForm_invariant (U : G → E →ₗ[ℂ] E) (F : E →ₗ[ℂ] E)
    (hF : ∀ x y : E, inner ℂ (F x) (F y) = (inner ℂ x y : ℂ))
    (hcomm : ∀ (q : G) (x : E), F (U q x) = U q⁻¹ (F x)) (f g : E) :
    connesOrbitForm U (F f) (F g) = connesOrbitForm U f g := by
  unfold connesOrbitForm
  have hcongr : (fun q : G => (inner ℂ (F f) (U q (F g)) : ℂ))
      = fun q : G => (inner ℂ f (U q⁻¹ g) : ℂ) :=
    funext fun q => connes_orbitForm_term U F hF hcomm f g q
  rw [hcongr]
  exact (Equiv.inv G).tsum_eq (fun q : G => (inner ℂ f (U q g) : ℂ))

/-- The quotient norm is preserved: the Fourier transform is isometric for the orbit form. -/
theorem connes_orbitForm_self_invariant (U : G → E →ₗ[ℂ] E) (F : E →ₗ[ℂ] E)
    (hF : ∀ x y : E, inner ℂ (F x) (F y) = (inner ℂ x y : ℂ))
    (hcomm : ∀ (q : G) (x : E), F (U q x) = U q⁻¹ (F x)) (f : E) :
    connesOrbitForm U (F f) (F f) = connesOrbitForm U f f :=
  connes_orbitForm_invariant U F hF hcomm f f

end

end GaloisForLFunctions.RHTower
