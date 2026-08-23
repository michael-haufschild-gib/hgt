import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Constructions

/-!
# The projective limit topology on an adic completion

The `I`-adic completion of a ring is a submodule of the product of the discrete quotients
`R / Iⁿ`; giving it the induced topology makes it a topological ring, and the canonical map from
`R` has dense image: a neighbourhood of a point of the completion constrains only finitely many
coordinates, and a lift of the largest one already matches all the smaller ones.
-/

namespace HTGeometry

open Submodule AdicCompletion

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The quotient `R / Iⁿ`, carrying the discrete topology. -/
def AdicQuot (I : Ideal R) (n : ℕ) : Type u :=
  R ⧸ (I ^ n • ⊤ : Submodule R R)

namespace AdicQuot

instance (n : ℕ) : CommRing (AdicQuot I n) :=
  inferInstanceAs (CommRing (R ⧸ (I ^ n • ⊤ : Submodule R R)))

instance (n : ℕ) : TopologicalSpace (AdicQuot I n) := ⊥

instance (n : ℕ) : DiscreteTopology (AdicQuot I n) := ⟨rfl⟩

/-- The coordinate of an element of the completion, viewed in the discrete quotient. -/
noncomputable def coord (n : ℕ) (x : AdicCompletion I R) : AdicQuot I n :=
  AdicCompletion.eval I R n x

@[simp] theorem coord_mul (n : ℕ) (x y : AdicCompletion I R) :
    coord I n (x * y) = coord I n x * coord I n y := rfl

@[simp] theorem coord_one (n : ℕ) : coord I n 1 = 1 := rfl

end AdicQuot

open AdicQuot

/-- The projective limit topology on the adic completion. -/
noncomputable instance adicCompletionTopology : TopologicalSpace (AdicCompletion I R) :=
  TopologicalSpace.induced (fun (x : AdicCompletion I R) (n : ℕ) => coord I n x)
    (inferInstance : TopologicalSpace (∀ n : ℕ, AdicQuot I n))

theorem continuous_adicCoord (n : ℕ) : Continuous (coord I n) :=
  (continuous_apply (A := fun n : ℕ => AdicQuot I n) n).comp continuous_induced_dom

instance adicCompletion_continuousMul : ContinuousMul (AdicCompletion I R) := by
  refine ⟨?_⟩
  rw [continuous_induced_rng]
  refine continuous_pi fun n => ?_
  have : (fun p : AdicCompletion I R × AdicCompletion I R => coord I n (p.1 * p.2))
      = (fun q : AdicQuot I n × AdicQuot I n => q.1 * q.2)
        ∘ (fun p : AdicCompletion I R × AdicCompletion I R => (coord I n p.1, coord I n p.2)) := by
    funext p
    exact coord_mul I n p.1 p.2
  show Continuous fun p : AdicCompletion I R × AdicCompletion I R => coord I n (p.1 * p.2)
  rw [this]
  exact continuous_of_discreteTopology.comp
    (((continuous_adicCoord I n).comp continuous_fst).prodMk
      ((continuous_adicCoord I n).comp continuous_snd))

theorem adicCoord_of (n : ℕ) (a : R) :
    coord I n (AdicCompletion.of I R a) = Submodule.Quotient.mk a := rfl

/-- **The image of `R` in its adic completion is dense.**  A neighbourhood of a point constrains
only finitely many coordinates, and a lift of the largest constrained one reduces correctly in all
the smaller ones. -/
theorem denseRange_adicCompletion_of :
    DenseRange (fun a : R => AdicCompletion.of I R a) := by
  intro x
  rw [mem_closure_iff_nhds]
  intro U hU
  rw [nhds_induced (fun (z : AdicCompletion I R) (n : ℕ) => coord I n z) x,
    Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨s, hsfin, t, ht, hst⟩ := hV
  obtain ⟨N, hN⟩ := hsfin.bddAbove
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
    ((I ^ N • ⊤ : Submodule R R)) (AdicCompletion.eval I R N x)
  have hcoord : ∀ n ∈ s, coord I n (AdicCompletion.of I R a) = coord I n x := by
    intro n hn
    have hnN : n ≤ N := hN hn
    have h1 : AdicCompletion.transitionMap I R hnN (AdicCompletion.eval I R N x)
        = AdicCompletion.eval I R n x :=
      AdicCompletion.transitionMap_comp_eval_apply I R hnN x
    rw [← ha] at h1
    show (AdicCompletion.eval I R n (AdicCompletion.of I R a) : AdicQuot I n) = _
    rw [AdicCompletion.eval_of]
    show (Submodule.Quotient.mk a : AdicQuot I n) = AdicCompletion.eval I R n x
    rw [← h1]
    have hfac : Submodule.factorPow I R hnN
        ((I ^ N • ⊤ : Submodule R R).mkQ a) = (I ^ n • ⊤ : Submodule R R).mkQ a :=
      Submodule.factor_mk _ a
    exact hfac.symm
  refine ⟨AdicCompletion.of I R a, hVU ?_, ⟨a, rfl⟩⟩
  refine hst ?_
  intro n hn
  have := ht n
  rw [← hcoord n hn] at this
  exact mem_of_mem_nhds this

theorem adicCompletion_algebraMap_eq_of (a : R) :
    algebraMap R (AdicCompletion I R) a = AdicCompletion.of I R a := rfl

/-- **The structure map of the adic completion has dense image.** -/
theorem denseRange_algebraMap_adicCompletion :
    DenseRange (algebraMap R (AdicCompletion I R)) := by
  have : (algebraMap R (AdicCompletion I R) : R → AdicCompletion I R)
      = fun a => AdicCompletion.of I R a := funext (adicCompletion_algebraMap_eq_of I)
  rw [this]
  exact denseRange_adicCompletion_of I

end HTGeometry
