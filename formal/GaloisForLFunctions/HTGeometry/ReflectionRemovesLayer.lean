import GaloisForLFunctions.HTGeometry.ReducedH0Components

/-!
# Reflection removes exactly one reduced-`H⁰` layer

The Stanley–Reisner Hochster mechanism of `hypertranscendental-hochster-source-coherence-duality`
removes exactly one face layer per reflection.  At degree zero this is a clean dimension count on the
combinatorial side: imposing one new incidence `a ∼ b` between two previously separate connected
components cuts the reduced zeroth cohomology by exactly one.

Concretely, the extra constraint is the kernel of the linear functional `f ↦ f a − f b` on the
component-constant `0`-cochains `componentConstant G F`.  When `a` and `b` lie in different components
this functional is nonzero (witnessed by the indicator of `a`'s component), so its kernel — the
`0`-cochains of the edge-augmented complex — has dimension `card (components) − 1`, one less than
`componentConstant G F`.
-/

namespace GaloisForLFunctions

open SimpleGraph

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (F : Type*) [Field F]

/-- The `0`-cochain that is `1` on the connected component of `a` and `0` elsewhere; it is
component-constant. -/
def componentIndicator (a : V) : componentConstant G F :=
  ⟨fun v => if G.Reachable a v then (1 : F) else 0, fun u w huw => by
    have hiff : G.Reachable a u ↔ G.Reachable a w :=
      ⟨fun h => h.trans huw.reachable, fun h => h.trans huw.reachable.symm⟩
    exact if_congr hiff rfl rfl⟩

/-- The reflection functional `f ↦ f a − f b` on component-constant `0`-cochains. -/
def diffFunctional (a b : V) : componentConstant G F →ₗ[F] F where
  toFun f := (f : V → F) a - (f : V → F) b
  map_add' f g := by simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' r f := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem diffFunctional_apply (a b : V) (f : componentConstant G F) :
    diffFunctional G F a b f = (f : V → F) a - (f : V → F) b := rfl

theorem diffFunctional_componentIndicator (a b : V) (hab : ¬ G.Reachable a b) :
    diffFunctional G F a b (componentIndicator G F a) = 1 := by
  rw [diffFunctional_apply]
  show (if G.Reachable a a then (1 : F) else 0) - (if G.Reachable a b then (1 : F) else 0) = 1
  rw [if_pos (Reachable.refl a), if_neg hab]; ring

/-- **Reflection removes one reduced-`H⁰` layer.**  If `a` and `b` lie in different connected
components, then the `0`-cochains satisfying the extra incidence `f a = f b` — the component-constant
cochains of the edge-augmented complex — have dimension `card (components) − 1`, exactly one less than
`componentConstant G F`. -/
theorem finrank_diffFunctional_ker (a b : V) (hab : ¬ G.Reachable a b) :
    Module.finrank F (LinearMap.ker (diffFunctional G F a b))
      = Fintype.card G.ConnectedComponent - 1 := by
  have hone : (1 : F) ∈ LinearMap.range (diffFunctional G F a b) :=
    LinearMap.mem_range.mpr ⟨componentIndicator G F a,
      diffFunctional_componentIndicator G F a b hab⟩
  have hrange_top : LinearMap.range (diffFunctional G F a b) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro c
    have h := (LinearMap.range (diffFunctional G F a b)).smul_mem c hone
    simpa using h
  have hrange : Module.finrank F (LinearMap.range (diffFunctional G F a b)) = 1 := by
    rw [hrange_top, finrank_top, Module.finrank_self]
  have hrn := LinearMap.finrank_range_add_finrank_ker (diffFunctional G F a b)
  rw [hrange, finrank_componentConstant] at hrn
  omega

end

end GaloisForLFunctions
