import GaloisForLFunctions.HTGeometry.MultiplierClosedGraph
import GaloisForLFunctions.HTGeometry.LinearPMapBoundedUnitaryTransport

/-!
# Maximal complex multiplication on scalar `L²`

Multiplication by an arbitrary complex symbol `a` on its maximal domain
`{f ∈ L² : a f ∈ L²}` is a closed operator: its graph is exactly the multiplier graph
`{(f, g) : g = a f a.e.}`, which is closed because `L²` convergence has almost everywhere
convergent subsequences.  If the symbol vanishes only on a null set the operator is injective.
Unitary conjugation transports both properties.
-/

open MeasureTheory Filter Topology
open scoped LinearPMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Maximal `L²` domain of multiplication by a complex symbol. -/
def maximalComplexL2MulDomain (μ : Measure α) (a : α → ℂ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (fun x => a x * f x) 2 μ}
  zero_mem' := by
    refine (memLp_congr_ae ?_).mpr MemLp.zero
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    rw [hx]
    simp
  add_mem' := by
    intro f g hf hg
    refine (memLp_congr_ae ?_).mpr (hf.add hg)
    filter_upwards [Lp.coeFn_add f g] with x hx
    rw [hx, Pi.add_apply, Pi.add_apply, mul_add]
  smul_mem' := by
    intro c f hf
    refine (memLp_congr_ae ?_).mpr (hf.const_mul c)
    filter_upwards [Lp.coeFn_smul c f] with x hx
    rw [hx]
    change a x * (c * (f : Lp ℂ 2 μ) x) = c * (a x * (f : Lp ℂ 2 μ) x)
    ring

/-- Multiplication by a complex symbol on its maximal `L²` domain. -/
def maximalComplexL2Mul (μ : Measure α) (a : α → ℂ) : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := maximalComplexL2MulDomain μ a
  toFun :=
    { toFun := fun f => f.property.toLp _
      map_add' := by
        intro f g
        rw [← MemLp.toLp_add f.property g.property]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_add (f : Lp ℂ 2 μ) (g : Lp ℂ 2 μ)] with x hx
        change a x * ((f : Lp ℂ 2 μ) + (g : Lp ℂ 2 μ)) x =
          ((fun y => a y * (f : Lp ℂ 2 μ) y) + fun y => a y * (g : Lp ℂ 2 μ) y) x
        rw [hx, Pi.add_apply, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul c f.property]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_smul c (f : Lp ℂ 2 μ)] with x hx
        change a x * (c • (f : Lp ℂ 2 μ)) x = (c • fun y => a y * (f : Lp ℂ 2 μ) y) x
        rw [hx, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring }

variable {μ : Measure α} {a : α → ℂ}

theorem maximalComplexL2Mul_apply_ae (f : (maximalComplexL2Mul μ a).domain) :
    (maximalComplexL2Mul μ a f : α → ℂ) =ᵐ[μ] fun x => a x * (f : Lp ℂ 2 μ) x :=
  MemLp.coeFn_toLp f.property

/-- `f` lies in the domain and is sent to `g` iff `g = a f` almost everywhere. -/
theorem mem_graph_maximalComplexL2Mul_iff (f g : Lp ℂ 2 μ) :
    (f, g) ∈ (maximalComplexL2Mul μ a).graph ↔
      (g : α → ℂ) =ᵐ[μ] fun x => a x * (f : α → ℂ) x := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨y, hy, hval⟩
    change (y : Lp ℂ 2 μ) = f at hy
    change maximalComplexL2Mul μ a y = g at hval
    rw [← hval, ← hy]
    exact maximalComplexL2Mul_apply_ae y
  · intro h
    have hmem : f ∈ (maximalComplexL2Mul μ a).domain :=
      (memLp_congr_ae h).mp (Lp.memLp g)
    refine ⟨⟨f, hmem⟩, rfl, ?_⟩
    exact Lp.ext ((maximalComplexL2Mul_apply_ae ⟨f, hmem⟩).trans h.symm)

theorem graph_maximalComplexL2Mul :
    ((maximalComplexL2Mul μ a).graph : Set (Lp ℂ 2 μ × Lp ℂ 2 μ)) = multiplierGraph a μ := by
  ext p
  exact mem_graph_maximalComplexL2Mul_iff p.1 p.2

/-- **Maximal multiplication is closed.** -/
theorem maximalComplexL2Mul_isClosed : (maximalComplexL2Mul μ a).IsClosed := by
  rw [LinearPMap.IsClosed, graph_maximalComplexL2Mul]
  exact isClosed_multiplierGraph a

/-- A symbol vanishing only on a null set gives an injective multiplication operator. -/
theorem maximalComplexL2Mul_eq_zero_iff (ha : ∀ᵐ x ∂μ, a x ≠ 0)
    (f : (maximalComplexL2Mul μ a).domain) :
    maximalComplexL2Mul μ a f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    have h0 : ∀ᵐ x ∂μ, a x * (f : Lp ℂ 2 μ) x = 0 := by
      filter_upwards [maximalComplexL2Mul_apply_ae f, Lp.coeFn_zero ℂ 2 μ] with x hx hx0
      rw [← hx, hf, hx0, Pi.zero_apply]
    have hf0 : (f : Lp ℂ 2 μ) = 0 := by
      refine Lp.ext ?_
      filter_upwards [h0, ha, Lp.coeFn_zero ℂ 2 μ] with x hx hax hx0
      rw [hx0, Pi.zero_apply]
      exact (mul_eq_zero.1 hx).resolve_left hax
    exact Subtype.ext hf0
  · rintro rfl
    exact map_zero _

end

end GaloisForLFunctions.HTGeometry
