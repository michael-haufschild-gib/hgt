import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Cofinite opens of a character projection

The character space over an arithmetic open is the preimage of that open under the projection: it
is open, it grows with the open, and — because every Frobenius map and every group element of the
suspension action preserves the projection — it is stable under all of them.

In the Frobenius colimit, whose topology is the inductive limit, the preimage of an arithmetic open
is open exactly because its preimage in each chart is the chart-level character space over that
open.  Both facts are statements about a projection commuting with the transition maps; nothing
about the internal structure of the character space is used.

* `deningerCharacterOver`, `_isOpen`, `_mono` : the character space over an open.
* `deningerCharacterOver_map_mem`, `_smul_mem` : Frobenius and suspension stability.
* `deningerColimitCharacterOver_isOpen` : openness in the inductive-limit topology.
-/

namespace RHTower

section CharacterProjection

variable {E S : Type*}

/-- The character space over an arithmetic open: the preimage under the projection. -/
def deningerCharacterOver (pr : E → S) (U : Set S) : Set E := pr ⁻¹' U

@[simp]
theorem deningerCharacterOver_mem {pr : E → S} {U : Set S} {x : E} :
    x ∈ deningerCharacterOver pr U ↔ pr x ∈ U := Iff.rfl

/-- **The character space over an open is open.** -/
theorem deningerCharacterOver_isOpen [TopologicalSpace E] [TopologicalSpace S] {pr : E → S}
    (hpr : Continuous pr) {U : Set S} (hU : IsOpen U) :
    IsOpen (deningerCharacterOver pr U) :=
  hU.preimage hpr

/-- It grows with the open, which gives the functoriality in `U_M ⊆ U_N`. -/
theorem deningerCharacterOver_mono (pr : E → S) {U V : Set S} (h : U ⊆ V) :
    deningerCharacterOver pr U ⊆ deningerCharacterOver pr V := fun _ hx => h hx

/-- **Frobenius stability.**  A map preserving the projection preserves the character space over
every open, since it does not move the underlying scheme point. -/
theorem deningerCharacterOver_map_mem {pr : E → S} (F : E → E) (hF : ∀ x, pr (F x) = pr x)
    (U : Set S) {x : E} (hx : x ∈ deningerCharacterOver pr U) :
    F x ∈ deningerCharacterOver pr U := by
  show pr (F x) ∈ U
  rw [hF x]
  exact hx

theorem deningerCharacterOver_image_subset {pr : E → S} (F : E → E) (hF : ∀ x, pr (F x) = pr x)
    (U : Set S) : F '' deningerCharacterOver pr U ⊆ deningerCharacterOver pr U := by
  rintro _ ⟨x, hx, rfl⟩
  exact deningerCharacterOver_map_mem F hF U hx

/-- **Suspension stability.**  If the group action preserves the projection, the character space
over an open is a saturated invariant subset for it. -/
theorem deningerCharacterOver_smul_mem {G : Type*} [Monoid G] [MulAction G E] {pr : E → S}
    (hG : ∀ (g : G) (x : E), pr (g • x) = pr x) (U : Set S) (g : G) {x : E}
    (hx : x ∈ deningerCharacterOver pr U) : g • x ∈ deningerCharacterOver pr U := by
  show pr (g • x) ∈ U
  rw [hG g x]
  exact hx

end CharacterProjection

section FrobeniusColimit

variable {ι : Type*} {X : ι → Type*} [∀ n, TopologicalSpace (X n)]
variable {C S : Type*} [TopologicalSpace S]

/-- **Openness in the Frobenius colimit.**  If the colimit carries the inductive-limit topology and
its projection restricts to the chart projections, then the character space over an arithmetic open
is open in the colimit, because in every chart it is the chart-level character space. -/
theorem deningerColimitCharacterOver_isOpen [tC : TopologicalSpace C] (iota : ∀ n, X n → C)
    (prC : C → S) (pr : ∀ n, X n → S) (hcompat : ∀ n x, prC (iota n x) = pr n x)
    (hpr : ∀ n, Continuous (pr n))
    (hcolim : tC = ⨆ n, TopologicalSpace.coinduced (iota n) inferInstance)
    {U : Set S} (hU : IsOpen U) : IsOpen (deningerCharacterOver prC U) := by
  subst hcolim
  rw [isOpen_iSup_iff]
  intro n
  rw [isOpen_coinduced]
  have hpre : iota n ⁻¹' deningerCharacterOver prC U = deningerCharacterOver (pr n) U := by
    ext x
    show prC (iota n x) ∈ U ↔ pr n x ∈ U
    rw [hcompat n x]
  rw [hpre]
  exact deningerCharacterOver_isOpen (hpr n) hU

end FrobeniusColimit

end RHTower
