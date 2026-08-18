import GaloisForLFunctions.HTGeometry.MacbeathSheets

/-!
# The developing map is an open quotient map

Every open set of the developed space is, on each sheet, an open subset of `V`, and the developing
map sends it to a translate of that subset — so the developing map is **open**.  Being also
continuous and surjective, it is a quotient map.

This is the first half of realising the developing map as a covering map of the quotient of the
developed space by the kernel of `macbeathHom`.

* `isOpenMap_devMap` : **the developing map is open.**
* `isQuotientMap_devMap` : and therefore a quotient map.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Pointwise Topology

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- The trace of a subset of the developed space on the sheet at `g`. -/
def sheetTrace (V : Set X) (W : Set (DevSpace (G := G) V)) (g : MacbeathGroup (G := G) V) :
    Set V := {x : V | Quot.mk (DevRel (G := G) V) ⟨g, x⟩ ∈ W}

omit [ContinuousConstSMul G X] in
theorem isOpen_sheetTrace {V : Set X} {W : Set (DevSpace (G := G) V)} (hW : IsOpen W)
    (g : MacbeathGroup (G := G) V) : IsOpen (sheetTrace (G := G) V W g) := by
  have hcont : Continuous fun x : V => (Quot.mk (DevRel (G := G) V) ⟨g, x⟩ : DevSpace (G := G) V) :=
    continuous_quot_mk.comp (continuous_sigmaMk (i := g))
  exact hcont.isOpen_preimage _ hW

/-- **The developing map is open.** -/
theorem isOpenMap_devMap {V : Set X} (hVopen : IsOpen V) : IsOpenMap (devMap (G := G) V) := by
  intro W hW
  have hEq : devMap V '' W
      = ⋃ g : MacbeathGroup (G := G) V,
          (macbeathHom V g) • (Subtype.val '' (sheetTrace (G := G) V W g)) := by
    ext z
    constructor
    · rintro ⟨y, hyW, rfl⟩
      obtain ⟨p, rfl⟩ := Quot.exists_rep y
      exact mem_iUnion.2 ⟨p.1, ⟨(p.2 : X), ⟨p.2, hyW, rfl⟩, rfl⟩⟩
    · intro hz
      obtain ⟨g, hzg⟩ := mem_iUnion.1 hz
      obtain ⟨a, ⟨x, hxW, rfl⟩, rfl⟩ := hzg
      exact ⟨Quot.mk _ ⟨g, x⟩, hxW, rfl⟩
  rw [hEq]
  refine isOpen_iUnion fun g => ?_
  exact (hVopen.isOpenMap_subtype_val _ (isOpen_sheetTrace hW g)).smul _

/-- **The developing map is a quotient map.** -/
theorem isQuotientMap_devMap [ConnectedSpace X] {V : Set X} (hVopen : IsOpen V)
    (hVne : V.Nonempty) (hcover : ⋃ g : G, g • V = (univ : Set X)) :
    IsQuotientMap (devMap (G := G) V) :=
  (isOpenMap_devMap hVopen).isQuotientMap (continuous_devMap V)
    (devMap_surjective hcover hVopen hVne)

end GaloisForLFunctions.HTGeometry
