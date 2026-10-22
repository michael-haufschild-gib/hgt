import GaloisForLFunctions.RHTower.Deninger.DeningerLocalSheaf
import GaloisForLFunctions.HTGeometry.DbarExhaustionSolve

/-!
# An open subset of `ℂ^n` as a space, and the ambient extension of its sections

To make an open subset of `ℂ^n` carry sheaves whose global sections are its own sections, it has to
be treated as a space in its own right.  A section over an open set of that space is a function on a
subtype, and every analytic condition on it is stated through the ambient extension by zero: since
the open set is open in `ℂ^n`, the extension agrees with the section near each of its points, so
differentiability of the extension is the right local condition and is preserved by restriction.

* `RHTower.deningerSpace` : an open subset of `ℂ^n` as a topological space.
* `RHTower.deningerAmb` : the ambient open set attached to an open set of that space.
* `RHTower.deningerExtend` : the extension of a section by zero to all of `ℂ^n`.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat Complex

variable {n : ℕ}

/-- An open subset of `ℂ^n`, as a topological space. -/
noncomputable abbrev deningerSpace (Ω : Opens (Fin n → ℂ)) : TopCat.{0} :=
  TopCat.of ↥(Ω : Set (Fin n → ℂ))

noncomputable instance (Ω : Opens (Fin n → ℂ)) : MetricSpace (deningerSpace Ω) :=
  inferInstanceAs (MetricSpace ↥(Ω : Set (Fin n → ℂ)))

noncomputable instance (Ω : Opens (Fin n → ℂ)) : ChartedSpace (Fin n → ℂ) ↥(deningerSpace Ω) :=
  inferInstanceAs (ChartedSpace (Fin n → ℂ) ↥Ω)

instance (Ω : Opens (Fin n → ℂ)) : LocallyCompactSpace ↥(deningerSpace Ω) :=
  (Ω.2 : IsOpen (Ω : Set (Fin n → ℂ))).locallyCompactSpace

instance (Ω : Opens (Fin n → ℂ)) :
    IsManifold (modelWithCornersSelf ℝ (Fin n → ℂ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      ↥(deningerSpace Ω) :=
  inferInstanceAs (IsManifold (modelWithCornersSelf ℝ (Fin n → ℂ)) ((⊤ : ℕ∞) : WithTop ℕ∞) ↥Ω)

section Ambient

variable {Ω : Opens (Fin n → ℂ)}

theorem deningerSpace_isOpenEmbedding :
    Topology.IsOpenEmbedding (Subtype.val : ↥(Ω : Set (Fin n → ℂ)) → (Fin n → ℂ)) :=
  Ω.2.isOpenEmbedding_subtypeVal

/-- The ambient open set attached to an open set of the domain. -/
def deningerAmb (U : Opens (deningerSpace Ω)) : Opens (Fin n → ℂ) :=
  ⟨Subtype.val '' (U : Set (deningerSpace Ω)),
    deningerSpace_isOpenEmbedding.isOpenMap _ U.2⟩

theorem mem_deningerAmb {U : Opens (deningerSpace Ω)} {z : Fin n → ℂ} :
    z ∈ deningerAmb U ↔ ∃ hz : z ∈ Ω, (⟨z, hz⟩ : ↥(Ω : Set (Fin n → ℂ))) ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hz, hzU⟩
    exact ⟨⟨z, hz⟩, hzU, rfl⟩

theorem deningerAmb_mem_of_mem {U : Opens (deningerSpace Ω)} (x : ↥U) :
    (x.1.1 : Fin n → ℂ) ∈ deningerAmb U :=
  ⟨x.1, x.2, rfl⟩

theorem deningerAmb_mono {U W : Opens (deningerSpace Ω)} (h : W ≤ U) :
    deningerAmb W ≤ deningerAmb U := by
  rintro z ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

/-- The point of an open set of the domain determined by a point of the ambient open set. -/
def deningerPt {U : Opens (deningerSpace Ω)} {z : Fin n → ℂ} (hz : z ∈ deningerAmb U) : ↥U :=
  ⟨⟨z, (mem_deningerAmb.1 hz).choose⟩, (mem_deningerAmb.1 hz).choose_spec⟩

@[simp] theorem deningerPt_val {U : Opens (deningerSpace Ω)} {z : Fin n → ℂ}
    (hz : z ∈ deningerAmb U) : ((deningerPt hz).1.1 : Fin n → ℂ) = z := rfl

theorem deningerPt_eq {U : Opens (deningerSpace Ω)} (x : ↥U) :
    deningerPt (deningerAmb_mem_of_mem x) = x :=
  Subtype.ext (Subtype.ext rfl)

open Classical in
/-- The extension of a section by zero to all of `ℂ^n`. -/
noncomputable def deningerExtend {V : Type} [Zero V] {U : Opens (deningerSpace Ω)}
    (f : ↥U → V) : (Fin n → ℂ) → V :=
  fun z => if hz : z ∈ deningerAmb U then f (deningerPt hz) else 0

theorem deningerExtend_apply {V : Type} [Zero V] {U : Opens (deningerSpace Ω)} (f : ↥U → V)
    (x : ↥U) : deningerExtend f (x.1.1 : Fin n → ℂ) = f x := by
  rw [deningerExtend, dif_pos (deningerAmb_mem_of_mem x), deningerPt_eq]

theorem deningerExtend_of_mem {V : Type} [Zero V] {U : Opens (deningerSpace Ω)} (f : ↥U → V)
    {z : Fin n → ℂ} (hz : z ∈ deningerAmb U) : deningerExtend f z = f (deningerPt hz) :=
  dif_pos hz

/-- On the smaller ambient open set the extension of a restricted section agrees with the extension
of the section. -/
theorem deningerExtend_res {V : Type} [Zero V] {U W : Opens (deningerSpace Ω)} (h : W ≤ U)
    (f : ↥U → V) {z : Fin n → ℂ} (hz : z ∈ deningerAmb W) :
    deningerExtend (fun x : ↥W => f ⟨x.1, h x.2⟩) z = deningerExtend f z := by
  rw [deningerExtend_of_mem _ hz, deningerExtend_of_mem f (deningerAmb_mono h hz)]
  congr 1

/-- Near a point of the smaller open set the two extensions agree. -/
theorem deningerExtend_eventuallyEq {V : Type} [Zero V] {U W : Opens (deningerSpace Ω)}
    (h : W ≤ U) (f : ↥U → V) {z : Fin n → ℂ} (hz : z ∈ deningerAmb W) :
    ∀ᶠ y in nhds z, deningerExtend (fun x : ↥W => f ⟨x.1, h x.2⟩) y = deningerExtend f y :=
  Filter.eventually_of_mem ((deningerAmb W).2.mem_nhds hz) fun _ hy =>
    deningerExtend_res h f hy

theorem deningerExtend_zero {V : Type} [Zero V] {U : Opens (deningerSpace Ω)} :
    deningerExtend (fun _ : ↥U => (0 : V)) = fun _ : Fin n → ℂ => (0 : V) := by
  funext z
  rw [deningerExtend]
  split <;> rfl

theorem deningerExtend_add {V : Type} [AddCommGroup V] {U : Opens (deningerSpace Ω)}
    (f g : ↥U → V) :
    deningerExtend (fun x => f x + g x) = fun z => deningerExtend f z + deningerExtend g z := by
  funext z
  rw [deningerExtend, deningerExtend, deningerExtend]
  split
  · rfl
  · rw [add_zero]

theorem deningerExtend_neg {V : Type} [AddCommGroup V] {U : Opens (deningerSpace Ω)}
    (f : ↥U → V) :
    deningerExtend (fun x => -f x) = fun z => -deningerExtend f z := by
  funext z
  rw [deningerExtend, deningerExtend]
  split
  · rfl
  · rw [neg_zero]

end Ambient

end RHTower
