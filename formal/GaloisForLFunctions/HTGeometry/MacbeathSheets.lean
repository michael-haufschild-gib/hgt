import GaloisForLFunctions.HTGeometry.MacbeathOneStep

/-!
# The sheets of the developing space

Over the open set `φ(h)·V` the developed space breaks into one **sheet** for every `h` with a fixed
image under `macbeathHom`.  Two points of the same sheet are equal only if they were equal already,
distinct sheets are disjoint, and each sheet is open — the images of open subsets of `V` are open,
because the gluing relation is one step and each step is given by a homeomorphism of `X`.

* `sheet` : the sheet at `h`, as the image of `V`.
* `devSpace_mk_eq_mk_of_macbeathHom_eq` : **sheets with the same image separate points.**
* `isOpen_sheetImage` : **the image of an open subset of `V` is open.**
-/

namespace GaloisForLFunctions.HTGeometry

open Set Pointwise

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- **Sheets with the same image under `macbeathHom` separate points.** -/
theorem devSpace_mk_eq_mk_of_macbeathHom_eq {V : Set X} (hVne : V.Nonempty)
    {h h' : MacbeathGroup (G := G) V} (hφ : macbeathHom V h = macbeathHom V h') {y y' : V}
    (heq : (Quot.mk (DevRel (G := G) V) ⟨h, y⟩ : DevSpace (G := G) V) = Quot.mk _ ⟨h', y'⟩) :
    h = h' ∧ y = y' := by
  rw [devSpace_mk_eq_iff hVne] at heq
  obtain ⟨γ, hγ, hy, hg⟩ := heq
  have hγ1 : γ = 1 := by
    have := congrArg (macbeathHom V) hg
    rw [map_mul, macbeathHom_of, ← hφ] at this
    have h1 : macbeathHom V h * (1 : G) = macbeathHom V h * γ := by
      rw [mul_one]; exact this
    exact (mul_left_cancel h1).symm
  subst hγ1
  have hg' : h' = h * macbeathOf V ⟨(1 : G), hγ⟩ := hg
  have hy' : (y' : X) = ((1 : G))⁻¹ • (y : X) := hy
  refine ⟨?_, ?_⟩
  · rw [hg', show (⟨(1 : G), hγ⟩ : meetSet (G := G) V) = ⟨(1 : G), one_mem_meetSet hVne⟩ from rfl,
      macbeathOf_one hVne, mul_one]
  · refine Subtype.ext ?_
    rw [hy', inv_one, one_smul]

/-- The image in the developed space of a subset of `V`, on the sheet at `h`. -/
def sheetImage (V : Set X) (h : MacbeathGroup (G := G) V) (O : Set X) :
    Set (DevSpace (G := G) V) :=
  {z | ∃ y : V, (y : X) ∈ O ∧ z = Quot.mk _ ⟨h, y⟩}

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem preimage_sheetImage {V : Set X} (hVne : V.Nonempty) (h : MacbeathGroup (G := G) V)
    (O : Set X) :
    (Quot.mk (DevRel (G := G) V)) ⁻¹' (sheetImage V h O)
      = {p : DevSheet (G := G) V | ∃ (γ : G) (hγ : γ ∈ meetSet (G := G) V),
          h = p.1 * macbeathOf V ⟨γ, hγ⟩ ∧ γ⁻¹ • (p.2 : X) ∈ O ∩ V} := by
  ext p
  constructor
  · rintro ⟨y, hyO, hy⟩
    rw [devSpace_mk_eq_iff hVne] at hy
    obtain ⟨γ, hγ, hxy, hg⟩ := hy
    exact ⟨γ, hγ, hg, by rw [← hxy]; exact ⟨hyO, y.2⟩⟩
  · rintro ⟨γ, hγ, hg, hmem⟩
    refine ⟨⟨γ⁻¹ • (p.2 : X), hmem.2⟩, hmem.1, ?_⟩
    rw [devSpace_mk_eq_iff hVne]
    exact ⟨γ, hγ, rfl, hg⟩

/-- **The image of an open subset of `V` on a sheet is open.** -/
theorem isOpen_sheetImage {V : Set X} (hVne : V.Nonempty) (hVopen : IsOpen V)
    (h : MacbeathGroup (G := G) V) {O : Set X} (hO : IsOpen O) :
    IsOpen (sheetImage (G := G) V h O) := by
  classical
  rw [isOpen_coinduced, preimage_sheetImage hVne]
  rw [isOpen_sigma_iff]
  intro g
  have hrw : (Sigma.mk g) ⁻¹' {p : DevSheet (G := G) V | ∃ (γ : G) (hγ : γ ∈ meetSet (G := G) V),
        h = p.1 * macbeathOf V ⟨γ, hγ⟩ ∧ γ⁻¹ • (p.2 : X) ∈ O ∩ V}
      = ⋃ (γ : meetSet (G := G) V), ⋃ (_ : h = g * macbeathOf V γ),
          (fun x : V => ((γ : G))⁻¹ • (x : X)) ⁻¹' (O ∩ V) := by
    ext x
    constructor
    · rintro ⟨γ, hγ, hg, hmem⟩
      exact mem_iUnion.2 ⟨⟨γ, hγ⟩, mem_iUnion.2 ⟨hg, hmem⟩⟩
    · intro hx
      obtain ⟨γ, hx'⟩ := mem_iUnion.1 hx
      obtain ⟨hg, hmem⟩ := mem_iUnion.1 hx'
      exact ⟨(γ : G), γ.2, hg, hmem⟩
  rw [hrw]
  refine isOpen_iUnion fun γ => isOpen_iUnion fun _ => ?_
  exact (((continuous_const_smul ((γ : G))⁻¹).comp continuous_subtype_val).isOpen_preimage _
    (hO.inter hVopen))

end GaloisForLFunctions.HTGeometry
