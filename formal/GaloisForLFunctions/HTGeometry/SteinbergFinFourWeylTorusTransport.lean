import GaloisForLFunctions.HTGeometry.SteinbergFinFourTorusNormalForm
import GaloisForLFunctions.HTGeometry.SteinbergTWTClosureFinFourWeyl

/-!
# Weyl transport of the rank-four torus subgroup

The signed-root action of a Weyl word upgrades to an exact transport formula for Weyl factors.
Although a conjugated torus factor need not be a single torus factor, its resulting two-Weyl
word is a product of torus factors. Thus the full rank-four torus subgroup is invariant under
conjugation by every signed Weyl word.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

/-- Exact transport of a Weyl factor through a signed Weyl word. -/
theorem fin4_weylWord_conj_weyl (word : SteinbergWeylWord F (Fin 4))
    {p q : Fin 4} (hpq : p ≠ q) (u : Fˣ) :
    word.eval * steinbergWeyl hpq u * word.eval⁻¹
      = steinbergWeyl (word.perm.injective.ne_iff.mpr hpq)
          (word.scale p * (word.scale q)⁻¹ * u) := by
  let hspare : ∀ i j : Fin 4, i ≠ j → ∃ m : Fin 4, i ≠ m ∧ j ≠ m := by
    intro i j hij
    obtain ⟨m, hmi, hmj⟩ := exists_third_index (by decide) i j
    exact ⟨m, hmi.symm, hmj.symm⟩
  let hσ : word.perm p ≠ word.perm q := word.perm.injective.ne_iff.mpr hpq
  let r : Fˣ := word.scale p * (word.scale q)⁻¹ * u
  have hpos := word.conj_root hspare hpq (u : F)
  have hneg := word.conj_root hspare (Ne.symm hpq) (-(((u⁻¹ : Fˣ) : F)))
  have hrval : (word.scale p : F) * ((word.scale q)⁻¹ : F) * (u : F) = (r : F) := by
    simp [r]
  have hrneg : (word.scale q : F) * ((word.scale p)⁻¹ : F) * -(((u⁻¹ : Fˣ) : F))
      = -(((r⁻¹ : Fˣ) : F)) := by
    simp [r, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  change word.eval * steinbergWeyl hpq u * word.eval⁻¹ = steinbergWeyl hσ r
  rw [steinbergWeyl]
  calc word.eval
        * (steinbergX hpq (u : F) * steinbergX (Ne.symm hpq) (-(((u⁻¹ : Fˣ) : F)))
          * steinbergX hpq (u : F))
        * word.eval⁻¹
      = (word.eval * steinbergX hpq (u : F) * word.eval⁻¹)
        * (word.eval * steinbergX (Ne.symm hpq) (-(((u⁻¹ : Fˣ) : F))) * word.eval⁻¹)
        * (word.eval * steinbergX hpq (u : F) * word.eval⁻¹) := by group
    _ = steinbergX hσ (r : F) * steinbergX (Ne.symm hσ) (-(((r⁻¹ : Fˣ) : F)))
        * steinbergX hσ (r : F) := by
      rw [hpos, hneg, hrval, hrneg]

/-- Two same-root Weyl factors with opposite second parameter form a torus word. -/
theorem fin4_weyl_mul_weyl_neg_mem_torus {i j : Fin 4} (hij : i ≠ j) (a b : Fˣ) :
    steinbergWeyl hij a * steinbergWeyl hij (-b) ∈ fin4TorusSubgroup (F := F) := by
  obtain ⟨k, hik, hjk⟩ := exists_third_index (by decide) i j
  have hone : steinbergWeyl hij (1 : Fˣ) * steinbergWeyl hij (-1 : Fˣ) = 1 := by
    simpa [steinbergTorus] using steinbergTorus_one hij
  have hone_eq : steinbergWeyl hij (1 : Fˣ) = (steinbergWeyl hij (-1 : Fˣ))⁻¹ :=
    eq_inv_of_mul_eq_one_left hone
  have hsquare : steinbergWeyl hij (1 : Fˣ) * steinbergWeyl hij (1 : Fˣ)
      = (steinbergTorus hij (-1 : Fˣ))⁻¹ := by
    calc
      steinbergWeyl hij (1 : Fˣ) * steinbergWeyl hij (1 : Fˣ)
        = (steinbergWeyl hij (-1 : Fˣ))⁻¹ * (steinbergWeyl hij (-1 : Fˣ))⁻¹ := by
          rw [hone_eq]
      _ = (steinbergWeyl hij (-1 : Fˣ) * steinbergWeyl hij (-1 : Fˣ))⁻¹ := by
          rw [mul_inv_rev]
      _ = (steinbergTorus hij (-1 : Fˣ))⁻¹ := by rw [steinbergTorus]
  have hconj := steinbergTorus_one_conj hij (Ne.symm hik) (Ne.symm hjk) (-b)
  have ha : steinbergTorus hij a ∈ fin4TorusSubgroup (F := F) :=
    Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩
  have hconj_mem : steinbergWeyl hij (1 : Fˣ) * steinbergTorus hij (-b)
      * (steinbergWeyl hij (1 : Fˣ))⁻¹ ∈ fin4TorusSubgroup (F := F) := by
    rw [hconj]
    exact (fin4TorusSubgroup (F := F)).mul_mem
      (Subgroup.subset_closure ⟨j, i, Ne.symm hij, -(-b), rfl⟩)
      ((fin4TorusSubgroup (F := F)).inv_mem
        (Subgroup.subset_closure ⟨j, i, Ne.symm hij, (-1 : Fˣ), rfl⟩))
  have hsquare_mem : steinbergWeyl hij (1 : Fˣ) * steinbergWeyl hij (1 : Fˣ)
      ∈ fin4TorusSubgroup (F := F) := by
    rw [hsquare]
    exact (fin4TorusSubgroup (F := F)).inv_mem
      (Subgroup.subset_closure ⟨i, j, hij, (-1 : Fˣ), rfl⟩)
  rw [fin4_weyl_eq_torus_mul_simple hij a, fin4_weyl_eq_torus_mul_simple hij (-b)]
  rw [show steinbergTorus hij a * steinbergWeyl hij (1 : Fˣ)
      * (steinbergTorus hij (-b) * steinbergWeyl hij (1 : Fˣ))
    = steinbergTorus hij a
      * (steinbergWeyl hij (1 : Fˣ) * steinbergTorus hij (-b)
        * (steinbergWeyl hij (1 : Fˣ))⁻¹)
      * (steinbergWeyl hij (1 : Fˣ) * steinbergWeyl hij (1 : Fˣ)) by group]
  exact (fin4TorusSubgroup (F := F)).mul_mem
    ((fin4TorusSubgroup (F := F)).mul_mem ha hconj_mem) hsquare_mem

/-- Every signed Weyl word normalizes the full rank-four torus subgroup. -/
theorem fin4_weylWord_conj_torus_mem (word : SteinbergWeylWord F (Fin 4))
    {p q : Fin 4} (hpq : p ≠ q) (u : Fˣ) :
    word.eval * steinbergTorus hpq u * word.eval⁻¹ ∈ fin4TorusSubgroup (F := F) := by
  let hσ : word.perm p ≠ word.perm q := word.perm.injective.ne_iff.mpr hpq
  let α : Fˣ := word.scale p * (word.scale q)⁻¹
  have hu := fin4_weylWord_conj_weyl word hpq u
  have hneg := fin4_weylWord_conj_weyl word hpq (-1 : Fˣ)
  have hneg' : word.eval * steinbergWeyl hpq (-1 : Fˣ) * word.eval⁻¹
      = steinbergWeyl hσ (-α) := by
    simpa [α] using hneg
  rw [steinbergTorus]
  have hconj : word.eval * (steinbergWeyl hpq u * steinbergWeyl hpq (-1 : Fˣ))
      * word.eval⁻¹
      = (word.eval * steinbergWeyl hpq u * word.eval⁻¹)
        * (word.eval * steinbergWeyl hpq (-1 : Fˣ) * word.eval⁻¹) := by group
  rw [hconj, hu, hneg']
  exact fin4_weyl_mul_weyl_neg_mem_torus hσ (α * u) α

/-- Conjugation by a signed Weyl word preserves every product of torus factors. -/
theorem fin4_weylWord_conj_torusSubgroup_mem (word : SteinbergWeylWord F (Fin 4))
    {t : SteinbergGroup F (Fin 4)} (ht : t ∈ fin4TorusSubgroup (F := F)) :
    word.eval * t * word.eval⁻¹ ∈ fin4TorusSubgroup (F := F) := by
  apply Subgroup.closure_induction
    (p := fun t _ => word.eval * t * word.eval⁻¹ ∈ fin4TorusSubgroup (F := F))
    ?_ ?_ ?_ ?_ ht
  · rintro x ⟨p, q, hpq, u, rfl⟩
    exact fin4_weylWord_conj_torus_mem word hpq u
  · simp
  · intro x y _ _ hx hy
    rw [show word.eval * (x * y) * word.eval⁻¹
      = (word.eval * x * word.eval⁻¹) * (word.eval * y * word.eval⁻¹) by group]
    exact (fin4TorusSubgroup (F := F)).mul_mem hx hy
  · intro x _ hx
    rw [show word.eval * x⁻¹ * word.eval⁻¹ = (word.eval * x * word.eval⁻¹)⁻¹ by group]
    exact (fin4TorusSubgroup (F := F)).inv_mem hx

/-- The subgroup generated by the unit-parameter Weyl factors. -/
def fin4SimpleWeylSubgroup : Subgroup (SteinbergGroup F (Fin 4)) :=
  Subgroup.closure {x | ∃ (i j : Fin 4) (hij : i ≠ j), x = steinbergWeyl hij (1 : Fˣ)}

/-- A group element preserves the torus subgroup under conjugation in both directions. -/
def fin4NormalizesTorus (s : SteinbergGroup F (Fin 4)) : Prop :=
  (∀ t ∈ fin4TorusSubgroup (F := F), s * t * s⁻¹ ∈ fin4TorusSubgroup (F := F))
    ∧ ∀ t ∈ fin4TorusSubgroup (F := F), s⁻¹ * t * s ∈ fin4TorusSubgroup (F := F)

theorem fin4_simpleWeyl_normalizes_torus {s : SteinbergGroup F (Fin 4)}
    (hs : s ∈ fin4SimpleWeylSubgroup (F := F)) :
    fin4NormalizesTorus (F := F) s := by
  apply Subgroup.closure_induction (p := fun s _ => fin4NormalizesTorus (F := F) s)
    ?_ ?_ ?_ ?_ hs
  · rintro s ⟨i, j, hij, rfl⟩
    constructor
    · intro t ht
      let word : SteinbergWeylWord F (Fin 4) := .snoc .one i j hij (1 : Fˣ)
      simpa [word, SteinbergWeylWord.eval] using
        fin4_weylWord_conj_torusSubgroup_mem word ht
    · intro t ht
      let word : SteinbergWeylWord F (Fin 4) := .snoc .one i j hij (-1 : Fˣ)
      have hinv : (steinbergWeyl hij (1 : Fˣ))⁻¹ = steinbergWeyl hij (-1 : Fˣ) :=
        (steinbergWeyl_neg hij (1 : Fˣ)).symm
      have hinv_neg : (steinbergWeyl hij (-1 : Fˣ))⁻¹ = steinbergWeyl hij (1 : Fˣ) :=
        by simpa using (steinbergWeyl_neg hij (-1 : Fˣ)).symm
      rw [hinv]
      simpa [word, SteinbergWeylWord.eval, hinv, hinv_neg] using
        fin4_weylWord_conj_torusSubgroup_mem word ht
  · constructor <;> intro t ht <;> simpa using ht
  · rintro x y _ _ ⟨hxf, hxb⟩ ⟨hyf, hyb⟩
    constructor
    · intro t ht
      rw [show (x * y) * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ by group]
      exact hxf _ (hyf _ ht)
    · intro t ht
      rw [show (x * y)⁻¹ * t * (x * y) = y⁻¹ * (x⁻¹ * t * x) * y by group]
      exact hyb _ (hxb _ ht)
  · rintro x _ ⟨hxf, hxb⟩
    constructor
    · intro t ht
      simpa using hxb t ht
    · intro t ht
      simpa using hxf t ht

/-- A Weyl-word element has a torus times simple-Weyl normal form. -/
def fin4WeylTorusSimpleNormal (x : SteinbergGroup F (Fin 4)) : Prop :=
  ∃ t ∈ fin4TorusSubgroup (F := F), ∃ s ∈ fin4SimpleWeylSubgroup (F := F), x = t * s

theorem fin4_weylWordSubgroup_torus_simple_normal {x : SteinbergGroup F (Fin 4)}
    (hx : x ∈ steinbergWeylWordSubgroup (F := F) (n := Fin 4)) :
    fin4WeylTorusSimpleNormal (F := F) x := by
  apply Subgroup.closure_induction
    (p := fun x _ => fin4WeylTorusSimpleNormal (F := F) x)
    ?_ ?_ ?_ ?_ hx
  · rintro x ⟨i, j, hij, u, rfl⟩
    refine ⟨steinbergTorus hij u, Subgroup.subset_closure ⟨i, j, hij, u, rfl⟩,
      steinbergWeyl hij (1 : Fˣ), Subgroup.subset_closure ⟨i, j, hij, rfl⟩, ?_⟩
    exact fin4_weyl_eq_torus_mul_simple hij u
  · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
  · rintro x y _ _ ⟨tx, htx, sx, hsx, hxeq⟩ ⟨ty, hty, sy, hsy, hyeq⟩
    refine ⟨tx * (sx * ty * sx⁻¹),
      (fin4TorusSubgroup (F := F)).mul_mem htx
        ((fin4_simpleWeyl_normalizes_torus hsx).1 ty hty),
      sx * sy, (fin4SimpleWeylSubgroup (F := F)).mul_mem hsx hsy, ?_⟩
    rw [hxeq, hyeq]
    group
  · rintro x _ ⟨tx, htx, sx, hsx, hxeq⟩
    refine ⟨sx⁻¹ * tx⁻¹ * sx,
      (fin4_simpleWeyl_normalizes_torus hsx).2 tx⁻¹
        ((fin4TorusSubgroup (F := F)).inv_mem htx),
      sx⁻¹, (fin4SimpleWeylSubgroup (F := F)).inv_mem hsx, ?_⟩
    rw [hxeq]
    group

end GaloisForLFunctions.HTGeometry
