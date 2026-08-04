import GaloisForLFunctions.HTGeometry.CDGA
import GaloisForLFunctions.HTGeometry.DirectLimitBilinear
import Mathlib.Algebra.Colimit.Module

/-!
# The colimit of a directed system of commutative differential graded algebras

A directed system of commutative differential graded algebras has, in each degree, a direct limit of
the modules of that degree, and the differentials assemble into a differential on the limit which
still squares to zero.  This is the underlying differential graded module of the colimit algebra.

* `CDGADirectedSystem` : the functoriality hypotheses of a directed system of morphisms.
* `colimDeg` : the direct limit in a degree.
* `colimD`, `colimD_comp` : the differential on the limit, and that it squares to zero.
* `colimMul` : the product on the limit, from the bilinear lifting principle.
* `colimCDGA` : the colimit algebra.
* `colimHom` : the morphism of colimit algebras induced by a compatible family of morphisms.
-/

set_option maxHeartbeats 1000000

universe u v w

namespace GaloisForLFunctions.HTGeometry

open CDGAStructure

section Colimit

variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [DecidableEq ι]
  {X : ι → ℕ → Type w} [∀ i n, AddCommGroup (X i n)] [∀ i n, Module R (X i n)]
  {A : ∀ i, CDGAStructure R (X i)}

/-- **The functoriality hypotheses of a directed system of algebras**: the morphism attached to a
relation with itself is the identity, and the morphisms compose. -/
structure CDGADirectedSystem (A : ∀ i, CDGAStructure R (X i))
    (φ : ∀ i j, i ≤ j → CDGAHom (A i) (A j)) : Prop where
  /-- The morphism of a reflexive relation is the identity. -/
  map_self : ∀ (i : ι) (h : i ≤ i) (n : ℕ) (x : X i n), (φ i i h).toFun n x = x
  /-- The morphisms compose. -/
  map_map : ∀ (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) (n : ℕ) (x : X i n),
    (φ j k hjk).toFun n ((φ i j hij).toFun n x) = (φ i k (hij.trans hjk)).toFun n x

variable (φ : ∀ i j, i ≤ j → CDGAHom (A i) (A j))

/-- The transition maps of the directed system in a given degree. -/
def degTransition (n : ℕ) (i j : ι) (h : i ≤ j) : X i n →ₗ[R] X j n := (φ i j h).mapₗ n

/-- **The direct limit of a directed system of algebras in a given degree.** -/
abbrev colimDeg (n : ℕ) := Module.DirectLimit (fun i => X i n) (degTransition φ n)

omit [DecidableEq ι] in
theorem directedSystem_deg (hsys : CDGADirectedSystem A φ) (n : ℕ) :
    DirectedSystem (fun i => X i n) (fun i j h => degTransition φ n i j h) where
  map_self := by
    intro i x
    exact hsys.map_self i le_rfl n x
  map_map := by
    intro k j i hij hjk x
    exact hsys.map_map i j k hij hjk n x

variable [∀ n : ℕ, DirectedSystem (fun i => X i n) fun i j h => degTransition φ n i j h]

/-- **The differential on the direct limit.** -/
noncomputable def colimD (n : ℕ) : colimDeg φ n →ₗ[R] colimDeg φ (n + 1) :=
  Module.DirectLimit.map (fun i => (A i).dₗ n) (fun i j h => by
    refine LinearMap.ext fun x => ?_
    show (A j).d n ((φ i j h).toFun n x) = (φ i j h).toFun (n + 1) ((A i).d n x)
    rw [(φ i j h).map_d n x])

omit [∀ n : ℕ, DirectedSystem (fun i => X i n) fun i j h => degTransition φ n i j h] in
@[simp]
theorem colimD_of (n : ℕ) (i : ι) (x : X i n) :
    colimD φ n (Module.DirectLimit.of R ι (fun i => X i n) (degTransition φ n) i x) =
      Module.DirectLimit.of R ι (fun i => X i (n + 1)) (degTransition φ (n + 1)) i
        ((A i).d n x) :=
  Module.DirectLimit.map_apply_of _ _ _

variable [IsDirectedOrder ι] [Nonempty ι]

omit [∀ n : ℕ, DirectedSystem (fun i => X i n) fun i j h => degTransition φ n i j h] in
/-- **The differential on the direct limit squares to zero**, so the limit of a directed system of
algebras is a differential graded module. -/
theorem colimD_comp (n : ℕ) : (colimD φ (n + 1)).comp (colimD φ n) = 0 := by
  refine LinearMap.ext fun ξ => ?_
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of ξ
  show colimD φ (n + 1) (colimD φ n
    (Module.DirectLimit.of R ι (fun i => X i n) (degTransition φ n) i x)) = 0
  rw [colimD_of, colimD_of, (A i).d_d n x]
  exact map_zero _

/-- The stagewise products as a family of bilinear maps. -/
def mulFamily {a b n : ℕ} (h : a + b = n) (i : ι) : X i a →ₗ[R] X i b →ₗ[R] X i n :=
  (A i).mulₗ h

omit [DecidableEq ι] [IsDirectedOrder ι] [Nonempty ι]
  [∀ n : ℕ, DirectedSystem (fun i => X i n) fun i j h => degTransition φ n i j h] in
theorem mulFamily_compat {a b n : ℕ} (h : a + b = n) (i j : ι) (hij : i ≤ j) (x : X i a)
    (y : X i b) :
    mulFamily (A := A) h j (degTransition φ a i j hij x) (degTransition φ b i j hij y) =
      degTransition φ n i j hij (mulFamily (A := A) h i x y) := by
  show (A j).mul h ((φ i j hij).toFun a x) ((φ i j hij).toFun b y) =
    (φ i j hij).toFun n ((A i).mul h x y)
  rw [(φ i j hij).map_mul h x y]

/-- **The product on the direct limit**, from the bilinear lifting principle. -/
noncomputable def colimMul {a b n : ℕ} (h : a + b = n) :
    colimDeg φ a →ₗ[R] colimDeg φ b →ₗ[R] colimDeg φ n :=
  directLimitBilinear (mulFamily (A := A) h) (mulFamily_compat φ h)

omit [Nonempty ι] in
theorem colimMul_of {a b n : ℕ} (h : a + b = n) (i : ι) (x : X i a) (y : X i b) :
    colimMul φ h (Module.DirectLimit.of R ι (fun i => X i a) (degTransition φ a) i x)
        (Module.DirectLimit.of R ι (fun i => X i b) (degTransition φ b) i y) =
      Module.DirectLimit.of R ι (fun i => X i n) (degTransition φ n) i ((A i).mul h x y) :=
  directLimitBilinear_of_of_same (mulFamily (A := A) h) (mulFamily_compat φ h) i x y

omit [∀ n : ℕ, DirectedSystem (fun i => X i n) fun i j h => degTransition φ n i j h] in
/-- Two elements of the limits in two degrees come from a common stage. -/
theorem exists_common₂ (a b : ℕ) (ξ : colimDeg φ a)
    (η : colimDeg φ b) :
    ∃ (m : ι) (u : X m a) (v : X m b),
      Module.DirectLimit.of R ι (fun i => X i a) (degTransition φ a) m u = ξ ∧
        Module.DirectLimit.of R ι (fun i => X i b) (degTransition φ b) m v = η := by
  obtain ⟨i, u, rfl⟩ := Module.DirectLimit.exists_of ξ
  obtain ⟨j, v, rfl⟩ := Module.DirectLimit.exists_of η
  obtain ⟨m, him, hjm⟩ := exists_ge_ge i j
  refine ⟨m, degTransition φ a i m him u, degTransition φ b j m hjm v, ?_, ?_⟩
  · exact Module.DirectLimit.of_f
  · exact Module.DirectLimit.of_f

omit [∀ n : ℕ, DirectedSystem (fun i => X i n) fun i j h => degTransition φ n i j h] in
/-- Three elements of the limits in three degrees come from a common stage. -/
theorem exists_common₃ (a b c : ℕ) (ξ : colimDeg φ a)
    (η : colimDeg φ b) (ζ : colimDeg φ c) :
    ∃ (m : ι) (u : X m a) (v : X m b) (w : X m c),
      Module.DirectLimit.of R ι (fun i => X i a) (degTransition φ a) m u = ξ ∧
        Module.DirectLimit.of R ι (fun i => X i b) (degTransition φ b) m v = η ∧
        Module.DirectLimit.of R ι (fun i => X i c) (degTransition φ c) m w = ζ := by
  obtain ⟨m, u, v, hu, hv⟩ := exists_common₂ φ a b ξ η
  obtain ⟨k, w, rfl⟩ := Module.DirectLimit.exists_of ζ
  obtain ⟨m', hmm', hkm'⟩ := exists_ge_ge m k
  refine ⟨m', degTransition φ a m m' hmm' u, degTransition φ b m m' hmm' v,
    degTransition φ c k m' hkm' w, ?_, ?_, ?_⟩
  · rw [Module.DirectLimit.of_f]; exact hu
  · rw [Module.DirectLimit.of_f]; exact hv
  · exact Module.DirectLimit.of_f

/-- **The colimit of a directed system of commutative differential graded algebras.** -/
noncomputable def colimCDGA : CDGAStructure R (colimDeg φ) where
  mul h x y := colimMul φ h x y
  d n := colimD φ n
  mul_add_left h x x' y := by
    show colimMul φ h (x + x') y = _
    rw [map_add, LinearMap.add_apply]
  mul_add_right h x y y' := by
    show colimMul φ h x (y + y') = _
    rw [map_add]
  mul_smul_left h c x y := by
    show colimMul φ h (c • x) y = _
    rw [map_smul, LinearMap.smul_apply]
  mul_smul_right h c x y := by
    show colimMul φ h x (c • y) = _
    rw [map_smul]
  mul_assoc h₁ h₂ h₃ h₄ x y z := by
    obtain ⟨m, u, v, w, rfl, rfl, rfl⟩ := exists_common₃ φ _ _ _ x y z
    show colimMul φ h₂ (colimMul φ h₁ _ _) _ = colimMul φ h₄ _ (colimMul φ h₃ _ _)
    rw [colimMul_of, colimMul_of, colimMul_of, colimMul_of, (A m).mul_assoc h₁ h₂ h₃ h₄]
  mul_comm h h' x y := by
    obtain ⟨m, u, v, rfl, rfl⟩ := exists_common₂ φ _ _ x y
    show colimMul φ h _ _ = _ • colimMul φ h' _ _
    rw [colimMul_of, colimMul_of, (A m).mul_comm h h', map_smul]
  d_add n x y := (colimD φ n).map_add x y
  d_smul n c x := (colimD φ n).map_smul c x
  d_d n x := LinearMap.congr_fun (colimD_comp φ n) x
  d_mul h x y := by
    obtain ⟨m, u, v, rfl, rfl⟩ := exists_common₂ φ _ _ x y
    show colimD φ _ (colimMul φ h _ _) =
      colimMul φ _ (colimD φ _ _) _ + _ • colimMul φ _ _ (colimD φ _ _)
    rw [colimMul_of, colimD_of, colimD_of, colimD_of, colimMul_of, colimMul_of,
      (A m).d_mul h u v, map_add, map_smul]

end Colimit

section ColimitHom

variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  [DecidableEq ι]
  {X : ι → ℕ → Type w} [∀ i n, AddCommGroup (X i n)] [∀ i n, Module R (X i n)]
  {A : ∀ i, CDGAStructure R (X i)} (φ : ∀ i j, i ≤ j → CDGAHom (A i) (A j))
  [∀ n : ℕ, DirectedSystem (fun i => X i n) fun i j h => degTransition φ n i j h]
  {Y : ι → ℕ → Type w} [∀ i n, AddCommGroup (Y i n)] [∀ i n, Module R (Y i n)]
  {B : ∀ i, CDGAStructure R (Y i)} (ψ : ∀ i j, i ≤ j → CDGAHom (B i) (B j))
  [∀ n : ℕ, DirectedSystem (fun i => Y i n) fun i j h => degTransition ψ n i j h]
  (Θ : ∀ i, CDGAHom (A i) (B i))
  (hΘ : ∀ (i j : ι) (hij : i ≤ j) (n : ℕ) (x : X i n),
    (Θ j).toFun n ((φ i j hij).toFun n x) = (ψ i j hij).toFun n ((Θ i).toFun n x))

include hΘ

/-- The map on the direct limits in a given degree induced by a compatible family of morphisms. -/
noncomputable def colimHomFun (n : ℕ) : colimDeg φ n →ₗ[R] colimDeg ψ n :=
  Module.DirectLimit.map (fun i => (Θ i).mapₗ n)
    (fun i j hij => LinearMap.ext fun x => hΘ i j hij n x)

omit [IsDirectedOrder ι] [Nonempty ι]
  [∀ n : ℕ, DirectedSystem (fun i => X i n) fun i j h => degTransition φ n i j h]
  [∀ n : ℕ, DirectedSystem (fun i => Y i n) fun i j h => degTransition ψ n i j h] in
@[simp]
theorem colimHomFun_of (n : ℕ) (i : ι) (x : X i n) :
    colimHomFun φ ψ Θ hΘ n (Module.DirectLimit.of R ι (fun i => X i n) (degTransition φ n) i x) =
      Module.DirectLimit.of R ι (fun i => Y i n) (degTransition ψ n) i ((Θ i).toFun n x) :=
  Module.DirectLimit.map_apply_of _ _ _

/-- **The morphism of colimit algebras induced by a compatible family of morphisms.** -/
noncomputable def colimHom : CDGAHom (colimCDGA φ) (colimCDGA ψ) where
  toFun n x := colimHomFun φ ψ Θ hΘ n x
  map_add n x y := (colimHomFun φ ψ Θ hΘ n).map_add x y
  map_smul n c x := (colimHomFun φ ψ Θ hΘ n).map_smul c x
  map_mul h x y := by
    obtain ⟨m, u, v, rfl, rfl⟩ := exists_common₂ φ _ _ x y
    show colimHomFun φ ψ Θ hΘ _ (colimMul φ h _ _) =
      colimMul ψ h (colimHomFun φ ψ Θ hΘ _ _) (colimHomFun φ ψ Θ hΘ _ _)
    rw [colimMul_of, colimHomFun_of, colimHomFun_of, colimHomFun_of, colimMul_of,
      (Θ m).map_mul h u v]
  map_d n x := by
    obtain ⟨i, u, rfl⟩ := Module.DirectLimit.exists_of x
    show colimHomFun φ ψ Θ hΘ _ (colimD φ n _) = colimD ψ n (colimHomFun φ ψ Θ hΘ _ _)
    rw [colimD_of, colimHomFun_of, colimHomFun_of, colimD_of, (Θ i).map_d n u]

end ColimitHom

end GaloisForLFunctions.HTGeometry
