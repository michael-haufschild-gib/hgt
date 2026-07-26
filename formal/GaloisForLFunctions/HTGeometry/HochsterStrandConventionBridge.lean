import GaloisForLFunctions.HTGeometry.HochsterStrandDegreeThree
import GaloisForLFunctions.HTGeometry.HochsterStrandGeneralDegree

/-!
# The two Koszul conventions define the same boundaries

Two presentations of the first Koszul boundary coexist in this development.  The concrete one indexes
`2`-chains by matrices and antisymmetrizes inside the differential,

`srKoszulBoundary facets c i = ∑_j (c i j − c j i) x_j`,

while the degree-uniform one indexes chains by tuples and contracts the first slot of an *alternating*
tensor, `koszulD x b w = ∑_k b (k ∷ w) x_k`.  All the concrete Hochster results (`Tor₁`, `Tor₂`, the
cycle families) are stated in the first; the degree-uniform strand equivalence is stated in the second.

This file shows the two produce the **same submodule of boundaries**, so the results are about one
object and not two:

* `tensorOfMatrix` / `matrixOfTensor` — the translation, with `matrixOfTensor_tensorOfMatrix`;
* `isAltTensor_tensorOfMatrix` — an antisymmetric matrix with zero diagonal becomes an alternating
  tensor (on `Fin 2` there is only one transposition, and non-injectivity means the two entries
  coincide);
* `matrixOfTensor_antisymm`, `matrixOfTensor_diag` — and conversely;
* `srKoszulBoundary_exists_iff_mem_koszulBoundaries` — the concrete boundary set
  `{srKoszulBoundary facets c}` is exactly the degree-`0` Koszul boundary submodule of the alternating
  complex, under the identification `α ≃ (Fin 1 → α)`.

The sign flip between the two is intrinsic and matches the one in `koszulD_strandTensor`: `koszulD`
contracts the first slot, so it reads the transposed matrix.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] [Fintype α] {F : Type*} [CommRing F]

/-! ### Translating matrices and `Fin 2`-tensors -/

/-- The `Fin 2`-tensor attached to a matrix. -/
def tensorOfMatrix {S : Type*} (a : α → α → S) : (Fin 2 → α) → S :=
  fun v => a (v 0) (v 1)

/-- The matrix attached to a `Fin 2`-tensor. -/
def matrixOfTensor {S : Type*} (b : (Fin 2 → α) → S) : α → α → S :=
  fun i j => b (Fin.cons i (fun _ => j))

omit [DecidableEq α] [LinearOrder α] [Fintype α] in
/-- The second entry of a `Fin 2`-tuple built by `Fin.cons`. -/
theorem cons_one {S : Type*} (i j : S) : (Fin.cons i (fun _ => j) : Fin 2 → S) 1 = j := by
  rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from Fin.succ_zero_eq_one.symm, Fin.cons_succ]

omit [DecidableEq α] [LinearOrder α] [Fintype α] in
/-- The translations are inverse to each other. -/
theorem matrixOfTensor_tensorOfMatrix {S : Type*} (a : α → α → S) :
    matrixOfTensor (tensorOfMatrix a) = a := by
  funext i j
  show tensorOfMatrix a (Fin.cons i (fun _ => j)) = a i j
  show a ((Fin.cons i (fun _ => j) : Fin 2 → α) 0) ((Fin.cons i (fun _ => j) : Fin 2 → α) 1) = a i j
  rw [Fin.cons_zero, cons_one]

omit [DecidableEq α] [LinearOrder α] [Fintype α] in
/-- Swapping the two slots of a `Fin 2`-tuple built by `Fin.cons`. -/
theorem cons_comp_swap_two {S : Type*} (i j : S) :
    (Fin.cons j (fun _ => i) : Fin 2 → S)
      = (Fin.cons i (fun _ => j) : Fin 2 → S) ∘ ⇑(Equiv.swap (0 : Fin 2) 1) := by
  funext t
  fin_cases t
  · show (Fin.cons j (fun _ => i) : Fin 2 → S) 0
        = (Fin.cons i (fun _ => j) : Fin 2 → S) (Equiv.swap (0 : Fin 2) 1 0)
    rw [Equiv.swap_apply_left, Fin.cons_zero, cons_one]
  · show (Fin.cons j (fun _ => i) : Fin 2 → S) 1
        = (Fin.cons i (fun _ => j) : Fin 2 → S) (Equiv.swap (0 : Fin 2) 1 1)
    rw [Equiv.swap_apply_right, Fin.cons_zero, cons_one]

omit [LinearOrder α] [Fintype α] in
/-- On `Fin 2` every transposition is the transposition of the two slots. -/
theorem swap_two_eq {i j : Fin 2} (hij : i ≠ j) :
    Equiv.swap i j = Equiv.swap (0 : Fin 2) 1 := by
  fin_cases i <;> fin_cases j <;> simp_all [Equiv.swap_comm]

omit [LinearOrder α] [Fintype α] in
/-- A non-injective `Fin 2`-tuple has equal entries. -/
theorem eq_of_not_injective_two {S : Type*} {v : Fin 2 → S} (hv : ¬ Function.Injective v) :
    v 0 = v 1 := by
  by_contra hne
  exact hv (by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all)

/-! ### The translation respects alternation -/

omit [DecidableEq α] [LinearOrder α] [Fintype α] in
/-- An antisymmetric matrix with vanishing diagonal becomes an alternating `Fin 2`-tensor. -/
theorem isAltTensor_tensorOfMatrix {S : Type*} [CommRing S] {a : α → α → S}
    (hanti : ∀ i j, a i j + a j i = 0) (hdiag : ∀ i, a i i = 0) :
    IsAltTensor (tensorOfMatrix a) := by
  refine ⟨fun v i j hij => ?_, fun v hv => ?_⟩
  · rw [swap_two_eq hij]
    show a ((v ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) 0) ((v ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) 1)
      = - a (v 0) (v 1)
    show a (v (Equiv.swap (0 : Fin 2) 1 0)) (v (Equiv.swap (0 : Fin 2) 1 1)) = - a (v 0) (v 1)
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact eq_neg_of_add_eq_zero_left (hanti (v 1) (v 0))
  · show a (v 0) (v 1) = 0
    rw [← eq_of_not_injective_two hv]
    exact hdiag (v 0)

omit [DecidableEq α] [LinearOrder α] [Fintype α] in
/-- The matrix of an alternating tensor is antisymmetric. -/
theorem matrixOfTensor_antisymm {S : Type*} [CommRing S] {b : (Fin 2 → α) → S}
    (hb : IsAltTensor b) (i j : α) :
    matrixOfTensor b i j + matrixOfTensor b j i = 0 := by
  have h := hb.swap_neg (Fin.cons i (fun _ => j) : Fin 2 → α) 0 1 (by decide)
  show b (Fin.cons i (fun _ => j)) + b (Fin.cons j (fun _ => i)) = 0
  rw [cons_comp_swap_two i j, h]
  ring

omit [DecidableEq α] [LinearOrder α] [Fintype α] in
/-- The matrix of an alternating tensor has vanishing diagonal. -/
theorem matrixOfTensor_diag {S : Type*} [CommRing S] {b : (Fin 2 → α) → S}
    (hb : IsAltTensor b) (i : α) : matrixOfTensor b i i = 0 := by
  refine hb.zero_of_not_injective _ (fun hinj => ?_)
  have h01 : (Fin.cons i (fun _ => i) : Fin 2 → α) 0 = (Fin.cons i (fun _ => i) : Fin 2 → α) 1 := by
    rw [Fin.cons_zero, cons_one]
  exact (by decide : (0 : Fin 2) ≠ 1) (hinj h01)

/-! ### The two boundary submodules agree -/

omit [DecidableEq α] [LinearOrder α] in
/-- The general Koszul differential of a translated matrix reads the transposed matrix. -/
theorem koszulD_tensorOfMatrix (facets : Finset (Finset α))
    (a : α → α → stanleyReisnerRing F facets) (i : α) :
    koszulD (srVertexX F facets) (tensorOfMatrix a) (fun _ => i)
      = ∑ k, a k i * srVertexX F facets k := by
  rw [koszulD]
  exact Finset.sum_congr rfl (fun k _ => rfl)

omit [DecidableEq α] in
/-- **The two conventions define the same first Koszul boundaries.**  A family `z : α → S` is a
concrete Koszul boundary `srKoszulBoundary facets c` for some matrix `c` **iff** its degree-`0`
avatar is a boundary of the alternating Koszul complex.  So the concrete Hochster results and the
degree-uniform strand equivalence speak about the same submodule. -/
theorem srKoszulBoundary_exists_iff_mem_koszulBoundaries (facets : Finset (Finset α))
    (z : α → stanleyReisnerRing F facets) :
    (∃ c : α → α → stanleyReisnerRing F facets, srKoszulBoundary facets c = z)
      ↔ (fun v : Fin 1 → α => z (v 0)) ∈ koszulBoundaries (p := 0) (srVertexX F facets) := by
  constructor
  · rintro ⟨c, rfl⟩
    have hanti : ∀ i j, (fun i j => c j i - c i j) i j + (fun i j => c j i - c i j) j i = 0 := by
      intro i j; show (c j i - c i j) + (c i j - c j i) = 0; ring
    have hdiag : ∀ i, (fun i j => c j i - c i j) i i = 0 := by
      intro i; show c i i - c i i = 0; ring
    refine ⟨tensorOfMatrix (fun i j => c j i - c i j),
      SetLike.mem_coe.mpr (isAltTensor_tensorOfMatrix hanti hdiag), ?_⟩
    funext v
    show koszulD (srVertexX F facets) (tensorOfMatrix (fun i j => c j i - c i j)) v
      = srKoszulBoundary facets c (v 0)
    rw [show v = (fun _ => v 0) from funext (fun t => by fin_cases t; rfl),
      koszulD_tensorOfMatrix facets (fun i j => c j i - c i j) (v 0), srKoszulBoundary]
  · rintro ⟨b, hb, hbz⟩
    have hbalt : IsAltTensor b := hb
    have hanti : ∀ i j, (fun i j => - matrixOfTensor b i j) i j
        + (fun i j => - matrixOfTensor b i j) j i = 0 := by
      intro i j
      show - matrixOfTensor b i j + - matrixOfTensor b j i = 0
      linear_combination - matrixOfTensor_antisymm hbalt i j
    have hdiag : ∀ i, (fun i j => - matrixOfTensor b i j) i i = 0 := by
      intro i
      show - matrixOfTensor b i i = 0
      rw [matrixOfTensor_diag hbalt i, neg_zero]
    refine ⟨koszulUpperTri (fun i j => - matrixOfTensor b i j), ?_⟩
    funext i
    rw [srKoszulBoundary_koszulUpperTri facets hanti hdiag i]
    have hzi : koszulD (srVertexX F facets) b (fun _ => i) = z i := congrFun hbz (fun _ => i)
    rw [← hzi, koszulD]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    show - matrixOfTensor b i k * srVertexX F facets k
      = b (Fin.cons k (fun _ => i)) * srVertexX F facets k
    congr 1
    show - matrixOfTensor b i k = matrixOfTensor b k i
    linear_combination - matrixOfTensor_antisymm hbalt i k

end

end GaloisForLFunctions.HTGeometry
