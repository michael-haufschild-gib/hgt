import Mathlib

/-!
# Lattice translations are `ℓ²` isometries

An `ℓᵖ` family precomposed with a bijection of the index set is again `ℓᵖ` with the same norm: the
defining sum is a reindexed sum.  On a valuation lattice this turns every translation into a linear
isometric equivalence of `ℓ²`, which is the structure the finite-range prime adjacency is built
from.
-/

open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section Reindex

variable {α β : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
theorem memℓp_comp_equiv (hp : 0 < p.toReal) (e : α ≃ β) {f : β → ℂ} (hf : Memℓp f p) :
    Memℓp (fun a => f (e a)) p := by
  rw [memℓp_gen_iff hp] at hf ⊢
  exact (e.summable_iff (f := fun b => ‖f b‖ ^ p.toReal)).mpr hf

/-- Reindexing an `ℓᵖ` element along a bijection of the index type. -/
def lpDomCongrFun (hp : 0 < p.toReal) (e : α ≃ β) (f : lp (fun _ : β => ℂ) p) :
    lp (fun _ : α => ℂ) p :=
  ⟨fun a => f (e a), memℓp_comp_equiv hp e f.2⟩

omit [Fact (1 ≤ p)] in
@[simp]
theorem lpDomCongrFun_apply (hp : 0 < p.toReal) (e : α ≃ β) (f : lp (fun _ : β => ℂ) p) (a : α) :
    (lpDomCongrFun hp e f : α → ℂ) a = f (e a) := rfl

omit [Fact (1 ≤ p)] in
theorem norm_lpDomCongrFun (hp : 0 < p.toReal) (e : α ≃ β)
    (f : lp (fun _ : β => ℂ) p) : ‖lpDomCongrFun hp e f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  congr 1
  exact (e.tsum_eq fun b => ‖f b‖ ^ p.toReal)

/-- Reindexing is a linear isometric equivalence of `ℓᵖ`. -/
def lpDomCongr (hp : 0 < p.toReal) (e : α ≃ β) :
    lp (fun _ : β => ℂ) p ≃ₗᵢ[ℂ] lp (fun _ : α => ℂ) p where
  toFun := lpDomCongrFun hp e
  invFun := lpDomCongrFun hp e.symm
  left_inv f := by
    ext b
    simp [lpDomCongrFun]
  right_inv f := by
    ext a
    simp [lpDomCongrFun]
  map_add' f g := by
    ext a
    simp [lpDomCongrFun]
  map_smul' c f := by
    ext a
    simp [lpDomCongrFun]
  norm_map' f := norm_lpDomCongrFun hp e f

@[simp]
theorem lpDomCongr_apply (hp : 0 < p.toReal) (e : α ≃ β)
    (f : lp (fun _ : β => ℂ) p) (a : α) :
    ((lpDomCongr hp e f : lp (fun _ : α => ℂ) p) : α → ℂ) a = f (e a) := rfl

end Reindex

section Shift

variable {G : Type*} [AddCommGroup G]

/-- Translation of an `ℓ²` lattice field. -/
def latticeShift (q : G) : lp (fun _ : G => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : G => ℂ) 2 :=
  lpDomCongr (p := 2) (by norm_num) (Equiv.addRight q)

@[simp]
theorem latticeShift_apply (q : G) (ψ : lp (fun _ : G => ℂ) 2) (ν : G) :
    ((latticeShift q ψ : lp (fun _ : G => ℂ) 2) : G → ℂ) ν = ψ (ν + q) :=
  lpDomCongr_apply (p := 2) (by norm_num) (Equiv.addRight q) ψ ν

theorem latticeShift_zero : latticeShift (0 : G) = LinearIsometryEquiv.refl ℂ _ := by
  ext ψ ν
  simp

theorem latticeShift_add (q r : G) :
    latticeShift (q + r) = (latticeShift r).trans (latticeShift q) := by
  ext ψ ν
  simp [add_comm, add_left_comm]

end Shift

end GaloisForLFunctions.HTGeometry
