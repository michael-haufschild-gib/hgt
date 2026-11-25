import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCechComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Flat.Basic

/-! The alternating Čech complex over a common scalar ring. -/

noncomputable section

open CategoryTheory HTGeometry

namespace HTGeometry.FinsetCechDatum

universe u v

variable {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι] [LinearOrder ι]
  (D : FinsetCechDatum.{v} ι) [∀ s, Module R (D.obj s)]

/-- The scalar-linear cochains in degree `n` are supported on subsets of size `n+1`. -/
def degreeSubmodule (n : ℕ) : Submodule R D.Cochain where
  carrier := {c | D.IsDeg c n}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro x y hx hy s hs
    change x s + y s = 0
    rw [hx s hs, hy s hs, zero_add]
  smul_mem' := by
    intro r x hx s hs
    change r • x s = 0
    rw [hx s hs, smul_zero]

def degreeLinearEquiv (n : ℕ) :
    D.degreeSubmodule (R := R) n ≃ₗ[R] (∀ s : {s : Finset ι // s.card = n + 1}, D.obj s.1) where
  toFun x s := x.1 s.1
  invFun x := ⟨fun s => if hs : s.card = n + 1 then x ⟨s, hs⟩ else 0,
    fun s hs => dif_neg hs⟩
  left_inv x := Subtype.ext (funext fun s => by
    by_cases hs : s.card = n + 1
    · exact dif_pos hs
    · exact (dif_neg hs).trans (x.2 s hs).symm)
  right_inv x := funext fun s => dif_pos s.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (hres : ∀ {s t : Finset ι} (h : s ⊆ t) (r : R) (x : D.obj s),
  D.res h (r • x) = r • D.res h x)

private def linearDifferential (n : ℕ) :
    D.degreeSubmodule (R := R) n →ₗ[R] D.degreeSubmodule (R := R) (n + 1) where
  toFun x := ⟨D.d x.1, D.d_isDeg x.2⟩
  map_add' x y := Subtype.ext (D.d_add x.1 y.1)
  map_smul' r x := Subtype.ext (funext fun s => by
    change D.d (r • x.1) s = r • D.d x.1 s
    simp only [FinsetCechDatum.d, Pi.smul_apply, Finset.smul_sum, hres]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ r _)

/-- Reuse the alternating differential and its square-zero identity over the scalar ring. -/
def linearComplex : CochainComplex (ModuleCat.{v} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (D.degreeSubmodule (R := R) n))
    (fun n => ModuleCat.ofHom (D.linearDifferential hres n)) (fun _ =>
      ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext (D.d_d x.1)))

theorem linearComplex_X_flat [Fintype ι] (n : ℕ)
    (hflat : ∀ s : Finset ι, s.Nonempty → Module.Flat R (D.obj s)) :
    Module.Flat R ((D.linearComplex hres).X n) := by
  classical
  let I := {s : Finset ι // s.card = n + 1}
  haveI (s : I) : Module.Flat R (D.obj s.1) :=
    hflat s.1 (Finset.card_pos.mp (by rw [s.2]; omega))
  let e : (Π₀ s : I, D.obj s.1) ≃ₗ[R] (∀ s : I, D.obj s.1) := DFinsupp.linearEquivFunOnFintype
  exact Module.Flat.of_linearEquiv ((D.degreeLinearEquiv (R := R) n).trans e.symm)

theorem linearComplex_X_isZero [Fintype ι] (n : ℕ) (hn : Fintype.card ι ≤ n) :
    Limits.IsZero ((D.linearComplex hres).X n) := by
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => ?_⟩
  refine Subtype.ext (funext fun s => ?_)
  have hs : s.card ≠ n + 1 := fun h => by
    have hle := Finset.card_le_univ s
    omega
  exact (x.2 s hs).trans (y.2 s hs).symm

end HTGeometry.FinsetCechDatum
