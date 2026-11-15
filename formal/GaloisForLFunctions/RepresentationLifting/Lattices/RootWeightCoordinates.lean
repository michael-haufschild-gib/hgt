import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Abel

/-!
# Type-A root and weight coordinates

The root lattice consists of integral vectors of sum zero. Representatives of
the weight lattice modulo the diagonal are chosen to vanish at one coordinate.
Subtracting that coordinate embeds the root lattice; its image is detected by
coordinate sum modulo the number of labels. This is the integral lattice map
underlying the torus isogeny in Section 2 of Kurnosov–Ríos Ortiz,
https://arxiv.org/abs/2611.01210.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.RepresentationLifting
variable (ι : Type*) [Fintype ι]

/-- The type-A integral root lattice. -/
def coordinateRootLattice : Submodule ℤ (ι → ℤ) where
  carrier := {v | ∑ i, v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change ∑ i, (v i + w i) = 0
    rw [Finset.sum_add_distrib, hv, hw, add_zero]
  smul_mem' := by
    intro c v hv
    change ∑ i, v i = 0 at hv
    change ∑ i, c * v i = 0
    rw [← Finset.mul_sum, hv, mul_zero]

/-- Integral representatives of the diagonal quotient, fixed by one zero coordinate. -/
def coordinateWeightLattice (p : ι) : Submodule ℤ (ι → ℤ) :=
  (LinearMap.proj p : (ι → ℤ) →ₗ[ℤ] ℤ).ker

/-- The natural root-to-weight inclusion in pointed coordinates. -/
def rootToWeight (p : ι) : coordinateRootLattice ι →ₗ[ℤ] coordinateWeightLattice ι p where
  toFun v := ⟨fun i => v.val i - v.val p, sub_self _⟩
  map_add' v w := by
    ext i
    change (v.val i + w.val i) - (v.val p + w.val p) =
      (v.val i - v.val p) + (w.val i - w.val p)
    abel
  map_smul' c v := by
    ext i
    change c * v.val i - c * v.val p = c * (v.val i - v.val p)
    exact (mul_sub c (v.val i) (v.val p)).symm

/-- No nonzero diagonal vector has coordinate sum zero. -/
theorem rootToWeight_injective (p : ι) : Function.Injective (rootToWeight ι p) := by
  letI : Nonempty ι := ⟨p⟩
  intro v w h
  have hd (i : ι) : v.val i - w.val i = v.val p - w.val p := by
    have hi := congrArg (fun z : coordinateWeightLattice ι p => z.val i) h
    change v.val i - v.val p = w.val i - w.val p at hi
    omega
  have hs : (Fintype.card ι : ℤ) * (v.val p - w.val p) = 0 := by
    calc
      _ = ∑ i : ι, (v.val p - w.val p) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ i : ι, (v.val i - w.val i) := Finset.sum_congr rfl fun i _ => (hd i).symm
      _ = 0 := by rw [Finset.sum_sub_distrib, v.property, w.property, sub_self]
  have hc : v.val p - w.val p = 0 :=
    (mul_eq_zero.mp hs).resolve_left (Int.natCast_ne_zero.mpr Fintype.card_ne_zero)
  apply Subtype.ext
  funext i
  exact sub_eq_zero.mp ((hd i).trans hc)

/-- Divisibility by the number of coordinates is the complete integral obstruction. -/
theorem mem_range_rootToWeight_iff (p : ι) (w : coordinateWeightLattice ι p) :
    w ∈ LinearMap.range (rootToWeight ι p) ↔
      (Fintype.card ι : ℤ) ∣ ∑ i, w.val i := by
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨-v.val p, ?_⟩
    change (∑ i, (v.val i - v.val p)) = _
    rw [Finset.sum_sub_distrib, v.property]
    simp
  · rintro ⟨a, ha⟩
    have hv : ∑ i, (w.val i - a) = 0 := by
      rw [Finset.sum_sub_distrib, ha]
      simp
    refine ⟨⟨fun i => w.val i - a, hv⟩, ?_⟩
    apply Subtype.ext
    funext i
    change (w.val i - a) - (w.val p - a) = w.val i
    have hp : w.val p = 0 := w.property
    rw [hp]
    abel

#print axioms rootToWeight_injective
#print axioms mem_range_rootToWeight_iff
end GaloisForLFunctions.RepresentationLifting
