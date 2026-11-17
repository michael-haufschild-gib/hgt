import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Primitive reduction of p-adic biprojective equations

Maximal-norm coordinates normalize each projective block to an integral
vector with a unit coordinate. Integral bilinear equations then descend
to the residue field with both blocks still nonzero. This is the local
normalization mechanism of Yang et al., arXiv:2611.21188, Lemma 1;
it makes no assertion about the paper’s numerical nonexistence certificates.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.RepresentationLifting.PrimitiveReduction
variable (p : ℕ) [Fact p.Prime]

/-- Every nonzero finite p-adic vector has a scalar multiple integral in every coordinate and equal to one in some coordinate. -/
theorem exists_primitive_model {ι : Type*} [Fintype ι] (x : ι → ℚ_[p]) (hx : x ≠ 0) :
    ∃ c : ℚ_[p], c ≠ 0 ∧ ∃ u : ι → ℤ_[p],
      (∀ i, (u i : ℚ_[p]) = c * x i) ∧ ∃ i, u i = 1 := by
  classical
  have hn : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  obtain ⟨j, hj⟩ := hn
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖)
    ⟨j, Finset.mem_univ j⟩
  have hi0 : x i ≠ 0 := norm_pos_iff.mp
    ((norm_pos_iff.mpr hj).trans_le (hi j (Finset.mem_univ j)))
  have hb (k : ι) : ‖(x i)⁻¹ * x k‖ ≤ 1 := by
    rw [norm_mul, norm_inv, mul_comm, ← div_eq_mul_inv]
    exact (div_le_one (norm_pos_iff.mpr hi0)).mpr (hi k (Finset.mem_univ k))
  let u : ι → ℤ_[p] := fun k => ⟨(x i)⁻¹ * x k, hb k⟩
  refine ⟨(x i)⁻¹, inv_ne_zero hi0, u, fun _ => rfl, i, ?_⟩
  apply PadicInt.ext
  exact inv_mul_cancel₀ hi0

/-- A finite bilinear equation in two separately projective coordinate blocks. -/
def pairing {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
    (A : ι → κ → R) (x : ι → R) (y : κ → R) : R := ∑ i, ∑ j, A i j * x i * y j

/-- Independent block rescaling preserves every bilinear zero equation. -/
theorem pairing_scale {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
    (A : ι → κ → R) (x : ι → R) (y : κ → R) (c d : R) :
    pairing A (fun i => c * x i) (fun j => d * y j) = c * d * pairing A x y := by
  unfold pairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every p-adic biprojective solution of an integral bilinear system reduces to a nonzero solution in each residue block. -/
theorem bilinear_solution_reduces {ι κ τ : Type*} [Fintype ι] [Fintype κ]
    (A : τ → ι → κ → ℤ_[p]) (x : ι → ℚ_[p]) (y : κ → ℚ_[p])
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : ∀ t, pairing (fun i j => (A t i j : ℚ_[p])) x y = 0) :
    ∃ u : ι → ZMod p, ∃ v : κ → ZMod p,
      u ≠ 0 ∧ v ≠ 0 ∧ ∀ t, pairing (fun i j => PadicInt.toZMod (A t i j)) u v = 0 := by
  obtain ⟨c, _, u, hu, i, hi⟩ := exists_primitive_model p x hx
  obtain ⟨d, _, v, hv, j, hj⟩ := exists_primitive_model p y hy
  have hz (t : τ) : pairing (A t) u v = 0 := by
    apply PadicInt.ext
    change ((pairing (A t) u v : ℤ_[p]) : ℚ_[p]) = 0
    simp only [pairing, PadicInt.coe_sum, PadicInt.coe_mul, hu, hv]
    change pairing (fun i j => (A t i j : ℚ_[p])) (fun i => c * x i) (fun j => d * y j) = 0
    rw [pairing_scale, hxy, mul_zero]
  refine ⟨fun k => PadicInt.toZMod (u k), fun k => PadicInt.toZMod (v k), ?_, ?_, ?_⟩
  · intro h
    have he := congrFun h i
    change PadicInt.toZMod (u i) = 0 at he
    rw [hi, map_one] at he
    exact one_ne_zero he
  · intro h
    have he := congrFun h j
    change PadicInt.toZMod (v j) = 0 at he
    rw [hj, map_one] at he
    exact one_ne_zero he
  · intro t
    have he := congrArg (PadicInt.toZMod : ℤ_[p] → ZMod p) (hz t)
    simpa only [pairing, map_sum, map_mul, map_zero] using he

#print axioms exists_primitive_model
#print axioms bilinear_solution_reduces
end GaloisForLFunctions.RepresentationLifting.PrimitiveReduction
