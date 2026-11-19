import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicGeneralQuadraticRank
import GaloisForLFunctions.HTGeometry.Lattices.IntegralCartanComponentShapes

/-!
# Quadratic capacity of a cubic order-valued form

Oller bounds unit trace vectors by the root counts of simply laced
Cartan systems. Counting their component shells gives the sharper
rank-dependent cap d max(15,d−1) for distinct represented elements of height one.
For cubic orders d is three times the order-form rank.
-/

noncomputable section
namespace RHTower.OrbitCubic.NumberFieldTrace.GeneralRank
open GaloisForLFunctions.HTGeometry.IntegralRootShell
variable {m : ℤ} {r : ℕ}

private theorem height_capacity {I : Type*} [Fintype I] (Q : OrderForm m r) (hp : positive Q)
    (z : I → heightOne m) (hi : Function.Injective z) (h : ∀ i, ∃ v, (Q v).val=(z i).val) :
    Fintype.card I≤3*r*max 15 (3*r-1) := by
  obtain ⟨x,separate⟩ := represented_root_lines Q z hi h
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm r 3] using
    quadratic_line_bound (traceForm Q) (traceForm_positive Q hp) x separate

/-- Capacity of the represented part of the actual height-one slice. -/
theorem represented_slice_quadratic_bound (n r : ℕ) (Q : OrderForm ((n:ℤ)+2) r) (hp : positive Q) :
    Nat.card {z : heightOne ((n:ℤ)+2) // ∃ v, (Q v).val=z.val}≤3*r*max 15 (3*r-1) := by
  classical
  let e := (enumeratePositiveSlice n).trans (heightOneEquiv ((n:ℤ)+2))
  letI : Fintype (heightOne ((n:ℤ)+2)) := Fintype.ofEquiv _ e
  rw [Nat.card_eq_fintype_card]
  exact height_capacity Q hp Subtype.val Subtype.val_injective fun z => z.property

/-- Representing the entire slice forces a rank linear in the orbit
parameter, even when the cross coefficients are odd. -/
theorem cartan_rank_obstruction (n r : ℕ) (Q : OrderForm ((n:ℤ)+2) r) :
    positive Q → (∀ z : heightOne ((n:ℤ)+2), ∃ v, (Q v).val=z.val) →
      3+(n+2)*(n+1)/2≤3*r*max 15 (3*r-1) := by
  intro hp h
  let e := (enumeratePositiveSlice n).trans (heightOneEquiv ((n:ℤ)+2))
  simpa only [Fintype.card_sum,Fintype.card_fin,card_triangleIndex] using
    height_capacity Q hp e e.injective (fun i => h (e i))

/-- Beyond the exceptional range the complete-square obstruction retains
the linear terms of both the triangular slice and the root count. -/
theorem large_parameter_rank (n r : ℕ) (Q : OrderForm ((n:ℤ)+2) r) :
    20≤n → positive Q → (∀ z : heightOne ((n:ℤ)+2), ∃ v, (Q v).val=z.val) →
      6≤r ∧ (2*n+3)^2+24*r+23≤72*r^2 := by
  intro large hp rep
  have H := cartan_rank_obstruction n r Q hp rep
  have rank : 6≤r := by
    by_contra! small
    have left := Nat.mul_le_mul (show 22≤n+2 by omega) (show 21≤n+1 by omega)
    have right : 3*r-1≤15 := by omega
    rw [max_eq_left right] at H
    omega
  rw [max_eq_right (by omega : 15≤3*r-1)] at H
  have even : Even ((n+2)*(n+1)) := by
    rcases Nat.even_or_odd (n+1) with h|h
    · exact h.mul_left _
    · exact h.add_one.mul_right _
  obtain ⟨k,hk⟩ := even
  have he : (n+2)*(n+1)/2=k := by rw [hk]; omega
  have sub : 3*r-1+1=3*r := by omega
  rw [he] at H
  refine ⟨rank,?_⟩
  nlinarith only [hk,H,congrArg (fun a : ℕ => (3*r)*a) sub]

#print axioms represented_slice_quadratic_bound
#print axioms cartan_rank_obstruction
#print axioms large_parameter_rank
end RHTower.OrbitCubic.NumberFieldTrace.GeneralRank
