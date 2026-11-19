import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceOneElements
import GaloisForLFunctions.HTGeometry.Lattices.CubicRootLineBound

/-!
# The integral root datum of a general quadratic form over a cubic order

Restrict scalars in an order-valued quadratic form and apply the weighted
field trace. This gives an integer quadratic form in 3r variables, including
when cross coefficients are odd. Distinct represented positive integers
of height one use different root lines. Both parity and cubic interpolation
bound their number in terms of rank.
-/

noncomputable section
namespace RHTower.OrbitCubic.NumberFieldTrace.GeneralRank
open GaloisForLFunctions.HTGeometry.IntegralRootShell
variable {m : ℤ} {r : ℕ}

abbrev OrderForm (m : ℤ) (r : ℕ) := QuadraticForm (orderRing m) (Fin r → orderRing m)

/-- Total positivity on every nonzero order vector. -/
def positive (Q : OrderForm m r) := ∀ x, x ≠ 0 → totallyPositive m (Q x).val

private def orderHeight (m : ℤ) (x : orderRing m) : ℤ := ⌊height m x.val⌋

private theorem orderHeight_cast (m : ℤ) (x : orderRing m) : (orderHeight m x:ℚ)=height m x.val := by
  obtain ⟨a,b,c,h⟩ := (powerOrder_eq_coords m x.val).mp (in_order.mp x.property)
  have ht : height m x.val = (a:ℚ) := by rw [height,h,trace_coords]
  simp only [orderHeight,ht,Int.floor_intCast]

private def heightHom (m : ℤ) : orderRing m →+ ℤ where
  toFun := orderHeight m
  map_zero' := by
    have h := orderHeight_cast m 0
    simp only [ZeroMemClass.coe_zero,height,mul_zero,map_zero] at h
    exact_mod_cast h
  map_add' x y := by
    apply (Int.cast_injective (α:=ℚ))
    rw [Int.cast_add,orderHeight_cast,orderHeight_cast,orderHeight_cast]
    change Algebra.trace ℚ (K m) (delta m*(x.val+y.val))=
      Algebra.trace ℚ (K m) (delta m*x.val)+Algebra.trace ℚ (K m) (delta m*y.val)
    rw [mul_add,map_add]

private def oneSite (m : ℤ) (a b c : ℤ) : orderRing m :=
  ⟨coords m a b c,in_order.mpr ((powerOrder_eq_coords m _).mpr ⟨a,b,c,rfl⟩)⟩

private def paramHom (m : ℤ) (r : ℕ) : (Fin r × Fin 3 → ℤ) →+ (Fin r → orderRing m) where
  toFun v i := oneSite m (v (i,0)) (v (i,1)) (v (i,2))
  map_zero' := by funext i; apply Subtype.ext; simp [oneSite,coords]
  map_add' v w := by
    funext i
    apply Subtype.ext
    change coords m _ _ _=coords m _ _ _+coords m _ _ _
    simp only [Pi.add_apply,coords,Int.cast_add,add_smul]
    abel

private theorem param_bijective (m : ℤ) (r : ℕ) : Function.Bijective (paramHom m r) := by
  constructor
  · intro v w he
    funext p
    obtain ⟨i,j⟩ := p
    have hx := congrArg (fun t : Fin r → orderRing m => (t i).val) he
    have hh := (coords_bijective m).1 (a₁ := ((v (i,0):ℚ),(v (i,1):ℚ),(v (i,2):ℚ)))
      (a₂ := ((w (i,0):ℚ),(w (i,1):ℚ),(w (i,2):ℚ))) hx
    obtain ⟨h0,h12⟩ := Prod.mk.inj hh
    obtain ⟨h1,h2⟩ := Prod.mk.inj h12
    fin_cases j
    · exact_mod_cast h0
    · exact_mod_cast h1
    · exact_mod_cast h2
  · intro v
    choose a b c h using fun i => (powerOrder_eq_coords m _).mp (in_order.mp (v i).property)
    refine ⟨fun p => ![a p.1,b p.1,c p.1] p.2,?_⟩
    funext i
    exact Subtype.ext (h i).symm

/-- The integral trace quadratic form on the genuine reciprocal coordinates. -/
def traceForm (Q : OrderForm m r) : Form (Fin r × Fin 3) :=
  ((heightHom m).toIntLinearMap.compQuadraticMap' Q).comp (paramHom m r).toIntLinearMap

theorem traceForm_value (Q : OrderForm m r) (v : Fin r × Fin 3 → ℤ) :
    (traceForm Q v : ℚ)=height m (Q (paramHom m r v)).val := orderHeight_cast m _

theorem traceForm_positive (Q : OrderForm m r) : positive Q → (traceForm Q).PosDef := by
  intro hp v hv
  have hx : paramHom m r v≠0 := fun h => hv ((param_bijective m r).1 (h.trans (map_zero _).symm))
  obtain ⟨a,ha,he⟩ := positive_height_integral m ⟨_,in_order.mp (Q (paramHom m r v)).property,hp _ hx⟩
  have ht : (traceForm Q v:ℚ)=(a:ℚ) := (traceForm_value Q v).trans he
  have eq : traceForm Q v=a := by exact_mod_cast ht
  omega

/-- Reflection in every represented trace-one vector preserves the original
integer coordinate lattice and gives a finite reduced root datum. -/
theorem trace_root_datum (Q : OrderForm m r) (hp : positive Q) :
    Finite (Root (traceForm Q)) ∧ (datum (traceForm Q) (traceForm_positive Q hp)).IsReduced :=
  ⟨finite_roots _ (traceForm_positive Q hp),reduced _ _⟩

/-- Distinct represented points of height one lift to distinct unoriented roots
of the integral trace form. -/
theorem represented_root_lines {I : Type*} (Q : OrderForm m r)
    (z : I → heightOne m) (hi : Function.Injective z)
    (h : ∀ i, ∃ v, (Q v).val=(z i).val) :
    ∃ x : I → Root (traceForm Q), ∀ i j, (x i).val=(x j).val ∨ (x i).val= -(x j).val → i=j := by
  classical
  choose v hv using h
  choose w hw using fun i => (param_bijective m r).2 (v i)
  let x (i : I) : Root (traceForm Q) := ⟨w i,by
    have H := traceForm_value Q (w i)
    rw [hw,hv,(z i).property.2.2] at H
    exact_mod_cast H⟩
  have sep (i j : I) (he : (x i).val=(x j).val ∨ (x i).val= -(x j).val) : i=j := by
    apply hi
    apply Subtype.ext
    rw [← hv,← hv,← hw,← hw]
    change w i=w j ∨ w i= -w j at he
    rcases he with he|he
    · rw [he]
    · rw [he,map_neg,Q.map_neg]
  exact ⟨x,sep⟩

private theorem request_bound {I : Type*} [Fintype I] (Q : OrderForm m r) (hp : positive Q)
    (z : I → heightOne m) (hi : Function.Injective z)
    (h : ∀ i, ∃ v, (Q v).val=(z i).val) :
    Fintype.card I+1 ≤ 2^(3*r) ∧ Fintype.card I ≤ (3*r+2).choose 3 := by
  obtain ⟨x,sep⟩ := represented_root_lines Q z hi h
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm r 3] using
    And.intro (line_bound (traceForm Q) (traceForm_positive Q hp) x sep)
      (cubic_line_bound (traceForm Q) (traceForm_positive Q hp) x sep)

/-- The parity obstruction already bounds the cardinality of the actual
represented part of the height-one slice, without any universality assumption. -/
theorem represented_slice_bound (n r : ℕ) (Q : OrderForm ((n:ℤ)+2) r) (hp : positive Q) :
    Nat.card {z : heightOne ((n:ℤ)+2) // ∃ v, (Q v).val=z.val}+1 ≤ 2^(3*r) := by
  classical
  let e := (enumeratePositiveSlice n).trans (heightOneEquiv ((n:ℤ)+2))
  letI : Fintype (heightOne ((n:ℤ)+2)) := Fintype.ofEquiv _ e
  rw [Nat.card_eq_fintype_card]
  exact (request_bound Q hp Subtype.val Subtype.val_injective fun z => z.property).1

/-- Cubic interpolation bounds the represented subset polynomially in the
rank, even for forms with odd cross coefficients. -/
theorem represented_slice_cubic_bound (n r : ℕ) (Q : OrderForm ((n:ℤ)+2) r) (hp : positive Q) :
    Nat.card {z : heightOne ((n:ℤ)+2) // ∃ v, (Q v).val=z.val} ≤ (3*r+2).choose 3 := by
  classical
  let e := (enumeratePositiveSlice n).trans (heightOneEquiv ((n:ℤ)+2))
  letI : Fintype (heightOne ((n:ℤ)+2)) := Fintype.ofEquiv _ e
  rw [Nat.card_eq_fintype_card]
  exact (request_bound Q hp Subtype.val Subtype.val_injective fun z => z.property).2

/-- A nonclassical universal form over the cubic order must pass this
logarithmic rank bound; its coefficients need no classical integrality. -/
theorem general_rank_obstruction (n r : ℕ) (Q : OrderForm ((n:ℤ)+2) r) :
    positive Q → (∀ z : heightOne ((n:ℤ)+2), ∃ v, (Q v).val=z.val) →
      3+(n+2)*(n+1)/2+1 ≤ 2^(3*r) := by
  intro hp h
  let e := (enumeratePositiveSlice n).trans (heightOneEquiv ((n:ℤ)+2))
  simpa only [Fintype.card_sum,Fintype.card_fin,card_triangleIndex] using
    (request_bound Q hp e e.injective (fun i => h (e i))).1

/-- Representing the full triangular trace slice forces a cubic lower
bound on rank in terms of the square of the field parameter. -/
theorem cubic_rank_obstruction (n r : ℕ) (Q : OrderForm ((n:ℤ)+2) r) :
    positive Q → (∀ z : heightOne ((n:ℤ)+2), ∃ v, (Q v).val=z.val) →
      3+(n+2)*(n+1)/2 ≤ (3*r+2).choose 3 := by
  intro hp h
  let e := (enumeratePositiveSlice n).trans (heightOneEquiv ((n:ℤ)+2))
  simpa only [Fintype.card_sum,Fintype.card_fin,card_triangleIndex] using
    (request_bound Q hp e e.injective (fun i => h (e i))).2

#print axioms traceForm_value
#print axioms traceForm_positive
#print axioms trace_root_datum
#print axioms represented_root_lines
#print axioms represented_slice_bound
#print axioms general_rank_obstruction
#print axioms represented_slice_cubic_bound
#print axioms cubic_rank_obstruction
end RHTower.OrbitCubic.NumberFieldTrace.GeneralRank
