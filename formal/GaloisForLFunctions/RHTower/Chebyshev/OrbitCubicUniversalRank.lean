import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceOneElements
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# A quadratic rank obstruction in every simplest cubic order

Oller, arXiv:2611.17965, Proposition 4.1 (Yatsyna), bounds classical rank
by counting totally positive elements of codifferent trace one. Here the
slice count is exact. Representatives of different height-one elements
are orthogonal for the integral trace pairing: their sum and difference
have strictly positive norm. This gives a rank obstruction already for
the finite trace-one representation problem.
-/

noncomputable section
open Matrix Finset Polynomial
namespace RHTower.OrbitCubic.NumberFieldTrace.UniversalRank
variable {m : ℤ} {r : ℕ}
private abbrev Vec (m : ℤ) (r : ℕ) := Fin r → K m

/-- A classical matrix has integral entries and is positive definite after
every real embedding; the represented value is its ordinary quadratic form. -/
def classicalPositive (Q : Matrix (Fin r) (Fin r) (K m)) :=
  (∀ i j, Q i j ∈ powerOrder m) ∧ (∀ i j, Q i j = Q j i) ∧
    ∀ σ : K m →+* ℝ, (Q.map σ).PosDef

def pair (Q : Matrix (Fin r) (Fin r) (K m)) (x y : Vec m r) := x ⬝ᵥ Q.mulVec y

def integralVector (x : Vec m r) := ∀ i, x i ∈ powerOrder m

/-- Arithmetic representations use only monogenic integers as coordinates. -/
def represents (Q : Matrix (Fin r) (Fin r) (K m)) (z : K m) :=
  ∃ x : Vec m r, integralVector x ∧ pair Q x x = z

private theorem integral_pair {Q : Matrix (Fin r) (Fin r) (K m)} (hQ : classicalPositive Q)
    {x y : Vec m r} (hx : integralVector x) (hy : integralVector y) : pair Q x y ∈ powerOrder m := by
  apply in_order.mp
  unfold pair dotProduct Matrix.mulVec
  exact (orderRing m).sum_mem fun i _ => (orderRing m).mul_mem (in_order.mpr (hx i))
    ((orderRing m).sum_mem fun j _ => (orderRing m).mul_mem (in_order.mpr (hQ.1 i j)) (in_order.mpr (hy j)))

private theorem symmetric_pair {Q : Matrix (Fin r) (Fin r) (K m)} (hQ : classicalPositive Q) (x y : Vec m r) :
    pair Q x y = pair Q y x := by
  simp only [pair,dotProduct,mulVec,Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hQ.2.1 j i]; ring

private theorem positive_pair {Q : Matrix (Fin r) (Fin r) (K m)} (hQ : classicalPositive Q)
    {x : Vec m r} (hx : x ≠ 0) : totallyPositive m (pair Q x x) := by
  intro σ
  let v := fun i => σ (x i)
  have hv : v ≠ 0 := by
    intro h
    apply hx
    funext i
    exact σ.injective ((congrFun h i).trans (map_zero σ).symm)
  have H := (Matrix.posDef_iff_dotProduct_mulVec.mp (hQ.2.2 σ)).2 hv
  simpa only [pair,dotProduct,Matrix.mulVec,Matrix.map_apply,v,map_sum,map_mul,star_trivial] using H

private def reading (Q : Matrix (Fin r) (Fin r) (K m)) (x : Vec m r) : Vec m r →ₗ[ℚ] ℚ where
  toFun y := height m (pair Q x y)
  map_add' a b := by simp only [height,pair,Matrix.mulVec_add,dotProduct_add,mul_add,map_add]
  map_smul' c y := by simp [height,pair,Matrix.mulVec_smul,dotProduct_smul,mul_smul_comm,map_smul]

private theorem reading_comm {Q : Matrix (Fin r) (Fin r) (K m)} (hQ : classicalPositive Q) (x y : Vec m r) :
    reading Q x y = reading Q y x := congrArg (height m) (symmetric_pair hQ x y)

private theorem reading_integer {Q : Matrix (Fin r) (Fin r) (K m)} (hQ : classicalPositive Q)
    {x y : Vec m r} (hx : integralVector x) (hy : integralVector y) :
    ∃ a : ℤ, reading Q x y = (a:ℚ) := by
  obtain ⟨a,b,c,h⟩ := (powerOrder_eq_coords m _).mp (integral_pair hQ hx hy)
  exact ⟨a,by change height m (pair Q x y) = _; rw [height,h,trace_coords]⟩

private theorem reading_pos {Q : Matrix (Fin r) (Fin r) (K m)} (hQ : classicalPositive Q)
    {x : Vec m r} (hx : integralVector x) (hn : x ≠ 0) : 0 < reading Q x x := by
  obtain ⟨i,hi,he⟩ := positive_height_integral m ⟨pair Q x x,integral_pair hQ hx hx,positive_pair hQ hn⟩
  change 0 < height m (pair Q x x)
  rw [he]
  exact_mod_cast (show 0 < i by omega)

private theorem orthogonal {Q : Matrix (Fin r) (Fin r) (K m)} (hQ : classicalPositive Q)
    {x y : Vec m r} (hx : integralVector x) (hy : integralVector y)
    (ex : reading Q x x = 1) (ey : reading Q y y = 1) (hne : pair Q x x ≠ pair Q y y) :
    reading Q x y = 0 := by
  have hm : x-y ≠ 0 := fun h => hne (congrArg (fun z => pair Q z z) (sub_eq_zero.mp h))
  have hp : x+y ≠ 0 := by
    intro h
    exact hne (by rw [eq_neg_of_add_eq_zero_left h]; simp [pair,Matrix.mulVec_neg])
  have minus := reading_pos hQ (x := x-y) (fun i => in_order.mp
    ((orderRing m).sub_mem (in_order.mpr (hx i)) (in_order.mpr (hy i)))) hm
  have plus := reading_pos hQ (x := x+y) (fun i => in_order.mp
    ((orderRing m).add_mem (in_order.mpr (hx i)) (in_order.mpr (hy i)))) hp
  rw [map_sub,reading_comm hQ (x-y) x,reading_comm hQ (x-y) y,map_sub,map_sub,
    ex,ey,reading_comm hQ y x] at minus
  rw [map_add,reading_comm hQ (x+y) x,reading_comm hQ (x+y) y,map_add,map_add,
    ex,ey,reading_comm hQ y x] at plus
  obtain ⟨i,hi⟩ := reading_integer hQ hx hy
  rw [hi] at minus plus ⊢
  have hl : (-1:ℚ) < (i:ℚ) := by linarith only [plus]
  have hu : (i:ℚ) < 1 := by linarith only [minus]
  have hl' : (-1:ℤ) < i := by exact_mod_cast hl
  have hu' : i < 1 := by exact_mod_cast hu
  exact_mod_cast (show i = 0 by omega)

private abbrev RationalVectors (r : ℕ) := Fin r → ℚ × ℚ × ℚ

private def synthesize (m : ℤ) (r : ℕ) : RationalVectors r →ₗ[ℚ] Vec m r where
  toFun v i := coords m (v i).1 (v i).2.1 (v i).2.2
  map_add' x y := by funext i; simp [coords,add_smul] <;> abel
  map_smul' a x := by
    funext i
    simp [coords,smul_add,smul_smul,smul_eq_mul]
    simp [Algebra.smul_def]

private theorem rational_rank_bound {I : Type*} [Fintype I] (z : I → heightOne m)
    (hz : Function.Injective z) (Q : Matrix (Fin r) (Fin r) (K m)) (hQ : classicalPositive Q)
    (H : ∀ i, represents Q (z i).val) : Fintype.card I ≤ 3*r := by
  classical
  choose v hv he using H
  choose c hc using fun i j => (coords_bijective m).2 (v i j)
  have hC (i) : synthesize m r (c i) = v i := funext (hc i)
  let T := fun i => (reading Q (v i)).comp (synthesize m r)
  have hself (i) : reading Q (v i) (v i) = 1 := by
    change height m (pair Q (v i) (v i)) = 1
    rw [he]
    exact (z i).property.2.2
  have Hdual (i j : I) : T i (c j) = if i = j then 1 else 0 := by
    simp only [T,LinearMap.comp_apply,hC]
    by_cases hij : i = j
    · subst j; simp [hself]
    · rw [if_neg hij]
      apply orthogonal hQ (hv i) (hv j) (hself i) (hself j)
      rw [he,he]
      exact fun h => hij (hz (Subtype.ext h))
  have hi : LinearIndependent ℚ c := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hg i
    have h := congrArg (T i) hg
    simpa [map_sum,map_smul,Hdual,smul_eq_mul] using h
  have dim : Module.finrank ℚ (RationalVectors r) = 3*r := by
    simp [RationalVectors,Module.finrank_pi_fintype,Module.finrank_prod,smul_eq_mul,Nat.mul_comm]
  exact dim ▸ hi.fintype_card_le_finrank

/-- The complete finite trace-one test forces the classical rank bound.
This already applies before testing any positive integer of larger height. -/
theorem trace_one_rank_obstruction (n r : ℕ) (Q : Matrix (Fin r) (Fin r) (K ((n:ℤ)+2))) :
    classicalPositive Q → (∀ z : heightOne ((n:ℤ)+2), represents Q z.val) →
      3+(n+2)*(n+1)/2 ≤ 3*r := by
  intro hQ H
  let e := (enumeratePositiveSlice n).trans (heightOneEquiv ((n:ℤ)+2))
  simpa only [Fintype.card_sum,Fintype.card_fin,card_triangleIndex] using
    rational_rank_bound e e.injective Q hQ (fun i => H (e i))

/-- No smaller classical matrix is universal over this order. -/
theorem no_universal_below_trace_bound (n r : ℕ) :
    3*r < 3+(n+2)*(n+1)/2 →
    ¬ ∃ Q : Matrix (Fin r) (Fin r) (K ((n:ℤ)+2)), classicalPositive Q ∧
      ∀ z ∈ powerOrder ((n:ℤ)+2), totallyPositive ((n:ℤ)+2) z → represents Q z := by
  rintro hr ⟨Q,hQ,h⟩
  exact hr.not_ge (trace_one_rank_obstruction n r Q hQ fun z => h z.val z.property.1 z.property.2.1)

end RHTower.OrbitCubic.NumberFieldTrace.UniversalRank
