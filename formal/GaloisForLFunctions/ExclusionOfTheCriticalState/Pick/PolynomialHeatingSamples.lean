import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.PolynomialJumpRealization
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots

/-!
# Sharp sampling of a polynomial heating profile

A single momentum jump heats the position square by the square of its
slope. A slope of degree d needs 2d+1 distinct fixed samples in the
worst case. After sampling at d+1 fixed nodes there are only finitely
many possible signed interpolants; one further adaptive sample resolves
every remaining physical ambiguity.
-/

noncomputable section
open Polynomial Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.HeatSamples
open JumpGrid
variable {d : ℕ}

/-- Measured scalar heating for a polynomial slope. -/
def power (P : ℝ[X]) (x : ℝ) := (P.eval x)^2

theorem power_eq_iff (P Q : ℝ[X]) : power P=power Q ↔ P=Q ∨ P= -Q := by
  constructor
  · intro h
    have e : P^2=Q^2 := Polynomial.funext fun x => by simpa only [power,eval_pow] using congrFun h x
    have hz : (P-Q)*(P+Q)=0 := by linear_combination e
    exact (mul_eq_zero.mp hz).imp sub_eq_zero.mp eq_neg_of_add_eq_zero_left
  · rintro (e|e)
    · rw [e]
    · rw [e]; funext x; simp [power]

/-- Polynomial primitive with zero constant term. -/
def primitive (P : ℝ[X]) : ℝ[X] := P.sum fun k c => monomial (k+1) (c/((k:ℝ)+1))

theorem derivative_primitive (P : ℝ[X]) : (primitive P).derivative=P := by
  conv_rhs => rw [← P.sum_monomial_eq]
  simp only [primitive,Polynomial.sum,map_sum,derivative_monomial_succ]
  exact sum_congr rfl fun k _ => by
    congr 1
    field_simp [show (k:ℝ)+1≠0 by positivity]

theorem primitive_degree (P : ℝ[X]) : (primitive P).natDegree≤P.natDegree+1 := by
  have h := natDegree_derivative (primitive P)
  rw [derivative_primitive] at h
  omega

def vanishing (S : Finset ℝ) : ℝ[X] := ∏ x ∈ S, (X-C x)

theorem vanishing_degree (S : Finset ℝ) : (vanishing S).natDegree=S.card :=
  natDegree_finsetProd_X_sub_C_eq_card S id

private theorem vanishing_ne (S : Finset ℝ) : vanishing S≠0 := (monic_prod_X_sub_C id S).ne_zero

theorem vanishing_eval (S : Finset ℝ) (x : ℝ) : (vanishing S).eval x=0 ↔ x∈S := by
  classical
  simp [vanishing,eval_prod,prod_eq_zero_iff,sub_eq_zero]

/-- Exactly the number of distinct fixed nodes required; repeated samples
carry no additional information. -/
theorem fixed_threshold (d : ℕ) (S : Finset ℝ) :
    (∀ P Q : Channel d, (∀ x∈S, power P.val x=power Q.val x) → power P.val=power Q.val) ↔
      2*d<S.card := by
  classical
  constructor
  · intro separates
    by_contra! small
    obtain ⟨A,hA,cardA⟩ := S.exists_subset_card_eq (min_le_right d S.card)
    let B := S \ A
    have da : (vanishing A).natDegree≤d := by rw [vanishing_degree,cardA]; exact min_le_left _ _
    have db : (vanishing B).natDegree≤d := by rw [vanishing_degree,show B=S \ A from rfl,card_sdiff_of_subset hA,cardA]; omega
    let P : Channel d := ⟨vanishing A+vanishing B,(natDegree_add_le _ _).trans (max_le da db)⟩
    let Q : Channel d := ⟨vanishing A-vanishing B,(natDegree_sub_le _ _).trans (max_le da db)⟩
    have h := separates P Q fun x hx => by
      by_cases ha : x∈A
      · simp [P,Q,power,(vanishing_eval A x).mpr ha]
      · have hb := (vanishing_eval B x).mpr (mem_sdiff.mpr ⟨hx,ha⟩)
        simp [P,Q,power,hb]
    rcases (power_eq_iff _ _).mp h with e|e
    · change vanishing A+vanishing B=vanishing A-vanishing B at e
      apply vanishing_ne B
      exact (mul_eq_zero.mp (show (2:ℝ[X])*vanishing B=0 by linear_combination e)).resolve_left (by norm_num)
    · change vanishing A+vanishing B= -(vanishing A-vanishing B) at e
      apply vanishing_ne A
      exact (mul_eq_zero.mp (show (2:ℝ[X])*vanishing A=0 by linear_combination e)).resolve_left (by norm_num)
  · intro h P Q e
    have deg (U : Channel d) : (U.val^2).natDegree≤2*d := by
      rw [natDegree_pow]
      exact Nat.mul_le_mul_left 2 U.property
    have he := eq_of_natDegree_lt_card_of_eval_eq' (P.val^2) (Q.val^2) S
      (fun i hi => by simpa only [power,eval_pow] using e i hi) ((max_le (deg _) (deg _)).trans_lt h)
    funext x
    simpa only [power,eval_pow] using congrArg (Polynomial.eval x) he

private def candidate (v : Nodes d) (data : Fin (d+1) → ℝ) (s : Fin (d+1) → Bool) : Channel d :=
  interpolateValues v (fun i => if s i then Real.sqrt (data i) else -Real.sqrt (data i))

private theorem candidate_complete (v : Nodes d) (P : Channel d) :
    ∃ s, candidate v (fun i => power P.val (v i)) s=P := by
  classical
  let s := fun i => decide (0≤P.val.eval (v i))
  refine ⟨s,Subtype.ext (Polynomial.funext fun x => ?_)⟩
  let Q := candidate v (fun i => power P.val (v i)) s
  have he (i : Fin (d+1)) : Q.val.eval (v i)=P.val.eval (v i) := by
    by_cases h : 0≤P.val.eval (v i)
    · simp [Q,candidate,eval_values,s,h,power,Real.sqrt_sq_eq_abs,abs_of_nonneg h]
    · simp [Q,candidate,eval_values,s,h,power,Real.sqrt_sq_eq_abs,abs_of_neg (lt_of_not_ge h)]
  rw [HTGeometry.eval_eq_sum_lagrangeBasis Q.val Q.property v v.injective,
    HTGeometry.eval_eq_sum_lagrangeBasis P.val P.property v v.injective]
  simp only [he]

private def excluded (v : Nodes d) (data : Fin (d+1) → ℝ) : Finset ℝ := by
  classical
  let P := candidate v data
  exact univ.biUnion fun s => univ.biUnion fun t => ((P s).val^2-(P t).val^2).roots.toFinset

/-- The final node depends only on the observed heating values. -/
def finalNode (v : Nodes d) (data : Fin (d+1) → ℝ) : ℝ := (excluded v data).exists_notMem.choose

/-- After d+1 fixed samples a single adaptive heating sample suffices for
all real slopes of degree at most d, including polynomials with sample zeros. -/
theorem adaptive_recovery (v : Nodes d) (P Q : Channel d)
    (h : ∀ i, power P.val (v i)=power Q.val (v i)) :
    let data := fun i => power P.val (v i)
    power P.val (finalNode v data)=power Q.val (finalNode v data) ↔ power P.val=power Q.val := by
  intro data
  refine ⟨fun ef => ?_,fun e => congrFun e _⟩
  obtain ⟨s,hs⟩ := candidate_complete v P
  obtain ⟨t,ht⟩ := candidate_complete v Q
  rw [← funext h] at ht
  let x := finalNode v data
  by_contra neq
  have hn : P.val^2-Q.val^2≠0 := by
    intro eq
    apply neq
    funext a
    simpa only [power,eval_pow] using congrArg (Polynomial.eval a) (sub_eq_zero.mp eq)
  have root : x∈(P.val^2-Q.val^2).roots.toFinset := by
    rw [Multiset.mem_toFinset,mem_roots hn,IsRoot.def,eval_sub,eval_pow,eval_pow,sub_eq_zero]
    exact ef
  apply (excluded v data).exists_notMem.choose_spec
  apply mem_biUnion.mpr
  refine ⟨s,mem_univ _,mem_biUnion.mpr ⟨t,mem_univ _,?_⟩⟩
  change x∈((candidate v data s).val^2-(candidate v data t).val^2).roots.toFinset
  rwa [show candidate v data s=P from hs,show candidate v data t=Q from ht]

#print axioms power_eq_iff
#print axioms derivative_primitive
#print axioms fixed_threshold
#print axioms adaptive_recovery
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.HeatSamples
