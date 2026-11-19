import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.AdaptiveHeatingThreshold
import GaloisForLFunctions.HTGeometry.UnivariateSumOfTwoSquares

/-!
# Two polynomial heating channels exhaust the nonnegative cone

A measured profile from two slopes of degree at most d is exactly a
nonnegative real polynomial of degree at most 2d. For any deterministic
sampling policy, the positive profile (1+x²)^d admits a perturbation that
vanishes at its first 2d visited points. The perturbed profile is still
nonnegative and therefore still realizable by two channels.
-/

noncomputable section
open Polynomial Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.HeatSamples
open JumpGrid

abbrev Pair (d : ℕ) := Channel d × Channel d

def pairSymbol {d : ℕ} (U : Pair d) : ℝ[X] := U.1.val^2+U.2.val^2

private theorem square_coeff (P : ℝ[X]) (k : ℕ) (h : P.natDegree≤k) :
    (P^2).coeff (2*k)=(P.coeff k)^2 := by
  rcases lt_or_eq_of_le h with h|rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_pow]; omega),coeff_eq_zero_of_natDegree_lt h,zero_pow (by norm_num)]
  · rw [← natDegree_pow,coeff_natDegree,leadingCoeff_pow,coeff_natDegree]

private theorem square_degrees {P A B : ℝ[X]} (d : ℕ) (hp : P.natDegree≤2*d)
    (he : P=A^2+B^2) : A.natDegree≤d ∧ B.natDegree≤d := by
  let m := max A.natDegree B.natDegree
  have ha : A.natDegree≤m := le_max_left _ _
  have hb : B.natDegree≤m := le_max_right _ _
  suffices hm : m≤d from ⟨ha.trans hm,hb.trans hm⟩
  by_contra! hm
  have hz := coeff_eq_zero_of_natDegree_lt (p:=P) (by omega : P.natDegree<2*m)
  rw [he,coeff_add,square_coeff A m ha,square_coeff B m hb] at hz
  have zero (U V : ℝ[X]) (hdeg : U.natDegree=m) (h : (U.coeff m)^2+(V.coeff m)^2=0) : False := by
    have hc : U.coeff m=0 := by nlinarith only [h,sq_nonneg (V.coeff m),sq_nonneg (U.coeff m)]
    rw [← hdeg,coeff_natDegree,leadingCoeff_eq_zero] at hc
    rw [hc,natDegree_zero] at hdeg
    omega
  rcases le_total B.natDegree A.natDegree with le|le
  · exact zero A B (max_eq_left le).symm hz
  · exact zero B A (max_eq_right le).symm (by linarith only [hz])

/-- Two jump slopes already realize every admissible heating polynomial. -/
theorem two_channel_cone (d : ℕ) (P : ℝ[X]) :
    (∃ U : Pair d, pairSymbol U=P) ↔ P.natDegree≤2*d ∧ ∀ x : ℝ, 0≤P.eval x := by
  constructor
  · rintro ⟨⟨A,B⟩,rfl⟩
    refine ⟨(natDegree_add_le _ _).trans (max_le ?_ ?_),fun x => ?_⟩
    · rw [natDegree_pow]; exact Nat.mul_le_mul_left _ A.property
    · rw [natDegree_pow]; exact Nat.mul_le_mul_left _ B.property
    · simp only [pairSymbol,eval_add,eval_pow]
      exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · rintro ⟨deg,pos⟩
    obtain ⟨A,B,he⟩ := HTGeometry.exists_sq_add_sq_of_nonneg (2*d) P deg pos
    obtain ⟨ha,hb⟩ := square_degrees d deg he
    exact ⟨(⟨A,ha⟩,⟨B,hb⟩),he.symm⟩

private def base (d : ℕ) : ℝ[X] := (1+X^2)^d

private theorem base_value (d : ℕ) (x : ℝ) : (base d).eval x=(1+x^2)^d := by simp [base]

private theorem base_degree (d : ℕ) : (base d).natDegree≤2*d := by
  rw [base,natDegree_pow,mul_comm 2 d]
  apply Nat.mul_le_mul_left
  apply (natDegree_add_le _ _).trans
  simp

private def normalizedLinear (u : ℝ) : ℝ[X] := (X-C u)*C (Real.sqrt (1+u^2))⁻¹

private theorem linear_value (u x : ℝ) : (normalizedLinear u).eval x=(x-u)/Real.sqrt (1+u^2) := by
  simp [normalizedLinear,div_eq_mul_inv]

private theorem linear_bound (u x : ℝ) : ((normalizedLinear u).eval x)^2≤1+x^2 := by
  rw [linear_value,div_pow,Real.sq_sqrt (by positivity),div_le_iff₀ (by positivity : 0<1+u^2)]
  nlinarith only [sq_nonneg (x*u+1)]

private def perturb {d : ℕ} (u : Fin (2*d) → ℝ) : ℝ[X] := ∏ i, normalizedLinear (u i)

private theorem perturb_degree {d : ℕ} (u : Fin (2*d) → ℝ) : (perturb u).natDegree≤2*d := by
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin (2*d), 1 := sum_le_sum fun i _ => by
      apply (natDegree_mul_le).trans
      simp [normalizedLinear,natDegree_X_sub_C]
    _ = _ := by simp

private theorem perturb_nonzero {d : ℕ} (u : Fin (2*d) → ℝ) : perturb u≠0 :=
  prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (X_sub_C_ne_zero _) (by
    apply C_ne_zero.mpr
    exact inv_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne')

private theorem perturb_at_node {d : ℕ} (u : Fin (2*d) → ℝ) (i : Fin (2*d)) :
    (perturb u).eval (u i)=0 := by
  rw [perturb,eval_prod]
  exact prod_eq_zero (mem_univ i) (by simp [linear_value])

private theorem positive_perturb {d : ℕ} (u : Fin (2*d) → ℝ) (x : ℝ) :
    0≤(base d+perturb u).eval x := by
  have bound : ((perturb u).eval x)^2≤((1+x^2)^d)^2 := by
    rw [perturb,eval_prod,← prod_pow]
    calc
      _ ≤ ∏ _i : Fin (2*d), (1+x^2) := prod_le_prod (fun _ _ => sq_nonneg _) (fun i _ => linear_bound (u i) x)
      _ = _ := by simp [← pow_mul,Nat.mul_comm]
  rw [eval_add,base_value]
  have h0 : 0≤(1+x^2)^d := by positivity
  have h := sq_le_sq.mp bound
  rw [abs_of_nonneg h0] at h
  linarith only [(abs_le.mp h).1]

/-- Two physically realizable profiles have identical complete transcripts
through 2d adaptive samples. Repeated sample locations are covered. -/
theorem two_channel_adaptive_lower (d : ℕ) (T : Policy) :
    ∃ U V : Pair d, readings T (pairSymbol U).eval (2*d)=readings T (pairSymbol V).eval (2*d) ∧
      pairSymbol U≠pairSymbol V := by
  let P := base d
  let u := fun i : Fin (2*d) => T (readings T P.eval i.val)
  let R := P+perturb u
  obtain ⟨U,hu⟩ := (two_channel_cone d P).mpr ⟨base_degree d,fun x => by rw [base_value]; positivity⟩
  obtain ⟨V,hv⟩ := (two_channel_cone d R).mpr ⟨(natDegree_add_le _ _).trans
    (max_le (base_degree d) (perturb_degree u)),positive_perturb u⟩
  refine ⟨U,V,?_,?_⟩ <;> rw [hu,hv]
  · have same (k : ℕ) (hk : k≤2*d) : readings T P.eval k=readings T R.eval k := by
      induction k with
      | zero => rfl
      | succ k ih =>
        have h : k<2*d := by omega
        simp only [readings,← ih h.le]
        change P.eval (u ⟨k,h⟩)::_=R.eval (u ⟨k,h⟩)::_
        rw [show R=P+perturb u from rfl,eval_add,perturb_at_node,add_zero]
    exact same _ le_rfl
  · intro e
    exact perturb_nonzero u (add_left_cancel ((add_zero P).trans e)).symm

/-- For two or more channels the degree bound on the profile is already
the exact sampling bound, even with sequentially chosen sample locations. -/
theorem two_channel_sequential_threshold (d n : ℕ) :
    (∃ T : Policy, ∀ U V : Pair d,
      readings T (pairSymbol U).eval n=readings T (pairSymbol V).eval n → pairSymbol U=pairSymbol V) ↔
        2*d<n := by
  classical
  constructor
  · rintro ⟨T,H⟩
    by_contra! hn
    obtain ⟨U,V,eq,ne⟩ := two_channel_adaptive_lower d T
    exact ne (H U V (readings_shorter _ _ _ hn eq))
  · intro hn
    let T : Policy := fun ys => (ys.length:ℝ)
    refine ⟨T,fun U V he => ?_⟩
    let P := pairSymbol U
    let Q := pairSymbol V
    let S := (range n).image (fun i : ℕ => (i:ℝ))
    have size : S.card=n := (card_image_of_injective _ Nat.cast_injective).trans (card_range n)
    have hp := ((two_channel_cone d P).mp ⟨U,rfl⟩).1
    have hq := ((two_channel_cone d Q).mp ⟨V,rfl⟩).1
    apply eq_of_natDegree_lt_card_of_eval_eq' P Q S _ ((max_le hp hq).trans_lt (by rwa [size]))
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    have e := readings_shorter T P.eval Q.eval (Nat.succ_le_of_lt (mem_range.mp hi)) he
    have heads := (List.cons.inj e).1
    simpa only [T,readings_length] using heads

#print axioms two_channel_cone
#print axioms two_channel_adaptive_lower
#print axioms two_channel_sequential_threshold
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.HeatSamples
