import GaloisForLFunctions.ExceptionalLayerTheory.TransposingTheComplementaryFactorTail
import GaloisForLFunctions.ExceptionalLayerTheory.TheCompletedCofactorRowRetainsThePrimeError

/-!
# The prime error on every complementary-factor tail

The factorial approximation at each divided horizon has logarithmic
error. Pairing that error with bounded prefixes of the inner jumps gives
square-root precision for every complementary cutoff.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Complete Mangoldt row above a complementary cutoff. -/
def completeComplementTail (D R X a : ℕ) : ℝ :=
  ∑ v ∈ Ioc a X, innerJump D v*
    ∑ u ∈ Icc 1 (X/v), vonMangoldt u*centeredPrimeWeight R (X/v/u)

/-- Signed dilation of the ordinary Chebyshev error above the same cutoff. -/
def primeErrorTail (D X a : ℕ) : ℝ :=
  ∑ v ∈ Ioc a X, innerJump D v*(Chebyshev.psi (X/v : ℕ)-(X/v : ℕ))

/-- The complete Mangoldt row may be replaced by one signed dilation of
the genuine prime error, uniformly over the entire range of cutoffs. -/
theorem completeComplementTail_sub_primeErrorTail {R : ℕ} (hR : 1≤R) (D X a : ℕ) :
    |completeComplementTail D R X a-primeErrorTail D X a|≤
      4*(1+mass (D+1))*(420*(1+mass R)*(3+Real.log (128*(128*R^2+1) : ℕ)+2*Real.log X))*Real.sqrt X := by
  let w (t : ℕ) := (∑ u ∈ Icc 1 t, vonMangoldt u*centeredPrimeWeight R (t/u))-(Chebyshev.psi t-t)
  let H := 3+Real.log (128*(128*R^2+1) : ℕ)+2*Real.log X
  let B := 420*(1+mass R)*H
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  have hd := (abs_nonneg _).trans (abs_prefix_le_mass (Nat.succ_pos D) 0)
  have hH : 0≤H := by
    dsimp [H]
    have := Real.log_natCast_nonneg (128*(128*R^2+1)); have := Real.log_natCast_nonneg X; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hw (t : ℕ) (ht : t≤X) : |w t|≤B := by
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · simpa [w,Chebyshev.psi] using hB
    dsimp only [w]; rw [abs_sub_comm]
    apply (centeredPrimeWeight_factorial hR hpos).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hl := Real.log_le_log (by exact_mod_cast hpos : (0 : ℝ)<t) (by exact_mod_cast ht : (t : ℝ)≤X)
    dsimp [H]; linarith only [hl]
  let W (t : ℕ) := if t≤X then w t else 0
  have bound (t : ℕ) : |W t|≤B := by
    by_cases h : t≤X
    · simpa only [W,if_pos h] using hw t h
    · simpa only [W,if_neg h,abs_zero] using hB
  have prefix (t : ℕ) (_ht : t≤X) : |∑ v ∈ Ioc 0 t, innerJump D v|≤1+mass (D+1) := by
    rw [show Ioc 0 t=Icc 1 t by ext n; simp only [mem_Ioc,mem_Icc]; omega]
    exact innerJump_prefix_bound D t
  have eq : completeComplementTail D R X a-primeErrorTail D X a=
      ∑ v ∈ Ioc a X, innerJump D v*W (X/v) := by
    unfold completeComplementTail primeErrorTail
    rw [←sum_sub_distrib]
    exact sum_congr rfl fun v _ => by rw [←mul_sub]; simp only [W,if_pos (Nat.div_le_self X v),w]
  have hs : ((Nat.sqrt X : ℕ) : ℝ)≤Real.sqrt X :=
    (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by
      simpa only [sq,Nat.cast_mul] using (by exact_mod_cast Nat.sqrt_le X :
        ((Nat.sqrt X : ℕ) : ℝ)*Nat.sqrt X≤X))
  rw [eq]
  exact (abs_truncated_quotient_pair a _ W (by positivity) hB prefix bound).trans
    (mul_le_mul_of_nonneg_left hs (by positivity))

private theorem jump_unit_and_divisors (D : ℕ) {v : ℕ} (hv : 1≤v) :
    innerJump D v=(if v=1 then 1 else 0)-stencil (D+1) (fun e => if e∣v then 1 else 0) := by
  by_cases h : v=1
  swap
  · rw [if_neg h,zero_sub]; exact innerJump_divisor_stencil (by omega) D
  subst v
  have div1 (d : ℕ) : ((1/d : ℕ) : ℝ)=(if d∣1 then 1 else 0) := by
    have he : (1/d : ℕ)=if d∣1 then 1 else 0 := by
      simpa only [Nat.zero_add,Nat.zero_div] using Nat.succ_div (a := 0) (b := d)
    by_cases h : d∣1
    · rw [if_pos h] at he ⊢; exact_mod_cast he
    · rw [if_neg h] at he ⊢; exact_mod_cast he
  change (if (1 : ℕ)=0 then 0 else 1-factorialPrefix (D+1) 1)-
    (if (1 : ℕ)-1=0 then 0 else 1-factorialPrefix (D+1) (1-1))=_
  simp only [if_neg Nat.one_ne_zero,Nat.sub_self,if_pos rfl,sub_zero,factorialPrefix,div1]

/-- Completing the inner error dilation leaves exactly the factorial
stencil of the unweighted complete divisor errors. -/
theorem complete_primeErrorTail_identity (D : ℕ) {X : ℕ} (hx : 1≤X) :
    primeErrorTail D X 0=(Chebyshev.psi X-X)-stencil (D+1) (fun e => completeDivisorError (X/e)) := by
  let E (t : ℕ) := Chebyshev.psi t-(t : ℝ)
  let z (v : ℕ) := E (X/v)
  let I := Ioc 0 X
  let ind (v e : ℕ) : ℝ := if e∣v then 1 else 0
  have one : (∑ v ∈ I, (if v=1 then (1 : ℝ) else 0)*z v)=E X := by
    rw [sum_eq_single 1]
    · simp [z]
    · intro b _ hb; simp [hb]
    · intro hn; exact (hn (mem_Ioc.mpr ⟨by decide,hx⟩)).elim
  have fibre (e : ℕ) : (∑ v ∈ I, z v*ind v e)=completeDivisorError (X/e) := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · have hz (v : ℕ) (hv : v ∈ I) : z v*ind v 0=0 := by
        simp [ind,Nat.ne_of_gt (mem_Ioc.mp hv).1]
      simpa only [sum_congr rfl hz,sum_const_zero,Nat.div_zero,completeDivisorError,Icc_eq_empty (by decide : ¬1≤(0 : ℕ)),sum_empty]
    have eq : (∑ v ∈ I, z v*ind v e)=(∑ v ∈ I with e∣v, z v) := by
      rw [sum_filter]; exact sum_congr rfl fun v _ => by by_cases h : e∣v <;> simp [h,ind]
    rw [eq,show I=Ioc 0 X from rfl,sum_divisible_Ioc he,Nat.zero_div]
    simp only [completeDivisorError,z,E,Nat.div_div_eq_div_mul]
    rw [show Ioc 0 (X/e)=Icc 1 (X/e) by ext v; simp only [mem_Icc,mem_Ioc]; omega]
  calc primeErrorTail D X 0 = ∑ v ∈ I, ((if v=1 then 1 else 0)*z v-z v*stencil (D+1) (ind v)) := by
         apply sum_congr rfl; intro v hv
         rw [jump_unit_and_divisors D (mem_Ioc.mp hv).1]; dsimp only [ind,z,E]; ring
       _ = _ := by
         rw [sum_sub_distrib,one,stencil_weighted_sum]
         simp_rw [fibre]

/-- The complete dilation reproduces the actual prime error with a
square-root remainder. The zero reciprocal moment cancels the entire
linear divisor mean. -/
theorem complete_primeErrorTail_bound (D : ℕ) {X : ℕ} (hx : 1≤X) :
    |(Chebyshev.psi X-X)-primeErrorTail D X 0|≤mass (D+1)*(25*Real.sqrt X+2*|Real.eulerMascheroniConstant|) := by
  let γ := Real.eulerMascheroniConstant
  let f (e : ℕ) := completeDivisorError (X/e)
  let main (e : ℕ) := ((-2*γ)*(X : ℝ))/e
  have hz : stencil (D+1) main=0 := stencil_linear_quotient (Nat.succ_pos D) _
  have hh := abs_stencil_le (Nat.succ_pos D) (fun e => f e-main e)
    (M := 25*Real.sqrt X+2*|γ|) (fun e he => by
      let n := X/e
      have hl : Real.sqrt (n : ℝ)≤Real.sqrt X := Real.sqrt_le_sqrt (by exact_mod_cast Nat.div_le_self X e)
      have ha : |((n : ℕ) : ℝ)-(X : ℝ)/e|≤1 := Sieve.abs_natDiv_sub_div_le (mem_Icc.mp he).1
      have eq : f e-main e=(completeDivisorError n+2*γ*n)-(2*γ)*((n : ℝ)-(X : ℝ)/e) := by dsimp [f,main,n]; ring
      rw [eq]
      apply (abs_sub _ _).trans
      rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
      exact add_le_add ((abs_completeDivisorError_add_le n).trans (mul_le_mul_of_nonneg_left hl (by norm_num)))
        ((mul_le_mul_of_nonneg_left ha (by positivity)).trans_eq (mul_one _)))
  rw [stencil_sub,hz,sub_zero] at hh
  rw [complete_primeErrorTail_identity D hx]
  change |(Chebyshev.psi X-X)-((Chebyshev.psi X-X)-stencil (D+1) f)|≤_
  rw [show (Chebyshev.psi X-X)-((Chebyshev.psi X-X)-stencil (D+1) f)=stencil (D+1) f by ring]
  exact hh

/-- Transposition bounds the entire tail by the absolute Mangoldt mass
at the reciprocal cutoff. Both primitive endpoints are bounded. -/
theorem primeErrorTail_reciprocal_bound (D X : ℕ) {a : ℕ} (ha : 1≤a) :
    |primeErrorTail D X a|≤16*mass (D+1)*(X/(a+1) : ℕ) := by
  let e (n : ℕ) := vonMangoldt n-1
  let U := X/(a+1)
  have herr (t : ℕ) : Chebyshev.psi t-t=∑ n ∈ Icc 1 t, e n := by
    have hψ : (∑ n ∈ Icc 1 t, vonMangoldt n)=Chebyshev.psi t := by
      unfold Chebyshev.psi; rw [Nat.floor_natCast]; rfl
    simp only [e,sum_sub_distrib,hψ,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one]
  have habs : (∑ n ∈ Icc 1 U, |e n|)≤8*U := by
    calc _ ≤ ∑ n ∈ Icc 1 U, (vonMangoldt n+1) := sum_le_sum fun n _ => by
              simpa only [e,abs_of_nonneg vonMangoldt_nonneg,abs_one] using abs_sub (vonMangoldt n) (1 : ℝ)
         _ ≤ _ := by
              rw [sum_add_distrib,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one]
              have h : (∑ n ∈ Icc 1 U, vonMangoldt n)≤7*U := chebyshevPsi_le_seven U
              linarith only [h]
  have heq : primeErrorTail D X a =
      ∑ n ∈ Icc 1 U, e n*∑ v ∈ Icc (a+1) (X/n), innerJump D v := by
    unfold primeErrorTail
    rw [show Ioc a X=Icc (a+1) X by ext n; simp only [mem_Ioc,mem_Icc]; omega]
    simp_rw [herr,mul_sum]
    calc _ = ∑ v ∈ Icc (a+1) X, ∑ n ∈ Icc 1 (X/v), e n*innerJump D v := by
                exact sum_congr rfl fun v _ => sum_congr rfl fun n _ => mul_comm ..
         _ = _ := by
                rw [sum_hyperbola_tail_swap_real X (a+1) _ (Nat.succ_pos a)]
                simp only [U,mul_sum]
  rw [heq]
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass (Nat.succ_pos D) 0)
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ n ∈ Icc 1 U, |e n|*(2*mass (D+1)) := by
            apply sum_le_sum; intro n hn
            obtain ⟨hn₁,hn₂⟩ := mem_Icc.mp hn
            have hna := (Nat.le_div_iff_mul_le (Nat.succ_pos a)).mp hn₂
            have hq : a+1≤X/n := (Nat.le_div_iff_mul_le hn₁).mpr (by rwa [Nat.mul_comm] at hna)
            rw [abs_mul,innerJump_sum_between D ha ((Nat.le_succ a).trans hq)]
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            rw [show factorialBoundary (D+1) (X/n)-factorialBoundary (D+1) a=
              factorialPrefix (D+1) a-factorialPrefix (D+1) (X/n) by unfold factorialBoundary; ring]
            exact (abs_sub _ _).trans ((add_le_add (abs_prefix_le_mass (Nat.succ_pos D) _)
              (abs_prefix_le_mass (Nat.succ_pos D) _)).trans_eq (by ring))
       _ ≤ _ := by
            rw [←sum_mul]
            exact (mul_le_mul_of_nonneg_right habs (by positivity)).trans_eq (by dsimp [U]; ring)

/-- The prime error is reproduced, to square-root precision times the
stencil mass, by genuinely smaller divided horizons. All indices through
the freely chosen inner cutoff vanish identically. -/
theorem prime_error_on_shorter_horizons {X : ℕ} (hx : 1≤X) (D : ℕ) :
    |(Chebyshev.psi X-X)-∑ v ∈ Ioc D ⌊Real.sqrt X⌋₊, innerJump D v*
        (Chebyshev.psi (X/v : ℕ)-(X/v : ℕ))|≤
      mass (D+1)*(41*Real.sqrt X+2*|Real.eulerMascheroniConstant|) := by
  let M := ⌊Real.sqrt X⌋₊
  let f (v : ℕ) := innerJump D v*(Chebyshev.psi (X/v : ℕ)-(X/v : ℕ))
  have hx₁ : (1 : ℝ)≤X := by exact_mod_cast hx
  have hroot := Real.one_le_sqrt.mpr hx₁
  have hm : 1≤M := (Nat.one_le_floor_iff _).mpr hroot
  have hmX : M≤X := Nat.floor_le_of_le ((le_mul_of_one_le_right (Real.sqrt_nonneg _) hroot).trans_eq
    (Real.mul_self_sqrt (Nat.cast_nonneg X)))
  have hu : ((X/(M+1) : ℕ) : ℝ)≤Real.sqrt X := by
    apply Nat.cast_div_le.trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<(M+1 : ℕ))).mpr
    have half : Real.sqrt X≤((M+1 : ℕ) : ℝ) := by push_cast; exact (Nat.lt_floor_add_one _).le
    exact (Real.mul_self_sqrt (Nat.cast_nonneg X)).symm.le.trans (mul_le_mul_of_nonneg_left half (Real.sqrt_nonneg _))
  have del : (∑ v ∈ Ioc D M, f v)=∑ v ∈ Ioc 0 M, f v := by
    apply sum_subset (fun v (hv : v ∈ Ioc D M) => mem_Ioc.mpr
      ⟨(Nat.zero_le D).trans_lt (mem_Ioc.mp hv).1,(mem_Ioc.mp hv).2⟩)
    intro v hv hn
    have hvD : v≤D := by by_contra! h; exact hn (mem_Ioc.mpr ⟨h,(mem_Ioc.mp hv).2⟩)
    simp only [f,innerJump_small hvD,zero_mul]
  have eq : (Chebyshev.psi X-X)-(∑ v ∈ Ioc D M, f v) =
      ((Chebyshev.psi X-X)-primeErrorTail D X 0)+primeErrorTail D X M := by
    rw [del]
    change _=(_-(∑ v ∈ Ioc 0 X, f v))+(∑ v ∈ Ioc M X, f v)
    rw [←sum_Ioc_consecutive f (Nat.zero_le M) hmX]; ring
  rw [eq]
  have hmass := (abs_nonneg _).trans (abs_prefix_le_mass (Nat.succ_pos D) 0)
  have ht := (primeErrorTail_reciprocal_bound D X hm).trans (mul_le_mul_of_nonneg_left hu (by positivity))
  exact (abs_add_le _ _).trans ((add_le_add (complete_primeErrorTail_bound D hx) ht).trans_eq (by ring))

/-- Power cutoff for the signed smaller-horizon prime errors. -/
def shorterPrimeErrors (δ : ℝ) (X : ℕ) : ℝ :=
  let D := ⌊(X : ℝ)^δ⌋₊
  ∑ v ∈ Ioc D ⌊Real.sqrt X⌋₊, innerJump D v*(Chebyshev.psi (X/v : ℕ)-(X/v : ℕ))

/-- Every retained error is evaluated below the complementary power
of the divided horizon. -/
theorem shorterPrimeErrors_horizon {X v : ℕ} {δ : ℝ} (hx : 1≤X)
    (hv : v ∈ Ioc ⌊(X : ℝ)^δ⌋₊ ⌊Real.sqrt X⌋₊) :
    ((X/v : ℕ) : ℝ)<(X : ℝ)^(1-δ) := by
  have hx₀ : (0 : ℝ)<X := by exact_mod_cast hx
  have hh : (X : ℝ)^δ < v := (Nat.lt_floor_add_one _).trans_le
    (by exact_mod_cast (show ⌊(X : ℝ)^δ⌋₊+1≤v from (mem_Ioc.mp hv).1))
  have hv₀ := (Real.rpow_pos_of_pos hx₀ δ).trans hh
  apply Nat.cast_div_le.trans_lt
  apply (div_lt_iff₀ hv₀).mpr
  have eq : (X : ℝ)^(1-δ)*(X : ℝ)^δ=X := by rw [←Real.rpow_add hx₀,sub_add_cancel,Real.rpow_one]
  exact eq.symm.le.trans_lt (mul_lt_mul_of_pos_left hh (Real.rpow_pos_of_pos hx₀ _))

/-- Both original Vaughan widths admit the same signed expansion in
smaller Chebyshev errors. A power cutoff costs exactly that power on
top of the square root, with one uniform constant for all cutoffs. -/
theorem shorter_prime_error_cofactors :
    ∃ K : ℝ, 0≤K ∧ ∀ {δ : ℝ}, 0≤δ → ∀ V W N : ℕ,
      |cofactorCountError V W N-∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*shorterPrimeErrors δ (N/d)|≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*(N : ℝ)^(1/2+δ)) := by
  obtain ⟨M,hM,hmass⟩ := mass_uniform
  let C := 41+2*|Real.eulerMascheroniConstant|
  have hC : 0≤C := by dsimp [C]; positivity
  let K := 2*M*C
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro δ hδ V W N
  let f (x : ℕ) := (Chebyshev.psi x-x)-shorterPrimeErrors δ x
  let g (x : ℕ) := K*(x : ℝ)^(1/2+δ)
  have he : 0≤(1/2 : ℝ)+δ := by linarith only [hδ]
  have bound (x : ℕ) (hx : 1≤x) : |f x|≤g x := by
    let D := ⌊(x : ℝ)^δ⌋₊
    have hx₁ : (1 : ℝ)≤x := by exact_mod_cast hx
    have hx₀ := zero_lt_one.trans_le hx₁
    have hp := Real.one_le_rpow hx₁ hδ
    have hroot := Real.one_le_sqrt.mpr hx₁
    have hd : ((D+1 : ℕ) : ℝ)≤2*(x : ℝ)^δ := by
      push_cast; linarith only [Nat.floor_le (zero_le_one.trans hp),hp]
    have hm := (hmass (D+1) (Nat.succ_pos D)).trans (mul_le_mul_of_nonneg_left hd hM)
    have hc : 41*Real.sqrt x+2*|Real.eulerMascheroniConstant|≤C*Real.sqrt x := by
      have hg := mul_le_mul_of_nonneg_left hroot (show 0≤2*|Real.eulerMascheroniConstant| by positivity)
      dsimp [C]; linarith only [hg]
    apply (prime_error_on_shorter_horizons hx D).trans
    apply (mul_le_mul hm hc (by positivity) (by positivity)).trans_eq
    dsimp only [g,K]
    rw [Real.rpow_add hx₀,←Real.sqrt_eq_rpow]
    ring
  have hh := cofactor_sum_majorant f g (fun n => mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun x n _ hn => mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hn) he) hK)
    bound V W N
  rw [cofactorCountError_eq,←sum_sub_distrib]
  simpa only [f,g,mul_sub] using hh

#print axioms shorterPrimeErrors_horizon
#print axioms shorter_prime_error_cofactors
#print axioms prime_error_on_shorter_horizons
#print axioms complete_primeErrorTail_identity
#print axioms complete_primeErrorTail_bound
#print axioms completeComplementTail_sub_primeErrorTail
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
