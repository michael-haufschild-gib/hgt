import GaloisForLFunctions.RestrictedFactorizationCalculus.TheExplicitLogSquareRoughSet
import GaloisForLFunctions.BezoutValuationIncidence.CoprimeSquarefreeDensityAndMobiusDilationMeans

/-!
# The common main term of the two log-square rough sign counts

Both sign counts have the same explicit center, half of the accumulated
local squarefree density. The sum of their errors has square-root-plus-
epsilon growth unconditionally, so either count recovers the signed test.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev density (y : ℕ) := coprimeSquarefreeDensity (primorial y)
private def discrepancy (y : ℕ) (x : ℝ) :=
  coprimeSquarefreeCount (primorial y) ⌊x⌋₊-density y*x

private theorem density_mem_unit (Q : ℕ) :
    0 ≤ coprimeSquarefreeDensity Q ∧ coprimeSquarefreeDensity Q ≤ 1 := by
  unfold coprimeSquarefreeDensity
  have h0 : 0 ≤ RHTower.Sieve.squarefreeDensity := by rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  have h1 : RHTower.Sieve.squarefreeDensity ≤ 1 := by
    rw [RHTower.Sieve.squarefreeDensity_eq,div_le_one (by positivity)]
    nlinarith only [Real.pi_gt_three, sq_nonneg (Real.pi-3)]
  have hP := prod_le_one (s := Q.primeFactors)
    (f := fun p : ℕ => (p:ℝ)/(p+1)) (fun p _ => by positivity)
    (fun p _ => by rw [div_le_one (by positivity)]; linarith)
  exact ⟨mul_nonneg h0 (prod_nonneg (fun _ _ => by positivity)),
    (mul_le_mul_of_nonneg_left hP h0).trans (by simpa using h1)⟩

private theorem discrepancy_small (y : ℕ) {s x : ℝ} (hs : 0<s) (hs1 : s ≤ 1)
    (hx : 0 ≤ x) (hx1 : x<1) : |discrepancy y x| ≤ x^s := by
  have hc : coprimeSquarefreeCount (primorial y) ⌊x⌋₊=0 := by
    rw [Nat.floor_eq_zero.mpr hx1]; simp [coprimeSquarefreeCount]
  have hδ := (density_mem_unit (primorial y)).1
  have h := mul_le_mul_of_nonneg_right (density_mem_unit (primorial y)).2 hx
  rw [discrepancy,hc,zero_sub,abs_neg,abs_of_nonneg (mul_nonneg hδ hx)]
  apply (h.trans_eq (one_mul _)).trans
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' hx hx1.le hs.le hs1

private theorem discrepancy_unrestricted {x s : ℝ} (hs : 1/2 ≤ s) (hs1 : s ≤ 1)
    (hx : 0 ≤ x) : |discrepancy 0 x| ≤ 4*x^s := by
  have hs0 : 0<s := by linarith only [hs]
  by_cases h : x<1
  · exact (discrepancy_small 0 hs0 hs1 hx h).trans (by linarith only [Real.rpow_nonneg hx s])
  have hx1 := le_of_not_gt h
  have hcnt := RHTower.Sieve.abs_sum_moebius_sq_Icc_sub_le ⌊x⌋₊
  have hh : coprimeSquarefreeCount 1 ⌊x⌋₊=∑ n ∈ Icc 1 ⌊x⌋₊,(μ n:ℝ)^2 := by
    simp [coprimeSquarefreeCount,coprimeSquarefreeIndicator]
  rw [←hh] at hcnt
  have hδ := (density_mem_unit 1).1
  have hδ1 := (density_mem_unit 1).2
  rw [coprimeSquarefreeDensity_one] at hδ hδ1
  have fr : 0 ≤ x-(⌊x⌋₊:ℝ) := sub_nonneg.mpr (Nat.floor_le hx)
  have hf : x-(⌊x⌋₊:ℝ) ≤ 1 := by linarith only [Nat.lt_floor_add_one x]
  have err := mul_le_mul hf hδ1 hδ (by norm_num : (0:ℝ) ≤ 1)
  let V := RHTower.Sieve.squarefreeDensity
  change (x-(⌊x⌋₊:ℝ))*V ≤ 1*1 at err
  have tri := abs_sub (coprimeSquarefreeCount 1 ⌊x⌋₊- (⌊x⌋₊:ℝ)*V) ((x-(⌊x⌋₊:ℝ))*V)
  rw [abs_of_nonneg (mul_nonneg fr hδ)] at tri
  have root : Real.sqrt (⌊x⌋₊:ℕ) ≤ x^s := (Real.sqrt_le_sqrt (Nat.floor_le hx)).trans (by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hx1 hs)
  have h1 := Real.one_le_rpow hx1 hs0.le
  simp only [discrepancy,density,primorial_zero,coprimeSquarefreeDensity_one]
  change |coprimeSquarefreeCount 1 ⌊x⌋₊-V*x| ≤ _
  rw [show coprimeSquarefreeCount 1 ⌊x⌋₊-V*x=
    (coprimeSquarefreeCount 1 ⌊x⌋₊-(⌊x⌋₊:ℝ)*V)-(x-(⌊x⌋₊:ℝ))*V by ring]
  change |coprimeSquarefreeCount 1 ⌊x⌋₊-(⌊x⌋₊:ℝ)*V| ≤ _ at hcnt
  linarith only [tri,err,hcnt,root,h1]

private theorem discrepancy_step {y : ℕ} (hp : (y+1).Prime) (x : ℝ) :
    discrepancy y x=discrepancy (y+1) x+discrepancy (y+1) (x/(y+1:ℕ)) := by
  let p := y+1
  let Q := primorial y
  have hd : ¬p ∣ Q := fun he => (Nat.not_succ_le_self y) (hp.dvd_primorial_iff.1 he)
  have hcnt := coprimeSquarefreeCount_prime_relation hp hd ⌊x⌋₊
  have hden := coprimeSquarefreeDensity_prime_mul hp hd (primorial_ne_zero _)
  have hpr : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have den : coprimeSquarefreeDensity Q=
      coprimeSquarefreeDensity (p*Q)+coprimeSquarefreeDensity (p*Q)/(p:ℝ) := by
    rw [hden]; field_simp; ring
  dsimp only [discrepancy,density]
  rw [Nat.floor_div_natCast,RHTower.DeletionResidueMartingale.primorial_succ_eq,if_pos hp]
  change coprimeSquarefreeCount Q ⌊x⌋₊-coprimeSquarefreeDensity Q*x=_
  rw [hcnt,den]
  change _=coprimeSquarefreeCount (p*Q) ⌊x⌋₊-coprimeSquarefreeDensity (p*Q)*x+
    (coprimeSquarefreeCount (p*Q) (⌊x⌋₊/p)-coprimeSquarefreeDensity (p*Q)*(x/p))
  ring

/-- Uniform squarefree discrepancy for every primorial, including real
endpoints strictly between two integers. -/
theorem primorial_squarefree_discrepancy {s : ℝ} (hs : 1/2 ≤ s) (hs1 : s ≤ 1)
    (y : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    |coprimeSquarefreeCount (primorial y) ⌊x⌋₊-coprimeSquarefreeDensity (primorial y)*x| ≤
      4*deletionPrice s y*x^s := by
  have hs0 : 0<s := by linarith only [hs]
  change |discrepancy y x| ≤ _
  induction y generalizing x with
  | zero => simpa [deletionPrice] using discrepancy_unrestricted hs hs1 hx
  | succ y prev =>
    by_cases hp : (y+1).Prime
    · let p := y+1
      let E := deletionPrice s p
      let r := (1/(p:ℝ))^s
      have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
      have gap : 0<1-r := sub_pos.mpr (deletion_weight_lt_one hs0 hp)
      have ege : 1 ≤ E := deletionPrice_one_le hs0 _
      have pay : E*(1-r)=deletionPrice s y := by
        dsimp only [E,r,p]; rw [deletionPrice_succ,if_pos hp,mul_assoc,inv_mul_cancel₀ gap.ne',mul_one]
      have bound (k : ℕ) (v : ℝ) (hv : 0 ≤ v) (hk : ⌊v⌋₊=k) : |discrepancy p v| ≤ 4*E*v^s := by
        induction k using Nat.strong_induction_on generalizing v with
        | h k ih =>
          by_cases z : k=0
          · have hlt := Nat.floor_eq_zero.mp (hk.trans z)
            apply (discrepancy_small p hs0 hs1 hv hlt).trans
            have he : 1 ≤ 4*E := by linarith only [ege]
            simpa only [one_mul] using mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hv s)
          have hf : ⌊v/(p:ℝ)⌋₊<k := by
            rw [Nat.floor_div_natCast,hk]; exact Nat.div_lt_self (Nat.pos_of_ne_zero z) hp.one_lt
          have hsmall := ih _ hf (v/p) (div_nonneg hv hp0.le) rfl
          have hpow : (v/(p:ℝ))^s=r*v^s := by
            rw [show v/(p:ℝ)=(1/(p:ℝ))*v by ring,Real.mul_rpow (by positivity) hv]
          rw [hpow] at hsmall
          have he : discrepancy p v=discrepancy y v-discrepancy p (v/(p:ℝ)) :=
            by linarith only [discrepancy_step hp v]
          rw [he]
          apply (abs_sub ..).trans
          calc _ ≤ 4*deletionPrice s y*v^s+4*E*(r*v^s) := add_le_add (prev v hv) hsmall
               _ = _ := by rw [←pay]; ring
      exact bound ⌊x⌋₊ x hx rfl
    · simpa only [discrepancy,density,RHTower.DeletionResidueMartingale.primorial_succ_eq,if_neg hp,
        deletionPrice_succ] using prev x hx

/-- Accumulated local density, with each integer tested at its own cutoff. -/
def roughSquarefreeMain (X : ℕ) := ∑ n ∈ Icc 1 X,density (logSquareCutoff n)

private def centered (y n : ℕ) := coprimeSquarefreeIndicator (primorial y) n-density y
private def centerPrefix (X : ℕ) := ∑ n ∈ Icc 1 X, centered (logSquareCutoff n) n

private theorem row_prefix (y X : ℕ) :
    (∑ n ∈ Icc 1 X,centered y n)=discrepancy y X := by
  simp [centered,sum_sub_distrib,discrepancy,coprimeSquarefreeCount,mul_comm]

private theorem center_plateau {l X : ℕ} (hl : l ≤ X)
    (flat : ∀ n,l<n → n ≤ X → logSquareCutoff n=logSquareCutoff X) :
    centerPrefix X-centerPrefix l=discrepancy (logSquareCutoff X) X-discrepancy (logSquareCutoff X) l := by
  have sub : Icc 1 l ⊆ Icc 1 X := Icc_subset_Icc le_rfl hl
  unfold centerPrefix
  rw [←row_prefix,←row_prefix,←sum_sdiff_eq_sub sub,←sum_sdiff_eq_sub sub]
  apply sum_congr rfl
  intro n hn
  obtain ⟨hi,ho⟩ := mem_sdiff.mp hn
  rw [flat n (lt_of_not_ge (fun h => ho (mem_Icc.mpr ⟨(mem_Icc.mp hi).1,h⟩))) (mem_Icc.mp hi).2]

private theorem center_bound {s : ℝ} (hs : 1/2 ≤ s) (hs1 : s ≤ 1) (X : ℕ) :
    |centerPrefix X| ≤ 8*((logSquareCutoff X:ℝ)+1)*deletionPrice s (logSquareCutoff X)*(X:ℝ)^s := by
  let b := logSquareCutoff
  have hs0 : 0<s := by linarith only [hs]
  induction X using Nat.strong_induction_on with
  | h X ih =>
    obtain ⟨l,hl,earlier,flat⟩ := interval_of_last_cutoff b logSquareCutoff_mono X
    let E := deletionPrice s (b X)
    have he : 0 ≤ E := zero_le_one.trans (deletionPrice_one_le hs0 _)
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg l) (Nat.cast_le.mpr hl) hs0.le
    have d1 := primorial_squarefree_discrepancy hs hs1 (b X) X (Nat.cast_nonneg _)
    have d2 := primorial_squarefree_discrepancy hs hs1 (b X) l (Nat.cast_nonneg _)
    change |discrepancy (b X) X| ≤ 4*E*(X:ℝ)^s at d1
    change |discrepancy (b X) l| ≤ 4*E*(l:ℝ)^s at d2
    have localError : |centerPrefix X-centerPrefix l| ≤ 8*E*(X:ℝ)^s := by
      rw [center_plateau hl flat]
      apply (abs_sub ..).trans
      have dl := d2.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
      linarith only [dl,d1]
    have old : |centerPrefix l| ≤ 8*(b X:ℝ)*E*(X:ℝ)^s := by
      rcases earlier with rfl | ⟨hlt,hjump⟩
      · have z : centerPrefix 0=0 := by simp [centerPrefix]
        rw [z,abs_zero]; positivity
      · have hj : (b l:ℝ)+1 ≤ b X := by exact_mod_cast hjump
        apply (ih l hlt).trans
        exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hj (by norm_num))
          (deletionPrice_mono hs0 (logSquareCutoff_mono hl))
          (zero_le_one.trans (deletionPrice_one_le hs0 _)) (by positivity)) hpow
          (Real.rpow_nonneg (Nat.cast_nonneg l) _) (by positivity)
    have tri := abs_add_le (centerPrefix X-centerPrefix l) (centerPrefix l)
    rw [sub_add_cancel] at tri
    change |centerPrefix X| ≤ 8*((b X:ℝ)+1)*E*(X:ℝ)^s
    linarith only [tri,localError,old]

private theorem center_power {s : ℝ} (hs : 1/2<s) : PrefixPower s centerPrefix := by
  let u := (1/2+min s 1)/2
  have hmin : (1/2:ℝ) < min s 1 := lt_min hs (by norm_num)
  have hu : (1/2:ℝ)<u := by dsimp only [u]; linarith only [hmin]
  have hu1 : u ≤ 1 := by dsimp only [u]; linarith only [min_le_right s 1]
  have hus : u<s := by dsimp only [u]; linarith only [hs,min_le_left s 1]
  apply prefixPower_of_eventual (C := 8) (by simp [centerPrefix]) (by linarith only [hs])
  filter_upwards [log_square_deletion_cost hu (sub_pos.mpr hus),eventually_ge_atTop (1:ℕ)] with X hprice hX
  let E := deletionPrice u (logSquareCutoff X)
  have he : 1 ≤ E := deletionPrice_one_le (by linarith only [hu]) _
  have he2 : E ≤ E^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr he) (zero_le_one.trans he)]
  have cost := (mul_le_mul_of_nonneg_left he2 (by positivity : 0 ≤ (logSquareCutoff X:ℝ)+1)).trans hprice
  have h := center_bound hu.le hu1 X
  apply h.trans
  calc _ = 8*(((logSquareCutoff X:ℝ)+1)*E)*(X:ℝ)^u := by ring
       _ ≤ 8*(X:ℝ)^(s-u)*(X:ℝ)^u := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cost (by norm_num))
         (Real.rpow_nonneg (Nat.cast_nonneg _) _)
       _ = _ := by rw [mul_assoc,←Real.rpow_add (Nat.cast_pos.mpr hX),sub_add_cancel]

private theorem center_eq (X : ℕ) :
    centerPrefix X=((squarefreeOf (logSquareRoughSet X)).card:ℝ)-roughSquarefreeMain X := by
  unfold centerPrefix centered roughSquarefreeMain
  rw [sum_sub_distrib]
  congr 1
  let S := squarefreeOf (logSquareRoughSet X)
  have eq : S=(Icc 1 X).filter (fun n => (primorial (logSquareCutoff n)).Coprime n ∧ Squarefree n) := by
    ext n; simp [S,squarefreeOf,logSquareRoughSet,and_assoc]
  change _=(S.card:ℝ)
  rw [eq,←sum_boole]
  apply sum_congr rfl
  intro n _
  by_cases hc : (primorial (logSquareCutoff n)).Coprime n
  · rw [coprimeSquarefreeIndicator,if_pos hc]
    by_cases hs : Squarefree n
    · rw [if_pos ⟨hc,hs⟩]
      have hz := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs
      rcases moebius_eq_or n with hh | hh | hh <;> simp_all
    · rw [if_neg (fun h => hs h.2),moebius_eq_zero_of_not_squarefree hs]; norm_num
  · simp [coprimeSquarefreeIndicator,hc]

/-- Uniform square-root-plus-epsilon discrepancy for the total squarefree
population of the explicit rough set. -/
theorem square_root_for_the_unsigned_rough_population {s : ℝ} (hs : 1/2<s) :
    PrefixPower s (fun X => ((squarefreeOf (logSquareRoughSet X)).card:ℝ)-roughSquarefreeMain X) := by
  have eq := funext center_eq
  rw [←eq]; exact center_power hs

/-- The deviation of one sign count from its common explicit main term. -/
def roughParityError (positive : Bool) (X : ℕ) :=
  ((if positive then posParity (logSquareRoughSet X) else negParity (logSquareRoughSet X)).card:ℝ)
    -roughSquarefreeMain X/2

private theorem parity_identity (positive : Bool) (X : ℕ) :
    2*roughParityError positive X=centerPrefix X+
      (if positive then 1 else -1)*(∑ n ∈ logSquareRoughSet X,(μ n:ℝ)) := by
  let S := logSquareRoughSet X
  have hc := congrArg ((↑):ℕ → ℝ) (card_squarefreeOf S)
  push_cast only [Nat.cast_add] at hc
  have hd : (∑ n ∈ S,(μ n:ℝ))=((posParity S).card:ℝ)-((negParity S).card:ℝ) := by
    exact_mod_cast sum_moebius_eq_card_pos_sub_neg S
  rw [center_eq]
  cases positive <;> simp only [roughParityError,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul] <;>
    change _=(((squarefreeOf S).card:ℝ)-roughSquarefreeMain X)+_ <;> rw [hc,hd] <;> ring

/-- For every exponent above one half, either individual parity error
has exactly the same power bound as the signed rough prefix. -/
theorem one_rough_sign_detects_the_signed_power (positive : Bool) {s : ℝ} (hs : 1/2<s) :
    PrefixPower s (roughParityError positive) ↔
      PrefixPower s (fun X => ∑ n ∈ logSquareRoughSet X,(μ n:ℝ)) := by
  obtain ⟨A,hA,ha⟩ := center_power hs
  constructor
  · rintro ⟨C,hC,h⟩
    refine ⟨2*C+A,by positivity,fun X => ?_⟩
    have eq := parity_identity positive X
    have ht := abs_sub (2*roughParityError positive X) (centerPrefix X)
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
    have habs : |2*roughParityError positive X-centerPrefix X|=|∑ n ∈ logSquareRoughSet X,(μ n:ℝ)| := by
      rw [eq,add_sub_cancel_left,abs_mul]
      cases positive <;> simp
    rw [habs] at ht
    linarith only [ht,h X,ha X]
  · rintro ⟨C,hC,h⟩
    refine ⟨(A+C)/2,by positivity,fun X => ?_⟩
    have eq := congrArg abs (parity_identity positive X)
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at eq
    have ht := abs_add_le (centerPrefix X) ((if positive then 1 else -1)*(∑ n ∈ logSquareRoughSet X,(μ n:ℝ)))
    rw [abs_mul,show |(if positive then (1:ℝ) else -1)|=1 by cases positive <;> norm_num,one_mul] at ht
    linarith only [ht,eq,h X,ha X]

/-- A square-root estimate for the discrepancy of either specified sign
alone is equivalent to the full Möbius square-root estimates. -/
theorem square_root_from_one_explicit_rough_sign (positive : Bool) :
    (∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (roughParityError positive)) ↔
    ∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (coprimeMoebiusSum 1) := by
  rw [←square_root_on_the_explicit_log_square_rough_set]
  exact forall_congr' (fun ε => forall_congr' (fun hε => one_rough_sign_detects_the_signed_power positive
    (lt_add_of_pos_right (1/2:ℝ) hε)))

#print axioms primorial_squarefree_discrepancy
#print axioms square_root_for_the_unsigned_rough_population
#print axioms one_rough_sign_detects_the_signed_power
#print axioms square_root_from_one_explicit_rough_sign

end GaloisForLFunctions.RestrictedFactorizationCalculus
