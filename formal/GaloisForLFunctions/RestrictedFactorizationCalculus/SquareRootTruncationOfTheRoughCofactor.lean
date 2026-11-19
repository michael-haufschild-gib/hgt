import GaloisForLFunctions.RestrictedFactorizationCalculus.TheExplicitLogSquareRoughSet
import GaloisForLFunctions.RHTower.Sieve.SmoothRough
import GaloisForLFunctions.RHTower.Sieve.MoebiusSquarefreeSmoothRankin
import GaloisForLFunctions.HTGeometry.RpowPartialSumBound

/-!
# Removing the small rough cofactor from the Möbius prefix

Squarefree cofactors supported on the small primes have a subpolynomial
Euler cost at every exponent above one half. Summing over the rough
cofactor gives a uniform estimate at both sharp cutoffs.
-/

noncomputable section

open Finset Filter ArithmeticFunction RHTower.Sieve
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Squarefree integers through X having rough part at most Y. -/
def smallRoughCofactors (z X Y : ℕ) :=
  (squarefreeOf (Icc 1 X)).filter (fun n => roughPart z n ≤ Y)

/-- Rankin's inequality with the same Euler product as in adaptive
Möbius recovery, uniformly over both integer endpoints. -/
theorem sharp_smooth_card {s : ℝ} (hs : 0<s) (z N : ℕ) :
    ((squarefreeSmoothUpTo z N).card:ℝ) ≤ (N:ℝ)^s*deletionPrice s z := by
  by_cases hz : N=0
  · have hem : squarefreeSmoothUpTo z N=∅ := eq_empty_iff_forall_notMem.mpr
      (fun n h => by have hi := (mem_squarefreeSmoothUpTo.mp h).1.1; omega)
    simp [hem,hz,Real.zero_rpow hs.ne']
  have h := card_squarefreeSmoothUpTo_le_rankin (a := 1-s) (by linarith) z (Nat.pos_of_ne_zero hz)
  rw [show (1:ℝ)-(1-s)=s by ring,show (1:ℝ)-s-1= -s by ring] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) s)
  apply prod_le_prod
  · intro p _; positivity
  · intro p hp
    have hpr := (Nat.mem_primesLE.mp hp).2
    let r := (1/(p:ℝ))^s
    have hr : (p:ℝ)^(-s)=r := by
      rw [Real.rpow_neg (Nat.cast_nonneg _)]
      dsimp only [r]; rw [one_div,Real.inv_rpow (Nat.cast_nonneg _)]
    have gap := sub_pos.mpr (deletion_weight_lt_one hs hpr)
    change 1+(p:ℝ)^(-s) ≤ (1-r)⁻¹
    rw [hr,←one_div]
    apply (le_div_iff₀ gap).2
    nlinarith only [sq_nonneg r]

private theorem cofactor_card (z X Y : ℕ) :
    (smallRoughCofactors z X Y).card ≤ ∑ r ∈ Icc 1 Y,(squarefreeSmoothUpTo z (X/r)).card := by
  let S := fun r : ℕ => squarefreeSmoothUpTo z (X/r)
  have sub : smallRoughCofactors z X Y ⊆ (Icc 1 Y).biUnion (fun r => (S r).image (· * r)) := by
    intro n hn
    obtain ⟨hi,hrY⟩ := mem_filter.mp hn
    obtain ⟨hI,hs⟩ := mem_filter.mp hi
    have hpos := (mem_Icc.mp hI).1
    let r := roughPart z n
    let d := smoothPart z n
    have hr := roughPart_pos z n
    have he : d*r=n := smoothPart_mul_roughPart (Nat.ne_of_gt hpos) z
    have hdX := (Nat.le_div_iff_mul_le hr).2 (he.trans_le (mem_Icc.mp hI).2)
    apply mem_biUnion.mpr
    refine ⟨r,mem_Icc.mpr ⟨hr,hrY⟩,mem_image.mpr ⟨d,mem_squarefreeSmoothUpTo.mpr ?_,he⟩⟩
    refine ⟨⟨⟨smoothPart_pos z n,hdX⟩,?_⟩,hs.squarefree_of_dvd (smoothPart_dvd z n)⟩
    intro p hp
    rw [primeFactors_smoothPart (Nat.ne_of_gt hpos) z] at hp
    exact Nat.mem_primesLE.mpr ⟨(mem_filter.mp hp).2,Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1⟩
  exact (card_le_card sub).trans ((card_biUnion_le ..).trans (sum_le_sum (fun r _ => card_image_le)))

/-- The entire small-rough-part sector has an unsigned sharp bound at
every prime cutoff z and every secondary cutoff Y. -/
theorem small_rough_cofactor_card_bound {s : ℝ} (hs : 0<s) (hs1 : s<1) (z X Y : ℕ) :
    ((smallRoughCofactors z X Y).card:ℝ) ≤
      deletionPrice s z*(X:ℝ)^s*((Y:ℝ)^(1-s)/(1-s)) := by
  let E := deletionPrice s z
  have E0 : 0 ≤ E := zero_le_one.trans (deletionPrice_one_le hs _)
  have hh : ((smallRoughCofactors z X Y).card:ℝ) ≤
      ∑ r ∈ Icc 1 Y,((squarefreeSmoothUpTo z (X/r)).card:ℝ) := by exact_mod_cast cofactor_card z X Y
  have hr (r : ℕ) (h : r ∈ Icc 1 Y) : ((squarefreeSmoothUpTo z (X/r)).card:ℝ)
      ≤ (E*(X:ℝ)^s)*(r:ℝ)^(-s) := by
    have hp := (mem_Icc.mp h).1
    have hf : ((X/r:ℕ):ℝ) ≤ (X:ℝ)/r :=
      (le_div_iff₀ (Nat.cast_pos.mpr hp)).2 (by exact_mod_cast Nat.div_mul_le_self X r)
    apply (sharp_smooth_card hs z (X/r)).trans
    have hw := Real.rpow_le_rpow (Nat.cast_nonneg _) hf hs.le
    rw [Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at hw
    calc _ ≤ ((X:ℝ)^s/(r:ℝ)^s)*E := mul_le_mul_of_nonneg_right hw E0
         _ = _ := by rw [Real.rpow_neg (Nat.cast_nonneg _)]; ring
  have sum : ∑ r ∈ Icc 1 Y,(r:ℝ)^(-s) ≤ (Y:ℝ)^(1-s)/(1-s) := by
    have h := HTGeometry.sum_rpow_sub_one_le (sub_pos.mpr hs1) (by linarith only [hs] : (1:ℝ)-s<1) Y
    rw [show (1:ℝ)-s-1= -s by ring] at h
    rw [sum_Icc_eq_sum_range]
    simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,add_comm (1:ℝ)] using h
  exact hh.trans ((sum_le_sum hr).trans (by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left sum (by positivity)))

/-- Every fixed power cut in the rough cofactor has unsigned exponent
at most the midpoint of that power and one. -/
theorem power_of_the_small_rough_sector {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {η : ℝ} (hη : 0<η) :
    PrefixPower ((1+γ)/2+η) (fun X => ((smallRoughCofactors (logSquareCutoff X) X ⌊(X:ℝ)^γ⌋₊).card:ℝ)) := by
  let e := min (η/4) (1/4)
  let s := 1/2+e
  have he : 0<e := lt_min (by positivity) (by norm_num)
  have hs : 1/2<s := lt_add_of_pos_right _ he
  have hs0 : 0<s := by linarith only [hs]
  have hs1 : s<1 := by dsimp only [s]; linarith only [min_le_right (η/4) (1/4:ℝ)]
  have hdiff := sub_pos.mpr hs1
  have power : s+γ*(1-s)+e ≤ (1+γ)/2+η := by
    dsimp only [s]
    nlinarith only [min_le_left (η/4) (1/4:ℝ),mul_nonneg hγ he,hη]
  apply prefixPower_of_eventual (C := 1/(1-s)) (by simp [smallRoughCofactors,squarefreeOf]) (by linarith only [hγ,hη])
  filter_upwards [log_square_deletion_cost hs he,eventually_ge_atTop (1:ℕ)] with X hprice hx
  let z := logSquareCutoff X
  let Y := ⌊(X:ℝ)^γ⌋₊
  let E := deletionPrice s z
  have hx1 : (1:ℝ) ≤ X := by exact_mod_cast hx
  have hx0 := zero_lt_one.trans_le hx1
  have E1 : 1 ≤ E := deletionPrice_one_le hs0 _
  have z1 : 1 ≤ (z:ℝ)+1 := by positivity
  have hE : E ≤ (X:ℝ)^e := by
    apply le_trans _ hprice
    calc E ≤ E^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr E1) (zero_le_one.trans E1)]
         _ ≤ _ := le_mul_of_one_le_left (sq_nonneg E) z1
  have hY := Real.rpow_le_rpow (Nat.cast_nonneg Y) (Nat.floor_le (Real.rpow_nonneg hx0.le γ)) hdiff.le
  rw [←Real.rpow_mul hx0.le] at hY
  change |((smallRoughCofactors z X Y).card:ℝ)| ≤ _
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  apply (small_rough_cofactor_card_bound hs0 hs1 z X Y).trans
  apply (mul_le_mul (mul_le_mul_of_nonneg_right hE (Real.rpow_nonneg hx0.le _))
    (div_le_div_of_nonneg_right hY hdiff.le) (by positivity) (by positivity)).trans
  calc _ = (1/(1-s))*(X:ℝ)^(s+γ*(1-s)+e) := by rw [Real.rpow_add hx0,Real.rpow_add hx0]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 power) (by positivity)


/-- Signed charge above a specified rough-cofactor stopping point. -/
def largeRoughCharge (Y : ℕ → ℕ) (X : ℕ) :=
  ∑ n ∈ (squarefreeOf (Icc 1 X)).filter (fun n => Y X<roughPart (logSquareCutoff X) n),(μ n:ℝ)

private theorem removed_charge (Y : ℕ → ℕ) (X : ℕ) :
    |coprimeMoebiusSum 1 X-largeRoughCharge Y X| ≤
      ((smallRoughCofactors (logSquareCutoff X) X (Y X)).card:ℝ) := by
  let S := squarefreeOf (Icc 1 X)
  let A := smallRoughCofactors (logSquareCutoff X) X (Y X)
  have all : coprimeMoebiusSum 1 X=∑ n ∈ S,(μ n:ℝ) := by
    simp only [coprimeMoebiusSum,coprimeMoebiusIndicator,Nat.coprime_one_left,if_true,S,squarefreeOf,sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hs : Squarefree n <;> simp [hs,moebius_eq_zero_of_not_squarefree]
  have split := sum_filter_add_sum_filter_not S (fun n => roughPart (logSquareCutoff X) n ≤ Y X)
    (fun n => (μ n:ℝ))
  simp only [not_le] at split
  change (∑ n ∈ A,(μ n:ℝ))+largeRoughCharge Y X=∑ n ∈ S,(μ n:ℝ) at split
  rw [all,←split,add_sub_cancel_right]
  calc _ ≤ ∑ n ∈ A,|(μ n:ℝ)| := abs_sum_le_sum_abs ..
       _ ≤ ∑ _n ∈ A,(1:ℝ) := sum_le_sum fun n _ => by exact_mod_cast abs_moebius_le_one (n := n)
       _ = _ := by simp [A]

/-- The removed charge itself satisfies the target at every subpower
rough-cofactor cutoff, without a bound for the complementary sum. -/
theorem square_root_charge_of_subpower_rough_cofactors (Y : ℕ → ℕ)
    (small : ∀ γ : ℝ,0<γ → ∀ᶠ X : ℕ in atTop,(Y X:ℝ) ≤ (X:ℝ)^γ)
    {ε : ℝ} (hε : 0<ε) :
    PrefixPower (1/2+ε) (fun X => coprimeMoebiusSum 1 X-largeRoughCharge Y X) := by
  let γ := min ε 1
  have hg : 0<γ := lt_min hε zero_lt_one
  obtain ⟨C,hC,hbound⟩ := power_of_the_small_rough_sector hg.le (min_le_right ..) (half_pos hε)
  apply prefixPower_of_eventual (C := C) (by simp [largeRoughCharge,squarefreeOf,coprimeMoebiusSum]) (by linarith only [hε])
  filter_upwards [small γ hg,eventually_ge_atTop (1:ℕ)] with X hx hx1
  have sub : smallRoughCofactors (logSquareCutoff X) X (Y X) ⊆
      smallRoughCofactors (logSquareCutoff X) X ⌊(X:ℝ)^γ⌋₊ :=
    filter_subset_filter _ (fun _ h => h.trans (Nat.le_floor hx))
  have hh := hbound X
  change |((smallRoughCofactors (logSquareCutoff X) X ⌊(X:ℝ)^γ⌋₊).card:ℝ)| ≤ _ at hh
  rw [abs_of_nonneg (Nat.cast_nonneg _)] at hh
  have he : (1+γ)/2+ε/2 ≤ (1:ℝ)/2+ε := by linarith only [min_le_left ε 1]
  exact ((removed_charge Y X).trans (Nat.cast_le.mpr (card_le_card sub))).trans
    (hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx1) he) hC))

/-- A prescribed unbounded cutoff faster than every logarithmic power. -/
def expSqrtLogCutoff (X : ℕ) := ⌊Real.exp (Real.sqrt (Real.log ((X:ℝ)+1)))⌋₊

private theorem expSqrtLog_subpower {γ : ℝ} (hg : 0<γ) :
    ∀ᶠ X : ℕ in atTop,(expSqrtLogCutoff X:ℝ) ≤ (X:ℝ)^γ := by
  have grow := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (2/γ^2)
  filter_upwards [grow,eventually_ge_atTop (2:ℕ)] with X hL hX
  let L := Real.log X
  change 2/γ^2 ≤ L at hL
  have hpos : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
  have lpos : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hx2 : (X:ℝ)+1 ≤ (X:ℝ)^2 := by
    have hh : (2:ℝ) ≤ X := by exact_mod_cast hX
    nlinarith only [sq_nonneg ((X:ℝ)-1),hh]
  have htop := Real.log_le_log (by positivity) hx2
  rw [Real.log_pow] at htop
  have budget := mul_le_mul_of_nonneg_right ((div_le_iff₀ (sq_pos_of_pos hg)).1 hL) lpos
  have root : Real.sqrt (Real.log ((X:ℝ)+1)) ≤ γ*L := by
    apply (Real.sqrt_le_iff).2
    exact ⟨mul_nonneg hg.le lpos,by change Real.log ((X:ℝ)+1) ≤ (γ*Real.log X)^2; dsimp only [L] at budget; nlinarith only [htop,budget]⟩
  have h := Real.exp_le_exp.mpr root
  apply (Nat.floor_le (Real.exp_pos _).le).trans
  rw [←Real.exp_log (Real.rpow_pos_of_pos hpos γ),Real.log_rpow hpos]
  exact h

/-- For the actual full prefix the square-root estimate already holds
on all integers with rough part at most exp(sqrt(log(X+1))). Only the
complementary signed charge needs an estimate. -/
theorem square_root_after_sharp_rough_truncation :
    (∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (fun X => coprimeMoebiusSum 1 X-largeRoughCharge expSqrtLogCutoff X)) ∧
    ((∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (largeRoughCharge expSqrtLogCutoff)) ↔
     ∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (coprimeMoebiusSum 1)) := by
  have he := fun (ε : ℝ) (hε : 0<ε) =>
    square_root_charge_of_subpower_rough_cofactors expSqrtLogCutoff (fun _ h => expSqrtLog_subpower h) hε
  refine ⟨he,?_⟩
  constructor <;> intro h ε hε
  · obtain ⟨A,hA,ha⟩ := h ε hε
    obtain ⟨B,hB,hb⟩ := he ε hε
    refine ⟨A+B,add_nonneg hA hB,fun X => ?_⟩
    let M := coprimeMoebiusSum 1 X
    let G := largeRoughCharge expSqrtLogCutoff X
    have hh := abs_add_le G (M-G)
    rw [show G+(M-G)=M by ring] at hh
    rw [add_mul]; exact hh.trans (add_le_add (ha X) (hb X))
  · obtain ⟨A,hA,ha⟩ := h ε hε
    obtain ⟨B,hB,hb⟩ := he ε hε
    refine ⟨A+B,add_nonneg hA hB,fun X => ?_⟩
    let M := coprimeMoebiusSum 1 X
    let G := largeRoughCharge expSqrtLogCutoff X
    have hh := abs_sub M (M-G)
    rw [show M-(M-G)=G by ring] at hh
    rw [add_mul]; exact hh.trans (add_le_add (ha X) (hb X))

#print axioms sharp_smooth_card
#print axioms small_rough_cofactor_card_bound
#print axioms power_of_the_small_rough_sector
#print axioms square_root_after_sharp_rough_truncation

end GaloisForLFunctions.RestrictedFactorizationCalculus
