import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CancellationInTheLongCofactorInterval
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFiniteMeshAtAnOrdinaryFirstPrime

/-!
# First-prime bounds on the full product range

A seventh difference in the cofactor pays first primes throughout the long
product sum, including products of quadratic size. The lower sharp cut is
kept in the first seven cofactor samples.
-/

noncomputable section
open Finset Filter ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Below any fixed exponent a < 2 the prime mesh p/n² and the lower
cofactor cut both shrink like a fixed negative power of the conductor. -/
private theorem eventually_small_prime_mesh {a : ℝ} (ha : a<2) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, 0<p → (p:ℝ)≤(n:ℝ)^a →
      let h := (p:ℝ)/(n:ℝ)^2
      let l := ⌊(n:ℝ)^(17/9:ℝ)⌋₊/p
      Real.sqrt h≤1/8 ∧ 112*max ((l:ℝ)*h) (Real.sqrt h)<Real.exp (-8) := by
  obtain ⟨ε,hε,hεa,hε9⟩ : ∃ ε : ℝ, 0<ε ∧ ε≤(2-a)/2 ∧ ε≤1/9 :=
    ⟨min ((2-a)/2) (1/9),lt_min (by linarith only [ha]) (by norm_num),min_le_left _ _,min_le_right _ _⟩
  have hlt : Tendsto (fun n : ℕ => (n:ℝ)^(-ε)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),
    hlt.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    hlt.eventually (gt_mem_nhds (div_pos (Real.exp_pos (-8)) (by norm_num : (0:ℝ)<112)))]
    with n hn h8 h112
  intro p hp hP
  let x := (n:ℝ)^(-ε)
  let d := (p:ℝ)/(n:ℝ)^2
  let U := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  have hn1 : (1:ℝ)≤n := Nat.one_le_cast.mpr hn
  have hn0 := zero_lt_one.trans_le hn1
  have hsq : 0<(n:ℝ)^2 := sq_pos_of_pos hn0
  have hx : 0<x := Real.rpow_pos_of_pos hn0 _
  have prod (a : ℝ) : (n:ℝ)^a*(n:ℝ)^2=(n:ℝ)^(a+2) := by
    rw [←Real.rpow_two,←Real.rpow_add hn0]
  have hx2 : x^2*(n:ℝ)^2=(n:ℝ)^(-ε*2+2) := by
    dsimp only [x]; rw [←Real.rpow_two ((n:ℝ)^_),←Real.rpow_mul hn0.le,prod]
  have hs : Real.sqrt d≤x := Real.sqrt_le_iff.mpr ⟨hx.le,(div_le_iff₀ hsq).mpr (by
    rw [hx2]; exact hP.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hεa])))⟩
  have hU : (U:ℝ)≤(n:ℝ)^(17/9:ℝ) := Nat.floor_le (Real.rpow_nonneg hn0.le _)
  have hlow : ((U/p:ℕ):ℝ)*d ≤ x := by
    dsimp only [d]
    rw [←mul_div_assoc,div_le_iff₀ hsq]
    have hnU : ((U/p:ℕ):ℝ)*(p:ℝ)≤U := by exact_mod_cast Nat.div_mul_le_self U p
    dsimp only [x]; rw [prod]
    exact (hnU.trans hU).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε9]))
  exact ⟨hs.trans h8.le,(mul_le_mul_of_nonneg_left (max_le hlow hs) (by norm_num : (0:ℝ)≤112)).trans_lt
    (by simpa only [mul_comm] using (lt_div_iff₀ (by norm_num : (0:ℝ)<112)).mp h112)⟩

/-- For every fixed subquadratic prime cut p ≤ n^a, a < 2, the actual
late cofactor mesh has square-root fifth-power decay. -/
theorem first_prime_cofactor_price_below_power {a : ℝ} (ha : a<2) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, 0<p → (p:ℝ)≤(n:ℝ)^a →
      let d := (p:ℝ)/(n:ℝ)^2
      let l := ⌊(n:ℝ)^(17/9:ℝ)⌋₊/p
      |∑ v ∈ Ioc l (splineHorizon n/p), innerJump 1 v * positiveCofactorProfile (splineHorizon n+1) d v| ≤
        C*((Real.sqrt d)^5+((l:ℝ)*d)^7) := by
  obtain ⟨C,hC,h⟩ := signed_cofactor_fine_mesh
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ),eventually_small_prime_mesh ha] with n hn hsmall
  intro p hp hP
  obtain ⟨hs,hcut⟩ := hsmall p hp hP
  obtain ⟨hb,hm⟩ := positive_mesh_reaches_support hn hp
  exact h _ _ _ (div_pos (Nat.cast_pos.mpr hp) (sq_pos_of_pos (Nat.cast_pos.mpr hn))) hs hcut hb hm

/-- The nineteen-tenths case of the subquadratic cofactor price. -/
theorem first_prime_cofactor_price_below_nineteen_tenths :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, 0<p → (p:ℝ)≤(n:ℝ)^(19/10:ℝ) →
      let d := (p:ℝ)/(n:ℝ)^2
      let l := ⌊(n:ℝ)^(17/9:ℝ)⌋₊/p
      |∑ v ∈ Ioc l (splineHorizon n/p), innerJump 1 v * positiveCofactorProfile (splineHorizon n+1) d v| ≤
        C*((Real.sqrt d)^5+((l:ℝ)*d)^7) :=
  first_prime_cofactor_price_below_power (by norm_num)

private theorem eventually_first_prime_power_price {a : ℝ} (ha : 12/7≤a) (ha' : a<2) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ n : ℕ in atTop,
      let U := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
      let P := ⌊(n:ℝ)^a⌋₊
      |(n:ℝ)^2*(capFreeFirstPrimeReading U n-unrestrictedFirstPrimeReading P U n)| ≤
        C*(n:ℝ)^(7/2*a-4) := by
  obtain ⟨C,hC,h⟩ := first_prime_cofactor_price_below_power ha'
  obtain ⟨K,hK,hgeom⟩ := capFreeFirstPrimeCut_linear
  have htop := (tendsto_rpow_atTop (by linarith only [ha] : 0<a-1)).comp tendsto_natCast_atTop_atTop
  refine ⟨14*C,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ),h,htop.eventually_ge_atTop K] with n hn hrow hk
  let F := capFreeFirstPrimeCut n
  let U := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  let P := ⌊(n:ℝ)^a⌋₊
  let S := (Ioc (max 4 F) (min P (splineHorizon n))).filter Nat.Prime
  let z := (5/2:ℝ)*(a-2)
  let H := (n:ℝ)^z
  have hn1 : (1:ℝ)≤n := Nat.one_le_cast.mpr hn
  have hn0 := zero_lt_one.trans_le hn1
  have hH : 0≤H := Real.rpow_nonneg hn0.le _
  have hP : (P:ℝ)≤(n:ℝ)^a := Nat.floor_le (Real.rpow_nonneg hn0.le _)
  have hFP : F≤P := by
    apply Nat.le_floor
    apply (hgeom hn).trans
    calc K*n ≤ (n:ℝ)^(a-1)*n := mul_le_mul_of_nonneg_right hk hn0.le
         _ = _ := by
           conv_lhs => rhs; rw [←Real.rpow_one (n:ℝ)]
           rw [←Real.rpow_add hn0,sub_add_cancel]
  have hmass : (∑ p ∈ S, vonMangoldt p) ≤ 7*(n:ℝ)^a := by
    have hsub : S ⊆ Icc 1 P := fun p hp => mem_Icc.mpr
      ⟨(mem_filter.mp hp).2.pos,(mem_Ioc.mp (mem_filter.mp hp).1).2.trans (min_le_left _ _)⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)).trans
      ((_root_.RHTower.sum_vonMangoldt_Icc_le_seven P).trans (mul_le_mul_of_nonneg_left hP (by norm_num)))
  let V (p : ℕ) := ∑ v ∈ Ioc (U/p) (splineHorizon n/p),
    innerJump 1 v*positiveCofactorProfile (splineHorizon n+1) (p/(n:ℝ)^2) v
  have hpv (p : ℕ) (hp : p∈S) : |V p|≤2*C*H := by
    have hp0 := (mem_filter.mp hp).2.pos
    have hpP := (mem_Ioc.mp (mem_filter.mp hp).1).2.trans (min_le_left _ _)
    have hpa := (Nat.cast_le.mpr hpP : (p:ℝ)≤P).trans hP
    let d := (p:ℝ)/(n:ℝ)^2
    have hd : 0<d := div_pos (Nat.cast_pos.mpr hp0) (sq_pos_of_pos hn0)
    have mulSq (e : ℝ) : (n:ℝ)^e*(n:ℝ)^2=(n:ℝ)^(e+2) := by rw [←Real.rpow_two,←Real.rpow_add hn0]
    have hm : Real.sqrt d≤(n:ℝ)^((a-2)/2) := by
      apply Real.sqrt_le_iff.mpr ⟨Real.rpow_nonneg hn0.le _,?_⟩
      apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
      rw [←Real.rpow_two ((n:ℝ)^_),←Real.rpow_mul hn0.le,mulSq,show (a-2)/2*2+2=a by ring]
      exact hpa
    have hs : (Real.sqrt d)^5 ≤ H := (pow_le_pow_left₀ (Real.sqrt_nonneg _) hm 5).trans_eq (by
      dsimp only [H,z]; rw [←Real.rpow_natCast _ 5,←Real.rpow_mul hn0.le]; congr 1; push_cast; ring)
    have hl : ((U/p:ℕ):ℝ)*d≤(n:ℝ)^(-(1/9):ℝ) := by
      dsimp only [d]
      rw [←mul_div_assoc,div_le_iff₀ (sq_pos_of_pos hn0),mulSq,show (-(1/9):ℝ)+2=17/9 by norm_num]
      exact (show ((U/p:ℕ):ℝ)*(p:ℝ)≤U by exact_mod_cast Nat.div_mul_le_self U p).trans
        (Nat.floor_le (Real.rpow_nonneg hn0.le _))
    have hl7 : (((U/p:ℕ):ℝ)*d)^7 ≤ H := by
      apply (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hd.le) hl 7).trans
      rw [←Real.rpow_natCast _ 7,←Real.rpow_mul hn0.le]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp only [z]; norm_num; linarith only [ha])
    exact (hrow p hp0 hpa).trans
      ((mul_le_mul_of_nonneg_left (add_le_add hs hl7) hC).trans_eq (by ring))
  change |(n:ℝ)^2*(unrestrictedFirstPrimeReading F U n-unrestrictedFirstPrimeReading P U n)| ≤ _
  rw [first_prime_mesh_band hn hFP U]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ p ∈ S, vonMangoldt p*(n*(2*C*H)) := by
            apply sum_le_sum
            intro p hp
            rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg,abs_mul,abs_of_pos hn0]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpv p hp) hn0.le) vonMangoldt_nonneg
       _ ≤ (7*(n:ℝ)^a)*(n*(2*C*H)) := by
            rw [←sum_mul]
            exact mul_le_mul_of_nonneg_right hmass (by positivity)
       _ = _ := by
            have he : (n:ℝ)^a*n*H=(n:ℝ)^(7/2*a-4) := by
              dsimp only [H,z]
              calc _ = (n:ℝ)^a*(n:ℝ)^(1:ℝ)*(n:ℝ)^(5/2*(a-2)) := by rw [Real.rpow_one]
                   _ = _ := by rw [←Real.rpow_add hn0,←Real.rpow_add hn0]; congr 1; ring
            linear_combination 14*C*he

/-- Every terminal fragment inherits the signed first-prime power saving
for each fixed first-prime cut n^a with 12/7 ≤ a < 2, with the original
lower product cutoff. -/
theorem cap_free_prime_power_fragments {a : ℝ} (ha : 12/7≤a) (ha' : a<2) :
    ∃ C : ℝ, 0≤C ∧ ∀ J M : ℕ, 0<M →
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(capFreeFirstPrimeReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n -
        unrestrictedFirstPrimeReading ⌊(n:ℝ)^a⌋₊ ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n)| ≤ C*(M:ℝ)^(7/2*a-3) := by
  obtain ⟨A,hA,hlate⟩ := eventually_first_prime_power_price ha ha'
  obtain ⟨k,hk⟩ := eventually_atTop.mp hlate
  let σ := 7/2*a-4
  have hσ : 0≤σ := by dsimp only [σ]; linarith only [ha]
  let U (n : ℕ) := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  let f (n : ℕ) := (n:ℝ)^2*(capFreeFirstPrimeReading (U n) n -
    unrestrictedFirstPrimeReading ⌊(n:ℝ)^a⌋₊ (U n) n)
  let B := ∑ n ∈ range k, |f n|
  have hB : 0≤B := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨A+B,add_nonneg hA hB,fun J M hM => ?_⟩
  have hm1 : (1:ℝ) ≤ M := Nat.one_le_cast.mpr hM
  have hpow := Real.one_le_rpow hm1 hσ
  have bound (n : ℕ) (hn : n ∈ Ioc J M) : |f n|≤(A+B)*(M:ℝ)^σ := by
    by_cases hkn : k≤n
    · exact (hk n hkn).trans (mul_le_mul (le_add_of_nonneg_right hB)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (mem_Ioc.mp hn).2) hσ)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _) (add_nonneg hA hB))
    · exact (single_le_sum (fun j _ => abs_nonneg (f j)) (mem_range.mpr (lt_of_not_ge hkn)) :
        |f n|≤B).trans ((le_add_of_nonneg_left hA).trans (le_mul_of_one_le_right (add_nonneg hA hB) hpow))
  apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum bound).trans _)
  rw [sum_const,Nat.card_Ioc,nsmul_eq_mul]
  apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M J))
    (mul_nonneg (add_nonneg hA hB) (Real.rpow_nonneg (Nat.cast_nonneg M) σ))).trans_eq
  rw [show 7/2*a-3=1+σ by dsimp only [σ]; ring,Real.rpow_add (Nat.cast_pos.mpr hM),Real.rpow_one]
  ring

private theorem prime_cut_clears_product_cut {U P : ℕ} (h : U≤P) (n : ℕ) :
    unrestrictedFirstPrimeReading P U n=unrestrictedFirstPrimeReading P 0 n := by
  unfold unrestrictedFirstPrimeReading
  congr 1
  funext k
  unfold ordinaryFactorTail
  apply sum_congr rfl
  intro p hp
  have hlt := h.trans_lt ((le_max_right 4 P).trans_lt (mem_Ioc.mp (mem_filter.mp hp).1).1)
  dsimp only
  rw [Nat.div_eq_of_lt hlt,Nat.zero_div]

/-- At the twelve-sevenths first-prime cutoff the whole discarded price
on every terminal fragment is at most cubic times one logarithm. -/
theorem twelve_sevenths_first_prime_fragments :
    ∃ C : ℝ, 0≤C ∧ ∀ J M : ℕ, 0<M →
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        unrestrictedFirstPrimeReading ⌊(n:ℝ)^(12/7:ℝ)⌋₊ ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n)| ≤
          C*(M:ℝ)^3*conductorLog M := by
  obtain ⟨A,hA,h⟩ := seventeenNinths_cap_free_first_prime_fragments
  obtain ⟨B,hB,hp⟩ := cap_free_prime_power_fragments (a := 12/7) le_rfl (by norm_num)
  refine ⟨A+B,add_nonneg hA hB,fun J M hM => ?_⟩
  let U (n : ℕ) := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  let R (n : ℕ) := unrestrictedFirstPrimeReading ⌊(n:ℝ)^(12/7:ℝ)⌋₊ (U n) n
  have he (n : ℕ) : (n:ℝ)^2*(cappedUpperProductReading (U n) n n-R n) =
      (n:ℝ)^2*(cappedUpperProductReading (U n) n n-capFreeFirstPrimeReading (U n) n) +
      (n:ℝ)^2*(capFreeFirstPrimeReading (U n) n-R n) := by ring
  rw [sum_congr rfl (fun n _ => he n),sum_add_distrib]
  have hs := hp J M hM
  rw [show 7/2*(12/7:ℝ)-3=3 by norm_num,show (M:ℝ)^(3:ℝ)=(M:ℝ)^3 from Real.rpow_natCast _ 3] at hs
  have hsc := le_mul_of_one_le_right (mul_nonneg hB (pow_nonneg (Nat.cast_nonneg M) 3)) (conductorLog_one_le M)
  exact (abs_add_le _ _).trans ((add_le_add (h J M) (hs.trans hsc)).trans_eq (by ring))

/-- First primes through nineteen tenths, including all products at quadratic
scale, cost exponent 73/20 on every fragment. The remaining signed reading
has no lower product cut, artificial cofactor cap, or coprimality test. -/
theorem nineteen_tenths_first_prime_fragments :
    ∃ C : ℝ, 0≤C ∧ ∀ J M : ℕ, 0<M →
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        unrestrictedFirstPrimeReading ⌊(n:ℝ)^(19/10:ℝ)⌋₊ 0 n)| ≤ C*(M:ℝ)^(73/20:ℝ) := by
  obtain ⟨A,hA,h⟩ := seventeenNinths_cap_free_first_prime_fragments
  obtain ⟨B,hB,hp⟩ := cap_free_prime_power_fragments (a := 19/10) (by norm_num) (by norm_num)
  obtain ⟨E,hE,he⟩ := conductorLog_subpower (by norm_num : (0:ℝ)<13/20)
  refine ⟨A*E+B,by positivity,fun J M hM => ?_⟩
  let U (n : ℕ) := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  let P (n : ℕ) := ⌊(n:ℝ)^(19/10:ℝ)⌋₊
  let R (n : ℕ) := unrestrictedFirstPrimeReading (P n) (U n) n
  have eqn (n : ℕ) (hn : n ∈ Ioc J M) : (n:ℝ)^2*(cappedUpperProductReading (U n) n n-
      unrestrictedFirstPrimeReading (P n) 0 n) =
      (n:ℝ)^2*(cappedUpperProductReading (U n) n n-capFreeFirstPrimeReading (U n) n) +
      (n:ℝ)^2*(capFreeFirstPrimeReading (U n) n-R n) := by
    have hN := (Nat.zero_le J).trans_lt (mem_Ioc.mp hn).1
    have hUP : U n≤P n := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN) (by norm_num))
    rw [←prime_cut_clears_product_cut hUP n]
    dsimp only [R]; ring
  rw [sum_congr rfl eqn,sum_add_distrib]
  have hs := hp J M hM
  rw [show 7/2*(19/10:ℝ)-3=73/20 by norm_num] at hs
  have hlog := (le_self_pow₀ (conductorLog_one_le M) (by decide : 6≠0)).trans (he hM)
  have hc : A*(M:ℝ)^3*conductorLog M ≤ A*E*(M:ℝ)^(73/20:ℝ) := by
    apply (mul_le_mul_of_nonneg_left hlog (mul_nonneg hA (pow_nonneg (Nat.cast_nonneg M) 3))).trans_eq
    rw [show (73/20:ℝ)=3+13/20 by norm_num,Real.rpow_add (Nat.cast_pos.mpr hM),
      show (M:ℝ)^(3:ℝ)=(M:ℝ)^3 from Real.rpow_natCast _ 3]
    ring
  exact (abs_add_le _ _).trans ((add_le_add ((h J M).trans hc) hs).trans_eq (by ring))

/-- Every surviving cofactor at the nineteen-tenths first-prime cutoff
is bounded by a constant times the tenth root of its conductor. -/
theorem remaining_cofactors_at_nineteen_tenths :
    ∃ A : ℝ, 0≤A ∧ ∀ {n p k v : ℕ}, 0<n → k ≤ splineHorizon n →
      ⌊(n:ℝ)^(19/10:ℝ)⌋₊<p → v≤k/p → (v:ℝ)≤A*(n:ℝ)^(1/10:ℝ) := by
  obtain ⟨T,_,hw⟩ := successorSquare_window_bound
  refine ⟨T^2,sq_nonneg _,fun {n p k v} hn hk hp hv => ?_⟩
  have hn0 : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hp0 := (Nat.zero_le _).trans_lt hp
  have hcut := (Nat.floor_lt (Real.rpow_nonneg hn0.le (19/10:ℝ))).mp hp
  have hvk : (v:ℝ)*p≤k := by exact_mod_cast (Nat.le_div_iff_mul_le hp0).mp hv
  have hu := hvk.trans ((Nat.cast_le.mpr hk).trans (hw hn))
  have hreal := (mul_le_mul_of_nonneg_left hcut.le (Nat.cast_nonneg v)).trans hu
  calc (v:ℝ) ≤ (T*n)^2/(n:ℝ)^(19/10:ℝ) := (le_div_iff₀ (Real.rpow_pos_of_pos hn0 _)).mpr hreal
       _ = _ := by
          apply (div_eq_iff (Real.rpow_pos_of_pos hn0 _).ne').mpr
          rw [mul_pow,mul_assoc,←Real.rpow_add hn0,show (1/10:ℝ)+19/10=2 by norm_num,Real.rpow_two]

/-- The one-sided eleven-thirds criterion can be tested using only first
primes above nineteen tenths, with the full range of their natural cofactors. -/
theorem eleven_thirds_iff_nineteen_tenths_first_primes :
    (∃ C : ℝ, 0≤C ∧ ∀ M : ℕ, 0<M →
      (∑ n ∈ Ioc 0 M, (n:ℝ)^2*cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n) ≤ C*(M:ℝ)^(11/3:ℝ)) ↔
    ∃ C : ℝ, 0≤C ∧ ∀ M : ℕ, 0<M →
      (∑ n ∈ Ioc 0 M, (n:ℝ)^2*unrestrictedFirstPrimeReading ⌊(n:ℝ)^(19/10:ℝ)⌋₊ 0 n) ≤ C*(M:ℝ)^(11/3:ℝ) := by
  obtain ⟨A,hA,h⟩ := nineteen_tenths_first_prime_fragments
  let B (M : ℕ) := ∑ n ∈ Ioc 0 M, (n:ℝ)^2*cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n
  let R (M : ℕ) := ∑ n ∈ Ioc 0 M, (n:ℝ)^2*unrestrictedFirstPrimeReading ⌊(n:ℝ)^(19/10:ℝ)⌋₊ 0 n
  have gap (M : ℕ) (hM : 0<M) : |B M - R M|≤A*(M:ℝ)^(11/3:ℝ) := by
    simp only [B,R,←sum_sub_distrib,←mul_sub]
    exact (h 0 M hM).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (Nat.one_le_cast.mpr hM) (by norm_num : (73/20:ℝ)≤11/3)) hA)
  change (∃ C : ℝ, 0≤C ∧ ∀ M : ℕ, 0<M → B M≤C*(M:ℝ)^(11/3:ℝ)) ↔
    ∃ C : ℝ, 0≤C ∧ ∀ M : ℕ, 0<M → R M≤C*(M:ℝ)^(11/3:ℝ)
  constructor <;> rintro ⟨C,hC,hB⟩ <;> refine ⟨C+A,add_nonneg hC hA,fun M hM => ?_⟩
  · linarith only [(abs_le.mp (gap M hM)).1,hB M hM]
  · linarith only [(abs_le.mp (gap M hM)).2,hB M hM]

#print axioms remaining_cofactors_at_nineteen_tenths
#print axioms eleven_thirds_iff_nineteen_tenths_first_primes
#print axioms twelve_sevenths_first_prime_fragments
#print axioms nineteen_tenths_first_prime_fragments
#print axioms eventually_first_prime_power_price
#print axioms first_prime_cofactor_price_below_nineteen_tenths
#print axioms first_prime_cofactor_price_below_power
#print axioms cap_free_prime_power_fragments
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
