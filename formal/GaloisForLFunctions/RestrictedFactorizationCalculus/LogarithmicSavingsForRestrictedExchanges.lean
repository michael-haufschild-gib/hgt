import GaloisForLFunctions.RestrictedFactorizationCalculus.SamplingPrimeDivisorsAtSharpCutoffs
import GaloisForLFunctions.RestrictedFactorizationCalculus.OneInvolutionForEverySharpPrefix

/-!
# The incomplete-period cost of a family of prime exchanges

Möbius inversion samples the same missed local divisors as a complete
period, with a bound in terms of the largest available prime. This allows
the number of independent exchange ranges to grow with the cutoff.
-/

noncomputable section

open Finset Filter RHTower
open scoped Classical
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem pattern_of_ranges {J : ℕ} {I : Finset ℕ} (n : ℕ) :
    missesSingles J I (n.gcd (exchangePeriod I)) ↔ missesSingles J I n := by
  unfold missesSingles
  refine forall_congr' fun k => forall_congr' fun hk => ?_
  rw [Nat.gcd_assoc,Nat.gcd_eq_right (divides_period hk)]

/-- Every bounded collection of coprime ranges can be sampled through an
arbitrary sharp cutoff, with no error proportional to their full period. -/
theorem sampled_missed_ranges {J X : ℕ} {I : Finset ℕ}
    (hco : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (switchModulus i).Coprime (switchModulus j))
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    let P := I.biUnion switchPrimes
    |(((Icc 1 X).filter (missesSingles J I)).card:ℝ) -
      (X:ℝ)*((missedClasses J I).card/exchangePeriod I)| ≤
        (X:ℝ)^s*∏ p ∈ P, (2/(p:ℝ)^s+1) := by
  let Q := exchangePeriod I
  let P := I.biUnion switchPrimes
  let f := fun a => if missesSingles J I a then (1:ℝ) else 0
  have hQ : 0 < Q := period_pos I
  have hP (p : ℕ) (h : p ∈ P) : p.Prime := by
    obtain ⟨k,_,hm⟩ := mem_biUnion.mp h
    exact (mem_switchPrimes.mp hm).1
  have he : (∏ p ∈ P,p)=Q := by
    have hdis : (I : Set ℕ).PairwiseDisjoint switchPrimes := by
      intro i hi j hj hn
      change Disjoint (switchPrimes i) (switchPrimes j)
      rw [←(switchModulus_spec i).2.1,←(switchModulus_spec j).2.1]
      exact (hco i hi j hj hn).disjoint_primeFactors
    exact prod_biUnion hdis
  have hf : ∀ d, |f d| ≤ 1 := by intro d; dsimp only [f]; split <;> norm_num
  have count (S : Finset ℕ) : ∑ n ∈ S, f (n.gcd Q) = ((S.filter (missesSingles J I)).card:ℝ) := by
    calc _ = ∑ n ∈ S, if missesSingles J I n then (1:ℝ) else 0 :=
           sum_congr rfl fun n _ => by
             dsimp only [f]
             by_cases hn : missesSingles J I n
             · rw [if_pos ((pattern_of_ranges n).2 hn),if_pos hn]
             · rw [if_neg (fun h => hn ((pattern_of_ranges n).1 h)),if_neg hn]
         _ = _ := by rw [←sum_filter]; simp
  have hfull := full_period_prime_pattern hQ f
  rw [count] at hfull
  have hav : primePatternMean Q f=((missedClasses J I).card:ℝ)/Q :=
    (eq_div_iff (by exact_mod_cast hQ.ne' : (Q:ℝ) ≠ 0)).2 (by rw [mul_comm]; exact hfull.symm)
  have h := prime_pattern_sampling hP hf hs hs1 X
  dsimp only at h ⊢
  rw [he,count,hav] at h
  exact h

/-- If the available primes are at most 2^D, the divisor Euler product with
Rankin parameter 1/D is bounded by a fourth power of the Mertens product. -/
private theorem rankin_product {P : Finset ℕ} {D : ℕ} (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p ∧ p ≤ 2^D) :
    ∏ p ∈ P, (2/(p:ℝ)^(1-1/(D:ℝ))+1) ≤ (mertensBandProductConst*(D:ℝ))^4 := by
  let Z := (2:ℕ)^D
  have hDr : (0:ℝ) < D := by exact_mod_cast hD
  have hZ : 2 ≤ Z := by simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hD
  have hsub : P ⊆ wholeAnchorBandPrimes 2 Z := by
    intro p hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr (hP p hp).2,(hP p hp).1⟩
  have hbound := bandPrimes_eulerProduct_le (by decide : 2 ≤ 2) hZ
  have hlog : Real.log (Z:ℝ)/Real.log 2 = D := by
    have hpos := Real.log_pos (by norm_num : (1:ℝ) < 2)
    dsimp only [Z]; rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,mul_div_cancel_right₀ _ hpos.ne']
  simp only [Nat.cast_ofNat] at hbound
  rw [hlog] at hbound
  have hprod : (∏ p ∈ P, (1+1/(p:ℝ))) ≤ mertensBandProductConst*D := by
    apply le_trans _ hbound
    exact prod_le_prod_of_subset_of_one_le hsub (fun _ _ => by positivity)
      (fun _ _ _ => le_add_of_nonneg_right (by positivity))
  have step {p : ℕ} (hp : p ∈ P) : 2/(p:ℝ)^(1-1/(D:ℝ))+1 ≤ (1+1/(p:ℝ))^4 := by
    have hp0 : (0:ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    have hh : (p:ℝ)^(1/(D:ℝ)) ≤ 2 := by
      have hcap : (p:ℝ) ≤ (2:ℝ)^D := by exact_mod_cast (hP p hp).2.2
      calc _ ≤ ((2:ℝ)^D)^(1/(D:ℝ)) := Real.rpow_le_rpow hp0.le hcap (by positivity)
           _ = _ := by rw [one_div,Real.pow_rpow_inv_natCast (by norm_num) hD.ne']
    have hmain : 2/(p:ℝ)^(1-1/(D:ℝ)) ≤ 4/p := by
      rw [Real.rpow_sub hp0,Real.rpow_one,div_div_eq_mul_div]
      exact div_le_div_of_nonneg_right (by linarith only [hh]) hp0.le
    have hpos : 0 ≤ 1/(p:ℝ) := by positivity
    have hB : 1+4*(1/(p:ℝ)) ≤ (1+1/(p:ℝ))^4 := by
      nlinarith only [sq_nonneg (1/(p:ℝ)),pow_nonneg hpos 3,pow_nonneg hpos 4]
    calc _ ≤ 4/(p:ℝ)+1 := add_le_add hmain le_rfl
         _ = 1+4*(1/(p:ℝ)) := by ring
         _ ≤ _ := hB
  calc _ ≤ ∏ p ∈ P, (1+1/(p:ℝ))^4 :=
           prod_le_prod (fun _ _ => by positivity) (fun _ hp => step hp)
       _ = (∏ p ∈ P,(1+1/(p:ℝ)))^4 := prod_pow ..
       _ ≤ _ := pow_le_pow_left₀ (prod_nonneg (fun _ _ => by positivity)) hprod 4

/-- Uniform sampling error for prime ranges whose logarithmic height is at
most D. The conjugate exponents separate the cutoff from the prime height. -/
theorem missed_ranges_at_height {J X D : ℕ} (hD : 0 < D) {I : Finset ℕ}
    (hco : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (switchModulus i).Coprime (switchModulus j))
    (hcap : ∀ i ∈ I, 24*i ≤ D) :
    (((Icc 1 X).filter (missesSingles J I)).card:ℝ) ≤
      (X:ℝ)*((missedClasses J I).card/exchangePeriod I) +
      (X:ℝ)^(1-1/(D:ℝ))*(mertensBandProductConst*D)^4 := by
  let P := I.biUnion switchPrimes
  have hp (p : ℕ) (h : p ∈ P) : p.Prime ∧ 2 < p ∧ p ≤ 2^D := by
    obtain ⟨k,hk,hm⟩ := mem_biUnion.mp h
    obtain ⟨hp,hl,hu⟩ := mem_switchPrimes.mp hm
    rw [←pow_mul,Nat.mul_comm k 24] at hu
    refine ⟨hp,?_,hu.trans (Nat.pow_le_pow_right (by decide) (hcap k hk))⟩
    cases k with
    | zero => norm_num at hu; omega
    | succ k =>
      have htwo := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_succ (Nat.zero_le k))
      rw [pow_one] at htwo
      exact htwo.trans_lt hl
  have hDr : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hs : 0 ≤ 1-1/(D:ℝ) := sub_nonneg.mpr ((div_le_one (zero_lt_one.trans_le hDr)).2 hDr)
  have hs1 : 1-1/(D:ℝ) ≤ 1 := sub_le_self _ (by positivity)
  have h := (abs_le.mp (sampled_missed_ranges (X := X) (J := J) hco hs hs1)).2
  have hp' := mul_le_mul_of_nonneg_left (rankin_product hD hp)
    (Real.rpow_nonneg (Nat.cast_nonneg X) (1-1/(D:ℝ)))
  linarith only [h,hp']

private def height (C m : ℕ) := C*50^m
private def threshold (C m : ℕ) : ℕ := 2^(C*100^(m+1))

/-- Above the mth threshold the high-dimensional floor error is already
smaller than a geometric fraction of the cutoff. -/
private theorem geometric_sampling_error {C m X : ℕ} (hC : 0 < C) (hX : threshold C m ≤ X) :
    let D := height C m
    (X:ℝ)^(1-1/(D:ℝ))*(mertensBandProductConst*D)^4 ≤
      (X:ℝ)*((mertensBandProductConst*C)^4/(2:ℝ)^m) := by
  let D := height C m
  have hD : 0 < D := Nat.mul_pos hC (pow_pos (by decide) _)
  have hDr : (0:ℝ) < D := by exact_mod_cast hD
  have hx : 0 < X := (pow_pos (by decide : 0 < 2) _).trans_le hX
  have hxr : (0:ℝ) < X := by exact_mod_cast hx
  have hexp : C*100^(m+1)=100*2^m*D := by
    dsimp only [D,height]
    rw [pow_succ,show (100:ℕ)^m=(2*50)^m by norm_num,mul_pow]
    ring
  have hlowNat : ((2:ℕ)^(100*2^m))^D ≤ X := by
    rw [←pow_mul,←hexp]
    exact hX
  have hlow : (2:ℝ)^(100*2^m) ≤ (X:ℝ)^(1/(D:ℝ)) := by
    have hcast : ((2:ℝ)^(100*2^m))^D ≤ X := by exact_mod_cast hlowNat
    calc _ = (((2:ℝ)^(100*2^m))^D)^(1/(D:ℝ)) := by
                rw [one_div,Real.pow_rpow_inv_natCast (by positivity) hD.ne']
         _ ≤ _ := Real.rpow_le_rpow (by positivity) hcast (by positivity)
  have hnum : (50:ℝ)^(m*4)*2^m ≤ (2:ℝ)^(100*2^m) := by
    calc _ ≤ ((2:ℝ)^6)^(m*4)*2^m :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) _) (by positivity)
         _ = (2:ℝ)^(25*m) := by rw [←pow_mul,←pow_add]; congr 1; omega
         _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by have h := Nat.lt_two_pow_self (n := m); omega)
  have hpow : (mertensBandProductConst*D)^4*(2:ℝ)^m ≤
      (mertensBandProductConst*C)^4*(X:ℝ)^(1/(D:ℝ)) := by
    have he : (D:ℝ)=(C:ℝ)*50^m := by dsimp [D,height]; push_cast; rfl
    calc _ = (mertensBandProductConst*C)^4*((50:ℝ)^(m*4)*2^m) := by rw [he,pow_mul]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (hnum.trans hlow) (by positivity)
  dsimp only
  rw [Real.rpow_sub hxr,Real.rpow_one]
  change (X:ℝ)/(X:ℝ)^(1/(D:ℝ))*(mertensBandProductConst*D)^4 ≤ _
  have hr := (div_le_div_iff₀ (Real.rpow_pos_of_pos hxr (1/(D:ℝ))) (pow_pos (by norm_num : (0:ℝ)<2) m)).2 hpow
  calc _ = (X:ℝ)*((mertensBandProductConst*D)^4/(X:ℝ)^(1/(D:ℝ))) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hr hxr.le

private theorem geometric_matchings :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ A : ℝ, 1 ≤ A ∧ ∀ m X : ℕ, threshold C m ≤ X →
      ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
        (M.unmatchedSet.card:ℝ) ≤ A*X*(1-coveredFraction)^m ∧
        ∀ n ∈ M.sources, |(M.partner n:ℝ)-n| ≤ A*X*(1-coveredFraction)^m := by
  obtain ⟨H,hH⟩ := eventually_atTop.mp uniform_positive_mass_short_exchanges
  let C := H+2
  let G := (mertensBandProductConst*C)^4
  let A := 8+2*G
  have hC : 2 ≤ C := by dsimp only [C]; omega
  have hC0 : 0 < C := by omega
  have hG : 0 ≤ G := pow_nonneg (mul_nonneg mertensBandProductConst_pos.le (Nat.cast_nonneg C)) _
  have hA : 2 ≤ A := by dsimp [A]; linarith only [hG]
  refine ⟨C,hC,A,by linarith only [hA],?_⟩
  intro m X hX
  let J := (2:ℕ)^m
  let U := C*J
  have hJ : 0 < J := pow_pos (by decide) _
  have hJr : (0:ℝ) < J := by exact_mod_cast hJ
  have hU : 0 < U := Nat.mul_pos hC0 hJ
  have ready (k : ℕ) (hk : U ≤ k) : bandReady J k := by
    have hbase : H ≤ k := (by dsimp only [C]; omega : H ≤ C).trans
      ((Nat.le_mul_of_pos_right C hJ).trans hk)
    have htwo : (2:ℝ)*J ≤ k := by exact_mod_cast (Nat.mul_le_mul_right J hC).trans hk
    have hlog : (1:ℝ)/2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
      linarith only [h]
    refine bandReady_of_table (hH k hbase J hJ ?_)
    linarith only [htwo,mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)]
  obtain ⟨I,_,hcap,hI,hco,hfrac⟩ := packing_within J U hU ready m
  let D := height C m
  have hD : 0 < D := Nat.mul_pos hC0 (pow_pos (by decide) _)
  have hcap' (i : ℕ) (hi : i ∈ I) : 24*i ≤ D := by
    have he : 25^m*U=D := by
      change 25^m*(C*2^m)=C*50^m
      rw [show (50:ℕ)^m=(25*2)^m by norm_num,mul_pow]; ring
    exact (hcap i hi).trans_eq he
  have hQ : (0:ℝ) < exchangePeriod I := by exact_mod_cast period_pos I
  have hf := (div_le_iff₀ hQ).2 hfrac
  have hmiss := missed_ranges_at_height (J := J) (X := 2*X) hD hco hcap'
  have herr := geometric_sampling_error (C := C) (m := m) (X := 2*X) hC0 (by omega)
  have hbad : (((Icc 1 (2*X)).filter (missesSingles J I)).card:ℝ) ≤
      2*(X:ℝ)*((1-coveredFraction)^m+G/(2:ℝ)^m) := by
    apply hmiss.trans
    have he := add_le_add (mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg (α := ℝ) (2*X))) herr
    push_cast at he ⊢
    exact he.trans_eq (by dsimp only [G]; ring)
  have hb : (1:ℝ)/2 ≤ 1-coveredFraction := by
    have h : coveredFraction ≤ 1/2 := min_le_left _ _
    linarith only [h]
  have hgeom : 1/(J:ℝ) ≤ (1-coveredFraction)^m := by
    change 1/((2^m:ℕ):ℝ) ≤ _
    rw [Nat.cast_pow,Nat.cast_ofNat,one_div,←inv_pow]
    simpa only [one_div] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hb m
  have hxJ : J ≤ X := by
    apply le_trans _ hX
    have hu : m ≤ 100^(m+1) := (Nat.lt_two_pow_self (n := m)).le.trans
      ((Nat.pow_le_pow_left (by decide : 2 ≤ 100) m).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))
    exact Nat.pow_le_pow_right (by decide) (hu.trans (Nat.le_mul_of_pos_left _ hC0))
  have hone : 1 ≤ (X:ℝ)/J := (one_le_div hJr).2 (Nat.cast_le.mpr hxJ)
  have hc := mul_le_mul_of_nonneg_left hgeom (Nat.cast_nonneg X)
  obtain ⟨M,hm,hd⟩ := matching_cost_of_ranges J X I hI hco
  have hsub : (Ioc X (2*X)).filter (missesSingles J I) ⊆ (Icc 1 (2*X)).filter (missesSingles J I) := by
    intro n hn
    obtain ⟨hi,hs⟩ := mem_filter.mp hn
    obtain ⟨h1,h2⟩ := mem_Ioc.mp hi
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,h2⟩,hs⟩
  have hm' := (Nat.cast_le (α := ℝ)).mpr (hm.trans
    (Nat.add_le_add_right (Nat.add_le_add_right (card_le_card hsub) _) _))
  push_cast at hm'
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 2*(X:ℝ)/J by positivity)
  have hJcast : (J:ℝ)=(2:ℝ)^m := by simp [J]
  rw [←hJcast] at hbad
  let u := (X:ℝ)/J
  let b := (X:ℝ)*(1-coveredFraction)^m
  have hb0 : 0 ≤ b := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith only [hb]) _)
  have hGb := mul_nonneg hG hb0
  have hu : u ≤ b := (by dsimp only [u]; ring : u=(X:ℝ)*(1/(J:ℝ))).le.trans hc
  have hGu := mul_le_mul_of_nonneg_left hu hG
  have hbad' := hbad.trans_eq (show 2*(X:ℝ)*((1-coveredFraction)^m+G/J)=2*b+2*(G*u) by dsimp [b,u]; ring)
  have hce := hceil.trans_eq (show 2*(X:ℝ)/J+1=2*u+1 by dsimp only [u]; ring)
  change 1 ≤ u at hone
  have hAeq : A*X*(1-coveredFraction)^m=8*b+2*(G*b) := by dsimp [b,A]; ring
  refine ⟨M,?_,fun n hn => (hd n hn).trans ?_⟩
  · rw [hAeq]
    linarith only [hm',hbad',hce,hone,hu,hGu]
  · rw [hAeq,show 2*(X:ℝ)/J=2*u by dsimp only [u]; ring]
    linarith only [hu,hb0,hGb]

private theorem enclosing_threshold {C X : ℕ} (hC : 0 < C) (hx : threshold C 0 ≤ X) :
    ∃ m : ℕ, threshold C m ≤ X ∧ X < threshold C (m+1) := by
  have hex : ∃ j : ℕ, X < threshold C j := by
    have hg : X ≤ 100^(X+1) := (Nat.lt_two_pow_self (n := X)).le.trans
      ((Nat.pow_le_pow_left (by decide : 2 ≤ 100) X).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))
    exact ⟨X,(Nat.lt_two_pow_self (n := X)).trans_le (Nat.pow_le_pow_right (by decide)
      (hg.trans (Nat.le_mul_of_pos_left _ hC)))⟩
  have hmin := Nat.find_spec hex
  cases he : Nat.find hex with
  | zero => rw [he] at hmin; omega
  | succ m =>
    refine ⟨m,le_of_not_gt (Nat.find_min hex (show m < Nat.find hex by omega)),he ▸ hmin⟩

private theorem from_geometric_scale {C : ℕ} (hC : 2 ≤ C) {A : ℝ} (hA : 1 ≤ A) :
    ∃ c L : ℝ, 0 < c ∧ 0 < L ∧ ∀ᶠ X : ℕ in atTop, ∃ m : ℕ, threshold C m ≤ X ∧
      A*X*(1-coveredFraction)^m ≤ L*X/(Real.log X)^c := by
  let b := 1-coveredFraction
  have hb : 0 < b := by
    have h : coveredFraction ≤ 1/2 := min_le_left _ _
    dsimp [b]; linarith
  have hb1 : b < 1 := sub_lt_self _ coveredFraction_pos
  let c := -Real.log b/Real.log 100
  have h100 := Real.log_pos (by norm_num : (1:ℝ) < 100)
  have hc : 0 < c := div_pos (neg_pos.mpr (Real.log_neg hb hb1)) h100
  let K := (C:ℝ)*100^2*Real.log 2
  have hC0 : (0:ℝ) < C := by exact_mod_cast (by omega : 0 < C)
  have hK : 0 < K := mul_pos (mul_pos hC0 (by norm_num)) (Real.log_pos (by norm_num))
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hinv : (100:ℝ)^c = b⁻¹ := by
    rw [Real.rpow_def_of_pos (by norm_num),show Real.log 100*c = -Real.log b by
      dsimp only [c]; field_simp [h100.ne'],Real.exp_neg,Real.exp_log hb]
  refine ⟨c,A*K^c,hc,mul_pos hA0 (Real.rpow_pos_of_pos hK _),?_⟩
  filter_upwards [eventually_ge_atTop (threshold C 0),eventually_ge_atTop 2] with X hx hx2
  obtain ⟨m,hm,hu⟩ := enclosing_threshold (by omega) hx
  have hXr : (1:ℝ) < X := by exact_mod_cast hx2
  have hlog : Real.log X ≤ K*(100:ℝ)^m := by
    have hr : (X:ℝ) ≤ ((2:ℝ)^(C*100^(m+1+1):ℕ)) := by exact_mod_cast hu.le
    apply (Real.log_le_log (zero_lt_one.trans hXr) hr).trans_eq
    rw [Real.log_pow,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_succ,pow_succ]
    dsimp only [K]; ring
  have hcomm : ((100:ℝ)^m)^c=((100:ℝ)^c)^m := (Real.rpow_pow_comm (by norm_num) c m).symm
  have hbnd : (Real.log X)^c*b^m ≤ K^c := by
    have h := Real.rpow_le_rpow (Real.log_pos hXr).le hlog hc.le
    rw [Real.mul_rpow hK.le (by positivity),hcomm,hinv] at h
    apply (mul_le_mul_of_nonneg_right h (pow_nonneg hb.le m)).trans_eq
    rw [mul_assoc,←mul_pow,inv_mul_cancel₀ hb.ne',one_pow,mul_one]
  have target : A*X*b^m ≤ (A*K^c)*X/(Real.log X)^c := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos (Real.log_pos hXr) _)).2
    have h := mul_le_mul_of_nonneg_left hbnd (mul_nonneg hA0.le (Nat.cast_nonneg X))
    linarith only [h]
  exact ⟨m,hm,target⟩

/-- The full restricted graph on every sufficiently large dyadic block admits
a logarithmic power saving simultaneously for the unmatched squarefree
population and the length of every actual prime exchange. -/
theorem logarithmic_saving_for_restricted_matchings :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ᶠ X : ℕ in atTop,
      ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
        (M.unmatchedSet.card:ℝ) ≤ A*X/(Real.log X)^c ∧
        ∀ n ∈ M.sources, |(M.partner n:ℝ)-n| ≤ A*X/(Real.log X)^c := by
  obtain ⟨C,hC,A,hA,hg⟩ := geometric_matchings
  obtain ⟨c,L,hc,hL,h⟩ := from_geometric_scale hC hA
  refine ⟨c,L,hc,hL,?_⟩
  filter_upwards [h] with X hx
  obtain ⟨m,hm,hb⟩ := hx
  obtain ⟨M,hn,hd⟩ := hg m X hm
  exact ⟨M,hn.trans hb,fun n h => (hd n h).trans hb⟩

/-- One fixed global involution realizes a logarithmic saving at every large
sharp prefix. Each unpaid count includes fixed vertices and the endpoints
whose actual partners cross the given cutoff. -/
theorem logarithmic_saving_for_one_involution :
    ∃ c L : ℝ, 0 < c ∧ 0 < L ∧ ∀ᶠ X : ℕ in atTop,
      ((prefixUnpaid dyadicPrimeSwitch X).card:ℝ) ≤ L*X/(Real.log X)^c ∧
      |(dyadicPrimeSwitch X:ℝ)-X| ≤ L*X/(Real.log X)^c := by
  obtain ⟨C,hC,A,hA,hg⟩ := geometric_matchings
  let B := 4+3*A
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hA]
  obtain ⟨c,L,hc,hL,h⟩ := from_geometric_scale (C := 100*C) (by omega) hB
  refine ⟨c,L,hc,hL,?_⟩
  filter_upwards [h] with X hx
  obtain ⟨m,ht,hr⟩ := hx
  let K := C*100^(m+1)
  let b := 1-coveredFraction
  have hhalf : (1:ℝ)/2 ≤ b := by
    have hh : coveredFraction ≤ 1/2 := min_le_left _ _
    dsimp [b]; linarith
  have hb : 0 ≤ b := (by norm_num : (0:ℝ) ≤ 1/2).trans hhalf
  have hK : 0 < K := Nat.mul_pos (by omega) (pow_pos (by decide) _)
  have hT : (2:ℕ)^(100*K) ≤ X := by
    have he : 100*K=(100*C)*100^(m+1) := by dsimp only [K]; ring
    rw [he]; exact ht
  have hmK : m ≤ K := by
    have he := (Nat.lt_two_pow_self (n := m)).le.trans (Nat.pow_le_pow_left (by decide : 2 ≤ 100) m)
    exact he.trans ((Nat.pow_le_pow_right (by decide) (Nat.le_succ _)).trans (Nat.le_mul_of_pos_left _ (by omega : 0 < C)))
  have gain : 1/(2:ℝ)^m ≤ b^m := by
    rw [one_div,←inv_pow]; simpa only [one_div] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hhalf m
  have hg0 : 0 ≤ b^m := pow_nonneg hb _
  have hprodN : (2:ℕ)^K*2^m ≤ X := by
    rw [←pow_add]
    exact (Nat.pow_le_pow_right (by decide) (by omega : K+m ≤ 100*K)).trans hT
  have hstart : (2:ℝ)^K ≤ (X:ℝ)*b^m := by
    have hh := (le_div_iff₀ (pow_pos (by norm_num : (0:ℝ) < 2) m)).2
      (by exact_mod_cast hprodN : (2:ℝ)^K*2^m ≤ X)
    exact hh.trans (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left gain (Nat.cast_nonneg X))
  have hx0 : 2*(2:ℕ)^K+2 ≤ X := by
    have hfour : 4*(2:ℕ)^K=2^(K+2) := by rw [pow_add]; ring
    have hroom := (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : K+2 ≤ 100*K)).trans hT
    rw [←hfour] at hroom
    have hp := Nat.two_pow_pos K
    omega
  let δ := (A+1)*b^m
  have hδ : 0 ≤ δ := mul_nonneg (by linarith only [hA]) hg0
  have costs (j : ℕ) (hj : K ≤ j) : (blockCost (2^j):ℝ) ≤ δ*(2:ℝ)^j := by
    have hbase : threshold C m ≤ 2^j := Nat.pow_le_pow_right (by decide) hj
    obtain ⟨M,hn,hd⟩ := hg m (2^j) hbase
    have hh := (Nat.cast_le (α := ℝ)).mpr (blockCost_le_of_matching M hn hd)
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ A*((2^j:ℕ):ℝ)*b^m by positivity)
    have hjm : (2:ℝ)^m ≤ 2^j := pow_le_pow_right₀ (by norm_num) (hmK.trans hj)
    have hone := (one_le_div (pow_pos (by norm_num : (0:ℝ)<2) m)).2 hjm
    have hgain := mul_le_mul_of_nonneg_left gain (pow_nonneg (by norm_num : (0:ℝ)≤2) j)
    push_cast at hh hceil
    change ((blockCost (2^j):ℕ):ℝ) ≤ ↑⌈A*(2:ℝ)^j*b^m⌉₊ at hh
    have hunit : 1 ≤ (2:ℝ)^j*b^m := hone.trans ((by ring :
      (2:ℝ)^j/2^m=(2:ℝ)^j*(1/2^m)).le.trans hgain)
    dsimp only [δ]
    linarith only [hh,hceil,hunit]
  have ⟨hfix,hmove⟩ := dyadic_switch_prefix_bound hδ hx0 costs
  have hAx : 0 ≤ A*(X:ℝ)*b^m := mul_nonneg (mul_nonneg (by linarith only [hA]) (Nat.cast_nonneg _)) hg0
  have hx : 0 ≤ (X:ℝ)*b^m := mul_nonneg (Nat.cast_nonneg _) hg0
  change B*(X:ℝ)*b^m ≤ _ at hr
  dsimp only [δ] at hfix hmove
  dsimp only [B] at hr
  constructor <;> linarith only [hfix,hmove,hstart,hr,hAx,hx]

#print axioms logarithmic_saving_for_restricted_matchings
#print axioms logarithmic_saving_for_one_involution

end GaloisForLFunctions.RestrictedFactorizationCalculus
