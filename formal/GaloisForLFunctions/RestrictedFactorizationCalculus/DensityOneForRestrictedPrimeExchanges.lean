import GaloisForLFunctions.RestrictedFactorizationCalculus.ReversibleSwitchesOnPrimeRanges

/-!
# Density-one matching by restricted prime exchanges

Each additional range removes a fixed fraction of the remaining residue
classes. The combined period is fixed before the sharp dyadic cutoff grows.
The first eligible exchange is reversible and has arbitrarily small relative
displacement. Thus both the exceptional population and the largest displacement
are sublinear on the entire squarefree dyadic block.
-/

noncomputable section

open Finset Filter RHTower
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The product modulus recording all selected prime ranges. -/
def exchangePeriod (I : Finset ℕ) := ∏ k ∈ I, switchModulus k

theorem period_pos (I : Finset ℕ) : 0 < exchangePeriod I :=
  prod_pos (fun k _ => (switchModulus_spec k).2.2)

theorem divides_period {k : ℕ} {I : Finset ℕ} (hk : k ∈ I) : switchModulus k ∣ exchangePeriod I :=
  dvd_prod_of_mem _ hk

/-- No selected range has a complete local gcd equal to a paired single prime. -/
def missesSingles (J : ℕ) (I : Finset ℕ) (n : ℕ) : Prop :=
  ∀ k ∈ I, n.gcd (switchModulus k) ∉ (switchProducts k).image (bandPartner J k)

/-- The residues which miss every test by a paired single prime. -/
def missedClasses (J : ℕ) (I : Finset ℕ) :=
  (range (exchangePeriod I)).filter (missesSingles J I)

private theorem residue_misses {J n : ℕ} {I : Finset ℕ} (hn : missesSingles J I n) :
    n % exchangePeriod I ∈ missedClasses J I := by
  refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (period_pos I)),fun k hk => ?_⟩
  rw [(Nat.ModEq.of_dvd (divides_period hk) (Nat.mod_modEq n (exchangePeriod I))).gcd_eq]
  exact hn k hk

/-- Independent ranges multiply the upper bound for the number of missed
residues. Injectivity in a complete period is the only CRT direction needed. -/
private theorem multiply_exceptions (J : ℕ) {I : Finset ℕ} {k : ℕ} (hk : k ∉ I)
    (hco : (exchangePeriod I).Coprime (switchModulus k)) :
    (missedClasses J (insert k I)).card ≤ (missedClasses J I).card*
      (missedResidues (switchModulus k) ((switchProducts k).image (bandPartner J k))).card := by
  let Q := exchangePeriod I
  let P := switchModulus k
  have he : exchangePeriod (insert k I)=Q*P := by
    change (∏ i ∈ insert k I, switchModulus i)=Q*P
    rw [prod_insert hk]; exact Nat.mul_comm ..
  let B := missedResidues P ((switchProducts k).image (bandPartner J k))
  calc _ ≤ ((missedClasses J I).product B).card := by
          apply card_le_card_of_injOn (fun n => (n%Q,n%P))
          · intro n hn
            obtain ⟨_,hm⟩ := mem_filter.mp hn
            refine mem_product.mpr ⟨residue_misses (fun j hj => hm j (mem_insert_of_mem hj)),?_⟩
            refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (switchModulus_spec k).2.2),?_⟩
            rw [(Nat.mod_modEq n P).gcd_eq]
            exact hm k (mem_insert_self ..)
          · intro a ha b hb hh
            have hab := (Nat.modEq_and_modEq_iff_modEq_mul hco).1
              ⟨(congrArg Prod.fst hh : a%Q=b%Q),(congrArg Prod.snd hh : a%P=b%P)⟩
            have h₁ := mem_range.mp (mem_filter.mp ha).1
            have h₂ := mem_range.mp (mem_filter.mp hb).1
            rw [he] at h₁ h₂
            change a%(Q*P)=b%(Q*P) at hab
            simpa only [Nat.mod_eq_of_lt h₁,Nat.mod_eq_of_lt h₂] using hab
       _ = _ := card_product _ _

private theorem separated_moduli {i k : ℕ} (hk : 24*i ≤ k) :
    (switchModulus i).Coprime (switchModulus k) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd h
  have mem {j : ℕ} (hv : p ∣ switchModulus j) : p ∈ switchPrimes j :=
    (switchModulus_spec j).2.1 ▸ Nat.mem_primeFactors.mpr ⟨hp,hv,(switchModulus_spec j).2.2.ne'⟩
  have hu := (mem_switchPrimes.mp (mem (hd.trans (Nat.gcd_dvd_left _ _)))).2.2
  have hl := (mem_switchPrimes.mp (mem (hd.trans (Nat.gcd_dvd_right _ _)))).2.1
  rw [←pow_mul,Nat.mul_comm i 24] at hu
  exact hl.not_ge (hu.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hk))

/-- An absolute lower bound for the fraction detected by any ready range. -/
def coveredFraction : ℝ := min (1/2) ((1/(24*mertensBandProductConst)^2)*(1/1040))

theorem coveredFraction_pos : 0 < coveredFraction := by
  have := mertensBandProductConst_pos
  exact lt_min (by norm_num) (by positivity)

/-- A geometric list of equally effective ranges with explicit control on
every prime in the combined modulus. -/
theorem packing_within (J U : ℕ) (hU0 : 0 < U) (hU : ∀ k ≥ U, bandReady J k) (l : ℕ) :
    ∃ I : Finset ℕ, I.card=l ∧ (∀ k ∈ I, 24*k ≤ 25^l*U) ∧ (∀ k ∈ I, bandReady J k) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → (switchModulus i).Coprime (switchModulus j)) ∧
      ((missedClasses J I).card:ℝ) ≤ (1-coveredFraction)^l*(exchangePeriod I) := by
  have hκ : 0 ≤ 1-coveredFraction := by
    have h : coveredFraction ≤ 1/2 := min_le_left _ _
    linarith
  induction l with
  | zero =>
    refine ⟨∅,rfl,by simp,by simp,by simp,?_⟩
    simp [missedClasses,missesSingles,exchangePeriod]
  | succ l ih =>
    obtain ⟨I,hcard,hcap,hI,hpair,hsize⟩ := ih
    let k := 25^l*U
    have hkU : U ≤ k := Nat.le_mul_of_pos_left U (pow_pos (by decide) _)
    have hkpos : 0 < k := hU0.trans_le hkU
    have hkn : k ∉ I := fun hm => by have hh : 24*k ≤ k := hcap k hm; omega
    have hdis (j : ℕ) (hj : j ∈ I) := separated_moduli (hcap j hj)
    have hco : (exchangePeriod I).Coprime (switchModulus k) := Nat.Coprime.prod_left hdis
    have hr := hU k hkU
    let P := (switchProducts k).image (bandPartner J k)
    have hP : P ⊆ switchPrimes k := by
      intro p hp
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hp
      exact (hr.1.2 w hw).1
    have hmass := missedResidues_density (k := k) hkpos hP
    have hgain : coveredFraction ≤ (1/(24*mertensBandProductConst)^2)*(∑ p ∈ P,1/(p:ℝ)) :=
      (min_le_right _ _).trans (mul_le_mul_of_nonneg_left hr.2 (by positivity))
    have hmid := hmass.trans (sub_le_sub_left hgain 1)
    have hm0 : (0:ℝ) < switchModulus k := by exact_mod_cast (switchModulus_spec k).2.2
    have hc := (div_le_iff₀ hm0).1 hmid
    have hm := multiply_exceptions J hkn hco
    refine ⟨insert k I,by rw [card_insert_of_notMem hkn,hcard],?_,?_,?_,?_⟩
    · intro j hj
      have he : 25^(l+1)*U = 25*k := by dsimp only [k]; rw [pow_succ]; ring
      rw [he]
      rcases mem_insert.mp hj with rfl | hj
      · omega
      · have hh : 24*j ≤ k := hcap j hj
        omega
    · intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · exact hr
      · exact hI j hj
    · intro i hi j hj hn
      rcases mem_insert.mp hi with rfl | hi <;> rcases mem_insert.mp hj with rfl | hj
      · exact False.elim (hn rfl)
      · exact (hdis j hj).symm
      · exact hdis i hi
      · exact hpair i hi j hj hn
    · have he : exchangePeriod (insert k I)=exchangePeriod I*switchModulus k := by
        change (∏ i ∈ insert k I, switchModulus i)=exchangePeriod I*switchModulus k
        rw [prod_insert hkn]; exact Nat.mul_comm ..
      rw [he,Nat.cast_mul,pow_succ]
      calc _ ≤ ((missedClasses J I).card:ℝ)*(missedResidues (switchModulus k) P).card := by exact_mod_cast hm
           _ ≤ ((1-coveredFraction)^l*(exchangePeriod I))*((1-coveredFraction)*(switchModulus k)) :=
             mul_le_mul hsize hc (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg hκ _) (Nat.cast_nonneg _))
           _ = _ := by ring

private theorem packing (J : ℕ) (hJ : 0 < J) (l : ℕ) :
    ∃ I : Finset ℕ, (∀ k ∈ I, bandReady J k) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → (switchModulus i).Coprime (switchModulus j)) ∧
      ((missedClasses J I).card:ℝ) ≤ (1-coveredFraction)^l*(exchangePeriod I) := by
  obtain ⟨H,hH⟩ := eventually_atTop.mp (eventually_bandReady J hJ)
  obtain ⟨I,_,_,hI,hpair,hsize⟩ := packing_within J (H+1) (Nat.succ_pos _) (fun k hk => hH k (by omega)) l
  exact ⟨I,hI,hpair,hsize⟩

/-- At any sharp cutoff the number of missed integers is controlled by its complete residue classes. -/
theorem missed_upto (J U : ℕ) (I : Finset ℕ) :
    (((Icc 1 U).filter (missesSingles J I)).card:ℝ) ≤
      ((missedClasses J I).card:ℝ)*((U:ℝ)/(exchangePeriod I)+1) := by
  let Q := exchangePeriod I
  have hQ : (0:ℝ) < Q := by exact_mod_cast period_pos I
  have hin : ((Icc 1 U).filter (missesSingles J I)).card ≤
      ((missedClasses J I).product (range (U/Q+1))).card := by
    apply card_le_card_of_injOn (fun n => (n%Q,n/Q))
    · intro n hn
      obtain ⟨hI,hm⟩ := mem_filter.mp hn
      exact mem_product.mpr ⟨residue_misses hm,mem_range.mpr
        (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp hI).2))⟩
    · intro a _ b _ hh
      exact (Nat.mod_add_div a Q).symm.trans (by rw [show a%Q=b%Q from congrArg Prod.fst hh,
        show a/Q=b/Q from congrArg Prod.snd hh,Nat.mod_add_div])
  have hcount := hin.trans_eq (card_product (missedClasses J I) (range (U/Q+1)))
  rw [card_range] at hcount
  have hv : ((U/Q:ℕ):ℝ) ≤ (U:ℝ)/Q :=
    (le_div_iff₀ hQ).2 (by exact_mod_cast Nat.div_mul_le_self (U) Q)
  apply le_trans (by exact_mod_cast hcount :
    (((Icc 1 U).filter (missesSingles J I)).card:ℝ) ≤ (missedClasses J I).card*(((U/Q:ℕ):ℝ)+1))
  exact mul_le_mul_of_nonneg_left (add_le_add_left hv 1) (Nat.cast_nonneg _)

private theorem missed_in_block (J X : ℕ) (I : Finset ℕ) :
    (((Ioc X (2*X)).filter (missesSingles J I)).card:ℝ) ≤
      ((missedClasses J I).card:ℝ)*(2*(X:ℝ)/(exchangePeriod I)+1) := by
  have hsub : (Ioc X (2*X)).filter (missesSingles J I) ⊆ (Icc 1 (2*X)).filter (missesSingles J I) := by
    intro n hn
    obtain ⟨hI,hm⟩ := mem_filter.mp hn
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hI
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hu⟩,hm⟩
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans (by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (missed_upto J (2*X) I))

private theorem choose_ranges {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ 16/(J:ℝ) ≤ ε ∧ ∃ I : Finset ℕ, (∀ k ∈ I, bandReady J k) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → (switchModulus i).Coprime (switchModulus j)) ∧
      ((missedClasses J I).card:ℝ)/exchangePeriod I ≤ ε/8 := by
  obtain ⟨J,hJbig⟩ := exists_nat_gt (16/ε)
  have hJr : 0 < (J:ℝ) := (div_pos (by norm_num) hε).trans hJbig
  have hJ : 0 < J := Nat.cast_pos.mp hJr
  have hwidth : 16/(J:ℝ) ≤ ε := (div_le_iff₀ hJr).2 (by
    simpa only [mul_comm] using ((div_lt_iff₀ hε).1 hJbig).le)
  have hκ := coveredFraction_pos
  obtain ⟨l,hl⟩ : ∃ l : ℕ, (1-coveredFraction)^l < ε/8 :=
    exists_pow_lt_of_lt_one (by positivity) (by linarith only [hκ])
  obtain ⟨I,hI,hpair,hres⟩ := packing J hJ l
  let B := missedClasses J I
  let Q := exchangePeriod I
  have hQ : (0:ℝ) < Q := by exact_mod_cast period_pos I
  have hfrac : (B.card:ℝ)/Q ≤ ε/8 :=
    ((div_le_iff₀ hQ).2 hres).trans hl.le
  exact ⟨J,hJ,hwidth,I,hI,hpair,hfrac⟩

/-- The complete matching cost consists of missed local divisors and two
cutoff strips. This finite bound also applies when the ranges vary with X. -/
theorem matching_cost_of_ranges (J X : ℕ) (I : Finset ℕ)
    (hI : ∀ k ∈ I, bandReady J k)
    (hpair : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (switchModulus i).Coprime (switchModulus j)) :
    ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
      M.unmatchedSet.card ≤ ((Ioc X (2*X)).filter (missesSingles J I)).card+
        ⌈2*(X:ℝ)/J⌉₊+⌈2*(X:ℝ)/J⌉₊ ∧ ∀ n ∈ M.sources, |(M.partner n:ℝ)-n| ≤ 2*(X:ℝ)/J := by
  obtain ⟨M,hboundary,hlocal⟩ := matching_from_disjoint_ranges J X I hI hpair
  let d := ⌈2*(X:ℝ)/J⌉₊
  have hd : 2*(X:ℝ)/J ≤ (d:ℝ) := Nat.le_ceil _
  let left := Ioc X (X+d)
  let right := Ioc (2*X-d) (2*X)
  let bad := (Ioc X (2*X)).filter (missesSingles J I)
  have hsub : M.unmatchedSet ⊆ (bad ∪ left) ∪ right := by
    intro n hn
    have hs : n ∈ Ioc X (2*X) := (mem_filter.mp (mem_sdiff.mp hn).1).1
    by_cases ha : (activeBands J I n).Nonempty
    · rcases hboundary n hn ha with h | h
      · apply mem_union_left
        apply mem_union_right
        apply mem_Ioc.mpr
        exact ⟨(mem_Ioc.mp hs).1,by exact_mod_cast h.trans (add_le_add_right hd (X:ℝ))⟩
      · have hlt : 2*X < n+d := by
          exact_mod_cast (show 2*(X:ℝ) < (n:ℝ)+d by linarith only [h,hd])
        obtain ⟨hnX,hnu⟩ := mem_Ioc.mp hs
        exact mem_union_right _ (mem_Ioc.mpr ⟨by omega,hnu⟩)
    · apply mem_union_left
      apply mem_union_left
      refine mem_filter.mpr ⟨hs,fun k hk hin => ha ⟨k,?_⟩⟩
      exact mem_filter.mpr ⟨hk,mem_union_right _ hin⟩
  have hleft : left.card ≤ d := by simp [left]
  have hright : right.card ≤ d := by simp only [right,Nat.card_Ioc]; omega
  have htotal : M.unmatchedSet.card ≤ bad.card+d+d :=
    (card_le_card hsub).trans ((card_union_le ..).trans
      (add_le_add ((card_union_le ..).trans (Nat.add_le_add_left hleft _)) hright))
  exact ⟨M,htotal,hlocal⟩

/-- On every sufficiently large sharp dyadic interval a single matching by
actual one-to-two exchanges leaves an arbitrarily small fraction of the block
unmatched and has arbitrarily small relative displacement. -/
theorem density_one_restricted_matching {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
        (M.unmatchedSet.card:ℝ) ≤ ε*X ∧ ∀ n ∈ M.sources, |(M.partner n:ℝ)-n| ≤ ε*X := by
  obtain ⟨J,hJ,hwidth,I,hI,hpair,hfrac⟩ := choose_ranges hε
  have hJr : 0 < (J:ℝ) := by exact_mod_cast hJ
  let B := missedClasses J I
  let Q := exchangePeriod I
  filter_upwards [eventually_ge_atTop ⌈4*((B.card:ℝ)+2)/ε⌉₊] with X hX
  have hX0 := Nat.cast_nonneg (α := ℝ) X
  have hcost := (div_le_iff₀ hε).1
    ((Nat.le_ceil (4*((B.card:ℝ)+2)/ε)).trans (Nat.cast_le.mpr hX))
  obtain ⟨M,htotal,hlocal⟩ := matching_cost_of_ranges J X I hI hpair
  let d := ⌈2*(X:ℝ)/J⌉₊
  let bad := (Ioc X (2*X)).filter (missesSingles J I)
  have hd' : (d:ℝ) < 2*(X:ℝ)/J+1 := Nat.ceil_lt_add_one (by positivity)
  have hbad : (bad.card:ℝ) ≤ 2*(X:ℝ)*(ε/8)+B.card := by
    apply (missed_in_block J X I).trans
    calc (B.card:ℝ)*(2*(X:ℝ)/Q+1) = 2*(X:ℝ)*((B.card:ℝ)/Q)+B.card := by ring
         _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hfrac (by positivity)) _
  have hwX := mul_le_mul_of_nonneg_right hwidth hX0
  have gap : 2*(X:ℝ)/J ≤ (ε*X)/8 := by
    calc _ = ((16/(J:ℝ))*X)/8 := by ring
         _ ≤ _ := div_le_div_of_nonneg_right hwX (by norm_num)
  change M.unmatchedSet.card ≤ bad.card+d+d at htotal
  have hnat := (Nat.cast_le (α := ℝ)).mpr htotal
  rw [Nat.cast_add,Nat.cast_add] at hnat
  have hbudget := mul_nonneg hε.le hX0
  refine ⟨M,by nlinarith only [hnat,hbad,hd',hcost,gap,hbudget],fun n hn => (hlocal n hn).trans ?_⟩
  linarith only [gap,hbudget]

#print axioms density_one_restricted_matching

/-- Fixed squarefree vertices and the endpoints whose partners cross a sharp prefix. -/
def prefixUnpaid (F : ℕ → ℕ) (X : ℕ) :=
  (squarefreeOf (Icc 1 X)).filter (fun n => F n=n ∨ X < F n)

/-- The unpaid fixed and crossing vertices carry the full signed sum at each cutoff. -/
theorem prefix_switch_balance (F : ℕ → ℕ)
    (hF : ∀ n : ℕ, Squarefree n → F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) (X : ℕ) :
    ∑ n ∈ Icc 1 X, μ n = ∑ n ∈ prefixUnpaid F X, μ n := by
  let S := Icc 1 X
  let A := (squarefreeOf S).filter (fun n => F n ≠ n ∧ F n ≤ X)
  have ends {n : ℕ} (hn : n ∈ A) : F n ∈ A ∧ F (F n)=n ∧ μ (F n) = -μ n := by
    obtain ⟨hs,hd,hle⟩ := mem_filter.mp hn
    obtain ⟨hS,hsq⟩ := mem_filter.mp hs
    obtain ⟨back,he⟩ := hF n hsq
    have edge := he.resolve_left hd
    have hmin : 1 ≤ F n := Nat.one_le_iff_ne_zero.mpr edge.2.1.ne_zero
    refine ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hmin,hle⟩,edge.2.1⟩,
      by rw [back]; exact hd.symm,by rw [back]; exact (mem_Icc.mp hS).2⟩,back,?_⟩
    have h := edge.2.2.1
    omega
  have hin : Set.InjOn F A := fun x hx y hy he =>
    (ends hx).2.1.symm.trans ((congrArg F he).trans (ends hy).2.1)
  have imageEq : A.image F=A := by
    ext n
    constructor
    · intro h
      obtain ⟨a,ha,rfl⟩ := mem_image.mp h
      exact (ends ha).1
    · exact fun h => mem_image.mpr ⟨F n,(ends h).1,(ends h).2.1⟩
  have perm : ∑ n ∈ A, μ (F n) = ∑ n ∈ A, μ n := by rw [←sum_image hin,imageEq]
  have sign : ∑ n ∈ A, μ (F n) = -∑ n ∈ A, μ n := by
    rw [←sum_neg_distrib]
    exact sum_congr rfl (fun _ hn => (ends hn).2.2)
  have hzero : ∑ n ∈ A, μ n = 0 := by omega
  have apart : squarefreeOf S \ prefixUnpaid F X = A := by
    ext n
    simp only [A,prefixUnpaid,S,Finset.mem_sdiff,mem_filter]
    constructor
    · rintro ⟨hs,hu⟩
      exact ⟨hs,fun h => hu ⟨hs,Or.inl h⟩,le_of_not_gt (fun h => hu ⟨hs,Or.inr h⟩)⟩
    · rintro ⟨hs,hn,hx⟩
      exact ⟨hs,fun ⟨_,h⟩ => h.elim hn (not_lt_of_ge hx)⟩
  have hsub : prefixUnpaid F X ⊆ squarefreeOf S := filter_subset _ _
  have hsum := sum_sdiff_eq_sub (f := fun n => μ n) hsub
  rw [apart,hzero] at hsum
  calc ∑ n ∈ S, μ n = ∑ n ∈ squarefreeOf S, μ n := by
          rw [squarefreeOf,sum_filter]
          apply sum_congr rfl
          intro n _
          by_cases h : Squarefree n <;> simp [h,moebius_eq_zero_of_not_squarefree]
       _ = _ := by omega

/-- One finite collection of prime ranges serves at every sharp
prefix for a fixed population and displacement tolerance. -/
theorem dense_prime_range_table_at_every_prefix {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∃ I : Finset ℕ, (∀ k ∈ I, bandReady J k) ∧
      let F := rangeSwitch J I
      (∀ n : ℕ, Squarefree n → F (F n)=n ∧
        (F n=n ∨ GlobalDyadicOneTwoRel n (F n)) ∧ |(F n:ℝ)-n| ≤ ε*n) ∧
      (∀ X : ℕ, ∑ n ∈ Icc 1 X, μ n = ∑ n ∈ prefixUnpaid F X, μ n) ∧
      ∀ᶠ X : ℕ in atTop, ((prefixUnpaid F X).card:ℝ) ≤ ε*X := by
  obtain ⟨J,hJ,hwidth,I,hI,hco,hfrac⟩ := choose_ranges hε
  let F := rangeSwitch J I
  let B := missedClasses J I
  let Q := exchangePeriod I
  have hJr : (0:ℝ) < J := by exact_mod_cast hJ
  have near (n : ℕ) : (n:ℝ)/J ≤ ε*n := by
    have h := (div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 16) hJr.le).trans hwidth
    calc _ = (1/(J:ℝ))*n := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n)
  have law (n : ℕ) (hn : Squarefree n) := rangeSwitch_involution J I hI hco hn
  refine ⟨J,I,hI,fun n hn => ⟨(law n hn).1,(law n hn).2.2.2,(law n hn).2.1.trans (near n)⟩,
    prefix_switch_balance F (fun n hn => ⟨(law n hn).1,(law n hn).2.2.2⟩),?_⟩
  filter_upwards [eventually_ge_atTop ⌈4*((B.card:ℝ)+1)/ε⌉₊] with X hX
  let d := ⌈(X:ℝ)/J⌉₊
  let T := (Icc 1 X).filter (missesSingles J I)
  have hd := Nat.le_ceil ((X:ℝ)/J)
  have hd' : (d:ℝ) < (X:ℝ)/J+1 := Nat.ceil_lt_add_one (by positivity)
  have hsub : prefixUnpaid F X ⊆ T ∪ Ioc (X-d) X := by
    intro n hn
    obtain ⟨hs,hun⟩ := mem_filter.mp hn
    obtain ⟨hS,hsq⟩ := mem_filter.mp hs
    rcases hun with hf | hover
    · apply mem_union_left
      refine mem_filter.mpr ⟨hS,fun k hk hp => (law n hsq).2.2.1.mp hf ⟨k,?_⟩⟩
      exact mem_filter.mpr ⟨hk,mem_union_right _ hp⟩
    · have hx : (X:ℝ) < F n := by exact_mod_cast hover
      have hdiff := (abs_le.mp (law n hsq).2.1).2
      have hdist := div_le_div_of_nonneg_right (Nat.cast_le.mpr (mem_Icc.mp hS).2 :
        (n:ℝ) ≤ X) hJr.le
      have hnat : X < n+d := by
        exact_mod_cast (show (X:ℝ) < (n:ℝ)+d by linarith only [hx,hdiff,hdist,hd])
      obtain ⟨hn1,hnX⟩ := mem_Icc.mp hS
      exact mem_union_right _ (mem_Ioc.mpr ⟨by omega,hnX⟩)
  have hcount : (prefixUnpaid F X).card ≤ T.card+d := by
    have hb : (Ioc (X-d) X).card ≤ d := by rw [Nat.card_Ioc]; omega
    exact (card_le_card hsub).trans ((card_union_le ..).trans (Nat.add_le_add_left hb _))
  have hT : (T.card:ℝ) ≤ (ε/8)*X+B.card := by
    apply (missed_upto J X I).trans
    calc (B.card:ℝ)*((X:ℝ)/Q+1) = ((B.card:ℝ)/Q)*X+B.card := by ring
         _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right hfrac (Nat.cast_nonneg _)) _
  have hceil := (div_le_iff₀ hε).1
    ((Nat.le_ceil (4*((B.card:ℝ)+1)/ε)).trans (Nat.cast_le.mpr hX))
  have hwide : (X:ℝ)/J ≤ (ε*X)/16 := by
    calc _ = ((16/(J:ℝ))*X)/16 := by ring
         _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hwidth (Nat.cast_nonneg X))
                    (by norm_num)
  have hr : ((prefixUnpaid F X).card:ℝ) ≤ (T.card:ℝ)+d := by exact_mod_cast hcount
  nlinarith only [hr,hT,hd',hceil,hwide,mul_nonneg hε.le (Nat.cast_nonneg X)]

/-- One involution for all sharp prefixes at the requested tolerance. Its
actual unpaid vertices recover the Möbius sum exactly at every cutoff and
have upper density at most ε. Each nontrivial edge is a prime exchange. -/
theorem one_switch_for_all_prefixes {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ℕ → ℕ, (∀ n : ℕ, Squarefree n → F (F n)=n ∧
        (F n=n ∨ GlobalDyadicOneTwoRel n (F n)) ∧ |(F n:ℝ)-n| ≤ ε*n) ∧
      (∀ X : ℕ, ∑ n ∈ Icc 1 X, μ n = ∑ n ∈ prefixUnpaid F X, μ n) ∧
      ∀ᶠ X : ℕ in atTop, ((prefixUnpaid F X).card:ℝ) ≤ ε*X := by
  obtain ⟨J,I,_,law,balance,count⟩ := dense_prime_range_table_at_every_prefix hε
  exact ⟨rangeSwitch J I,law,balance,count⟩

#print axioms dense_prime_range_table_at_every_prefix
#print axioms one_switch_for_all_prefixes

end GaloisForLFunctions.RestrictedFactorizationCalculus
