import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheSquareRootBiasOfTheOddBalancedComposites
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheOuterCellsOfTheFractionalPrimeMidpoint
import GaloisForLFunctions.RHTower.Sieve.PrimeSupportedConvolutionBound

/-!
# The prime powers removed from one balanced octave

For each prime dividing the center, at most one of its powers can lie in
the half-open octave. The two products deleted on the opposite sides of
the midpoint are therefore coprime. Their signed log vanishes exactly
when no power was deleted. The complementary fractional kernels of
Meiners and Gnewuch read that same signed log at every order in (0,1).
-/

noncomputable section
open Finset MeasureTheory
open GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

def removedProperPowers (n a b : ℕ) : Finset ℕ :=
  (Ioc a b).filter (fun k => ¬n.Coprime k ∧ ¬k.Prime ∧ k.primeFactors.card=1)

def removedProperMass (n a b : ℕ) : ℝ := ∑ k ∈ removedProperPowers n a b, Real.log k

private theorem removed_base {n a b k : ℕ} (hk : k∈removedProperPowers n a b) :
    k.minFac.Prime ∧ k.minFac ∣ n ∧ ∃ j : ℕ, 0<j ∧ k=k.minFac^j := by
  obtain ⟨_,hc,_,hcard⟩ := mem_filter.mp hk
  obtain ⟨p,j,hp,hj,rfl⟩ :=
    (isPrimePow_nat_iff k).mp (isPrimePow_iff_card_primeFactors_eq_one.mpr hcard)
  rw [hp.pow_minFac hj.ne']
  refine ⟨hp,?_,j,hj,rfl⟩
  by_contra hd
  exact hc ((Nat.coprime_pow_right_iff hj n p).mpr (hp.coprime_iff_not_dvd.mpr hd).symm)

private theorem powers_in_one_octave {a p i j : ℕ} (hp : 2≤p)
    (hi : p^i∈Ioc a (2*a)) (hj : p^j∈Ioc a (2*a)) : i=j := by
  have separated {r s : ℕ} (hrs : r<s) (hr : p^r∈Ioc a (2*a)) (hs : p^s∈Ioc a (2*a)) : False := by
    have h := Nat.pow_le_pow_right (by omega : 0 < p) (show r+1 ≤ s from hrs)
    rw [pow_succ] at h
    have hd := Nat.mul_le_mul_left (p^r) hp
    have hl := (mem_Ioc.mp hr).1
    have hu := (mem_Ioc.mp hs).2
    omega
  exact le_antisymm (le_of_not_gt fun h => separated h hj hi) (le_of_not_gt fun h => separated h hi hj)

/-- Distinct removed powers in a half-open octave have distinct prime bases. -/
theorem distinct_removed_bases_in_an_octave (n a b : ℕ) (hb : b≤2*a) :
    Set.InjOn Nat.minFac (removedProperPowers n a b : Set ℕ) := by
  intro x hx y hy hxy
  obtain ⟨hp,_,i,_,hi⟩ := removed_base hx
  obtain ⟨_,_,j,_,hj⟩ := removed_base hy
  change x.minFac=y.minFac at hxy
  rw [←hxy] at hj
  have inside {k : ℕ} (hk : k∈removedProperPowers n a b) : k∈Ioc a (2*a) := by
    obtain ⟨hl,hu⟩ := mem_Ioc.mp (mem_filter.mp hk).1
    exact mem_Ioc.mpr ⟨hl,hu.trans hb⟩
  have he := powers_in_one_octave hp.two_le
    (show x.minFac^i∈Ioc a (2*a) by rw [←hi]; exact inside hx)
    (show x.minFac^j∈Ioc a (2*a) by rw [←hj]; exact inside hy)
  exact hi.trans ((congrArg (x.minFac^·) he).trans hj.symm)

/-- In a half-open octave each prime divisor of the center costs at most
one full logarithm, regardless of its exponent in the center. -/
theorem removed_power_mass_bound {n : ℕ} (hn : 0<n) (a b : ℕ) (hb : b≤2*a) :
    0≤removedProperMass n a b ∧ removedProperMass n a b≤(n.primeFactors.card:ℝ)*Real.log b := by
  have hc : (removedProperPowers n a b).card≤n.primeFactors.card := by
    refine card_le_card_of_injOn Nat.minFac ?_ (distinct_removed_bases_in_an_octave n a b hb)
    intro k hk
    exact Nat.mem_primeFactors.mpr ⟨(removed_base hk).1,(removed_base hk).2.1,hn.ne'⟩
  refine ⟨sum_nonneg (fun k _ => Real.log_natCast_nonneg k),?_⟩
  calc removedProperMass n a b ≤ ∑ _k ∈ removedProperPowers n a b, Real.log b := by
         apply sum_le_sum
         intro k hk
         obtain ⟨hl,hu⟩ := mem_Ioc.mp (mem_filter.mp hk).1
         exact Real.log_le_log (Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt hl)) (Nat.cast_le.mpr hu)
       _ ≤ _ := by
         rw [sum_const,nsmul_eq_mul]
         exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (Real.log_natCast_nonneg _)

private theorem prefix_loss (n a b : ℕ) (hab : a≤b) :
    (fullLogProperPrefix 1 b-fullLogProperPrefix 1 a) -
      (fullLogProperPrefix n b-fullLogProperPrefix n a) = removedProperMass n a b := by
  have interval (c : ℕ) : fullLogProperPrefix c b-fullLogProperPrefix c a=∑ k ∈ Ioc a b, purePowerLog c k := by
    simp only [fullLogProperPrefix,Nat.floor_natCast]
    linarith only [sum_Ioc_consecutive (purePowerLog c) (Nat.zero_le a) hab]
  rw [interval,interval,←sum_sub_distrib,removedProperMass,removedProperPowers,sum_filter]
  refine sum_congr rfl fun k _ => ?_
  unfold purePowerLog
  by_cases h : ¬k.Prime ∧ k.primeFactors.card=1
  · rw [if_pos (And.intro (Nat.coprime_one_left k) h)]
    by_cases hc : n.Coprime k
    · have keep : ¬(¬n.Coprime k ∧ ¬k.Prime ∧ k.primeFactors.card=1) := fun hk => hk.1 hc
      rw [if_pos (And.intro hc h),if_neg keep,sub_self]
    · have hdrop : ¬(n.Coprime k ∧ ¬k.Prime ∧ k.primeFactors.card=1) := fun hk => hc hk.1
      rw [if_neg hdrop,if_pos (And.intro hc h),sub_zero]
  · have off (P : Prop) : ¬(P ∧ ¬k.Prime ∧ k.primeFactors.card=1) := fun hk => h hk.2
    rw [if_neg (off (Nat.Coprime 1 k)),if_neg (off (n.Coprime k)),if_neg (off (¬n.Coprime k)),sub_self]

/-- The exact signed discrepancy from dropping coprimality at the three
cuts, with the closed middle endpoint assigned to the lower interval. -/
theorem removed_prime_powers_price_the_composite_defect {n : ℕ} (hn : 0<n) :
    realMidpointObservation (fullLogProperPrefix 1) n-
      (oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n) =
        removedProperMass n (2*n) (3*n)-removedProperMass n (3*n) (4*n) := by
  have hL := prefix_loss n (2*n) (3*n) (by omega)
  have hU := prefix_loss n (3*n) (4*n) (by omega)
  rw [composite_midpoint_minus_prime hn,realMidpointObservation]
  push_cast at hL hU ⊢
  linarith only [hL,hU]

/-- The total signed perturbation costs at most one endpoint logarithm
per distinct prime factor of the center. -/
theorem composite_coprimality_error_by_prime_divisors {n : ℕ} (hn : 0<n) :
    |realMidpointObservation (fullLogProperPrefix 1) n-
      (oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n)| ≤
        (n.primeFactors.card:ℝ)*Real.log (4*(n:ℝ)) := by
  obtain ⟨hL,eL⟩ := removed_power_mass_bound hn (2*n) (3*n) (by omega)
  obtain ⟨hU,eU⟩ := removed_power_mass_bound hn (3*n) (4*n) (by omega)
  have hlog := Real.log_le_log (Nat.cast_pos.mpr (by omega : 0<3*n))
    (Nat.cast_le.mpr (by omega : 3*n≤4*n))
  have he := eL.trans (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))
  rw [removed_prime_powers_price_the_composite_defect hn,abs_le]
  push_cast at eU he
  constructor <;> linarith only [hL,hU,eU,he]

/-- An elementary logarithm-squared bound suffices to drop the center's
coprimality condition simultaneously at all root scales. -/
theorem logarithmic_composite_coprimality_error {n : ℕ} (hn : 0<n) :
    |realMidpointObservation (fullLogProperPrefix 1) n-
      (oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n)| ≤
        (Real.log n/Real.log 2)*Real.log (4*(n:ℝ)) := by
  have h := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    (_root_.RHTower.Sieve.card_primeFactors_mul_log_two_le_log hn)
  have hx := (Nat.one_le_cast (α:=ℝ)).mpr hn
  exact (composite_coprimality_error_by_prime_divisors hn).trans
    (mul_le_mul_of_nonneg_right h (Real.log_nonneg (by linarith only [hx])))

private theorem contained_removed {n a b A B : ℕ} (ha : A≤a) (hb : b≤B) :
    removedProperPowers n a b ⊆ removedProperPowers n A B := by
  intro k hk
  obtain ⟨h,hk⟩ := mem_filter.mp hk
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨ha.trans_lt (mem_Ioc.mp h).1,(mem_Ioc.mp h).2.trans hb⟩,hk⟩

private theorem split_removed (n : ℕ) :
    removedProperPowers n (2*n) (4*n) =
      removedProperPowers n (2*n) (3*n) ∪ removedProperPowers n (3*n) (4*n) := by
  ext k
  simp only [removedProperPowers,mem_filter,mem_Ioc,mem_union]
  constructor
  · rintro ⟨⟨hl,hu⟩,hk⟩
    rcases le_or_gt k (3*n) with h | h
    · exact Or.inl ⟨⟨hl,h⟩,hk⟩
    · exact Or.inr ⟨⟨h,hu⟩,hk⟩
  · rintro (⟨⟨hl,hu⟩,hk⟩ | ⟨⟨hl,hu⟩,hk⟩) <;> exact ⟨⟨by omega,by omega⟩,hk⟩

private theorem barred_halves_disjoint (n : ℕ) :
    Disjoint (removedProperPowers n (2*n) (3*n)) (removedProperPowers n (3*n) (4*n)) :=
  disjoint_left.mpr fun _ hl hu => (mem_Ioc.mp (mem_filter.mp hu).1).1.not_ge (mem_Ioc.mp (mem_filter.mp hl).1).2

private theorem signed_log_of_removed_powers {n : ℕ} (hn : 0<n) :
    realMidpointObservation (fullLogProperPrefix 1) n-
      (oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n) =
        ∑ k ∈ removedProperPowers n (2*n) (4*n), if k≤3*n then Real.log k else -Real.log k := by
  rw [removed_prime_powers_price_the_composite_defect hn,split_removed,sum_union (barred_halves_disjoint n)]
  have lower (k : ℕ) (hk : k∈removedProperPowers n (2*n) (3*n)) := (mem_Ioc.mp (mem_filter.mp hk).1).2
  have upper (k : ℕ) (hk : k∈removedProperPowers n (3*n) (4*n)) := (mem_Ioc.mp (mem_filter.mp hk).1).1.not_ge
  rw [sum_congr rfl (fun k hk => if_pos (lower k hk)),sum_congr rfl (fun k hk => if_neg (upper k hk)),
    sum_neg_distrib,sub_eq_add_neg]
  rfl

private theorem removed_products_coprime (n : ℕ) :
    Nat.Coprime (∏ k ∈ removedProperPowers n (2*n) (3*n), k) (∏ k ∈ removedProperPowers n (3*n) (4*n), k) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro x hx
  apply Nat.coprime_prod_right_iff.mpr
  intro y hy
  obtain ⟨p,_,i,_,hi⟩ := removed_base hx
  obtain ⟨q,_,j,_,hj⟩ := removed_base hy
  have hne : x.minFac≠y.minFac := by
    intro he
    have h := distinct_removed_bases_in_an_octave n (2*n) (4*n) (by omega)
      (contained_removed le_rfl (by omega) hx) (contained_removed (by omega) le_rfl hy) he
    have hl := (mem_Ioc.mp (mem_filter.mp hx).1).2
    have hu := (mem_Ioc.mp (mem_filter.mp hy).1).1
    omega
  rw [hi,hj]
  exact ((Nat.coprime_primes p q).mpr hne).pow i j

/-- Opposite sides cannot conceal a lost power by exact cancellation.
The unrestricted price agrees with the true composite correction exactly
when the entire octave contains no removed power. -/
theorem unrestricted_composite_iff_no_removed_power {n : ℕ} (hn : 0<n) :
    realMidpointObservation (fullLogProperPrefix 1) n =
      oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n ↔
        removedProperPowers n (2*n) (4*n)=∅ := by
  rw [←sub_eq_zero,removed_prime_powers_price_the_composite_defect hn,sub_eq_zero,split_removed]
  let L := removedProperPowers n (2*n) (3*n)
  let U := removedProperPowers n (3*n) (4*n)
  have members {a b k : ℕ} (ha : 2*n≤a) (hk : k∈removedProperPowers n a b) : 1<k := by
    have hl := (mem_Ioc.mp (mem_filter.mp hk).1).1
    omega
  have logged (a b : ℕ) (ha : 2*n≤a) : Real.log ((∏ k ∈ removedProperPowers n a b, k : ℕ):ℝ) =
      removedProperMass n a b := by
    rw [Nat.cast_prod]
    exact Real.log_prod fun k hk => Nat.cast_ne_zero.mpr (by have := members ha hk; omega)
  constructor
  · intro he
    rw [←logged (2*n) (3*n) le_rfl,←logged (3*n) (4*n) (by omega)] at he
    have hp (S : Finset ℕ) (hS : ∀ k∈S, 1<k) : 0<((∏ k ∈ S,k : ℕ):ℝ) :=
      Nat.cast_pos.mpr (prod_pos fun k hk => Nat.zero_lt_one.trans (hS k hk))
    have hL := hp L (fun _ hk => members le_rfl hk)
    have hU := hp U (fun _ hk => members (by omega) hk)
    have ee := congrArg Real.exp he
    rw [Real.exp_log hL,Real.exp_log hU] at ee
    have eq : (∏ k ∈ L,k) = ∏ k ∈ U,k := by exact_mod_cast ee
    have hc : Nat.gcd (∏ k ∈ L,k) (∏ k ∈ U,k)=1 := removed_products_coprime n
    rw [eq,Nat.gcd_self] at hc
    have empty (S : Finset ℕ) (hh : (∏ k ∈ S,k)=1) (hm : ∀ k∈S, 1<k) : S=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro k hk
      have hd := dvd_prod_of_mem (fun k : ℕ => k) hk
      rw [hh] at hd
      exact (hm k hk).ne' (Nat.eq_one_of_dvd_one hd)
    change L∪U=∅
    rw [empty L (eq.trans hc) (fun _ hk => members le_rfl hk),empty U hc (fun _ hk => members (by omega) hk),union_empty]
  · intro he
    obtain ⟨hL,hU⟩ := union_eq_empty.mp he
    simp only [removedProperMass,hL,hU,sum_empty]

private theorem own_power_removed {p j : ℕ} (hp : p.Prime) (hj : 0<j)
    (i : ℕ) (hi : 2 ≤ i) (h : p^i∈Ioc (2*p^j) (4*p^j)) :
      p^i∈removedProperPowers (p^j) (2*p^j) (4*p^j) := by
  have hi₀ : i≠0 := by omega
  refine mem_filter.mpr ⟨h,?_,Nat.Prime.not_prime_pow hi,?_⟩
  · intro hc
    have hd := Nat.dvd_gcd (dvd_pow_self p hj.ne') (dvd_pow_self p hi₀)
    rw [show (p^j).gcd (p^i)=1 from hc] at hd
    exact hp.ne_one (Nat.eq_one_of_dvd_one hd)
  · rw [Nat.primeFactors_prime_pow hi₀ hp,card_singleton]

private theorem removed_dyadic_endpoint {j : ℕ} (hj : 0<j) :
    4*2^j ∈ removedProperPowers (2^j) (2*2^j) (4*2^j) := by
  have he : 2^(j+2)=4*2^j := by rw [pow_add,show (2:ℕ)^2=4 by decide,Nat.mul_comm]
  have hk := own_power_removed Nat.prime_two hj (j+2) (by omega) (by
    rw [he,mem_Ioc]
    have := pow_pos (by decide : 0<2) j
    omega)
  rwa [he] at hk

private theorem removed_ternary_endpoint {j : ℕ} (hj : 0<j) :
    3*3^j ∈ removedProperPowers (3^j) (2*3^j) (4*3^j) := by
  have he : 3^(j+1)=3*3^j := by rw [pow_succ,Nat.mul_comm]
  have hk := own_power_removed Nat.prime_three hj (j+1) (by omega) (by
    rw [he,mem_Ioc]
    have := pow_pos (by decide : 0<3) j
    omega)
  rwa [he] at hk

/-- On positive powers of a prime, exactly the bases two and three
produce a coprimality defect. -/
theorem unrestricted_composite_at_prime_powers_iff {p j : ℕ} (hp : p.Prime) (hj : 0<j) :
    realMidpointObservation (fullLogProperPrefix 1) (p^j:ℕ) =
      oddSmoothCompositePrice (p^j)-unitaryMidpointCenter (p^j)-primeMidpointPrice (p^j) ↔ 4<p := by
  rw [unrestricted_composite_iff_no_removed_power (pow_pos hp.pos j)]
  constructor
  · intro he
    by_contra! hsmall
    have hfour : p≠4 := fun h => (by decide : ¬Nat.Prime 4) (h ▸ hp)
    have hp₂ := hp.two_le
    rcases (by omega : p=2 ∨ p=3) with rfl | rfl
    · have h := removed_dyadic_endpoint hj
      rw [he] at h
      exact notMem_empty _ h
    · have h := removed_ternary_endpoint hj
      rw [he] at h
      exact notMem_empty _ h
  · intro hbig
    apply eq_empty_iff_forall_notMem.mpr
    intro k hk
    obtain ⟨hq,hd,i,_,hi⟩ := removed_base hk
    have he := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd)
    rw [he] at hi
    obtain ⟨hl,hu⟩ := mem_Ioc.mp (mem_filter.mp hk).1
    rw [hi] at hl hu
    by_cases hh : i≤j
    · have := Nat.pow_le_pow_right hp.pos hh
      omega
    · have h := Nat.pow_le_pow_right hp.pos (show j+1 ≤ i by omega)
      rw [pow_succ] at h
      have ht := Nat.mul_lt_mul_of_pos_left hbig (pow_pos hp.pos j)
      rw [Nat.mul_comm _ 4] at ht
      omega

/-- At powers of two the loss saturates the one-prime logarithmic bound
with negative sign. Powers of three give the opposite sign at the middle
cut. Every other prime power has zero defect. -/
theorem exact_composite_defect_at_prime_powers {p j : ℕ} (hp : p.Prime) (hj : 0<j) :
    let n := p^j
    realMidpointObservation (fullLogProperPrefix 1) n-
      (oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n) =
        if p=2 then -Real.log (4*(n:ℝ)) else if p=3 then Real.log (3*(n:ℝ)) else 0 := by
  let n := p^j
  have base {k : ℕ} (hk : k∈removedProperPowers n (2*n) (4*n)) : k.minFac=p :=
    (Nat.prime_dvd_prime_iff_eq (removed_base hk).1 hp).mp ((removed_base hk).1.dvd_of_dvd_pow (removed_base hk).2.1)
  have single {k : ℕ} (hk : k∈removedProperPowers n (2*n) (4*n)) :
      realMidpointObservation (fullLogProperPrefix 1) n-
        (oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n) =
          if k≤3*n then Real.log k else -Real.log k := by
    rw [signed_log_of_removed_powers (pow_pos hp.pos j)]
    apply sum_eq_single_of_mem k hk
    intro z hz hne
    exact (hne (distinct_removed_bases_in_an_octave n (2*n) (4*n) (by omega) hz hk ((base hz).trans (base hk).symm))).elim
  by_cases h₂ : p=2
  · subst p
    have h := single (removed_dyadic_endpoint hj)
    have hpos : 0<(2:ℕ)^j := pow_pos (by decide) j
    have hcut : ¬4*2^j ≤ 3*2^j := by omega
    simpa [n,hcut] using h
  by_cases h₃ : p=3
  · subst p
    simpa [n,h₂] using single (removed_ternary_endpoint hj)
  have hn₄ : p≠4 := fun he => (by decide : ¬Nat.Prime 4) (he ▸ hp)
  have hp₂ := hp.two_le
  have hz := (unrestricted_composite_at_prime_powers_iff hp hj).mpr (by omega)
  simp only [if_neg h₂,if_neg h₃,sub_eq_zero]
  exact hz

/-- A single complementary fractional test reads the entire arithmetic
defect, even though the two bins have opposite signs. -/
theorem fractional_reading_of_removed_powers {n : ℕ} (hn : 0<n) {b : ℝ} (hb : b∈Set.Ioo (0:ℝ) 1) :
    (∫ t : ℝ, midpointFractionalTest n b t *
      field (removedProperPowers n (2*n) (4*n)) Nat.cast (fun k => Real.log k) (b-1) t) =
      ProbabilityTheory.beta (1-b) b * (realMidpointObservation (fullLogProperPrefix 1) n-
        (oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n)) := by
  let S := removedProperPowers n (2*n) (4*n)
  let w := fun k : ℕ => Real.log k
  let B := ProbabilityTheory.beta (1-b) b
  have hi (j : ℕ) : Integrable (fun t => cutPower (-b) (t-j)*field S Nat.cast w (b-1) t) := by
    simpa only [show 1-b-1= -b by ring] using
      integrable_pairing S Nat.cast w (sub_pos.mpr hb.2) hb.1 (j:ℝ)
  have ev (j : ℕ) : (∫ t, cutPower (-b) (t-j)*field S Nat.cast w (b-1) t) =
      B * ∑ k ∈ S.filter (j < ·), w k := by
    simpa only [sum_filter,Nat.cast_lt,B] using complementary_tail S Nat.cast w hb (j:ℝ)
  have hL : S.filter (2*n < ·)=S := filter_true_of_mem fun k hk => (mem_Ioc.mp (mem_filter.mp hk).1).1
  have hU : S.filter (3*n < ·)=removedProperPowers n (3*n) (4*n) := by
    ext k
    simp only [S,removedProperPowers,mem_filter,mem_Ioc]
    constructor
    · rintro ⟨⟨⟨_,hu⟩,h⟩,hl⟩; exact ⟨⟨hl,hu⟩,h⟩
    · rintro ⟨⟨hl,hu⟩,h⟩; exact ⟨⟨⟨by omega,hu⟩,h⟩,hl⟩
  change (∫ t, midpointFractionalTest n b t*field S Nat.cast w (b-1) t)=B*_
  simp only [midpointFractionalTest,sub_mul,mul_assoc]
  rw [integral_sub (hi (2*n)) ((hi (3*n)).const_mul 2), integral_const_mul,ev,ev,hL,hU,
    removed_prime_powers_price_the_composite_defect hn]
  dsimp only [S,removedProperMass,w]
  rw [split_removed,sum_union (barred_halves_disjoint n)]
  ring

/-- At any single complementary order, a zero fractional reading certifies
that the entire octave contains no suppressed prime power. -/
theorem fractional_null_iff_no_removed_power {n : ℕ} (hn : 0<n) {b : ℝ} (hb : b∈Set.Ioo (0:ℝ) 1) :
    (∫ t : ℝ, midpointFractionalTest n b t *
      field (removedProperPowers n (2*n) (4*n)) Nat.cast (fun k => Real.log k) (b-1) t)=0 ↔
      removedProperPowers n (2*n) (4*n)=∅ := by
  rw [fractional_reading_of_removed_powers hn hb,mul_eq_zero,
    or_iff_right (ProbabilityTheory.beta_pos (sub_pos.mpr hb.2) hb.1).ne',
    sub_eq_zero,unrestricted_composite_iff_no_removed_power hn]

/-- Every positive even center gives a nonzero reading. Its octave
contains the first power of two strictly above the lower cut. -/
theorem fractional_coprimality_defect_at_even_centers {n : ℕ} (hn : 0<n) (hd : 2∣n)
    {b : ℝ} (hb : b∈Set.Ioo (0:ℝ) 1) :
    (∫ t : ℝ, midpointFractionalTest n b t *
      field (removedProperPowers n (2*n) (4*n)) Nat.cast (fun k => Real.log k) (b-1) t)≠0 := by
  let j := Nat.log 2 (2*n)+1
  have hn₂ : 2*n≠0 := by omega
  have hj : 2≤j := by
    have h : 1≤Nat.log 2 (2*n) :=
      (Nat.le_log_iff_pow_le (by decide : 1<2) hn₂).mpr (by rw [pow_one]; omega)
    dsimp only [j]
    omega
  have hlo : 2*n<2^j := Nat.lt_pow_succ_log_self (by decide : 1<2) _
  have hu : 2^j≤4*n := by
    have h := Nat.pow_log_le_self 2 hn₂
    dsimp only [j]
    rw [pow_succ]
    omega
  have he : 2^j∈removedProperPowers n (2*n) (4*n) := by
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨hlo,hu⟩,?_,Nat.Prime.not_prime_pow hj,?_⟩
    · intro hc
      have h := Nat.dvd_gcd hd (dvd_pow_self 2 (by omega : j≠0))
      rw [show n.gcd (2^j)=1 from hc] at h
      exact (by decide : ¬2∣1) h
    · rw [Nat.primeFactors_prime_pow (by omega : j≠0) Nat.prime_two,card_singleton]
  intro hz
  rw [(fractional_null_iff_no_removed_power hn hb).mp hz] at he
  exact notMem_empty _ he

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
