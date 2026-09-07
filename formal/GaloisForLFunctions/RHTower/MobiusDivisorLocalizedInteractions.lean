import GaloisForLFunctions.RHTower.DivisorSmoothSquareMaximum
import GaloisForLFunctions.RHTower.MobiusDivisorTwoPrimeLocalCriterion
import GaloisForLFunctions.RHTower.RetainedPrimeSupportThreshold
import GaloisForLFunctions.RHTower.MobiusDivisorFirstPrimeReserve

/-!
# Product-localized mixed interactions of the actual divisor source

Every prime-containing partner is supported on cofactors below its quotient.
The uniform unsigned ceiling and exact prime differences bound all retained
amplitudes, including fields with reversed signs. Counting only product-born
labels gives inverse-prime bounds for merger gains and separate joint-child
and cross-child costs for their mixed second differences.

The smaller prime's arithmetic reserve pays a sufficiently separated larger
prime's gain. The general estimates retain a processed-cardinality factor;
no uniform complete-order or signed Abel bound is assumed or proved.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

private lemma abs_oriented (M : ℕ) (P R : Finset ℕ) :
    |mobiusDivisorOrientedFibre M P R|=|mobiusDivisorSelectionFibre M P R| := by
  simp [mobiusDivisorOrientedFibre,abs_mul,abs_pow]

private lemma oriented_amplitude (M : ℕ) (P : Finset ℕ)
    (hP : ∀ p∈P,p.Prime) (R : Finset ℕ) (hR : ∀ r∈R,r.Prime) :
    |mobiusDivisorOrientedFibre M P R|≤(3/5:ℝ)*2^(P.card-1)*Real.sqrt M := by
  induction P using Finset.induction_on generalizing R with
  | empty =>
    rw [mobiusDivisorOrientedFibre_empty_eq_unsigned_product R hR,
      abs_of_nonneg (divisorUnsignedDilationChannel_nonneg M _)]
    simpa using divisorUnsignedDilationChannel_le_three_fifths_sqrt M (∏ p∈R,p)
  | @insert p P hpP ih =>
    have hp := hP p (mem_insert_self p P)
    have hP' : ∀ q∈P,q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have hiR : ∀ q∈insert p R,q.Prime := by simpa using And.intro hp hR
    by_cases hpR : p∈R
    · rw [abs_oriented,mobiusDivisorSelectionFibre_insert,if_pos hpR,abs_zero]
      positivity
    rw [mobiusDivisorOrientedFibre_insert M P R p hpR,card_insert_of_notMem hpP]
    by_cases hPe : P=∅
    · subst P
      have ha0 := mobiusDivisorSelectionFibre_empty_parity_nonneg M R
      have hb0 := mobiusDivisorSelectionFibre_empty_parity_nonneg M (insert p R)
      have ha := ih (by simp) R hR
      have hb := ih (by simp) (insert p R) hiR
      change 0 ≤ mobiusDivisorOrientedFibre M ∅ R at ha0
      change 0 ≤ mobiusDivisorOrientedFibre M ∅ (insert p R) at hb0
      norm_num only [card_empty,zero_add,Nat.zero_sub,Nat.sub_self,pow_zero,mul_one] at ha hb ⊢
      rw [abs_of_nonneg ha0] at ha
      rw [abs_of_nonneg hb0] at hb
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    · have hcard : 1≤P.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hPe)
      have he : P.card-1+1=P.card := by omega
      have hpow : (2:ℝ)^P.card=2*2^(P.card-1) := by
        calc
          _ = (2:ℝ)^(P.card-1+1) := congrArg (fun n : ℕ => (2:ℝ)^n) he.symm
          _ = _ := by rw [pow_succ]; ring
      calc
        _ ≤ |mobiusDivisorOrientedFibre M P R|+
            |mobiusDivisorOrientedFibre M P (insert p R)| := abs_sub _ _
        _ ≤ (3/5:ℝ)*2^(P.card-1)*Real.sqrt M+
            (3/5:ℝ)*2^(P.card-1)*Real.sqrt M := add_le_add (ih hP' R hR) (ih hP' _ hiR)
        _ = _ := by rw [Nat.add_sub_cancel,hpow]; ring

/-- Every retained prime coordinate has a source-derived amplitude ceiling;
the first difference does not amplify the original nonnegative interval. -/
theorem abs_mobiusDivisorSelectionFibre_le_source_amplitude (M : ℕ) (P R : Finset ℕ)
    (hP : ∀ p∈P,p.Prime) (hR : ∀ r∈R,r.Prime) :
    |mobiusDivisorSelectionFibre M P R|≤(3/5:ℝ)*2^(P.card-1)*Real.sqrt M := by
  rw [← abs_oriented]
  exact oriented_amplitude M P hP R hR

private lemma product_label_count (T : Finset (Finset ℕ)) (N : ℕ)
    (hT : ∀ R∈T,∀ p∈R,p.Prime) :
    (T.filter (fun R => (∏ p∈R,p)≤N)).card≤N := by
  let S := T.filter (fun R => (∏ p∈R,p)≤N)
  have hmap : Set.MapsTo (fun R : Finset ℕ => ∏ p∈R,p) (↑S) (↑(Icc 1 N)) := by
    intro R hR
    have hpos : 0<∏ p∈R,p := prod_pos (fun p hp => (hT R (mem_filter.mp hR).1 p hp).pos)
    exact mem_Icc.mpr ⟨hpos,(mem_filter.mp hR).2⟩
  have hinj : Set.InjOn (fun R : Finset ℕ => ∏ p∈R,p) (↑S) := by
    intro R hR V hV he
    have h := congrArg Nat.primeFactors he
    simpa only [Nat.primeFactors_prod (hT R (mem_filter.mp hR).1),
      Nat.primeFactors_prod (hT V (mem_filter.mp hV).1)] using h
  simpa [S] using card_le_card_of_injOn _ hmap hinj

private lemma sum_abs_product_bound (T : Finset (Finset ℕ)) (N : ℕ)
    (hT : ∀ R∈T,∀ p∈R,p.Prime) (f g : Finset ℕ → ℝ) (H : ℝ)
    (hf : ∀ R∈T,|f R|≤H) (hg : ∀ R∈T,|g R|≤H)
    (hz : ∀ R∈T,N<∏ p∈R,p → f R*g R=0) :
    (∑ R∈T,|f R*g R|)≤(N:ℝ)*H^2 := by
  let S := T.filter (fun R => (∏ p∈R,p)≤N)
  have he : (∑ R∈T,|f R*g R|)=∑ R∈S,|f R*g R| := by
    symm
    apply sum_subset (filter_subset _ _)
    intro R hR hn
    have hlt : N<∏ p∈R,p := by simpa [S,hR] using hn
    rw [hz R hR hlt,abs_zero]
  rw [he]
  calc
    _ ≤ ∑ _R∈S,H^2 := by
      apply sum_le_sum
      intro R hR
      have hRt := (mem_filter.mp hR).1
      rw [abs_mul,pow_two]
      exact mul_le_mul (hf R hRt) (hg R hRt) (abs_nonneg _) ((abs_nonneg _).trans (hf R hRt))
    _ = (S.card:ℝ)*H^2 := by simp
    _ ≤ (N:ℝ)*H^2 := mul_le_mul_of_nonneg_right
      (by exact_mod_cast product_label_count T N hT) (sq_nonneg H)

private lemma source_amplitude_square (M k : ℕ) :
    ((3/5:ℝ)*2^k*Real.sqrt M)^2=(9/25:ℝ)*4^k*(M:ℝ) := by
  have hp : ((2:ℝ)^k)^2=4^k := by
    rw [← pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  rw [mul_pow,mul_pow,hp,Real.sq_sqrt (Nat.cast_nonneg M)]
  ring

/-- The full gain of any prime merger is localized to its actual product-born
cofactor labels, giving an inverse-prime bound even after sign changes. -/
theorem abs_mobiusDivisorSelectionEnergy_insert_le_source_support
    (M : ℕ) (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    {q : ℕ} (hq : q.Prime) (hqM : q<M) (hqP : q∉P) :
    |mobiusDivisorSelectionEnergy M (insert q P)-mobiusDivisorSelectionEnergy M P|≤
      (18/25:ℝ)*4^(P.card-1)*(M:ℝ)*((M-1)/q:ℕ) := by
  let T := ((mobiusDivisorSelectionPrimes M).erase q).powerset
  let H := (3/5:ℝ)*2^(P.card-1)*Real.sqrt M
  have hprime (R : Finset ℕ) (hR : R∈T) : ∀ p∈R,p.Prime := by
    intro p hp
    exact (mem_filter.mp (mem_erase.mp (mem_powerset.mp hR hp)).2).2
  have hqR (R : Finset ℕ) (hR : R∈T) : q∉R := by
    intro h
    exact (mem_erase.mp (mem_powerset.mp hR h)).1 rfl
  have hleft (R : Finset ℕ) (hR : R∈T) : |mobiusDivisorSelectionFibre M P R|≤H :=
    abs_mobiusDivisorSelectionFibre_le_source_amplitude M P R hP (hprime R hR)
  have hright (R : Finset ℕ) (hR : R∈T) :
      |mobiusDivisorSelectionFibre M P (insert q R)|≤H :=
    abs_mobiusDivisorSelectionFibre_le_source_amplitude M P _ hP
      (by simpa using And.intro hq (hprime R hR))
  have hz (R : Finset ℕ) (hR : R∈T) (hn : (M-1)/q<∏ p∈R,p) :
      mobiusDivisorSelectionFibre M P R*mobiusDivisorSelectionFibre M P (insert q R)=0 := by
    have hmul := (Nat.div_lt_iff_lt_mul hq.pos).mp hn
    rw [Nat.mul_comm] at hmul
    have hcut : M≤∏ p∈insert q R,p := by
      rw [prod_insert (hqR R hR)]
      omega
    rw [mobiusDivisorSelectionFibre_eq_zero_of_le_product M P _ hcut,mul_zero]
  have hb := sum_abs_product_bound T ((M-1)/q) hprime
    (mobiusDivisorSelectionFibre M P) (fun R => mobiusDivisorSelectionFibre M P (insert q R))
    H hleft hright hz
  rw [mobiusDivisorSelectionEnergy_insert_cross hq M P hqM hqP,abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ 2*(∑ R∈T,|mobiusDivisorSelectionFibre M P R*
        mobiusDivisorSelectionFibre M P (insert q R)|) :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2*(((M-1)/q:ℕ):ℝ)*H^2 := by linarith only [hb]
    _ = _ := by dsimp [H]; rw [source_amplitude_square]; ring

private def mixedOverlap (M : ℕ) (P : Finset ℕ) (p q : ℕ) : ℝ :=
  ∑ R∈(((mobiusDivisorSelectionPrimes M).erase q).erase p).powerset,
    (mobiusDivisorSelectionFibre M P R*mobiusDivisorSelectionFibre M P (insert p (insert q R))+
      mobiusDivisorSelectionFibre M P (insert p R)*mobiusDivisorSelectionFibre M P (insert q R))

private lemma mixed_identity (M : ℕ) (P : Finset ℕ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpM : p<M) (hqM : q<M)
    (_hpP : p∉P) (hqP : q∉P) (hpq : p≠q) :
    mobiusDivisorSelectionEnergy M (insert q (insert p P))-
      mobiusDivisorSelectionEnergy M (insert p P)-
      mobiusDivisorSelectionEnergy M (insert q P)+mobiusDivisorSelectionEnergy M P =
        2*mixedOverlap M P p q := by
  let U := (mobiusDivisorSelectionPrimes M).erase q
  let T := (U.erase p).powerset
  have hpU : p∈U := mem_erase.mpr ⟨hpq,mem_filter.mpr ⟨mem_range.mpr hpM,hp⟩⟩
  have hpR (R : Finset ℕ) (hR : R∈T) : p∉R := by
    intro h
    exact (mem_erase.mp (mem_powerset.mp hR h)).1 rfl
  have hsplit (f : Finset ℕ → ℝ) :
      (∑ R∈U.powerset,f R)=∑ R∈T,(f R+f (insert p R)) := by
    conv_lhs => rw [← insert_erase hpU]
    rw [sum_powerset_insert (notMem_erase p U),← sum_add_distrib]
  have hnew := mobiusDivisorSelectionEnergy_insert_cross hq M (insert p P) hqM
    (by simp [hqP,hpq.symm])
  have hold := mobiusDivisorSelectionEnergy_insert_cross hq M P hqM hqP
  have heq : mobiusDivisorSelectionEnergy M (insert q (insert p P))-
      mobiusDivisorSelectionEnergy M (insert p P)-
      mobiusDivisorSelectionEnergy M (insert q P)+mobiusDivisorSelectionEnergy M P =
      (mobiusDivisorSelectionEnergy M (insert q (insert p P))-
        mobiusDivisorSelectionEnergy M (insert p P))-
      (mobiusDivisorSelectionEnergy M (insert q P)-mobiusDivisorSelectionEnergy M P) := by ring
  rw [heq,hnew,hold]
  change 2*(∑ R∈U.powerset,_)-2*(∑ R∈U.powerset,_)=_
  rw [hsplit,hsplit,← mul_sub,← sum_sub_distrib]
  unfold mixedOverlap
  congr 1
  apply sum_congr rfl
  intro R hR
  rw [mobiusDivisorSelectionFibre_insert,mobiusDivisorSelectionFibre_insert,
    mobiusDivisorSelectionFibre_insert,mobiusDivisorSelectionFibre_insert]
  simp only [hpR R hR,mem_insert,hpq,false_or,true_or,if_false,if_true,zero_mul,add_zero]
  rw [insert_comm q p R]
  ring

private lemma mixed_overlap_bound (M : ℕ) (P : Finset ℕ) (hP : ∀ r∈P,r.Prime)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) :
    |mixedOverlap M P p q|≤(9/25:ℝ)*4^(P.card-1)*(M:ℝ)*
      (((M-1)/(p*q):ℕ)+((M-1)/max p q:ℕ)) := by
  let T := (((mobiusDivisorSelectionPrimes M).erase q).erase p).powerset
  let H := (3/5:ℝ)*2^(P.card-1)*Real.sqrt M
  let f := mobiusDivisorSelectionFibre M P
  have hprime (R : Finset ℕ) (hR : R∈T) : ∀ r∈R,r.Prime := by
    intro r hr
    exact (mem_filter.mp (mem_erase.mp (mem_erase.mp (mem_powerset.mp hR hr)).2).2).2
  have hpR (R : Finset ℕ) (hR : R∈T) : p∉R := by
    intro h
    exact (mem_erase.mp (mem_powerset.mp hR h)).1 rfl
  have hqR (R : Finset ℕ) (hR : R∈T) : q∉R := by
    intro h
    exact (mem_erase.mp (mem_erase.mp (mem_powerset.mp hR h)).2).1 rfl
  have ha (R : Finset ℕ) (hR : R∈T) : |f R|≤H :=
    abs_mobiusDivisorSelectionFibre_le_source_amplitude M P R hP (hprime R hR)
  have hb (R : Finset ℕ) (hR : R∈T) : |f (insert p R)|≤H :=
    abs_mobiusDivisorSelectionFibre_le_source_amplitude M P _ hP
      (by simpa using And.intro hp (hprime R hR))
  have hc (R : Finset ℕ) (hR : R∈T) : |f (insert q R)|≤H :=
    abs_mobiusDivisorSelectionFibre_le_source_amplitude M P _ hP
      (by simpa using And.intro hq (hprime R hR))
  have hd (R : Finset ℕ) (hR : R∈T) : |f (insert p (insert q R))|≤H :=
    abs_mobiusDivisorSelectionFibre_le_source_amplitude M P _ hP
      (by simpa using And.intro hp (And.intro hq (hprime R hR)))
  have hzd (R : Finset ℕ) (hR : R∈T) (hn : (M-1)/(p*q)<∏ r∈R,r) :
      f R*f (insert p (insert q R))=0 := by
    have hmul := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hp.pos hq.pos)).mp hn
    have hcut : M≤∏ r∈insert p (insert q R),r := by
      rw [prod_insert (by simp [hpq,hpR R hR]),prod_insert (hqR R hR)]
      have hmul' : M-1<p*(q*∏ r∈R,r) := by
        simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hmul
      omega
    have hz := mobiusDivisorSelectionFibre_eq_zero_of_le_product M P _ hcut
    change _*mobiusDivisorSelectionFibre M P _=0
    rw [hz,mul_zero]
  have hzbc (R : Finset ℕ) (hR : R∈T) (hn : (M-1)/max p q<∏ r∈R,r) :
      f (insert p R)*f (insert q R)=0 := by
    rcases le_total p q with hpq' | hqp'
    · rw [max_eq_right hpq'] at hn
      have hmul := (Nat.div_lt_iff_lt_mul hq.pos).mp hn
      rw [Nat.mul_comm] at hmul
      have hcut : M≤∏ r∈insert q R,r := by rw [prod_insert (hqR R hR)]; omega
      have hz := mobiusDivisorSelectionFibre_eq_zero_of_le_product M P _ hcut
      change _*mobiusDivisorSelectionFibre M P _=0
      rw [hz,mul_zero]
    · rw [max_eq_left hqp'] at hn
      have hmul := (Nat.div_lt_iff_lt_mul hp.pos).mp hn
      rw [Nat.mul_comm] at hmul
      have hcut : M≤∏ r∈insert p R,r := by rw [prod_insert (hpR R hR)]; omega
      have hz := mobiusDivisorSelectionFibre_eq_zero_of_le_product M P _ hcut
      change mobiusDivisorSelectionFibre M P _*_=0
      rw [hz,zero_mul]
  have h1 := sum_abs_product_bound T ((M-1)/(p*q)) hprime f
    (fun R => f (insert p (insert q R))) H ha hd hzd
  have h2 := sum_abs_product_bound T ((M-1)/max p q) hprime
    (fun R => f (insert p R)) (fun R => f (insert q R)) H hb hc hzbc
  change |∑ R∈T,(f R*f (insert p (insert q R))+f (insert p R)*f (insert q R))|≤_
  calc
    _ ≤ ∑ R∈T,|f R*f (insert p (insert q R))+f (insert p R)*f (insert q R)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ R∈T,(|f R*f (insert p (insert q R))|+|f (insert p R)*f (insert q R)|) :=
      sum_le_sum (fun R _ => abs_add_le _ _)
    _ = (∑ R∈T,|f R*f (insert p (insert q R))|)+
        ∑ R∈T,|f (insert p R)*f (insert q R)| := sum_add_distrib
    _ ≤ (((M-1)/(p*q):ℕ):ℝ)*H^2+(((M-1)/max p q:ℕ):ℝ)*H^2 := add_le_add h1 h2
    _ = _ := by dsimp [H]; rw [source_amplitude_square]; ring

/-- The exact mixed second energy difference has separate joint-child and
cross-child support costs, uniformly over every already mixed prime field. -/
theorem abs_mobiusDivisorSelectionEnergy_mixed_le_source_support
    (M : ℕ) (P : Finset ℕ) (hP : ∀ r∈P,r.Prime)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpM : p<M) (hqM : q<M)
    (hpP : p∉P) (hqP : q∉P) (hpq : p≠q) :
    |mobiusDivisorSelectionEnergy M (insert q (insert p P))-
      mobiusDivisorSelectionEnergy M (insert p P)-
      mobiusDivisorSelectionEnergy M (insert q P)+mobiusDivisorSelectionEnergy M P|≤
        (18/25:ℝ)*4^(P.card-1)*(M:ℝ)*
          (((M-1)/(p*q):ℕ)+((M-1)/max p q:ℕ)) := by
  rw [mixed_identity M P hp hq hpM hqM hpP hqP hpq,abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h := mixed_overlap_bound M P hP hp hq hpq
  linarith only [h]

/-- Widely separated first primes meet the original diagonal uniformly in the
cutoff: the smaller prime's actual reserve pays the larger prime's localized gain. -/
theorem exists_mobiusDivisor_two_prime_separation_ceiling :
    ∃ D : ℝ, 1<D ∧ ∃ T : ℕ, 1≤T ∧ ∀ M p q : ℕ,
      p.Prime → q.Prime → p<M → D*(q:ℝ)≤(p:ℝ) → T≤M/q →
      mobiusDivisorSelectionEnergy M (insert p {q})≤ mobiusDivisorSelectionEnergy M ∅ := by
  obtain ⟨c,hc,T,hT,hreserve⟩ := exists_mobiusDivisorSelectionEnergy_first_prime_reserve
  have hD : (1:ℝ)<2+1/c := by have := one_div_pos.mpr hc; linarith
  refine ⟨2+1/c,hD,T,hT,?_⟩
  intro M p q hp hq hpM hpq hquot
  have hq0 : (0:ℝ)<q := by exact_mod_cast hq.pos
  have hM0 : (0:ℝ)≤M := Nat.cast_nonneg M
  have hpq' : q<p := by
    have h := mul_lt_mul_of_pos_right hD hq0
    have hr : (q:ℝ)<p := by linarith only [h,hpq]
    exact_mod_cast hr
  have hpqne : p≠q := (Nat.ne_of_lt hpq').symm
  have hqp : (q:ℝ)≤c*(p:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hpq hc.le
    have he : c*((2+1/c)*(q:ℝ))=(2*c+1)*(q:ℝ) := by field_simp [hc.ne']
    rw [he] at h
    nlinarith only [h,mul_nonneg hc.le hq0.le]
  let N := (M-1)/p
  have hN0 : (0:ℝ)≤N := Nat.cast_nonneg N
  have hNM : (N:ℝ)*(p:ℝ)≤M := by
    exact_mod_cast ((Nat.div_mul_le_self (M-1) p).trans (Nat.sub_le M 1))
  have hNq : (N:ℝ)*(q:ℝ)≤c*(M:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hqp hN0
    have h2 := mul_le_mul_of_nonneg_left hNM hc.le
    nlinarith only [h1,h2]
  have hpay : (M:ℝ)*(N:ℝ)≤c*(M:ℝ)^2/(q:ℝ) := by
    apply (le_div_iff₀ hq0).mpr
    have h := mul_le_mul_of_nonneg_left hNq hM0
    nlinarith only [h]
  have hgain := (abs_le.mp (abs_mobiusDivisorSelectionEnergy_insert_le_source_support M {q}
    (by simpa using hq) hp hpM (by simpa using hpqne))).2
  simp only [card_singleton,Nat.sub_self,pow_zero,mul_one] at hgain
  have hrelease := hreserve M q hq hquot
  change _≤(18/25:ℝ)*(M:ℝ)*(N:ℝ) at hgain
  have hMN0 := mul_nonneg hM0 hN0
  linarith only [hgain,hpay,hrelease,hMN0]

end RHTower
