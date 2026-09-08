import GaloisForLFunctions.RHTower.DivisorTwentyTwoAnalyticBounds
import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreHomothety
import GaloisForLFunctions.RHTower.MobiusDivisorPrimeSeparation
/-!
# Successor averaging fails while a separated prime preserves admission

At cutoff 22 and processed core {3,7,11,17,19}, the literal signed source
has five retained coordinates. Analytic bounds certify an admitted state
whose uniform average of successor envelopes exceeds its original budget.
Prime two is the unique least-energy choice and remains contracting after
every subset of the other mergers, so its successor is still admitted.

Every source coordinate and available alternative is retained. Numerical
experiments supply no premise. Neither exact successor extension nor its
least-energy version is proved or refuted at arbitrary cutoffs here.
-/
noncomputable section
open Finset
namespace RHTower
private def witnessCore : Finset ℕ := {3,7,11,17,19}
private def a : ℝ := divisorUnsignedDilationChannel 22 1-divisorUnsignedDilationChannel 22 3-
  divisorUnsignedDilationChannel 22 7-divisorUnsignedDilationChannel 22 11-
  divisorUnsignedDilationChannel 22 17-divisorUnsignedDilationChannel 22 19+
  divisorUnsignedDilationChannel 22 21
private def b : ℝ := -divisorUnsignedDilationChannel 22 2+
  divisorUnsignedDilationChannel 22 6+divisorUnsignedDilationChannel 22 14
private def c : ℝ := -divisorUnsignedDilationChannel 22 5+divisorUnsignedDilationChannel 22 15
private def d : ℝ := divisorUnsignedDilationChannel 22 10
private def e : ℝ := -divisorUnsignedDilationChannel 22 13
private lemma boxes : (-0.480≤a ∧ a≤-0.479) ∧ (0.182≤b ∧ b≤0.183) ∧
    (-0.127≤c ∧ c≤-0.126) ∧ (0.202≤d ∧ d≤0.203) ∧ (-0.168≤e ∧ e≤-0.167) :=
  divisorUnsignedDilationChannel_twentyTwo_profile_boxes

private def profile (a b c d e : ℝ) (R : Finset ℕ) : ℝ :=
  (if R=∅ then a else 0)+(if R={2} then b else 0)+(if R={5} then c else 0)+
    (if R={2,5} then d else 0)+(if R={13} then e else 0)

private lemma signed_prime (p : ℕ) (hp : p.Prime) :
    mobiusDivisorDilationChannel 22 p = -divisorUnsignedDilationChannel 22 p := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,ArithmeticFunction.moebius_apply_prime hp]
  norm_num
private lemma signed_pair (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    mobiusDivisorDilationChannel 22 (p*q) = divisorUnsignedDilationChannel 22 (p*q) := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hp.coprime_iff_not_dvd.mpr
      (fun h => hne ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one))),
    ArithmeticFunction.moebius_apply_prime hp,ArithmeticFunction.moebius_apply_prime hq]
  norm_num
private lemma factors_pair (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (p*q).primeFactors=({p,q}:Finset ℕ) := by
  rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero,hp.primeFactors,hq.primeFactors]
  simp
private lemma square_zero (n p : ℕ) (hp : 1<p) (hd : p*p∣n) :
    mobiusDivisorDilationChannel 22 n=0 := by
  have hn : ¬Squarefree n := by
    intro h
    have he : p=1 := Nat.isUnit_iff.mp (h p hd)
    omega
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  norm_num
private lemma terminal_zero : mobiusDivisorDilationChannel 22 22=0 := by
  simp [mobiusDivisorDilationChannel]

set_option maxHeartbeats 800000 in
private lemma source_profile (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 22 witnessCore R=profile a b c d e R := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  have hp17 : Nat.Prime 17 := by norm_num
  have hp19 : Nat.Prime 19 := by norm_num
  have z4 := square_zero 4 2 (by omega) (by norm_num)
  have z8 := square_zero 8 2 (by omega) (by norm_num)
  have z9 := square_zero 9 3 (by omega) (by norm_num)
  have z12 := square_zero 12 2 (by omega) (by norm_num)
  have z16 := square_zero 16 2 (by omega) (by norm_num)
  have z18 := square_zero 18 3 (by omega) (by norm_num)
  have z20 := square_zero 20 2 (by omega) (by norm_num)
  have f6 := factors_pair 2 3 Nat.prime_two Nat.prime_three
  have f10 := factors_pair 2 5 Nat.prime_two Nat.prime_five
  have f14 := factors_pair 2 7 Nat.prime_two hp7
  have f15 := factors_pair 3 5 Nat.prime_three Nat.prime_five
  have f21 := factors_pair 3 7 Nat.prime_three hp7
  have s6 := signed_pair 2 3 Nat.prime_two Nat.prime_three (by omega)
  have s10 := signed_pair 2 5 Nat.prime_two Nat.prime_five (by omega)
  have s14 := signed_pair 2 7 Nat.prime_two hp7 (by omega)
  have s15 := signed_pair 3 5 Nat.prime_three Nat.prime_five (by omega)
  have s21 := signed_pair 3 7 Nat.prime_three hp7 (by omega)
  norm_num only at f6 f10 f14 f15 f21 s6 s10 s14 s15 s21
  have s1 : mobiusDivisorDilationChannel 22 1=divisorUnsignedDilationChannel 22 1 := by
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned]; norm_num
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
  norm_num [Finset.sum_Icc_succ_top,z4,z8,z9,z12,z16,z18,z20,terminal_zero,
    Nat.prime_two.primeFactors,Nat.prime_three.primeFactors,Nat.prime_five.primeFactors,
    hp7.primeFactors,hp11.primeFactors,hp13.primeFactors,hp17.primeFactors,hp19.primeFactors,
    f6,f10,f14,f15,f21,witnessCore,Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton]
  simp only [s1,s6,s10,s14,s15,s21,signed_prime 2 Nat.prime_two,
    signed_prime 3 Nat.prime_three,signed_prime 5 Nat.prime_five,signed_prime 7 hp7,
    signed_prime 11 hp11,signed_prime 13 hp13,signed_prime 17 hp17,signed_prime 19 hp19]
  have hn0 : ({2,5}:Finset ℕ)≠∅ := by
    intro he; have ht := (Finset.ext_iff.mp he) 2; norm_num at ht
  have hn2 : ({2,5}:Finset ℕ)≠{2} := by
    intro he; have ht := (Finset.ext_iff.mp he) 5; norm_num at ht
  have hn5 : ({2,5}:Finset ℕ)≠{5} := by
    intro he; have ht := (Finset.ext_iff.mp he) 2; norm_num at ht
  have hn13 : ({2,5}:Finset ℕ)≠{13} := by
    intro he; have ht := (Finset.ext_iff.mp he) 2; norm_num at ht
  by_cases h0 : R=∅
  · subst R; simp [profile,a,hn0,Ne.symm hn0]; ring
  by_cases h2 : R={2}
  · subst R; simp [profile,b,hn2,Ne.symm hn2]
  by_cases h5 : R={5}
  · subst R; simp [profile,c,hn5,Ne.symm hn5]
  by_cases h25 : R={2,5}
  · subst R; simp [profile,d,hn0,hn2,hn5,hn13,Ne.symm hn0,Ne.symm hn2,Ne.symm hn5,Ne.symm hn13]
  by_cases h13 : R={13}
  · subst R; simp [profile,e,hn13,Ne.symm hn13]
  simp [profile,h0,h2,h5,h25,h13,Ne.symm h0,Ne.symm h2,Ne.symm h5,Ne.symm h25,Ne.symm h13]
private lemma energy_profile {P : Finset ℕ} {A B C D E : ℝ}
    (hf : ∀ R,mobiusDivisorSelectionFibre 22 P R=profile A B C D E R) :
    mobiusDivisorSelectionEnergy 22 P=A^2+B^2+C^2+D^2+E^2 := by
  let L : Finset (Finset ℕ) := {∅,{2},{5},{2,5},{13}}
  have hs : L ⊆ (mobiusDivisorSelectionPrimes 22).powerset := by
    intro R hR
    simp only [L,mem_insert,mem_singleton] at hR
    rcases hR with rfl|rfl|rfl|rfl|rfl
    all_goals norm_num [mem_powerset,insert_subset_iff,singleton_subset_iff,mobiusDivisorSelectionPrimes]
  have hzero (R : Finset ℕ) (_hR : R∈(mobiusDivisorSelectionPrimes 22).powerset) (hn : R∉L) :
      (mobiusDivisorSelectionFibre 22 P R)^2=0 := by
    have h0 : R≠∅ := fun he => hn (by simp [L,he])
    have h2 : R≠{2} := fun he => hn (by simp [L,he])
    have h5 : R≠{5} := fun he => hn (by simp [L,he])
    have h25 : R≠{2,5} := fun he => hn (by simp [L,he])
    have h13 : R≠{13} := fun he => hn (by simp [L,he])
    simp [hf,profile,h0,h2,h5,h25,h13]
  have he := sum_subset (f:=fun R => (mobiusDivisorSelectionFibre 22 P R)^2) hs hzero
  change (∑ R∈(mobiusDivisorSelectionPrimes 22).powerset,
    (mobiusDivisorSelectionFibre 22 P R)^2)=_
  rw [← he]
  simp_rw [hf]
  have hn0 : ({2,5}:Finset ℕ)≠∅ := by
    intro he; have ht := (Finset.ext_iff.mp he) 2; norm_num at ht
  have hn2 : ({2,5}:Finset ℕ)≠{2} := by
    intro he; have ht := (Finset.ext_iff.mp he) 5; norm_num at ht
  have hn5 : ({2,5}:Finset ℕ)≠{5} := by
    intro he; have ht := (Finset.ext_iff.mp he) 2; norm_num at ht
  have hn13 : ({2,5}:Finset ℕ)≠{13} := by
    intro he; have ht := (Finset.ext_iff.mp he) 2; norm_num at ht
  simp [L,profile,hn0,hn2,hn5,hn13,Ne.symm hn0,Ne.symm hn2,Ne.symm hn5,Ne.symm hn13]
  ring

/-- The actual mixed cutoff-twenty-two source separates its entire field
by membership of prime two, including the live overlapping pair. -/
theorem mobiusDivisorPrimeSeparated_twentyTwo :
    MobiusDivisorPrimeSeparated 22 {3,7,11,17,19} 2 := by
  change MobiusDivisorPrimeSeparated 22 witnessCore 2
  intro R
  rw [source_profile]
  obtain ⟨ha,hb,hc,hd,he⟩ := boxes
  constructor
  · intro hpR
    have hn2 : R≠{2} := by rintro rfl; simp at hpR
    have hn25 : R≠{2,5} := by rintro rfl; simp at hpR
    simp only [profile,hn2,hn25,if_false,add_zero]
    split_ifs <;> linarith only [ha.2,hc.2,he.2]
  · intro hpR
    have hn0 : R≠∅ := by rintro rfl; simp at hpR
    have hn5 : R≠{5} := by rintro rfl; norm_num at hpR
    have hn13 : R≠{13} := by rintro rfl; norm_num at hpR
    simp only [profile,hn0,hn5,hn13,if_false,zero_add,add_zero]
    split_ifs <;> linarith only [hb.1,hd.1]

/-- Prime two contracts the actual energy after every additional subset of
other labels at this mixed state, without a reserve or parity premise. -/
theorem mobiusDivisorSelectionEnergy_twentyTwo_two_persistently_contracts
    (T : Finset ℕ) (hT : 2∉T) :
    mobiusDivisorSelectionEnergy 22 (insert 2 ({3,7,11,17,19}∪T)) ≤
      mobiusDivisorSelectionEnergy 22 ({3,7,11,17,19}∪T) :=
  mobiusDivisorSelectionEnergy_insert_le_of_separated Nat.prime_two (by omega)
    (by norm_num) mobiusDivisorPrimeSeparated_twentyTwo T hT
private lemma initial_energy :
    mobiusDivisorSelectionEnergy 22 ∅ =
      ∑ n∈({1,2,3,5,6,7,10,11,13,14,15,17,19,21}:Finset ℕ),
        (divisorUnsignedDilationChannel 22 n)^2 := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  have hp17 : Nat.Prime 17 := by norm_num
  have hp19 : Nat.Prime 19 := by norm_num
  have z4 := square_zero 4 2 (by omega) (by norm_num)
  have z8 := square_zero 8 2 (by omega) (by norm_num)
  have z9 := square_zero 9 3 (by omega) (by norm_num)
  have z12 := square_zero 12 2 (by omega) (by norm_num)
  have z16 := square_zero 16 2 (by omega) (by norm_num)
  have z18 := square_zero 18 3 (by omega) (by norm_num)
  have z20 := square_zero 20 2 (by omega) (by norm_num)
  have s6 := signed_pair 2 3 Nat.prime_two Nat.prime_three (by omega)
  have s10 := signed_pair 2 5 Nat.prime_two Nat.prime_five (by omega)
  have s14 := signed_pair 2 7 Nat.prime_two hp7 (by omega)
  have s15 := signed_pair 3 5 Nat.prime_three Nat.prime_five (by omega)
  have s21 := signed_pair 3 7 Nat.prime_three hp7 (by omega)
  norm_num only at s6 s10 s14 s15 s21
  have s1 : mobiusDivisorDilationChannel 22 1=divisorUnsignedDilationChannel 22 1 := by
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned]; norm_num
  rw [mobiusDivisorSelectionEnergy_empty]
  norm_num [Finset.sum_Icc_succ_top,z4,z8,z9,z12,z16,z18,z20,terminal_zero,
    s1,s6,s10,s14,s15,s21,signed_prime 2 Nat.prime_two,
    signed_prime 3 Nat.prime_three,signed_prime 5 Nat.prime_five,signed_prime 7 hp7,
    signed_prime 11 hp11,signed_prime 13 hp13,signed_prime 17 hp17,signed_prime 19 hp19]
  ring
private lemma budget_box : (0.550:ℝ) ≤ mobiusDivisorSelectionEnergy 22 ∅ ∧
    mobiusDivisorSelectionEnergy 22 ∅ ≤ 0.553 := by
  rw [initial_energy]
  exact sum_divisorUnsignedDilationChannel_twentyTwo_sq_bounds

private lemma profile_zero {R : Finset ℕ} (hR : ¬R⊆{2,5,13}) (A B C D E : ℝ) :
    profile A B C D E R=0 := by
  have h0 : R≠∅ := by rintro rfl; exact hR (by simp)
  have h2 : R≠{2} := by rintro rfl; exact hR (by simp)
  have h5 : R≠{5} := by rintro rfl; exact hR (by simp)
  have h25 : R≠{2,5} := by rintro rfl; exact hR (by simp)
  have h13 : R≠{13} := by rintro rfl; exact hR (by simp)
  simp [profile,h0,h2,h5,h25,h13]

set_option maxHeartbeats 800000 in
private lemma profile_mergers (A B C D E : ℝ) (R : Finset ℕ) :
    (if 2∈R then 0 else profile A B C D E R+profile A B C D E (insert 2 R))=
      profile (A+B) 0 (C+D) 0 E R ∧
    (if 5∈R then 0 else profile A B C D E R+profile A B C D E (insert 5 R))=
      profile (A+C) (B+D) 0 0 E R ∧
    (if 13∈R then 0 else profile A B C D E R+profile A B C D E (insert 13 R))=
      profile (A+E) B C D 0 R := by
  by_cases hR : R⊆{2,5,13}
  · have hm := mem_powerset.mpr hR
    norm_num [Finset.powerset_insert,Finset.image_union,Finset.image_insert] at hm
    simp only [or_assoc] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [profile,Finset.ext_iff,iff_def,or_imp,forall_and]
  · have hn (q : ℕ) : ¬insert q R⊆{2,5,13} :=
      fun h => hR ((subset_insert q R).trans h)
    simp only [profile_zero hR,profile_zero (hn 2),profile_zero (hn 5),profile_zero (hn 13),add_zero,ite_self]
    simp
private lemma profile_two (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 22 (insert 2 witnessCore) R=profile (a+b) 0 (c+d) 0 e R := by
  rw [mobiusDivisorSelectionFibre_insert,source_profile,source_profile]
  exact (profile_mergers a b c d e R).1
private lemma profile_five (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 22 (insert 5 witnessCore) R=profile (a+c) (b+d) 0 0 e R := by
  rw [mobiusDivisorSelectionFibre_insert,source_profile,source_profile]
  exact (profile_mergers a b c d e R).2.1
private lemma profile_thirteen (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 22 (insert 13 witnessCore) R=profile (a+e) b c d 0 R := by
  rw [mobiusDivisorSelectionFibre_insert,source_profile,source_profile]
  exact (profile_mergers a b c d e R).2.2
private lemma profile_two_thirteen (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 22 (insert 13 (insert 2 witnessCore)) R=
      profile (a+b+e) 0 (c+d) 0 0 R := by
  rw [mobiusDivisorSelectionFibre_insert,profile_two,profile_two]
  exact (profile_mergers (a+b) 0 (c+d) 0 e R).2.2
private lemma profile_five_thirteen (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 22 (insert 13 (insert 5 witnessCore)) R=
      profile (a+c+e) (b+d) 0 0 0 R := by
  rw [mobiusDivisorSelectionFibre_insert,profile_five,profile_five]
  exact (profile_mergers (a+c) (b+d) 0 0 e R).2.2

private lemma energy_formulas :
    mobiusDivisorSelectionEnergy 22 witnessCore=a^2+b^2+c^2+d^2+e^2 ∧
    mobiusDivisorSelectionEnergy 22 (insert 2 witnessCore)=(a+b)^2+(c+d)^2+e^2 ∧
    mobiusDivisorSelectionEnergy 22 (insert 5 witnessCore)=(a+c)^2+(b+d)^2+e^2 ∧
    mobiusDivisorSelectionEnergy 22 (insert 13 witnessCore)=(a+e)^2+b^2+c^2+d^2 ∧
    mobiusDivisorSelectionEnergy 22 (insert 13 (insert 2 witnessCore))=(a+b+e)^2+(c+d)^2 ∧
    mobiusDivisorSelectionEnergy 22 (insert 13 (insert 5 witnessCore))=(a+c+e)^2+(b+d)^2 := by
  exact ⟨energy_profile source_profile,by simpa using energy_profile profile_two,
    by simpa using energy_profile profile_five,by simpa using energy_profile profile_thirteen,
    by simpa using energy_profile profile_two_thirteen,by simpa using energy_profile profile_five_thirteen⟩

private lemma square_box {x l u : ℝ} (hl : 0≤l) (h : l≤x ∧ x≤u) :
    l^2≤x^2 ∧ x^2≤u^2 := by
  have hx := hl.trans h.1
  constructor
  · simpa only [pow_two] using mul_le_mul h.1 h.1 hl hx
  · simpa only [pow_two] using mul_le_mul h.2 h.2 hx (hx.trans h.2)

set_option maxHeartbeats 1000000 in
private lemma energy_bounds :
    mobiusDivisorSelectionEnergy 22 witnessCore≤0.546 ∧
    mobiusDivisorSelectionEnergy 22 (insert 2 witnessCore)≤0.123 ∧
    0.540≤ mobiusDivisorSelectionEnergy 22 (insert 5 witnessCore) ∧
    mobiusDivisorSelectionEnergy 22 (insert 5 witnessCore)≤0.546 ∧
    0.505≤ mobiusDivisorSelectionEnergy 22 (insert 13 witnessCore) ∧
    mobiusDivisorSelectionEnergy 22 (insert 13 witnessCore)≤0.546 ∧
    0.219≤ mobiusDivisorSelectionEnergy 22 (insert 13 (insert 2 witnessCore)) ∧
    0.743≤ mobiusDivisorSelectionEnergy 22 (insert 13 (insert 5 witnessCore)) := by
  obtain ⟨ha,hb,hc,hd,he⟩ := boxes
  have sa := square_box (x:=-a) (l:=0.479) (u:=0.480) (by norm_num) ⟨by linarith,by linarith⟩
  have sb := square_box (by norm_num : (0:ℝ)≤0.182) hb
  have sc := square_box (x:=-c) (l:=0.126) (u:=0.127) (by norm_num) ⟨by linarith,by linarith⟩
  have sd := square_box (by norm_num : (0:ℝ)≤0.202) hd
  have se := square_box (x:=-e) (l:=0.167) (u:=0.168) (by norm_num) ⟨by linarith,by linarith⟩
  have sab := square_box (x:=-(a+b)) (l:=0.296) (u:=0.298) (by norm_num) ⟨by linarith,by linarith⟩
  have scd := square_box (x:=c+d) (l:=0.075) (u:=0.077) (by norm_num) ⟨by linarith,by linarith⟩
  have sac := square_box (x:=-(a+c)) (l:=0.605) (u:=0.607) (by norm_num) ⟨by linarith,by linarith⟩
  have sbd := square_box (x:=b+d) (l:=0.384) (u:=0.386) (by norm_num) ⟨by linarith,by linarith⟩
  have sae := square_box (x:=-(a+e)) (l:=0.646) (u:=0.648) (by norm_num) ⟨by linarith,by linarith⟩
  have sabe := square_box (x:=-(a+b+e)) (l:=0.463) (u:=0.466) (by norm_num) ⟨by linarith,by linarith⟩
  have sace := square_box (x:=-(a+c+e)) (l:=0.772) (u:=0.775) (by norm_num) ⟨by linarith,by linarith⟩
  simp only [neg_sq] at sa sc se sab sac sae sabe sace
  obtain ⟨f0,f2,f5,f13,f213,f513⟩ := energy_formulas
  rw [f0,f2,f5,f13,f213,f513]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    nlinarith only [sa.1,sa.2,sb.1,sb.2,sc.1,sc.2,sd.1,sd.2,se.1,se.2,
      sab.1,sab.2,scd.1,scd.2,sac.1,sac.2,sbd.1,sbd.2,sae.1,sae.2,sabe.1,sabe.2,sace.1,sace.2]
/-- Current energy together with every available immediate successor. -/
noncomputable def mobiusDivisorSuccessorEnvelope (M : ℕ) (P : Finset ℕ) : ℝ :=
  (insert P (((mobiusDivisorSelectionPrimes M) \ P).image (fun p => insert p P))).sup'
    (by simp) (mobiusDivisorSelectionEnergy M)

/-- Exact admission retains the current energy and every available prime. -/
theorem mobiusDivisorSuccessorEnvelope_le_iff (M : ℕ) (P : Finset ℕ) (B : ℝ) :
    mobiusDivisorSuccessorEnvelope M P ≤ B ↔
      mobiusDivisorSelectionEnergy M P ≤ B ∧
      ∀ p ∈ mobiusDivisorSelectionPrimes M \ P,
        mobiusDivisorSelectionEnergy M (insert p P) ≤ B := by
  unfold mobiusDivisorSuccessorEnvelope
  rw [Finset.sup'_le_iff]
  constructor
  · intro h
    exact ⟨h P (mem_insert_self _ _), fun p hp =>
      h (insert p P) (mem_insert_of_mem (mem_image.mpr ⟨p,hp,rfl⟩))⟩
  · rintro ⟨h0,hs⟩ S hS
    rcases mem_insert.mp hS with rfl|hS
    · exact h0
    · obtain ⟨p,hp,rfl⟩ := mem_image.mp hS
      exact hs p hp

private lemma successor_le_envelope {M p : ℕ} {P : Finset ℕ}
    (hp : p ∈ mobiusDivisorSelectionPrimes M \ P) :
    mobiusDivisorSelectionEnergy M (insert p P) ≤ mobiusDivisorSuccessorEnvelope M P :=
  ((mobiusDivisorSuccessorEnvelope_le_iff M P _).mp le_rfl).2 p hp

private lemma available : mobiusDivisorSelectionPrimes 22 \ witnessCore = {2,5,13} := by
  norm_num [mobiusDivisorSelectionPrimes, witnessCore, Finset.range_add_one,
    Finset.filter_insert, Finset.filter_singleton, Finset.sdiff_eq_filter, Finset.insert_comm]

/-- The actual counterexample starts strictly inside its original budget. -/
theorem mobiusDivisorSuccessorEnvelope_twentyTwo_admitted :
    mobiusDivisorSuccessorEnvelope 22 {3,7,11,17,19} + 1/250 ≤
      mobiusDivisorSelectionEnergy 22 ∅ := by
  change mobiusDivisorSuccessorEnvelope 22 witnessCore + 1/250 ≤ _
  obtain ⟨h0,h2,_,h5,_,h13,_,_⟩ := energy_bounds
  have henv : mobiusDivisorSuccessorEnvelope 22 witnessCore ≤ 0.546 := by
    rw [mobiusDivisorSuccessorEnvelope_le_iff, available]
    refine ⟨h0,?_⟩
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl|rfl|rfl
    · linarith
    · exact h5
    · exact h13
  linarith only [henv,budget_box.1]

/-- Prime two is the unique least-energy available choice at this source. -/
theorem mobiusDivisorSelectionEnergy_twentyTwo_two_unique_minimum :
    ∀ p ∈ mobiusDivisorSelectionPrimes 22 \ {3,7,11,17,19}, p ≠ 2 →
      mobiusDivisorSelectionEnergy 22 (insert 2 {3,7,11,17,19}) <
        mobiusDivisorSelectionEnergy 22 (insert p {3,7,11,17,19}) := by
  change ∀ p ∈ mobiusDivisorSelectionPrimes 22 \ witnessCore, p ≠ 2 → _
  rw [available]
  obtain ⟨_,h2,h5,_,h13,_,_,_⟩ := energy_bounds
  intro p hp hn
  simp only [mem_insert,mem_singleton] at hp
  rcases hp with rfl|rfl|rfl
  · exact (hn rfl).elim
  · change mobiusDivisorSelectionEnergy 22 (insert 2 witnessCore) <
      mobiusDivisorSelectionEnergy 22 (insert 5 witnessCore)
    linarith
  · change mobiusDivisorSelectionEnergy 22 (insert 2 witnessCore) <
      mobiusDivisorSelectionEnergy 22 (insert 13 witnessCore)
    linarith

/-- Hereditary separation preserves admission at the least-energy choice. -/
theorem mobiusDivisorSuccessorEnvelope_twentyTwo_two_admitted :
    mobiusDivisorSuccessorEnvelope 22 (insert 2 {3,7,11,17,19}) ≤
      mobiusDivisorSelectionEnergy 22 ∅ := by
  have hbase : mobiusDivisorSuccessorEnvelope 22 {3,7,11,17,19} ≤
      mobiusDivisorSelectionEnergy 22 ∅ := by
    linarith only [mobiusDivisorSuccessorEnvelope_twentyTwo_admitted]
  obtain ⟨h0,hnext⟩ := (mobiusDivisorSuccessorEnvelope_le_iff _ _ _).mp hbase
  rw [mobiusDivisorSuccessorEnvelope_le_iff]
  constructor
  · apply hnext 2
    change 2 ∈ mobiusDivisorSelectionPrimes 22 \ witnessCore
    rw [available]
    simp
  · intro q hq
    obtain ⟨hqprime,hqnot⟩ := mem_sdiff.mp hq
    have hq2 : q ≠ 2 := by intro heq; subst q; simp at hqnot
    have hqP : q ∉ ({3,7,11,17,19} : Finset ℕ) :=
      fun h => hqnot (mem_insert_of_mem h)
    have hc := mobiusDivisorSelectionEnergy_twentyTwo_two_persistently_contracts
      {q} (by simpa using Ne.symm hq2)
    have hqbase := hnext q (mem_sdiff.mpr ⟨hqprime,hqP⟩)
    rw [Finset.union_singleton, Finset.insert_comm 2 q] at hc
    exact hc.trans hqbase

set_option maxHeartbeats 800000 in
/-- Uniform successor averaging fails by a fixed rational margin at a
literal admitted source, despite its admissible least-energy successor. -/
theorem mobiusDivisorSuccessorEnvelope_twentyTwo_average_exceeds :
    mobiusDivisorSelectionEnergy 22 ∅ + 1/75 <
      (∑ p ∈ mobiusDivisorSelectionPrimes 22 \ {3,7,11,17,19},
        mobiusDivisorSuccessorEnvelope 22 (insert p {3,7,11,17,19})) /
        ((mobiusDivisorSelectionPrimes 22 \ {3,7,11,17,19}).card : ℝ) := by
  change mobiusDivisorSelectionEnergy 22 ∅ + 1/75 <
    (∑ p ∈ mobiusDivisorSelectionPrimes 22 \ witnessCore,
      mobiusDivisorSuccessorEnvelope 22 (insert p witnessCore)) /
      ((mobiusDivisorSelectionPrimes 22 \ witnessCore).card : ℝ)
  have h132 : 13 ∈ mobiusDivisorSelectionPrimes 22 \ insert 2 witnessCore := by
    norm_num [mobiusDivisorSelectionPrimes,witnessCore]
  have h135 : 13 ∈ mobiusDivisorSelectionPrimes 22 \ insert 5 witnessCore := by
    norm_num [mobiusDivisorSelectionPrimes,witnessCore]
  have h513 : 5 ∈ mobiusDivisorSelectionPrimes 22 \ insert 13 witnessCore := by
    norm_num [mobiusDivisorSelectionPrimes,witnessCore]
  have h2 := successor_le_envelope h132
  have h5 := successor_le_envelope h135
  have h13 := successor_le_envelope h513
  rw [Finset.insert_comm 5 13] at h13
  obtain ⟨_,_,_,_,_,_,l2,l5⟩ := energy_bounds
  rw [available]
  norm_num
  linarith only [h2,h5,h13,l2,l5,budget_box.2]
set_option maxHeartbeats 800000 in
/-- The unconditional uniform-average admission law is false for the actual
signed divisor source. The original energy budget and all alternatives remain. -/
theorem not_mobiusDivisorSuccessorEnvelope_average_law :
    ¬ (∀ (M : ℕ) (P : Finset ℕ), P ⊆ mobiusDivisorSelectionPrimes M →
      (mobiusDivisorSelectionPrimes M \ P).Nonempty →
      mobiusDivisorSuccessorEnvelope M P ≤ mobiusDivisorSelectionEnergy M ∅ →
      (∑ p ∈ mobiusDivisorSelectionPrimes M \ P,
        mobiusDivisorSuccessorEnvelope M (insert p P)) /
        ((mobiusDivisorSelectionPrimes M \ P).card : ℝ) ≤ mobiusDivisorSelectionEnergy M ∅) := by
  intro h
  have hP : ({3,7,11,17,19} : Finset ℕ) ⊆ mobiusDivisorSelectionPrimes 22 := by
    norm_num [mobiusDivisorSelectionPrimes,Finset.insert_subset_iff]
  have hn : (mobiusDivisorSelectionPrimes 22 \ {3,7,11,17,19}).Nonempty := by
    change (mobiusDivisorSelectionPrimes 22 \ witnessCore).Nonempty
    rw [available]
    simp
  have ha : mobiusDivisorSuccessorEnvelope 22 {3,7,11,17,19} ≤
      mobiusDivisorSelectionEnergy 22 ∅ := by
    linarith only [mobiusDivisorSuccessorEnvelope_twentyTwo_admitted]
  have hc := h 22 {3,7,11,17,19} hP hn ha
  linarith only [hc,mobiusDivisorSuccessorEnvelope_twentyTwo_average_exceeds]
end RHTower
