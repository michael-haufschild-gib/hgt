import GaloisForLFunctions.RHTower.DivisorTwentyTwoAnalyticBounds
import GaloisForLFunctions.RHTower.MobiusDivisorSuccessorAverageObstruction

/-!
# A repair increases matching energies while contracting the full envelope

The actual cutoff-seventeen field after primes three, five and seven has
four coordinates. Forcing eleven leaves successor admission; prime two is
the unique least-energy repair. Both repaired states increase relative to
their matching original states, but both lie strictly below the original
eleven-successor energy. Analytic source enclosures prove every comparison.
-/

noncomputable section
open Finset
namespace RHTower
private def repairCore : Finset ℕ := {3,5,7}
private def a : ℝ := divisorUnsignedDilationChannel 17 1-divisorUnsignedDilationChannel 17 3-
  divisorUnsignedDilationChannel 17 5-divisorUnsignedDilationChannel 17 7+
  divisorUnsignedDilationChannel 17 15
private def b : ℝ := -divisorUnsignedDilationChannel 17 2+divisorUnsignedDilationChannel 17 6+
  divisorUnsignedDilationChannel 17 10+divisorUnsignedDilationChannel 17 14
private def c : ℝ := -divisorUnsignedDilationChannel 17 11
private def d : ℝ := -divisorUnsignedDilationChannel 17 13
private lemma boxes : (-0.402≤a ∧ a≤-0.401) ∧ (0.076≤b ∧ b≤0.078) ∧
    (-0.125≤c ∧ c≤-0.124) ∧ (-0.080≤d ∧ d≤-0.079) :=
  divisorUnsignedDilationChannel_seventeen_profile_boxes
private def profile (A B C D : ℝ) (R : Finset ℕ) : ℝ :=
  (if R=∅ then A else 0)+(if R={2} then B else 0)+
  (if R={11} then C else 0)+(if R={13} then D else 0)

private lemma signed_prime (p : ℕ) (hp : p.Prime) :
    mobiusDivisorDilationChannel 17 p = -divisorUnsignedDilationChannel 17 p := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,ArithmeticFunction.moebius_apply_prime hp]
  norm_num
private lemma signed_pair (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    mobiusDivisorDilationChannel 17 (p*q) = divisorUnsignedDilationChannel 17 (p*q) := by
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
    mobiusDivisorDilationChannel 17 n=0 := by
  have hn : ¬Squarefree n := by
    intro h
    have he : p=1 := Nat.isUnit_iff.mp (h p hd)
    omega
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  norm_num
private lemma terminal_zero : mobiusDivisorDilationChannel 17 17=0 := by
  simp [mobiusDivisorDilationChannel]
private lemma signed_one : mobiusDivisorDilationChannel 17 1=divisorUnsignedDilationChannel 17 1 := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned]; norm_num

set_option maxHeartbeats 800000 in
private lemma source_profile (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 17 repairCore R=profile a b c d R := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  have z4 := square_zero 4 2 (by omega) (by norm_num)
  have z8 := square_zero 8 2 (by omega) (by norm_num)
  have z9 := square_zero 9 3 (by omega) (by norm_num)
  have z12 := square_zero 12 2 (by omega) (by norm_num)
  have z16 := square_zero 16 2 (by omega) (by norm_num)
  have f6 := factors_pair 2 3 Nat.prime_two Nat.prime_three
  have f10 := factors_pair 2 5 Nat.prime_two Nat.prime_five
  have f14 := factors_pair 2 7 Nat.prime_two hp7
  have f15 := factors_pair 3 5 Nat.prime_three Nat.prime_five
  have s6 := signed_pair 2 3 Nat.prime_two Nat.prime_three (by omega)
  have s10 := signed_pair 2 5 Nat.prime_two Nat.prime_five (by omega)
  have s14 := signed_pair 2 7 Nat.prime_two hp7 (by omega)
  have s15 := signed_pair 3 5 Nat.prime_three Nat.prime_five (by omega)
  norm_num only at f6 f10 f14 f15 s6 s10 s14 s15
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
  norm_num [Finset.sum_Icc_succ_top,z4,z8,z9,z12,z16,terminal_zero,
    Nat.prime_two.primeFactors,Nat.prime_three.primeFactors,Nat.prime_five.primeFactors,
    hp7.primeFactors,hp11.primeFactors,hp13.primeFactors,
    f6,f10,f14,f15,repairCore,Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton]
  simp only [signed_one,s6,s10,s14,s15,signed_prime 2 Nat.prime_two,
    signed_prime 3 Nat.prime_three,signed_prime 5 Nat.prime_five,signed_prime 7 hp7,
    signed_prime 11 hp11,signed_prime 13 hp13]
  by_cases h0 : R=∅
  · subst R; simp [profile,a]; ring
  by_cases h2 : R={2}
  · subst R; simp [profile,b]
  by_cases h11 : R={11}
  · subst R; simp [profile,c]
  by_cases h13 : R={13}
  · subst R; simp [profile,d]
  simp [profile,h0,h2,h11,h13,Ne.symm h0,Ne.symm h2,Ne.symm h11,Ne.symm h13]

private lemma energy_profile {P : Finset ℕ} {A B C D : ℝ}
    (hf : ∀ R,mobiusDivisorSelectionFibre 17 P R=profile A B C D R) :
    mobiusDivisorSelectionEnergy 17 P=A^2+B^2+C^2+D^2 := by
  let L : Finset (Finset ℕ) := {∅,{2},{11},{13}}
  have hs : L ⊆ (mobiusDivisorSelectionPrimes 17).powerset := by
    intro R hR
    simp only [L,mem_insert,mem_singleton] at hR
    rcases hR with rfl|rfl|rfl|rfl
    all_goals norm_num [mem_powerset,insert_subset_iff,singleton_subset_iff,mobiusDivisorSelectionPrimes]
  have hz (R : Finset ℕ) (_ : R∈(mobiusDivisorSelectionPrimes 17).powerset) (hn : R∉L) :
      (mobiusDivisorSelectionFibre 17 P R)^2=0 := by
    have h0 : R≠∅ := fun he => hn (by simp [L,he])
    have h2 : R≠{2} := fun he => hn (by simp [L,he])
    have h11 : R≠{11} := fun he => hn (by simp [L,he])
    have h13 : R≠{13} := fun he => hn (by simp [L,he])
    simp [hf,profile,h0,h2,h11,h13]
  have he := sum_subset (f:=fun R => (mobiusDivisorSelectionFibre 17 P R)^2) hs hz
  change (∑ R∈(mobiusDivisorSelectionPrimes 17).powerset,
    (mobiusDivisorSelectionFibre 17 P R)^2)=_
  rw [← he]
  simp_rw [hf]
  simp [L,profile]
  ring

private lemma profile_zero {R : Finset ℕ} (hR : ¬R⊆{2,11,13}) (A B C D : ℝ) :
    profile A B C D R=0 := by
  have h0 : R≠∅ := by rintro rfl; exact hR (by simp)
  have h2 : R≠{2} := by rintro rfl; exact hR (by simp)
  have h11 : R≠{11} := by rintro rfl; exact hR (by simp)
  have h13 : R≠{13} := by rintro rfl; exact hR (by simp)
  simp [profile,h0,h2,h11,h13]
private lemma profile_mergers (A B C D : ℝ) (R : Finset ℕ) :
    (if 2∈R then 0 else profile A B C D R+profile A B C D (insert 2 R))=
      profile (A+B) 0 C D R ∧
    (if 11∈R then 0 else profile A B C D R+profile A B C D (insert 11 R))=
      profile (A+C) B 0 D R ∧
    (if 13∈R then 0 else profile A B C D R+profile A B C D (insert 13 R))=
      profile (A+D) B C 0 R := by
  by_cases hR : R⊆{2,11,13}
  · have hm := mem_powerset.mpr hR
    norm_num [Finset.powerset_insert,Finset.image_union,Finset.image_insert] at hm
    simp only [or_assoc] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [profile,Finset.ext_iff,iff_def,or_imp,forall_and]
  · have hn (q : ℕ) : ¬insert q R⊆{2,11,13} :=
      fun h => hR ((subset_insert q R).trans h)
    simp only [profile_zero hR,profile_zero (hn 2),profile_zero (hn 11),profile_zero (hn 13),add_zero,ite_self]
    simp
private lemma profile_two (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 17 (insert 2 repairCore) R=profile (a+b) 0 c d R := by
  rw [mobiusDivisorSelectionFibre_insert,source_profile,source_profile]
  exact (profile_mergers a b c d R).1
private lemma profile_eleven (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 17 (insert 11 repairCore) R=profile (a+c) b 0 d R := by
  rw [mobiusDivisorSelectionFibre_insert,source_profile,source_profile]
  exact (profile_mergers a b c d R).2.1
private lemma profile_thirteen (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 17 (insert 13 repairCore) R=profile (a+d) b c 0 R := by
  rw [mobiusDivisorSelectionFibre_insert,source_profile,source_profile]
  exact (profile_mergers a b c d R).2.2
private lemma profile_repair (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 17 (insert 2 (insert 11 repairCore)) R=profile (a+c+b) 0 0 d R := by
  rw [mobiusDivisorSelectionFibre_insert,profile_eleven,profile_eleven]
  exact (profile_mergers (a+c) b 0 d R).1
private lemma profile_forced_thirteen (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 17 (insert 13 (insert 11 repairCore)) R=profile (a+c+d) b 0 0 R := by
  rw [mobiusDivisorSelectionFibre_insert,profile_eleven,profile_eleven]
  exact (profile_mergers (a+c) b 0 d R).2.2
private lemma profile_repair_thirteen (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 17 (insert 13 (insert 2 (insert 11 repairCore))) R=
      profile (a+c+b+d) 0 0 0 R := by
  rw [mobiusDivisorSelectionFibre_insert,profile_repair,profile_repair]
  exact (profile_mergers (a+c+b) 0 0 d R).2.2
private lemma energy_formulas :
    mobiusDivisorSelectionEnergy 17 repairCore=a^2+b^2+c^2+d^2 ∧
    mobiusDivisorSelectionEnergy 17 (insert 2 repairCore)=(a+b)^2+c^2+d^2 ∧
    mobiusDivisorSelectionEnergy 17 (insert 11 repairCore)=(a+c)^2+b^2+d^2 ∧
    mobiusDivisorSelectionEnergy 17 (insert 13 repairCore)=(a+d)^2+b^2+c^2 ∧
    mobiusDivisorSelectionEnergy 17 (insert 2 (insert 11 repairCore))=(a+c+b)^2+d^2 ∧
    mobiusDivisorSelectionEnergy 17 (insert 13 (insert 11 repairCore))=(a+c+d)^2+b^2 ∧
    mobiusDivisorSelectionEnergy 17 (insert 13 (insert 2 (insert 11 repairCore)))=(a+c+b+d)^2 := by
  exact ⟨energy_profile source_profile,by simpa using energy_profile profile_two,
    by simpa using energy_profile profile_eleven,by simpa using energy_profile profile_thirteen,
    by simpa using energy_profile profile_repair,by simpa using energy_profile profile_forced_thirteen,
    by simpa using energy_profile profile_repair_thirteen⟩

private lemma initial_energy : mobiusDivisorSelectionEnergy 17 ∅=
    ∑ d∈({1,2,3,5,6,7,10,11,13,14,15}:Finset ℕ),(divisorUnsignedDilationChannel 17 d)^2 := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  have z4 := square_zero 4 2 (by omega) (by norm_num)
  have z8 := square_zero 8 2 (by omega) (by norm_num)
  have z9 := square_zero 9 3 (by omega) (by norm_num)
  have z12 := square_zero 12 2 (by omega) (by norm_num)
  have z16 := square_zero 16 2 (by omega) (by norm_num)
  have s6 := signed_pair 2 3 Nat.prime_two Nat.prime_three (by omega)
  have s10 := signed_pair 2 5 Nat.prime_two Nat.prime_five (by omega)
  have s14 := signed_pair 2 7 Nat.prime_two hp7 (by omega)
  have s15 := signed_pair 3 5 Nat.prime_three Nat.prime_five (by omega)
  norm_num only at s6 s10 s14 s15
  rw [mobiusDivisorSelectionEnergy_empty]
  norm_num [Finset.sum_Icc_succ_top,z4,z8,z9,z12,z16,terminal_zero,signed_one,
    s6,s10,s14,s15,signed_prime 2 Nat.prime_two,signed_prime 3 Nat.prime_three,
    signed_prime 5 Nat.prime_five,signed_prime 7 hp7,signed_prime 11 hp11,signed_prime 13 hp13]
  ring
private lemma budget_box : (0.360:ℝ) ≤ mobiusDivisorSelectionEnergy 17 ∅ ∧
    mobiusDivisorSelectionEnergy 17 ∅ ≤ 0.365 := by
  rw [initial_energy]
  exact sum_divisorUnsignedDilationChannel_seventeen_sq_bounds
private lemma square_box {x l u : ℝ} (hl : 0≤l) (h : l≤x ∧ x≤u) :
    l^2≤x^2 ∧ x^2≤u^2 := by
  have hx := hl.trans h.1
  constructor
  · simpa only [pow_two] using mul_le_mul h.1 h.1 hl hx
  · simpa only [pow_two] using mul_le_mul h.2 h.2 hx (hx.trans h.2)

set_option maxHeartbeats 1000000 in
private lemma energy_bounds :
    mobiusDivisorSelectionEnergy 17 repairCore ≤ 0.291 ∧
    mobiusDivisorSelectionEnergy 17 (insert 2 repairCore) ≤ 0.291 ∧
    0.287 ≤ mobiusDivisorSelectionEnergy 17 (insert 11 repairCore) ∧
    mobiusDivisorSelectionEnergy 17 (insert 11 repairCore) ≤ 0.291 ∧
    mobiusDivisorSelectionEnergy 17 (insert 13 repairCore) ≤ 0.291 ∧
    mobiusDivisorSelectionEnergy 17 (insert 2 (insert 11 repairCore)) ≤ 0.210 ∧
    0.370 ≤ mobiusDivisorSelectionEnergy 17 (insert 13 (insert 11 repairCore)) ∧
    mobiusDivisorSelectionEnergy 17 (insert 13 (insert 2 (insert 11 repairCore))) ≤ 0.282 ∧
    mobiusDivisorSelectionEnergy 17 repairCore+1/100 ≤
      mobiusDivisorSelectionEnergy 17 (insert 2 (insert 11 repairCore)) ∧
    mobiusDivisorSelectionEnergy 17 (insert 13 repairCore)+1/50 ≤
      mobiusDivisorSelectionEnergy 17 (insert 13 (insert 2 (insert 11 repairCore))) := by
  obtain ⟨ha,hb,hc,hd⟩ := boxes
  have sa := square_box (x:=-a) (l:=0.401) (u:=0.402) (by norm_num) ⟨by linarith,by linarith⟩
  have sb := square_box (by norm_num : (0:ℝ)≤0.076) hb
  have sc := square_box (x:=-c) (l:=0.124) (u:=0.125) (by norm_num) ⟨by linarith,by linarith⟩
  have sd := square_box (x:=-d) (l:=0.079) (u:=0.080) (by norm_num) ⟨by linarith,by linarith⟩
  have sab := square_box (x:=-(a+b)) (l:=0.323) (u:=0.326) (by norm_num) ⟨by linarith,by linarith⟩
  have sac := square_box (x:=-(a+c)) (l:=0.525) (u:=0.527) (by norm_num) ⟨by linarith,by linarith⟩
  have sad := square_box (x:=-(a+d)) (l:=0.480) (u:=0.482) (by norm_num) ⟨by linarith,by linarith⟩
  have sacb := square_box (x:=-(a+c+b)) (l:=0.447) (u:=0.451) (by norm_num) ⟨by linarith,by linarith⟩
  have sacd := square_box (x:=-(a+c+d)) (l:=0.604) (u:=0.607) (by norm_num) ⟨by linarith,by linarith⟩
  have sacbd := square_box (x:=-(a+c+b+d)) (l:=0.526) (u:=0.531) (by norm_num) ⟨by linarith,by linarith⟩
  simp only [neg_sq] at sa sc sd sab sac sad sacb sacd sacbd
  obtain ⟨f0,f2,f11,f13,f211,f1113,f21113⟩ := energy_formulas
  rw [f0,f2,f11,f13,f211,f1113,f21113]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    nlinarith only [sa.1,sa.2,sb.1,sb.2,sc.1,sc.2,sd.1,sd.2,
      sab.1,sab.2,sac.1,sac.2,sad.1,sad.2,sacb.1,sacb.2,sacd.1,sacd.2,sacbd.1,sacbd.2]

/-- The unique greedy repair at seventeen restores admission by comparison
with the forced successor. Its two matching parent energies both increase,
so individual inherited contraction is strictly stronger than envelope control. -/
theorem mobiusDivisorSeventeen_repair_certificate :
    let P : Finset ℕ := {3,5,7}
    let S := insert 11 P
    let E := insert 2 S
    (mobiusDivisorSuccessorEnvelope 17 P+1/20 ≤ mobiusDivisorSelectionEnergy 17 ∅) ∧
    (mobiusDivisorSelectionEnergy 17 ∅+1/200 ≤ mobiusDivisorSuccessorEnvelope 17 S) ∧
    (∀q∈mobiusDivisorSelectionPrimes 17 \ S,q≠2 →
      mobiusDivisorSelectionEnergy 17 E < mobiusDivisorSelectionEnergy 17 (insert q S)) ∧
    (mobiusDivisorSuccessorEnvelope 17 E+1/200 ≤ mobiusDivisorSelectionEnergy 17 S) ∧
    (mobiusDivisorSelectionEnergy 17 P+1/100 ≤ mobiusDivisorSelectionEnergy 17 E) ∧
    (mobiusDivisorSelectionEnergy 17 (insert 13 P)+1/50 ≤
      mobiusDivisorSelectionEnergy 17 (insert 13 E)) := by
  change (mobiusDivisorSuccessorEnvelope 17 repairCore+1/20 ≤ _) ∧ _
  obtain ⟨h0,h2,h11lo,h11,h13,hE,hbad,hfull,hgain,hgain13⟩ := energy_bounds
  have available : mobiusDivisorSelectionPrimes 17 \ repairCore={2,11,13} := by
    norm_num [mobiusDivisorSelectionPrimes,repairCore,Finset.range_add_one,
      Finset.filter_insert,Finset.filter_singleton,Finset.sdiff_eq_filter,Finset.insert_comm]
  have forced_available : mobiusDivisorSelectionPrimes 17 \ insert 11 repairCore={2,13} := by
    norm_num [mobiusDivisorSelectionPrimes,repairCore,Finset.range_add_one,
      Finset.filter_insert,Finset.filter_singleton,Finset.sdiff_eq_filter,Finset.insert_comm]
  have end_available : mobiusDivisorSelectionPrimes 17 \ insert 2 (insert 11 repairCore)={13} := by
    norm_num [mobiusDivisorSelectionPrimes,repairCore,Finset.range_add_one,
      Finset.filter_insert,Finset.filter_singleton,Finset.sdiff_eq_filter,Finset.insert_comm]
  have hparent : mobiusDivisorSuccessorEnvelope 17 repairCore ≤ 0.291 := by
    rw [mobiusDivisorSuccessorEnvelope_le_iff,available]
    refine ⟨h0,?_⟩
    intro p hp
    simp only [mem_insert,mem_singleton] at hp
    rcases hp with rfl|rfl|rfl
    · exact h2
    · exact h11
    · exact h13
  have hforced : 0.370 ≤ mobiusDivisorSuccessorEnvelope 17 (insert 11 repairCore) := by
    have h := ((mobiusDivisorSuccessorEnvelope_le_iff 17 (insert 11 repairCore) _).mp le_rfl).2
      13 (by rw [forced_available]; simp)
    exact hbad.trans h
  have hend : mobiusDivisorSuccessorEnvelope 17 (insert 2 (insert 11 repairCore)) ≤ 0.282 := by
    rw [mobiusDivisorSuccessorEnvelope_le_iff,end_available]
    refine ⟨by linarith,?_⟩
    intro p hp
    have he : p=13 := mem_singleton.mp hp
    subst p
    exact hfull
  refine ⟨by linarith only [hparent,budget_box.1],
    by
      change mobiusDivisorSelectionEnergy 17 ∅+1/200 ≤
        mobiusDivisorSuccessorEnvelope 17 (insert 11 repairCore)
      linarith only [hforced,budget_box.2],?_,by
      change mobiusDivisorSuccessorEnvelope 17 (insert 2 (insert 11 repairCore))+1/200 ≤
        mobiusDivisorSelectionEnergy 17 (insert 11 repairCore)
      linarith only [hend,h11lo],hgain,hgain13⟩
  intro q hq hn
  change q∈mobiusDivisorSelectionPrimes 17 \ insert 11 repairCore at hq
  rw [forced_available] at hq
  simp only [mem_insert,mem_singleton] at hq
  rcases hq with rfl|rfl
  · exact (hn rfl).elim
  · change mobiusDivisorSelectionEnergy 17 (insert 2 (insert 11 repairCore)) <
      mobiusDivisorSelectionEnergy 17 (insert 13 (insert 11 repairCore))
    linarith
end RHTower
