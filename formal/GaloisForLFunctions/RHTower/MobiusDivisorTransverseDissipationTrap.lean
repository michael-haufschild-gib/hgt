import GaloisForLFunctions.RHTower.DivisorTwentyTwoAnalyticBounds
import GaloisForLFunctions.RHTower.MobiusDivisorNonemptyEnergy
import GaloisForLFunctions.RHTower.TwoCoordinateMergerCeiling
import GaloisForLFunctions.RHTower.MobiusDivisorSuccessorAverageObstruction
/-!
# Forced transverse growth paid by the actual head square

At cutoff twenty-five, a processed core with only primes three and five
remaining satisfies strict original-diagonal admission. Both next operations
strictly increase nonempty fibre energy but strictly contract the complete
successor envelope. The large negative head pays the positive mixed overlap.
Analytic source intervals certify all margins independently of computation.

For arbitrary two-coordinate fields, the sharp uniform minimum next nonempty
energy factor is three halves. This bounds unavoidable transverse growth;
neither that boundary nor the arithmetic witness proves RH.
-/
noncomputable section
open Finset
namespace RHTower

/-- The actual processed core leaving only primes three and five at cutoff twenty-five. -/
def mobiusDivisorTwentyFiveCore : Finset ℕ := {2,7,11,13,17,19,23}
private def h : ℝ := divisorUnsignedDilationChannel 25 1-divisorUnsignedDilationChannel 25 2-
  divisorUnsignedDilationChannel 25 7-divisorUnsignedDilationChannel 25 11-
  divisorUnsignedDilationChannel 25 13+divisorUnsignedDilationChannel 25 14-
  divisorUnsignedDilationChannel 25 17-divisorUnsignedDilationChannel 25 19+
  divisorUnsignedDilationChannel 25 22-divisorUnsignedDilationChannel 25 23
private def a : ℝ := -divisorUnsignedDilationChannel 25 3+divisorUnsignedDilationChannel 25 6+
  divisorUnsignedDilationChannel 25 21
private def b : ℝ := -divisorUnsignedDilationChannel 25 5+divisorUnsignedDilationChannel 25 10
private def c : ℝ := divisorUnsignedDilationChannel 25 15
private def profile (R : Finset ℕ) : ℝ := (if R=∅ then h else 0)+
  (if R={3} then a else 0)+(if R={5} then b else 0)+(if R={3,5} then c else 0)
private lemma boxes : (-0.75 ≤ h ∧ h ≤ -0.73) ∧ (0.007 ≤ a ∧ a ≤ 0.010) ∧
    (0.013 ≤ b ∧ b ≤ 0.015) ∧ (0.173 ≤ c ∧ c ≤ 0.175) :=
  divisorUnsignedDilationChannel_twentyFive_profile_boxes

private lemma signed_prime (p : ℕ) (hp : p.Prime) :
    mobiusDivisorDilationChannel 25 p = -divisorUnsignedDilationChannel 25 p := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,ArithmeticFunction.moebius_apply_prime hp]
  norm_num
private lemma signed_pair (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    mobiusDivisorDilationChannel 25 (p*q) = divisorUnsignedDilationChannel 25 (p*q) := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (hp.coprime_iff_not_dvd.mpr
      (fun hd => hne ((Nat.dvd_prime hq).mp hd |>.resolve_left hp.ne_one))),
    ArithmeticFunction.moebius_apply_prime hp,ArithmeticFunction.moebius_apply_prime hq]
  norm_num
private lemma factors_pair (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (p*q).primeFactors=({p,q}:Finset ℕ) := by
  rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero,hp.primeFactors,hq.primeFactors]
  simp
private lemma square_zero (n p : ℕ) (hp : 1<p) (hd : p*p∣n) :
    mobiusDivisorDilationChannel 25 n=0 := by
  have hn : ¬Squarefree n := by
    intro hn
    have he : p=1 := Nat.isUnit_iff.mp (hn p hd)
    omega
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  norm_num
private lemma terminal_zero : mobiusDivisorDilationChannel 25 25=0 := by simp [mobiusDivisorDilationChannel]

set_option maxHeartbeats 1000000 in
private lemma source_profile (R : Finset ℕ) :
    mobiusDivisorSelectionFibre 25 mobiusDivisorTwentyFiveCore R=profile R := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  have hp17 : Nat.Prime 17 := by norm_num
  have hp19 : Nat.Prime 19 := by norm_num
  have hp23 : Nat.Prime 23 := by norm_num
  have z4 := square_zero 4 2 (by omega) (by norm_num)
  have z8 := square_zero 8 2 (by omega) (by norm_num)
  have z9 := square_zero 9 3 (by omega) (by norm_num)
  have z12 := square_zero 12 2 (by omega) (by norm_num)
  have z16 := square_zero 16 2 (by omega) (by norm_num)
  have z18 := square_zero 18 3 (by omega) (by norm_num)
  have z20 := square_zero 20 2 (by omega) (by norm_num)
  have z24 := square_zero 24 2 (by omega) (by norm_num)
  have f6 := factors_pair 2 3 Nat.prime_two Nat.prime_three
  have f10 := factors_pair 2 5 Nat.prime_two Nat.prime_five
  have f14 := factors_pair 2 7 Nat.prime_two hp7
  have f15 := factors_pair 3 5 Nat.prime_three Nat.prime_five
  have f21 := factors_pair 3 7 Nat.prime_three hp7
  have f22 := factors_pair 2 11 Nat.prime_two hp11
  have s6 := signed_pair 2 3 Nat.prime_two Nat.prime_three (by omega)
  have s10 := signed_pair 2 5 Nat.prime_two Nat.prime_five (by omega)
  have s14 := signed_pair 2 7 Nat.prime_two hp7 (by omega)
  have s15 := signed_pair 3 5 Nat.prime_three Nat.prime_five (by omega)
  have s21 := signed_pair 3 7 Nat.prime_three hp7 (by omega)
  have s22 := signed_pair 2 11 Nat.prime_two hp11 (by omega)
  norm_num only at f6 f10 f14 f15 f21 f22 s6 s10 s14 s15 s21 s22
  have s1 : mobiusDivisorDilationChannel 25 1=divisorUnsignedDilationChannel 25 1 := by
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned]; norm_num
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
  norm_num [Finset.sum_Icc_succ_top,z4,z8,z9,z12,z16,z18,z20,z24,terminal_zero,
    Nat.prime_two.primeFactors,Nat.prime_three.primeFactors,Nat.prime_five.primeFactors,
    hp7.primeFactors,hp11.primeFactors,hp13.primeFactors,hp17.primeFactors,hp19.primeFactors,hp23.primeFactors,
    f6,f10,f14,f15,f21,f22,mobiusDivisorTwentyFiveCore,Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton]
  simp only [s1,s6,s10,s14,s15,s21,s22,signed_prime 2 Nat.prime_two,
    signed_prime 3 Nat.prime_three,signed_prime 5 Nat.prime_five,signed_prime 7 hp7,
    signed_prime 11 hp11,signed_prime 13 hp13,signed_prime 17 hp17,signed_prime 19 hp19,signed_prime 23 hp23]
  have hn0 : ({3,5}:Finset ℕ)≠∅ := by
    intro he; have ht := (Finset.ext_iff.mp he) 3; norm_num at ht
  have hn3 : ({3,5}:Finset ℕ)≠{3} := by
    intro he; have ht := (Finset.ext_iff.mp he) 5; norm_num at ht
  have hn5 : ({3,5}:Finset ℕ)≠{5} := by
    intro he; have ht := (Finset.ext_iff.mp he) 3; norm_num at ht
  by_cases h0 : R=∅
  · subst R; simp [profile,h,hn0,Ne.symm hn0]; ring
  by_cases h3 : R={3}
  · subst R; simp [profile,a,hn3,Ne.symm hn3]
  by_cases h5 : R={5}
  · subst R; simp [profile,b,hn5,Ne.symm hn5]
  by_cases h35 : R={3,5}
  · subst R; simp [profile,c,hn0,hn3,hn5,Ne.symm hn0,Ne.symm hn3,Ne.symm hn5]
  simp [profile,h0,h3,h5,h35,Ne.symm h0,Ne.symm h3,Ne.symm h5,Ne.symm h35]

private lemma remaining : mobiusDivisorSelectionPrimes 25 \ mobiusDivisorTwentyFiveCore={3,5} := by
  norm_num [mobiusDivisorSelectionPrimes,mobiusDivisorTwentyFiveCore,Finset.range_add_one,
    Finset.filter_insert,Finset.sdiff_eq_filter,Finset.filter_singleton]
  ext p
  simp [or_comm]

private lemma heads :
    mobiusDivisorSelectionFibre 25 mobiusDivisorTwentyFiveCore ∅=h ∧
    mobiusDivisorSelectionFibre 25 mobiusDivisorTwentyFiveCore {3}=a ∧
    mobiusDivisorSelectionFibre 25 mobiusDivisorTwentyFiveCore {5}=b ∧
    mobiusDivisorSelectionFibre 25 mobiusDivisorTwentyFiveCore {3,5}=c := by
  have hn0 : ({3,5}:Finset ℕ)≠∅ := by intro he; have ht := (Finset.ext_iff.mp he) 3; norm_num at ht
  have hn3 : ({3,5}:Finset ℕ)≠{3} := by intro he; have ht := (Finset.ext_iff.mp he) 5; norm_num at ht
  have hn5 : ({3,5}:Finset ℕ)≠{5} := by intro he; have ht := (Finset.ext_iff.mp he) 3; norm_num at ht
  simp [source_profile,profile,hn0,hn3,hn5,Ne.symm hn0,Ne.symm hn3,Ne.symm hn5]

private lemma energies :
    mobiusDivisorSelectionEnergy 25 mobiusDivisorTwentyFiveCore=h^2+a^2+b^2+c^2 ∧
    mobiusDivisorSelectionEnergy 25 (insert 3 mobiusDivisorTwentyFiveCore)=(h+a)^2+(b+c)^2 ∧
    mobiusDivisorSelectionEnergy 25 (insert 5 mobiusDivisorTwentyFiveCore)=(h+b)^2+(a+c)^2 ∧
    mobiusDivisorSelectionEnergy 25 (insert 5 (insert 3 mobiusDivisorTwentyFiveCore))=(h+a+b+c)^2 := by
  have hpair : ({5,3}:Finset ℕ)={3,5} := by ext p; simp [or_comm]
  have h0 := subsetLabelEnergy_two_remaining (mobiusDivisorSelectionPrimes 25)
    (mobiusDivisorSelectionIndices 25) Nat.primeFactors (mobiusDivisorDilationChannel 25)
    mobiusDivisorTwentyFiveCore 3 5 (by omega) remaining
  have h3 := subsetLabelEnergy_insert_two_remaining (mobiusDivisorSelectionPrimes 25)
    (mobiusDivisorSelectionIndices 25) Nat.primeFactors (mobiusDivisorDilationChannel 25)
    mobiusDivisorTwentyFiveCore 3 5 (by omega) remaining
  have h5 := subsetLabelEnergy_insert_two_remaining (mobiusDivisorSelectionPrimes 25)
    (mobiusDivisorSelectionIndices 25) Nat.primeFactors (mobiusDivisorDilationChannel 25)
    mobiusDivisorTwentyFiveCore 5 3 (by omega) (remaining.trans hpair.symm)
  have hf := subsetLabelEnergy_insert_insert_two_remaining (mobiusDivisorSelectionPrimes 25)
    (mobiusDivisorSelectionIndices 25) Nat.primeFactors (mobiusDivisorDilationChannel 25)
    mobiusDivisorTwentyFiveCore 3 5 (by omega) remaining
  change mobiusDivisorSelectionEnergy _ _=_ at h0 h3 h5 hf
  change mobiusDivisorSelectionEnergy _ _= (mobiusDivisorSelectionFibre _ _ ∅)^2+
    (mobiusDivisorSelectionFibre _ _ {3})^2+(mobiusDivisorSelectionFibre _ _ {5})^2+
    (mobiusDivisorSelectionFibre _ _ {3,5})^2 at h0
  change mobiusDivisorSelectionEnergy _ _=
    (mobiusDivisorSelectionFibre _ _ ∅+mobiusDivisorSelectionFibre _ _ {3})^2+
    (mobiusDivisorSelectionFibre _ _ {5}+mobiusDivisorSelectionFibre _ _ {3,5})^2 at h3
  change mobiusDivisorSelectionEnergy _ _=
    (mobiusDivisorSelectionFibre _ _ ∅+mobiusDivisorSelectionFibre _ _ {5})^2+
    (mobiusDivisorSelectionFibre _ _ {3}+mobiusDivisorSelectionFibre _ _ {5,3})^2 at h5
  change mobiusDivisorSelectionEnergy _ _=
    (mobiusDivisorSelectionFibre _ _ ∅+mobiusDivisorSelectionFibre _ _ {3}+
      mobiusDivisorSelectionFibre _ _ {5}+mobiusDivisorSelectionFibre _ _ {3,5})^2 at hf
  rw [hpair] at h5
  simp only [heads.1,heads.2.1,heads.2.2.1,heads.2.2.2] at h0 h3 h5 hf
  exact ⟨h0,h3,by nlinarith only [h5],hf⟩

set_option maxHeartbeats 1000000 in
private lemma initial_lower : (0.8:ℝ) ≤ mobiusDivisorSelectionEnergy 25 ∅ := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hp11 : Nat.Prime 11 := by norm_num
  have hp13 : Nat.Prime 13 := by norm_num
  have hp17 : Nat.Prime 17 := by norm_num
  have hp19 : Nat.Prime 19 := by norm_num
  have hp23 : Nat.Prime 23 := by norm_num
  have z4 := square_zero 4 2 (by omega) (by norm_num)
  have z8 := square_zero 8 2 (by omega) (by norm_num)
  have z9 := square_zero 9 3 (by omega) (by norm_num)
  have z12 := square_zero 12 2 (by omega) (by norm_num)
  have z16 := square_zero 16 2 (by omega) (by norm_num)
  have z18 := square_zero 18 3 (by omega) (by norm_num)
  have z20 := square_zero 20 2 (by omega) (by norm_num)
  have z24 := square_zero 24 2 (by omega) (by norm_num)
  have f6 := factors_pair 2 3 Nat.prime_two Nat.prime_three
  have f10 := factors_pair 2 5 Nat.prime_two Nat.prime_five
  have f14 := factors_pair 2 7 Nat.prime_two hp7
  have f15 := factors_pair 3 5 Nat.prime_three Nat.prime_five
  have f21 := factors_pair 3 7 Nat.prime_three hp7
  have f22 := factors_pair 2 11 Nat.prime_two hp11
  have s6 := signed_pair 2 3 Nat.prime_two Nat.prime_three (by omega)
  have s10 := signed_pair 2 5 Nat.prime_two Nat.prime_five (by omega)
  have s14 := signed_pair 2 7 Nat.prime_two hp7 (by omega)
  have s15 := signed_pair 3 5 Nat.prime_three Nat.prime_five (by omega)
  have s21 := signed_pair 3 7 Nat.prime_three hp7 (by omega)
  have s22 := signed_pair 2 11 Nat.prime_two hp11 (by omega)
  norm_num only at f6 f10 f14 f15 f21 f22 s6 s10 s14 s15 s21 s22
  have s1 : mobiusDivisorDilationChannel 25 1=divisorUnsignedDilationChannel 25 1 := by
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned]; norm_num
  have hb := sum_divisorUnsignedDilationChannel_twentyFive_sq_lower
  rw [mobiusDivisorSelectionEnergy_empty]
  norm_num [Finset.sum_Icc_succ_top,z4,z8,z9,z12,z16,z18,z20,z24,terminal_zero]
  simp only [s1,s6,s10,s14,s15,s21,s22,signed_prime 2 Nat.prime_two,
    signed_prime 3 Nat.prime_three,signed_prime 5 Nat.prime_five,signed_prime 7 hp7,
    signed_prime 11 hp11,signed_prime 13 hp13,signed_prime 17 hp17,signed_prime 19 hp19,signed_prime 23 hp23,neg_sq]
  norm_num [Finset.sum_insert,Finset.sum_singleton] at hb
  nlinarith only [hb]

private lemma arithmetic_inequalities :
    1/500+(a^2+b^2+c^2)<(b+c)^2 ∧
    1/500+(a^2+b^2+c^2)<(a+c)^2 ∧
    1/250+((h+a)^2+(b+c)^2)<h^2+a^2+b^2+c^2 ∧
    1/250+((h+b)^2+(a+c)^2)<h^2+a^2+b^2+c^2 ∧
    (h+a+b+c)^2<(h+a)^2+(b+c)^2 ∧
    (h+a+b+c)^2<(h+b)^2+(a+c)^2 ∧
    h^2+a^2+b^2+c^2<(0.6:ℝ) := by
  obtain ⟨hh,ha,hb,hc⟩ := boxes
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hac := mul_le_mul ha.1 hc.1 (by norm_num : (0:ℝ) ≤ 0.173) ha0
  have hbc := mul_le_mul hb.1 hc.1 (by norm_num : (0:ℝ) ≤ 0.173) hb0
  have hac' := mul_le_mul ha.2 hc.2 hc0 (by norm_num : (0:ℝ) ≤ 0.010)
  have hbc' := mul_le_mul hb.2 hc.2 hc0 (by norm_num : (0:ℝ) ≤ 0.015)
  have ha2 := (sq_le_sq₀ ha0 (by norm_num : (0:ℝ) ≤ 0.010)).mpr ha.2
  have hb2 := (sq_le_sq₀ hb0 (by norm_num : (0:ℝ) ≤ 0.015)).mpr hb.2
  have hc2 := (sq_le_sq₀ hc0 (by norm_num : (0:ℝ) ≤ 0.175)).mpr hc.2
  have hha := mul_le_mul (show (0.73:ℝ) ≤ -h by linarith) ha.1
    (by norm_num : (0:ℝ) ≤ 0.007) (by linarith : 0 ≤ -h)
  have hhb := mul_le_mul (show (0.73:ℝ) ≤ -h by linarith) hb.1
    (by norm_num : (0:ℝ) ≤ 0.013) (by linarith : 0 ≤ -h)
  have hf3 := mul_neg_of_neg_of_pos (show h+a<0 by linarith) (show 0<b+c by linarith)
  have hf5 := mul_neg_of_neg_of_pos (show h+b<0 by linarith) (show 0<a+c by linarith)
  have hh2 := mul_nonneg (show 0 ≤ h+0.75 by linarith) (show 0 ≤ 0.75-h by linarith)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · nlinarith only [hbc,ha2]
  · nlinarith only [hac,hb2]
  · nlinarith only [hha,hbc']
  · nlinarith only [hhb,hac']
  · nlinarith only [hf3]
  · nlinarith only [hf5]
  · nlinarith only [hh2,ha2,hb2,hc2]

private lemma nonempty_values :
    mobiusDivisorNonemptyEnergy 25 mobiusDivisorTwentyFiveCore=a^2+b^2+c^2 ∧
    mobiusDivisorNonemptyEnergy 25 (insert 3 mobiusDivisorTwentyFiveCore)=(b+c)^2 ∧
    mobiusDivisorNonemptyEnergy 25 (insert 5 mobiusDivisorTwentyFiveCore)=(a+c)^2 := by
  have hh3 : mobiusDivisorSelectionFibre 25 (insert 3 mobiusDivisorTwentyFiveCore) ∅=h+a := by
    rw [mobiusDivisorSelectionFibre_insert]
    simp only [notMem_empty,if_false,insert_empty_eq,heads.1,heads.2.1]
  have hh5 : mobiusDivisorSelectionFibre 25 (insert 5 mobiusDivisorTwentyFiveCore) ∅=h+b := by
    rw [mobiusDivisorSelectionFibre_insert]
    simp only [notMem_empty,if_false,insert_empty_eq,heads.1,heads.2.2.1]
  unfold mobiusDivisorNonemptyEnergy
  rw [energies.1,energies.2.1,energies.2.2.1,heads.1,hh3,hh5]
  constructor
  · ring
  constructor <;> ring

private lemma envelope_values :
    mobiusDivisorSuccessorEnvelope 25 mobiusDivisorTwentyFiveCore=h^2+a^2+b^2+c^2 ∧
    mobiusDivisorSuccessorEnvelope 25 (insert 3 mobiusDivisorTwentyFiveCore)=(h+a)^2+(b+c)^2 ∧
    mobiusDivisorSuccessorEnvelope 25 (insert 5 mobiusDivisorTwentyFiveCore)=(h+b)^2+(a+c)^2 := by
  have hbase (P : Finset ℕ) : mobiusDivisorSelectionEnergy 25 P ≤ mobiusDivisorSuccessorEnvelope 25 P :=
    ((mobiusDivisorSuccessorEnvelope_le_iff 25 P _).mp le_rfl).1
  obtain ⟨_,_,h3,h5,hf3,hf5,_⟩ := arithmetic_inequalities
  refine ⟨le_antisymm ?_ (by simpa only [energies.1] using hbase mobiusDivisorTwentyFiveCore),
    le_antisymm ?_ (by simpa only [energies.2.1] using hbase (insert 3 mobiusDivisorTwentyFiveCore)),
    le_antisymm ?_ (by simpa only [energies.2.2.1] using hbase (insert 5 mobiusDivisorTwentyFiveCore))⟩
  · rw [mobiusDivisorSuccessorEnvelope_le_iff]
    refine ⟨energies.1.le,?_⟩
    intro p hp
    rw [remaining] at hp
    rcases mem_insert.mp hp with rfl|hp
    · rw [energies.2.1]; linarith only [h3]
    · have he : p=5 := mem_singleton.mp hp
      subst p
      rw [energies.2.2.1]; linarith only [h5]
  · rw [mobiusDivisorSuccessorEnvelope_le_iff]
    refine ⟨energies.2.1.le,?_⟩
    intro p hp
    have hpold : p ∈ mobiusDivisorSelectionPrimes 25 \ mobiusDivisorTwentyFiveCore :=
      mem_sdiff.mpr ⟨(mem_sdiff.mp hp).1,fun ht => (mem_sdiff.mp hp).2 (mem_insert_of_mem ht)⟩
    have hp3 : p≠3 := fun he => (mem_sdiff.mp hp).2 (mem_insert.mpr (Or.inl he))
    rw [remaining] at hpold
    have he : p=5 := mem_singleton.mp ((mem_insert.mp hpold).resolve_left hp3)
    subst p
    rw [energies.2.2.2]
    exact hf3.le
  · rw [mobiusDivisorSuccessorEnvelope_le_iff]
    refine ⟨energies.2.2.1.le,?_⟩
    intro p hp
    have hpold : p ∈ mobiusDivisorSelectionPrimes 25 \ mobiusDivisorTwentyFiveCore :=
      mem_sdiff.mpr ⟨(mem_sdiff.mp hp).1,fun ht => (mem_sdiff.mp hp).2 (mem_insert_of_mem ht)⟩
    have hp5 : p≠5 := fun he => (mem_sdiff.mp hp).2 (mem_insert.mpr (Or.inl he))
    rw [remaining] at hpold
    have he : p=3 := (mem_insert.mp hpold).resolve_right (fun ht => hp5 (mem_singleton.mp ht))
    subst p
    rw [Finset.insert_comm,energies.2.2.2]
    exact hf5.le

/-- An admitted actual arithmetic state forces every next prime to increase nonempty energy, while every next complete successor envelope strictly contracts. The head square pays both increases. -/
theorem mobiusDivisorTwentyFive_admitted_transverse_trap :
    mobiusDivisorSuccessorEnvelope 25 mobiusDivisorTwentyFiveCore+1/5 < mobiusDivisorSelectionEnergy 25 ∅ ∧
    ∀ p ∈ mobiusDivisorSelectionPrimes 25 \ mobiusDivisorTwentyFiveCore,
      mobiusDivisorNonemptyEnergy 25 mobiusDivisorTwentyFiveCore+1/500 <
        mobiusDivisorNonemptyEnergy 25 (insert p mobiusDivisorTwentyFiveCore) ∧
      mobiusDivisorSuccessorEnvelope 25 (insert p mobiusDivisorTwentyFiveCore)+1/250 <
        mobiusDivisorSuccessorEnvelope 25 mobiusDivisorTwentyFiveCore := by
  obtain ⟨hv3,hv5,h3,h5,_,_,hsmall⟩ := arithmetic_inequalities
  constructor
  · rw [envelope_values.1]
    linarith only [hsmall,initial_lower]
  · intro p hp
    rw [remaining] at hp
    rcases mem_insert.mp hp with rfl|hp
    · rw [nonempty_values.1,nonempty_values.2.1,envelope_values.1,envelope_values.2.1]
      constructor <;> linarith only [hv3,h3]
    · have he : p=5 := mem_singleton.mp hp
      subst p
      rw [nonempty_values.1,nonempty_values.2.2,envelope_values.1,envelope_values.2.2]
      constructor <;> linarith only [hv5,h5]

/-- One of two remaining coordinate mergers increases nonempty energy by at most a factor of three halves. -/
theorem min_twoCoordinateNonemptyEnergy_le (a b c : ℝ) :
    min ((a+c)^2) ((b+c)^2) ≤ (3/2:ℝ)*(a^2+b^2+c^2) := by
  rcases le_total (a^2) (b^2) with hab|hba
  · exact (min_le_left _ _).trans (by nlinarith only [hab,sq_nonneg (2*a-c)])
  · exact (min_le_right _ _).trans (by nlinarith only [hba,sq_nonneg (2*b-c)])

/-- Three halves is the sharp uniform two-coordinate nonempty-energy factor, including all signs. -/
theorem twoCoordinateNonemptyEnergy_factor_iff (K : ℝ) :
    (∀ a b c : ℝ,min ((a+c)^2) ((b+c)^2) ≤ K*(a^2+b^2+c^2)) ↔ (3/2:ℝ) ≤ K := by
  constructor
  · intro hk
    have ht := hk 1 1 2
    norm_num at ht
    linarith
  · intro hk a b c
    exact (min_twoCoordinateNonemptyEnergy_le a b c).trans
      (mul_le_mul_of_nonneg_right hk (by positivity))
end RHTower
