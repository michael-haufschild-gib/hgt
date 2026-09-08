import GaloisForLFunctions.RHTower.MobiusDivisorCoupledTwoSourceCone
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

A fixed weight on the head square cannot provide a contracting next operation
at every actual state, already at cutoff twenty-five. Two source states have
exact disjoint intervals of weights permitting their complete remaining orders.
The weighted potential remains coercive at every fixed positive weight;
existence of suitable complete paths from the initial source remains open.
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

/-- Retained energy with a fixed weight on the actual empty-label head square. -/
def mobiusDivisorWeightedHeadEnergy (α : ℝ) (M : ℕ) (P : Finset ℕ) : ℝ :=
  mobiusDivisorNonemptyEnergy M P+α*(mobiusDivisorSelectionFibre M P ∅)^2

/-- Every positive head weight retains uniform control of the complete energy. -/
theorem mobiusDivisorWeightedHeadEnergy_bounds (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (M : ℕ) (P : Finset ℕ) :
    0 ≤ mobiusDivisorWeightedHeadEnergy α M P ∧
    α*mobiusDivisorSelectionEnergy M P ≤ mobiusDivisorWeightedHeadEnergy α M P ∧
      mobiusDivisorWeightedHeadEnergy α M P ≤ mobiusDivisorSelectionEnergy M P := by
  have hn : 0 ≤ mobiusDivisorWeightedHeadEnergy α M P :=
    add_nonneg (mobiusDivisorNonemptyEnergy_nonneg M P) (mul_nonneg hα0 (sq_nonneg _))
  refine ⟨hn,?_⟩
  have hv := mul_nonneg (sub_nonneg.mpr hα1) (mobiusDivisorNonemptyEnergy_nonneg M P)
  have hh := mul_nonneg (sub_nonneg.mpr hα1) (sq_nonneg (mobiusDivisorSelectionFibre M P ∅))
  unfold mobiusDivisorWeightedHeadEnergy mobiusDivisorNonemptyEnergy at *
  constructor <;> nlinarith only [hv,hh]

/-- Exact head weight at which the favorable five-then-three completion starts to contract. -/
def mobiusDivisorTwentyFiveWeightThreshold : ℝ :=
  let H := mobiusDivisorSelectionFibre 25 mobiusDivisorTwentyFiveCore ∅
  let A := mobiusDivisorSelectionFibre 25 mobiusDivisorTwentyFiveCore {3}
  let B := mobiusDivisorSelectionFibre 25 mobiusDivisorTwentyFiveCore {5}
  let C := mobiusDivisorSelectionFibre 25 mobiusDivisorTwentyFiveCore {3,5}
  (2*A*C-B^2)/(H^2-(H+B)^2)

private def sevenCore : Finset ℕ := mobiusDivisorSelectionPrimes 25\{7}
private def t : ℝ := -divisorUnsignedDilationChannel 25 7+
  divisorUnsignedDilationChannel 25 14+divisorUnsignedDilationChannel 25 21
private def g : ℝ := h+a+b+c-t
private def w0 (α : ℝ) : ℝ := α*h^2+a^2+b^2+c^2
private def w3 (α : ℝ) : ℝ := α*(h+a)^2+(b+c)^2
private def w5 (α : ℝ) : ℝ := α*(h+b)^2+(a+c)^2
private def wf (α : ℝ) : ℝ := α*(h+a+b+c)^2

private lemma weighted_values (α : ℝ) :
    mobiusDivisorWeightedHeadEnergy α 25 mobiusDivisorTwentyFiveCore=w0 α ∧
    mobiusDivisorWeightedHeadEnergy α 25 (insert 3 mobiusDivisorTwentyFiveCore)=w3 α ∧
    mobiusDivisorWeightedHeadEnergy α 25 (insert 5 mobiusDivisorTwentyFiveCore)=w5 α ∧
    mobiusDivisorWeightedHeadEnergy α 25 (insert 3 (insert 5 mobiusDivisorTwentyFiveCore))=wf α := by
  have hf : mobiusDivisorSelectionFibre 25 (insert 3 (insert 5 mobiusDivisorTwentyFiveCore)) ∅=h+a+b+c := by
    rw [mobiusDivisorSelectionFibre_insert,mobiusDivisorSelectionFibre_insert,
      mobiusDivisorSelectionFibre_insert]
    simp only [notMem_empty,if_false,insert_empty_eq,heads.1,heads.2.1,heads.2.2.1]
    have hn : 5∉({3}:Finset ℕ) := by norm_num
    have hp : ({5,3}:Finset ℕ)={3,5} := by ext p; simp [or_comm]
    simp [hn,hp,heads.2.2.2]
    ring
  have h3 : mobiusDivisorSelectionFibre 25 (insert 3 mobiusDivisorTwentyFiveCore) ∅=h+a := by
    rw [mobiusDivisorSelectionFibre_insert]; simp [heads.1,heads.2.1]
  have h5 : mobiusDivisorSelectionFibre 25 (insert 5 mobiusDivisorTwentyFiveCore) ∅=h+b := by
    rw [mobiusDivisorSelectionFibre_insert]; simp [heads.1,heads.2.2.1]
  unfold mobiusDivisorWeightedHeadEnergy
  rw [nonempty_values.1,nonempty_values.2.1,nonempty_values.2.2,heads.1,h3,h5,hf]
  refine ⟨by dsimp [w0]; ring,by dsimp [w3]; ring,by dsimp [w5]; ring,?_⟩
  unfold mobiusDivisorNonemptyEnergy
  rw [Finset.insert_comm 3 5,energies.2.2.2]
  rw [← Finset.insert_comm 3 5,hf]
  dsimp [wf]
  ring

private lemma head_square_decreases :
    (h+a)^2 < h^2 ∧ (h+b)^2 < h^2 ∧
    (h+a+b+c)^2 < (h+a)^2 ∧ (h+a+b+c)^2 < (h+b)^2 := by
  obtain ⟨hh,ha,hb,hc⟩ := boxes
  have h3 := mul_neg_of_pos_of_neg (show 0 < a by linarith) (show 2*h+a < 0 by linarith)
  have h5 := mul_neg_of_pos_of_neg (show 0 < b by linarith) (show 2*h+b < 0 by linarith)
  have hf3 := mul_neg_of_pos_of_neg (show 0 < b+c by linarith) (show 2*(h+a)+b+c < 0 by linarith)
  have hf5 := mul_neg_of_pos_of_neg (show 0 < a+c by linarith) (show 2*(h+b)+a+c < 0 by linarith)
  exact ⟨by nlinarith only [h3],by nlinarith only [h5],by nlinarith only [hf3],by nlinarith only [hf5]⟩

private lemma weighted_small_increases {α : ℝ} (hα : α ≤ 1/20) :
    w0 α < w3 α ∧ w0 α < w5 α := by
  obtain ⟨hh,ha,hb,hc⟩ := boxes
  have hha := mul_le_mul (show -h ≤ (0.75:ℝ) by linarith) ha.2
    (by linarith : 0 ≤ a) (by norm_num : (0:ℝ) ≤ 0.75)
  have hhb := mul_le_mul (show -h ≤ (0.75:ℝ) by linarith) hb.2
    (by linarith : 0 ≤ b) (by norm_num : (0:ℝ) ≤ 0.75)
  have hm3 := mul_nonneg (show 0 ≤ 1/20-α by linarith) (sub_nonneg.mpr head_square_decreases.1.le)
  have hm5 := mul_nonneg (show 0 ≤ 1/20-α by linarith) (sub_nonneg.mpr head_square_decreases.2.1.le)
  obtain ⟨hv3,hv5,_,_,_,_,_⟩ := arithmetic_inequalities
  dsimp [w0,w3,w5]
  constructor
  · nlinarith only [hha,hm3,hv3,sq_nonneg a]
  · nlinarith only [hhb,hm5,hv5,sq_nonneg b]

private lemma weighted_five_at_fifth : w5 (1/5) < w0 (1/5) := by
  obtain ⟨hh,ha,hb,hc⟩ := boxes
  have hac := mul_le_mul ha.2 hc.2 (by linarith : 0 ≤ c) (by norm_num : (0:ℝ) ≤ 0.010)
  have hhb := mul_le_mul (show (0.73:ℝ) ≤ -h by linarith) hb.1
    (by norm_num : (0:ℝ) ≤ 0.013) (by linarith : 0 ≤ -h)
  have hb2 := mul_le_mul hb.1 hb.1 (by norm_num : (0:ℝ) ≤ 0.013) (by linarith : 0 ≤ b)
  dsimp [w5,w0]
  nlinarith only [hac,hhb,hb2]

private lemma weighted_five_preferred {α : ℝ} (hα : 0 ≤ α) : w5 α  <  w3 α := by
  obtain ⟨hh,ha,hb,hc⟩ := boxes
  have hs : α*(2*h+a+b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα (by linarith)
  have hm := mul_pos_of_neg_of_neg (show a-b < 0 by linarith)
    (show α*(2*h+a+b)-(a+b+2*c) < 0 by linarith)
  dsimp [w5,w3]
  nlinarith only [hm]

private lemma weighted_final_decreases {α : ℝ} (hα : 0 ≤ α) : wf α < w3 α ∧ wf α < w5 α := by
  obtain ⟨hh,ha,hb,hc⟩ := boxes
  have h3 := mul_le_mul_of_nonneg_left head_square_decreases.2.2.1.le hα
  have h5 := mul_le_mul_of_nonneg_left head_square_decreases.2.2.2.le hα
  have hbcsq : 0 < (b+c)^2 := sq_pos_of_pos (by linarith)
  have hacsq : 0 < (a+c)^2 := sq_pos_of_pos (by linarith)
  dsimp [wf,w3,w5]
  exact ⟨by linarith only [h3,hbcsq],by linarith only [h5,hacsq]⟩

private lemma threshold_eq : mobiusDivisorTwentyFiveWeightThreshold=(2*a*c-b^2)/(h^2-(h+b)^2) := by
  simp [mobiusDivisorTwentyFiveWeightThreshold,heads.1,heads.2.1,heads.2.2.1,heads.2.2.2]

/-- The favorable completion requires weight strictly above one twentieth and starts strictly below one fifth. -/
theorem mobiusDivisorTwentyFiveWeightThreshold_bounds :
    1/20 < mobiusDivisorTwentyFiveWeightThreshold ∧ mobiusDivisorTwentyFiveWeightThreshold < 1/5 := by
  rw [threshold_eq]
  have hd : 0 < h^2-(h+b)^2 := sub_pos.mpr head_square_decreases.2.1
  constructor
  · apply (lt_div_iff₀ hd).mpr
    have hw := (weighted_small_increases (α:=(1/20:ℝ)) le_rfl).2
    dsimp [w5,w0] at hw
    nlinarith only [hw]
  · apply (div_lt_iff₀ hd).mpr
    have hw := weighted_five_at_fifth
    dsimp [w5,w0] at hw
    nlinarith only [hw]

/-- Exact feasibility of both complete remaining orders under a fixed nonnegative head weight; prime five is uniformly the better first choice. -/
theorem mobiusDivisorTwentyFive_weighted_completion_iff (α : ℝ) (hα : 0 ≤ α) :
    ((mobiusDivisorWeightedHeadEnergy α 25 (insert 3 mobiusDivisorTwentyFiveCore) ≤
        mobiusDivisorWeightedHeadEnergy α 25 mobiusDivisorTwentyFiveCore ∧
      mobiusDivisorWeightedHeadEnergy α 25 (insert 3 (insert 5 mobiusDivisorTwentyFiveCore)) ≤
        mobiusDivisorWeightedHeadEnergy α 25 (insert 3 mobiusDivisorTwentyFiveCore)) ∨
     (mobiusDivisorWeightedHeadEnergy α 25 (insert 5 mobiusDivisorTwentyFiveCore) ≤
        mobiusDivisorWeightedHeadEnergy α 25 mobiusDivisorTwentyFiveCore ∧
      mobiusDivisorWeightedHeadEnergy α 25 (insert 3 (insert 5 mobiusDivisorTwentyFiveCore)) ≤
        mobiusDivisorWeightedHeadEnergy α 25 (insert 5 mobiusDivisorTwentyFiveCore))) ↔
      mobiusDivisorTwentyFiveWeightThreshold ≤ α := by
  rw [(weighted_values α).1,(weighted_values α).2.1,(weighted_values α).2.2.1,
    (weighted_values α).2.2.2,threshold_eq,
    div_le_iff₀ (sub_pos.mpr head_square_decreases.2.1)]
  have hfinal := weighted_final_decreases hα
  have hpref := weighted_five_preferred hα
  constructor
  · rintro (⟨h3,_⟩|⟨h5,_⟩)
    · have hw := hpref.le.trans h3
      dsimp [w5,w0] at hw
      nlinarith only [hw]
    · dsimp [w5,w0] at h5
      nlinarith only [h5]
  · intro hw
    right
    refine ⟨?_,hfinal.2.le⟩
    dsimp [w5,w0]
    nlinarith only [hw]

private lemma seven_remaining : mobiusDivisorSelectionPrimes 25\sevenCore={7} := by
  have hp : 7∈mobiusDivisorSelectionPrimes 25 := by norm_num [mobiusDivisorSelectionPrimes]
  ext p
  simp [sevenCore]
  intro he
  subst p
  exact hp

private lemma seven_fibre : mobiusDivisorSelectionFibre 25 sevenCore {7}=t := by
  have hf := (mobiusDivisorSelectionFibre_one_remaining 25 7 sevenCore (by norm_num)
    (by simp [sevenCore]) (by exact subset_rfl)).2
  rw [hf]
  have hs7 := signed_prime 7 (by norm_num)
  have hs14 := signed_pair 2 7 Nat.prime_two (by norm_num) (by omega)
  have hs21 := signed_pair 3 7 Nat.prime_three (by norm_num) (by omega)
  norm_num only at hs14 hs21
  norm_num [mobiusDivisorLastPrimeDivisible,sum_filter,Finset.sum_Icc_succ_top,hs7,hs14,hs21,t]

private lemma total_value : (∑ d∈Icc 1 25,mobiusDivisorDilationChannel 25 d)=h+a+b+c := by
  have hs := mobiusDivisorSelectionFibre_sum 25 mobiusDivisorTwentyFiveCore
  simp_rw [source_profile] at hs
  have h3 : ({3}:Finset ℕ)∈(mobiusDivisorSelectionPrimes 25).powerset := by
    norm_num [mem_powerset,mobiusDivisorSelectionPrimes]
  have h5 : ({5}:Finset ℕ)∈(mobiusDivisorSelectionPrimes 25).powerset := by
    norm_num [mem_powerset,mobiusDivisorSelectionPrimes]
  have h35 : ({3,5}:Finset ℕ)∈(mobiusDivisorSelectionPrimes 25).powerset := by
    norm_num [mem_powerset,mobiusDivisorSelectionPrimes,Finset.insert_subset_iff]
  simpa [profile,sum_add_distrib,h3,h5,h35] using hs.symm

private lemma seven_head : mobiusDivisorSelectionFibre 25 sevenCore ∅=g := by
  have hf := mobiusDivisorSelectionFibre_one_remaining 25 7 sevenCore (by norm_num)
    (by simp [sevenCore]) (by exact subset_rfl)
  have hs := mobiusDivisorLastPrime_add_eq_total 25 7
  rw [← hf.1,← hf.2,seven_fibre,total_value] at hs
  dsimp [g]
  linarith only [hs]

private lemma seven_weighted_values (α : ℝ) :
    mobiusDivisorWeightedHeadEnergy α 25 sevenCore=α*g^2+t^2 ∧
    mobiusDivisorWeightedHeadEnergy α 25 (insert 7 sevenCore)=α*(g+t)^2 := by
  have hq : mobiusDivisorSelectionEnergy 25 sevenCore=g^2+t^2 := by
    unfold mobiusDivisorSelectionEnergy
    rw [subsetLabelEnergy_remaining,seven_remaining]
    change (∑ R∈({7}:Finset ℕ).powerset,(mobiusDivisorSelectionFibre 25 sevenCore R)^2)=_
    simpa only [powerset_empty,sum_singleton,insert_empty_eq,seven_head,seven_fibre] using
      sum_powerset_insert (notMem_empty (7:ℕ)) (fun R => (mobiusDivisorSelectionFibre 25 sevenCore R)^2)
  have hf : mobiusDivisorSelectionFibre 25 (insert 7 sevenCore) ∅=g+t := by
    rw [mobiusDivisorSelectionFibre_insert]; simp [seven_head,seven_fibre]
  have hqf : mobiusDivisorSelectionEnergy 25 (insert 7 sevenCore)=(g+t)^2 := by
    unfold mobiusDivisorSelectionEnergy
    rw [subsetLabelEnergy_remaining,sdiff_insert,seven_remaining]
    simp only [erase_singleton,powerset_empty,sum_singleton]
    change (mobiusDivisorSelectionFibre 25 (insert 7 sevenCore) ∅)^2=_
    rw [hf]
  unfold mobiusDivisorWeightedHeadEnergy mobiusDivisorNonemptyEnergy
  rw [hq,seven_head,hqf,hf]
  constructor  <;> ring

private lemma seven_large_increases {α : ℝ} (hα : 1/20 ≤ α) :
    mobiusDivisorWeightedHeadEnergy α 25 sevenCore  <
      mobiusDivisorWeightedHeadEnergy α 25 (insert 7 sevenCore) := by
  obtain ⟨hh,ha,hb,hc⟩ := boxes
  have ht : (-0.020:ℝ) ≤ t ∧ t ≤ -0.017 := divisorUnsignedDilationChannel_twentyFive_seven_leaf_box
  have hg : g ≤ (-0.51:ℝ) := by dsimp [g]; linarith only [hh.2,ha.2,hb.2,hc.2,ht.1]
  have hgt := mul_le_mul (show (0.51:ℝ) ≤ -g by linarith) (show (0.017:ℝ) ≤ -t by linarith)
    (by norm_num : (0:ℝ) ≤ 0.017) (by linarith : 0 ≤ -g)
  have ht2 := mul_le_mul (show -t ≤ (0.020:ℝ) by linarith) (show -t ≤ (0.020:ℝ) by linarith)
    (by linarith : 0 ≤ -t) (by norm_num : (0:ℝ) ≤ 0.020)
  have hd : 0 ≤ (g+t)^2-g^2 := by nlinarith only [hgt,sq_nonneg t]
  have hm := mul_nonneg (show 0 ≤ α-1/20 by linarith) hd
  rw [(seven_weighted_values α).1,(seven_weighted_values α).2]
  nlinarith only [hgt,ht2,hm]

/-- No real fixed head weight provides a nonincreasing next operation at every proper actual state, already at one cutoff. -/
theorem mobiusDivisorWeightedHeadEnergy_twentyFive_local_obstruction (α : ℝ) :
    ∃ P : Finset ℕ,P ⊆ mobiusDivisorSelectionPrimes 25 ∧
      (mobiusDivisorSelectionPrimes 25\P).Nonempty ∧
      ∀ p∈mobiusDivisorSelectionPrimes 25\P,
        mobiusDivisorWeightedHeadEnergy α 25 P  <  mobiusDivisorWeightedHeadEnergy α 25 (insert p P) := by
  by_cases hα : α ≤ 1/20
  · refine ⟨mobiusDivisorTwentyFiveCore,?_,?_,?_⟩
    · norm_num [mobiusDivisorTwentyFiveCore,mobiusDivisorSelectionPrimes,Finset.insert_subset_iff]
    · rw [remaining]; exact ⟨3,by simp⟩
    · intro p hp
      rw [remaining] at hp
      rcases mem_insert.mp hp with rfl|hp
      · rw [(weighted_values α).1,(weighted_values α).2.1]
        exact (weighted_small_increases hα).1
      · have he : p=5 := mem_singleton.mp hp
        subst p
        rw [(weighted_values α).1,(weighted_values α).2.2.1]
        exact (weighted_small_increases hα).2
  · refine ⟨sevenCore,sdiff_subset,?_,?_⟩
    · rw [seven_remaining]; exact singleton_nonempty 7
    · intro p hp
      rw [seven_remaining,mem_singleton] at hp
      subst p
      exact seven_large_increases (le_of_not_ge hα)

/-- Exact largest head weight permitting the literal final-seven absorption at cutoff twenty-five. -/
def mobiusDivisorTwentyFiveSevenWeightThreshold : ℝ :=
  let P := mobiusDivisorSelectionPrimes 25\{7}
  let H := mobiusDivisorSelectionFibre 25 P ∅
  let A := mobiusDivisorSelectionFibre 25 P {7}
  A^2/((H+A)^2-H^2)

private lemma seven_denominator_pos : 0 < (g+t)^2-g^2 := by
  obtain ⟨hh,ha,hb,hc⟩ := boxes
  have ht : (-0.020:ℝ) ≤ t ∧ t ≤ -0.017 := divisorUnsignedDilationChannel_twentyFive_seven_leaf_box
  have hg : g < 0 := by dsimp [g]; linarith
  have hgt := mul_pos_of_neg_of_neg hg (show t < 0 by linarith)
  nlinarith only [hgt,sq_nonneg t]

private lemma seven_threshold_eq : mobiusDivisorTwentyFiveSevenWeightThreshold=t^2/((g+t)^2-g^2) := by
  change (mobiusDivisorSelectionFibre 25 sevenCore {7})^2/
    ((mobiusDivisorSelectionFibre 25 sevenCore ∅+mobiusDivisorSelectionFibre 25 sevenCore {7})^2-
      (mobiusDivisorSelectionFibre 25 sevenCore ∅)^2)=_
  rw [seven_head,seven_fibre]

/-- The terminal-seven state admits positive head weights only below a threshold strictly smaller than one twentieth. -/
theorem mobiusDivisorTwentyFiveSevenWeightThreshold_bounds :
    0 < mobiusDivisorTwentyFiveSevenWeightThreshold ∧ mobiusDivisorTwentyFiveSevenWeightThreshold < 1/20 := by
  rw [seven_threshold_eq]
  have htupper : t ≤ (-0.017:ℝ) := divisorUnsignedDilationChannel_twentyFive_seven_leaf_box.2
  have ht : t < 0 := by linarith only [htupper]
  have ht2 : 0 < t^2 := sq_pos_of_ne_zero (ne_of_lt ht)
  refine ⟨div_pos ht2 seven_denominator_pos,(div_lt_iff₀ seven_denominator_pos).mpr ?_⟩
  have hw := seven_large_increases (α:=(1/20:ℝ)) le_rfl
  rw [(seven_weighted_values (1/20)).1,(seven_weighted_values (1/20)).2] at hw
  nlinarith only [hw]

/-- Exact admissible-weight classification for the other actual state; its interval is disjoint from the two-prime completion interval. -/
theorem mobiusDivisorTwentyFive_seven_weighted_completion_iff (α : ℝ) :
    mobiusDivisorWeightedHeadEnergy α 25 (insert 7 (mobiusDivisorSelectionPrimes 25\{7})) ≤
      mobiusDivisorWeightedHeadEnergy α 25 (mobiusDivisorSelectionPrimes 25\{7}) ↔
    α ≤ mobiusDivisorTwentyFiveSevenWeightThreshold := by
  change mobiusDivisorWeightedHeadEnergy α 25 (insert 7 sevenCore) ≤
    mobiusDivisorWeightedHeadEnergy α 25 sevenCore ↔ _
  rw [(seven_weighted_values α).1,(seven_weighted_values α).2,seven_threshold_eq,
    le_div_iff₀ seven_denominator_pos]
  constructor <;> intro hw <;> nlinarith only [hw]

end RHTower
