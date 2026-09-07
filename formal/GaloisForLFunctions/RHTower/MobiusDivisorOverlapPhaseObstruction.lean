import GaloisForLFunctions.RHTower.TwoCoordinateMergerCeiling
import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreInterpolation
import GaloisForLFunctions.RHTower.MobiusDivisorGcdCrossObstruction

/-!
# Forced growth before the overlapping-prime phase ends

At cutoff eleven, processing primes three and seven leaves a nonzero joint
{2,5} fibre, yet both possible next mergers strictly increase energy. Analytic
channel boxes certify every sign. Both complete remaining orders nevertheless
retain a fixed positive reserve below the original diagonal.
-/
noncomputable section
open Finset
namespace RHTower

local notation "H11" => mobiusDivisorSelectionFibre 11 {3,7} ∅
local notation "A11" => mobiusDivisorSelectionFibre 11 {3,7} {2}
local notation "B11" => mobiusDivisorSelectionFibre 11 {3,7} {5}
local notation "C11" => mobiusDivisorSelectionFibre 11 {3,7} {2,5}

/-- The actual overlap state at eleven has exactly the two unprocessed primes two and five. -/
theorem mobiusDivisorSelectionPrimes_eleven_overlap_remaining :
    mobiusDivisorSelectionPrimes 11 \ {3,7} = {2,5} := by
  norm_num [mobiusDivisorSelectionPrimes,Finset.range_add_one,Finset.filter_insert,Finset.sdiff_eq_filter,Finset.filter_singleton]
  ext p
  simp [or_comm]

private theorem eleven_overlap_fibres :
    H11=mobiusDivisorDilationChannel 11 1+mobiusDivisorDilationChannel 11 3+mobiusDivisorDilationChannel 11 7 ∧
    A11=mobiusDivisorDilationChannel 11 2+mobiusDivisorDilationChannel 11 6 ∧
    B11=mobiusDivisorDilationChannel 11 5 ∧ C11=mobiusDivisorDilationChannel 11 10 := by
  have hp5 : Nat.Prime 5 := by norm_num
  have hp7 : Nat.Prime 7 := by norm_num
  have h6 : Nat.primeFactors 6=({2,3} : Finset ℕ) := by
    rw [show (6:ℕ)=2*3 by omega,Nat.primeFactors_mul (by omega) (by omega),
      Nat.prime_two.primeFactors,Nat.prime_three.primeFactors]
    simp
  have h10 : Nat.primeFactors 10=({2,5} : Finset ℕ) := by
    rw [show (10:ℕ)=2*5 by omega,Nat.primeFactors_mul (by omega) (by omega),
      Nat.prime_two.primeFactors,hp5.primeFactors]
    simp
  obtain ⟨h4,h8,h9,h11⟩ := mobiusDivisorDilationChannel_eleven_zero
  have hn0 : ({2,5} : Finset ℕ) ≠ ∅ := by
    intro he
    have hm := Finset.ext_iff.mp he 2
    norm_num at hm
  have hn2 : ({2,5} : Finset ℕ) ≠ {2} := by
    intro he
    have hm := Finset.ext_iff.mp he 5
    norm_num at hm
  have hn5 : ({2,5} : Finset ℕ) ≠ {5} := by
    intro he
    have hm := Finset.ext_iff.mp he 2
    norm_num at hm
  refine ⟨?_,?_,?_,?_⟩
  all_goals rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
  all_goals norm_num [sum_Icc_succ_top,h4,h8,h9,h11,h6,h10,hn0,hn2,hn5,Ne.symm hn0,Ne.symm hn2,Ne.symm hn5,Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton,Nat.prime_two.primeFactors,
    Nat.prime_three.primeFactors,hp5.primeFactors,hp7.primeFactors]

/-- Analytic boxes for all four retained overlap-state fibres; no experiment enters the proof. -/
theorem mobiusDivisorSelectionFibre_eleven_overlap_box :
    (-0.16 ≤ H11 ∧ H11 ≤ -0.11) ∧ (-0.08 ≤ A11 ∧ A11 ≤ -0.06) ∧
    (-0.15 ≤ B11 ∧ B11 ≤ -0.14) ∧ (0.023 ≤ C11 ∧ C11 ≤ 0.025) := by
  obtain ⟨hx,ha,hb,hc,hy,he,hz⟩ := mobiusDivisorDilationChannel_eleven_box
  obtain ⟨hH,hA,hB,hC⟩ := eleven_overlap_fibres
  rw [hH,hA,hB,hC]
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,
    ⟨by linarith,by linarith⟩,hz⟩

private theorem eleven_overlap_energies :
    mobiusDivisorSelectionEnergy 11 {3,7}=H11^2+A11^2+B11^2+C11^2 ∧
    mobiusDivisorSelectionEnergy 11 (insert 2 {3,7})=(H11+A11)^2+(B11+C11)^2 ∧
    mobiusDivisorSelectionEnergy 11 (insert 5 {3,7})=(H11+B11)^2+(A11+C11)^2 ∧
    mobiusDivisorSelectionEnergy 11 (insert 5 (insert 2 {3,7}))=(H11+A11+B11+C11)^2 := by
  have hrem := mobiusDivisorSelectionPrimes_eleven_overlap_remaining
  have hpair : ({5,2} : Finset ℕ)={2,5} := by ext x; simp [or_comm]
  refine ⟨?_,?_,?_,?_⟩
  · exact subsetLabelEnergy_two_remaining _ _ _ _ _ 2 5 (by omega) hrem
  · exact subsetLabelEnergy_insert_two_remaining _ _ _ _ _ 2 5 (by omega) hrem
  · simpa only [hpair,mobiusDivisorSelectionEnergy,mobiusDivisorSelectionFibre] using subsetLabelEnergy_insert_two_remaining
      (mobiusDivisorSelectionPrimes 11) (mobiusDivisorSelectionIndices 11) Nat.primeFactors
      (mobiusDivisorDilationChannel 11) {3,7} 5 2 (by omega) (hrem.trans hpair.symm)
  · exact subsetLabelEnergy_insert_insert_two_remaining _ _ _ _ _ 2 5 (by omega) hrem

private theorem eleven_overlap_growth_box (h a b c : ℝ)
    (hh : -0.16 ≤ h ∧ h ≤ -0.11) (ha : -0.08 ≤ a ∧ a ≤ -0.06)
    (hb : -0.15 ≤ b ∧ b ≤ -0.14) (hc : 0.023 ≤ c ∧ c ≤ 0.025) :
    1/200+(h^2+a^2+b^2+c^2)<(h+a)^2+(b+c)^2 ∧
    1/200+(h^2+a^2+b^2+c^2)<(h+b)^2+(a+c)^2 ∧
    (h+a)^2+(b+c)^2<(h+a+b+c)^2 ∧ (h+b)^2+(a+c)^2<(h+a+b+c)^2 := by
  have hha := mul_le_mul (show (0.11:ℝ) ≤ -h by linarith) (show (0.06:ℝ) ≤ -a by linarith)
    (by norm_num : (0:ℝ) ≤ 0.06) (by linarith : 0 ≤ -h)
  have hbc := mul_le_mul (show -b ≤ (0.15:ℝ) by linarith) hc.2
    (by linarith : 0 ≤ c) (by norm_num : (0:ℝ) ≤ 0.15)
  have hhb := mul_le_mul (show (0.11:ℝ) ≤ -h by linarith) (show (0.14:ℝ) ≤ -b by linarith)
    (by norm_num : (0:ℝ) ≤ 0.14) (by linarith : 0 ≤ -h)
  have hac := mul_le_mul (show -a ≤ (0.08:ℝ) by linarith) hc.2
    (by linarith : 0 ≤ c) (by norm_num : (0:ℝ) ≤ 0.08)
  have hlastp := mul_pos_of_neg_of_neg (show h+a<0 by linarith) (show b+c<0 by linarith)
  have hlastq := mul_pos_of_neg_of_neg (show h+b<0 by linarith) (show a+c<0 by linarith)
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [hha,hbc]
  · nlinarith only [hhb,hac]
  · nlinarith only [hlastp]
  · nlinarith only [hlastq]

/-- Both next mergers grow by a fixed positive amount, and both final mergers grow as well. -/
theorem mobiusDivisorSelectionEnergy_eleven_overlap_strict_growth :
    1/200+mobiusDivisorSelectionEnergy 11 {3,7}< mobiusDivisorSelectionEnergy 11 (insert 2 {3,7}) ∧
    1/200+mobiusDivisorSelectionEnergy 11 {3,7}< mobiusDivisorSelectionEnergy 11 (insert 5 {3,7}) ∧
    mobiusDivisorSelectionEnergy 11 (insert 2 {3,7})< mobiusDivisorSelectionEnergy 11 (insert 5 (insert 2 {3,7})) ∧
    mobiusDivisorSelectionEnergy 11 (insert 5 {3,7})< mobiusDivisorSelectionEnergy 11 (insert 5 (insert 2 {3,7})) := by
  obtain ⟨h0,h2,h5,hf⟩ := eleven_overlap_energies
  rw [h0,h2,h5,hf]
  obtain ⟨hh,ha,hb,hc⟩ := mobiusDivisorSelectionFibre_eleven_overlap_box
  exact eleven_overlap_growth_box H11 A11 B11 C11 hh ha hb hc

/-- The joint unprocessed-prime fibre is strictly positive while every next merger increases energy. -/
theorem mobiusDivisorSelection_eleven_overlap_stalled :
    0< C11 ∧ ∀ p ∈ mobiusDivisorSelectionPrimes 11 \ {3,7},
      mobiusDivisorSelectionEnergy 11 {3,7}< mobiusDivisorSelectionEnergy 11 (insert p {3,7}) := by
  obtain ⟨_,_,_,hc⟩ := mobiusDivisorSelectionFibre_eleven_overlap_box
  obtain ⟨h2,h5,_,_⟩ := mobiusDivisorSelectionEnergy_eleven_overlap_strict_growth
  refine ⟨by linarith,?_⟩
  intro p hp
  rw [mobiusDivisorSelectionPrimes_eleven_overlap_remaining] at hp
  simp only [mem_insert,mem_singleton] at hp
  rcases hp with rfl|rfl <;> linarith

/-- A nonzero two-prime overlap does not guarantee a contracting next prime. -/
theorem not_forall_overlap_state_has_contracting_prime :
    ¬∀ (M : ℕ) (P : Finset ℕ),
      (∃ p ∈ mobiusDivisorSelectionPrimes M \ P,∃ q ∈ mobiusDivisorSelectionPrimes M \ P,
        p≠q ∧ p*q< M ∧ 0< mobiusDivisorSelectionFibre M P {p,q}) →
      ∃ r ∈ mobiusDivisorSelectionPrimes M \ P,
        mobiusDivisorSelectionEnergy M (insert r P) ≤ mobiusDivisorSelectionEnergy M P := by
  intro hall
  have hstate := mobiusDivisorSelection_eleven_overlap_stalled
  obtain ⟨r,hr,he⟩ := hall 11 {3,7} ⟨2,by rw [mobiusDivisorSelectionPrimes_eleven_overlap_remaining]; simp,
    5,by rw [mobiusDivisorSelectionPrimes_eleven_overlap_remaining]; simp,by omega,by omega,hstate.1⟩
  exact (not_le_of_gt (hstate.2 r hr)) he

/-- Every completion subset of the stalled overlap state retains a fixed positive original-diagonal reserve. -/
theorem mobiusDivisorSelectionEnergy_eleven_overlap_reserve (R : Finset ℕ) (hR : R ⊆ {2,5}) :
    mobiusDivisorSelectionEnergy 11 ({3,7} ∪ R)+1/100 < mobiusDivisorSelectionEnergy 11 ∅ := by
  have hU : mobiusDivisorSelectionPrimes 11=insert 5 (insert 2 {3,7}) := by
    norm_num [mobiusDivisorSelectionPrimes,Finset.range_add_one,Finset.filter_insert]
    ext p
    simp only [mem_insert,mem_singleton]
    tauto
  have hmargin := sum_mobiusDivisorGcdCross_eleven_lt_neg_oneHundredth
  rw [sum_mobiusDivisorGcdCross,← mobiusDivisorSelectionEnergy_empty,
    ← mobiusDivisorSelectionEnergy_full,hU] at hmargin
  obtain ⟨h2,h5,h2f,h5f⟩ := mobiusDivisorSelectionEnergy_eleven_overlap_strict_growth
  have hsubset : mobiusDivisorSelectionEnergy 11 ({3,7} ∪ R) ≤
      mobiusDivisorSelectionEnergy 11 (insert 5 (insert 2 {3,7})) := by
    have hmem := mem_powerset.mpr hR
    norm_num [powerset_insert] at hmem
    rcases hmem with (rfl|rfl)|(rfl|rfl)
    all_goals simp only [union_empty,union_singleton,union_insert]
    all_goals try linarith
    · rw [insert_comm]
  linarith only [hsubset,hmargin]
end RHTower
