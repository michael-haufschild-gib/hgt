import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Radicals.Reduction
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Prime
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Observation.SingleLaw

/-! # An exclusive prime detects every nonzero rational inverse temperature -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic

open Finset Real
open _root_.HTGeometry (finiteGibbsPartition)

variable {I : Type*} [Fintype I]

private theorem ratio_obstruction {a : I → ℕ+} {p u v : ℕ} (hu : 0<u) (hv : 0<v)
    (hp : p.Prime) (x : I) (hx : p ∣ (a x : ℕ)) (other : ∀ y, y≠x → ¬p ∣ (a y : ℕ))
    (hn : 2<Fintype.card I) : ¬Coincides a ((u : ℝ)/v) := by
  let t := (u : ℝ)/v
  let b := fun i => exp (t*labelEnergy a i)
  have pn : (v : ℝ)≠0 := Nat.cast_ne_zero.mpr hv.ne'
  have power (i : I) : b i^v=((a i : ℕ) : ℝ)^u := by
    have ex : (v : ℝ)*(t*labelEnergy a i)=(u : ℝ)*labelEnergy a i := by unfold t; field_simp
    change exp (t*labelEnergy a i)^v=_
    rw [← exp_nat_mul,ex,exp_nat_mul]
    simp only [labelEnergy,energy,exp_log (Nat.cast_pos.mpr (a i).pos)]
  exact fun eq => Radicals.radical_obstruction hu hv power hp x hx other hn
    ((Radicals.thermal_condition_iff (labelEnergy a) t hn.le).mp eq)

private theorem positive_obstruction {a : I → ℕ+} {p : ℕ} {q : ℚ} (hq : 0<q)
    (hp : p.Prime) (x : I) (hx : p ∣ (a x : ℕ)) (other : ∀ y, y≠x → ¬p ∣ (a y : ℕ))
    (hn : 2<Fintype.card I) : ¬Coincides a q := by
  have pos := Rat.num_pos.mpr hq
  have num : (q.num.toNat : ℝ)=(q.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg pos.le
  have cast : (q : ℝ)=(q.num.toNat : ℝ)/q.den := by rw [num,Rat.cast_def]
  rw [cast]
  exact ratio_obstruction (by omega) q.den_pos hp x hx other hn

/-- No nonzero rational probe is blind to a logarithmic spectrum with at least
three levels and a prime factor confined to one label. -/
theorem rational_exclusive {a : I → ℕ+} {p : ℕ} (q : ℚ) (hp : p.Prime) (x : I)
    (hx : p ∣ (a x : ℕ)) (other : ∀ y, y≠x → ¬p ∣ (a y : ℕ))
    (hn : 2<Fintype.card I) : Coincides a q ↔ q=0 := by
  rcases lt_trichotomy q 0 with neg | rfl | pos
  · have off := positive_obstruction (neg_pos.mpr neg) hp x hx other hn
    have no : ¬Coincides a q := fun eq => off (by
      simpa only [Coincides,Rat.cast_neg,neg_neg] using eq.symm)
    exact iff_of_false no neg.ne
  · simp only [Coincides,Rat.cast_zero,neg_zero]
  · exact iff_of_false (positive_obstruction pos hp x hx other hn) pos.ne'

/-- Complete rational-temperature classification for a packet of distinct primes. -/
theorem rational_prime_packet (S : Finset Nat.Primes) (q : ℚ) :
    Coincides (elementary (S := S)) q ↔ q=0 ∨ S.card≤2 := by
  by_cases small : S.card≤2
  · exact iff_of_true (small_packet _ (by simpa only [Fintype.card_coe] using small) _) (Or.inr small)
  obtain ⟨p,hp⟩ := card_pos.mp (show 0<S.card by omega)
  let x : S := ⟨p,hp⟩
  rw [rational_exclusive (a := elementary) q p.property x (dvd_refl _) (elementary_exclusive x)
    (by rw [Fintype.card_coe]; omega),or_iff_left small]

/-- For up to four primes the classification extends to every real temperature. -/
theorem small_real_prime_packet (S : Finset Nat.Primes) (small : S.card≤4) (t : ℝ) :
    Coincides (elementary (S := S)) t ↔ t=0 ∨ S.card≤2 := by
  let E := labelEnergy (elementary (S := S))
  have hsize : Fintype.card S ≤ 4 := by simpa only [Fintype.card_coe] using small
  change finiteGibbsPartition t (centered E)=finiteGibbsPartition (-t) (centered E) ↔ _
  rw [Observation.small_single_test E t hsize]
  apply or_congr_right
  have h := Observation.small_single_test E 1 hsize
  have one : Reflects E ↔ Coincides (elementary (S := S)) (1 : ℝ) := by
    simpa only [one_ne_zero,false_or,Coincides,E] using h.symm
  rw [one]
  simpa only [Nat.cast_one,Nat.one_ne_zero,false_or] using prime_packet_iff S 1

private theorem order_one (E : I → ℝ) : HeatTests E 1 ↔
    finiteGibbsPartition 1 E = finiteGibbsPartition (-1) E := by
  constructor
  · intro h; simpa only [Nat.cast_one] using h 1 le_rfl le_rfl
  · intro h j lo hi
    obtain rfl : j=1 := le_antisymm hi lo
    simpa only [Nat.cast_one] using h

/-- One comparison on one joint probability list detects zero rational damping,
with balanced particle and hole counts and packets of size at most two as the exact exceptions. -/
theorem mixed_prime_reading (S : Finset Nat.Primes) (C : ℝ) (k l : ℕ) (q : ℚ) :
    let E := labelEnergy (elementary (S := S))
    let Y := centered (Observation.information
      (_root_.HTGeometry.finiteGibbsStateWeight (q : ℝ) (Mixed.mixedEnergy E C k l)))
    finiteGibbsPartition 1 Y=finiteGibbsPartition (-1) Y ↔ k=l ∨ q=0 ∨ S.card≤2 := by
  dsimp only
  rw [← order_one,Observation.centered_joint_information,Observation.mixed_tests,order_one,
    ← rational_prime_packet]
  apply or_congr_right
  unfold Coincides
  simp only [finiteGibbsPartition,neg_neg,neg_mul,one_mul]

#print axioms small_real_prime_packet
#print axioms mixed_prime_reading
#print axioms rational_exclusive
#print axioms rational_prime_packet

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic
