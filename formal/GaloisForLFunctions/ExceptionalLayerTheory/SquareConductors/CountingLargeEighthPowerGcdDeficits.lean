import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.HarmonicSuperlevelCounting
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheGcdDeficitAtTheEighthPowerEndpoints

/-!
# Counting large eighth-power shortfalls

The eighth-power half-step law orders the shortfalls asymptotically even
though the prime readings need not be monotone. The number above 1/t is
asymptotic to t/2. Deleting the proper powers changes the classification
of only o(t) indices, including indices arbitrarily far along the grid.
-/

noncomputable section
open Filter Set
open scoped Topology
open GaloisForLFunctions.HarmonicSuperlevel

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Signed eighth-power shortfall after selecting either ordinary primes
or the full Mangoldt octave. The zero index has no asymptotic effect. -/
def eighthReading (ordinary : Bool) (m : ℕ) : ℝ :=
  Real.log 2 - (if ordinary then eighthOrdinaryPrimePrice m
    else Real.log (octaveGcdProduct (m^8) (m^9))) / (m:ℝ)^9

/-- Each reading has harmonic coefficient one half even before clipping. -/
theorem eighth_reading_harmonic_limit (ordinary : Bool) :
    Tendsto (fun m : ℕ => (m:ℝ)*eighthReading ordinary m) atTop (𝓝 (1/2)) := by
  let δ : ℝ := 1/6000
  have hp : 0 < δ := by norm_num [δ]
  have hδ : δ < 1/3000 := by norm_num [δ]
  have hrow : ∃ B : ℝ, 0 ≤ B ∧ ∀ {m : ℕ}, 2 ≤ m →
      |eighthReading ordinary m - 1/(2*(m:ℝ))| ≤ B*(m:ℝ)^(-1-δ) := by
    cases ordinary
    · exact eighth_power_gcd_deficit_half_step hδ
    · exact eighth_ordinary_prime_deficit_half_step hδ
  obtain ⟨B,_,hB⟩ := hrow
  have h := ((tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop).const_mul B
  rw [mul_zero] at h
  have hb : ∀ᶠ m : ℕ in atTop, |(m:ℝ)*eighthReading ordinary m - 1/2| ≤ B*(m:ℝ)^(-δ) := by
    filter_upwards [eventually_ge_atTop 2] with m hm
    have hm₀ : 0 < (m:ℝ) := Nat.cast_pos.mpr (by omega)
    have hu := mul_le_mul_of_nonneg_left (hB hm) hm₀.le
    have he : (m:ℝ) * (m:ℝ)^(-1-δ) = (m:ℝ)^(-δ) := by
      conv_lhs => lhs; rw [← Real.rpow_one (m:ℝ)]
      rw [← Real.rpow_add hm₀]
      congr 1; ring
    rw [mul_left_comm _ B,he] at hu
    have hdiv : (m:ℝ)*(1/(2*(m:ℝ))) = 1/2 := by field_simp
    calc |(m:ℝ)*eighthReading ordinary m - 1/2| =
           |(m:ℝ)*(eighthReading ordinary m - 1/(2*(m:ℝ)))| := by rw [mul_sub,hdiv]
         _ = (m:ℝ)*|eighthReading ordinary m - 1/(2*(m:ℝ))| := by rw [abs_mul,abs_of_pos hm₀]
         _ ≤ _ := hu
  have hlo := h.neg.const_add (1/2:ℝ)
  have hhi := h.const_add (1/2:ℝ)
  rw [neg_zero,add_zero] at hlo
  rw [add_zero] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi <;> filter_upwards [hb] with m hm
  · exact (le_sub_iff_add_le'.mp (abs_le.mp hm).1)
  · exact (sub_le_iff_le_add'.mp (abs_le.mp hm).2)

/-- The Weyl count is finite at every threshold and its density is exactly
one half for both arithmetic readings. -/
theorem eighth_shortfall_counting_law (ordinary : Bool) :
    (∀ t : ℝ, 0 < t → {m : ℕ | 1 < t*eighthReading ordinary m}.Finite) ∧
    Tendsto (fun t : ℝ => (count (eighthReading ordinary) t : ℝ)/t) atTop (𝓝 (1/2)) :=
  harmonic_counting_law (by norm_num) (eighth_reading_harmonic_limit ordinary)

private theorem reading_order (m : ℕ) : eighthReading false m ≤ eighthReading true m := by
  cases m with
  | zero => simp [eighthReading]
  | succ m =>
    have h := (octave_gcd_product_ordinary_primes (pow_pos (Nat.succ_pos m) 8) ((m+1)^9)).1
    exact sub_le_sub_left (div_le_div_of_nonneg_right (sub_nonneg.mp h) (by positivity)) _

/-- Proper prime powers change the superlevel decision on a set of
asymptotically zero density at the counting scale. -/
theorem proper_power_switch_count :
    Tendsto (fun t : ℝ => ({m : ℕ | 1 < t*eighthReading true m ∧ t*eighthReading false m ≤ 1}.ncard : ℝ)/t)
      atTop (𝓝 0) := by
  have hp := eighth_shortfall_counting_law true
  have hg := eighth_shortfall_counting_law false
  have h := hp.2.sub hg.2
  rw [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  let P := {m : ℕ | 1 < t*eighthReading true m}
  let G := {m : ℕ | 1 < t*eighthReading false m}
  have hsub : G ⊆ P := fun m hm => lt_of_lt_of_le hm (mul_le_mul_of_nonneg_left (reading_order m) ht.le)
  have he : {m : ℕ | 1 < t*eighthReading true m ∧ t*eighthReading false m ≤ 1} = P \ G := by
    ext m
    simp only [P,G,mem_sdiff,mem_setOf_eq,not_lt]
  rw [he,ncard_sdiff' hsub (hp.1 t ht),Nat.cast_sub (ncard_le_ncard hsub (hp.1 t ht)),sub_div]
  rfl

#print axioms eighth_shortfall_counting_law
#print axioms proper_power_switch_count

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
