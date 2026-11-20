import GaloisForLFunctions.RestrictedFactorizationCalculus.TheRobustSignRadiusOfTheFirstRoughPrimeBand

/-!
# The smooth density read by relative errors

For an arbitrary polynomial cofactor band the minimum relative change
needed to erase the arithmetic reading tracks d/(2−d), where d is the
actual smooth proportion. This includes moving cofactor cutoffs and
nonnegative edits at all proper prime powers.
-/
noncomputable section
open Finset Filter ArithmeticFunction _root_.RHTower.CoprimeMobius
open scoped Classical
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The smallest coordinatewise relative error that can erase the reading. -/
def bandErasureRadius (a : ArithmeticFunction ℝ) (y X Z : ℕ) : ℝ :=
  |upperQuotientReading a y X Z|/primeBandVariation a y X Z

/-- The formula for the erasure radius includes rows whose every entry is zero. -/
theorem band_erasure_iff (a : ArithmeticFunction ℝ) (y X Z : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∃ e : ℕ → ℝ, (∀ q, |e q| ≤ δ) ∧ upperQuotientReading (perturbIncrements a e) y X Z=0) ↔
      bandErasureRadius a y X Z ≤ δ := by
  have h := possible_perturbed_band_readings a y X Z hδ 0
  simp only [zero_sub,abs_neg] at h
  refine Iff.trans (exists_congr fun e => and_congr_right fun _ => eq_comm) (h.trans ?_)
  unfold bandErasureRadius
  have bound : |upperQuotientReading a y X Z| ≤ primeBandVariation a y X Z :=
    abs_sum_le_sum_abs ..
  rcases eq_or_lt_of_le ((abs_nonneg _).trans bound) with zero|pos
  · rw [←zero,div_zero,mul_zero]
    rw [←zero] at bound
    exact iff_of_true bound hδ
  · exact (div_le_iff₀ pos).symm

private theorem stable_ratio {s v d η : ℝ} (d0 : 0 ≤ d) (d1 : d ≤ 1)
    (η0 : 0 ≤ η) (small : η ≤ 1/2) (hs : |s-d| ≤ η) (hv : |v-(2-d)| ≤ η) :
    abs (|s|/v-d/(2-d)) ≤ 4*η := by
  let u := d/(2-d)
  have den : 0 < 2-d := by linarith only [d1]
  have u0 : 0 ≤ u := div_nonneg d0 den.le
  have u1 : u ≤ 1 := (div_le_iff₀ den).mpr (by linarith only [d1])
  have vu : 1/2 ≤ v := by linarith only [(abs_le.mp hv).1,d1,small]
  have vp : 0 < v := lt_of_lt_of_le (by norm_num) vu
  have abs_s : abs (|s|-d) ≤ η := by
    obtain ⟨hl,hh⟩ := abs_le.mp hs
    have up : |s| ≤ d+η := abs_le.mpr ⟨by linarith only [hl,d0],by linarith only [hh]⟩
    apply abs_le.mpr
    exact ⟨by linarith only [hl,le_abs_self s],by linarith only [up]⟩
  have perturb : |u*((2-d)-v)| ≤ η := by
    rw [abs_mul,abs_of_nonneg u0,abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left hv u0).trans (by simpa using mul_le_mul_of_nonneg_right u1 η0)
  have ud : u*(2-d)=d := div_mul_cancel₀ _ den.ne'
  have num : abs (|s|-u*v) ≤ 2*η := by
    rw [show |s|-u*v=(|s|-d)+u*((2-d)-v) by linear_combination -ud]
    exact (abs_add_le ..).trans ((add_le_add abs_s perturb).trans_eq (by ring))
  change abs (|s|/v-u) ≤ _
  rw [←show (|s|-u*v)/v=|s|/v-u by rw [sub_div,mul_div_cancel_right₀ _ vp.ne'],
    abs_div,abs_of_pos vp,div_le_iff₀ vp]
  exact num.trans (by nlinarith only [mul_nonneg η0 (sub_nonneg.mpr vu)])

private def smoothFraction (y Z : ℕ) : ℝ :=
  ((RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card:ℝ)/(Z:ℝ)

private theorem smoothFraction_bounds {y Z : ℕ} (hZ : 0 < Z) :
    0 ≤ smoothFraction y Z ∧ smoothFraction y Z ≤ 1 := by
  have sub : RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z ⊆ Icc 1 Z :=
    fun _ h => mem_Icc.mpr (RHTower.Sieve.mem_smoothUpTo.mp h).1
  have card := card_le_card sub
  rw [Nat.card_Icc,Nat.add_sub_cancel] at card
  refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg Z),
    (div_le_iff₀ (Nat.cast_pos.mpr hZ : 0 < (Z:ℝ))).mpr ?_⟩
  rw [one_mul]
  exact_mod_cast card

/-- Uniformly on every polynomial cofactor band the relative erasure radius
is the smooth proportion divided by its complement in two, up to an error
tending to zero. The proper-power increments may vary with the observation. -/
theorem smooth_density_from_relative_robustness (j : ℕ) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ y : ℕ in atTop,∀ Z X : ℕ, y ≤ Z → Z ≤ y^j → y*Z ≤ X → ∀ a : ArithmeticFunction ℝ,
      (∀ q,0 ≤ a q) → (∀ q,|a q| ≤ vonMangoldt q) → (∀ p,p.Prime → a p=roughMangoldtWeight y p) →
      let d := ((RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card:ℝ)/(Z:ℝ)
      |bandErasureRadius a y X Z-d/(2-d)| ≤ ε := by
  let η := min (ε/4) (1/2)
  have ηp : 0 < η := lt_min (by positivity) (by norm_num)
  filter_upwards [total_variation_and_smooth_proportion j ηp,
    raw_prime_profile_at_every_interior_cut ηp,eventually_ge_atTop (1:ℕ)] with y variation charge yp
  intro Z X yz top room a nn dom same
  have zp := (show 0 < y from yp).trans_le yz
  have hx : 0 < (X:ℝ) := Nat.cast_pos.mpr ((Nat.mul_pos yp zp).trans_le room)
  have hz : 0 < (Z:ℝ) := Nat.cast_pos.mpr zp
  have fix (p : ℕ) (prime : p.Prime) : a p=roughOrdinaryPrimeWeight y p := by
    rw [same p prime,roughMangoldtWeight,roughRestriction_apply,vonMangoldt_apply_prime prime]
    have free : IsFree (RoughReading.banned y) p ↔ y < p := by
      simpa only [RoughReading.banned,Set.mem_setOf_eq,not_le] using isFree_prime (RoughReading.banned y) prime
    change _=(if p.Prime ∧ y < p then Real.log p else 0)
    simp only [prime,true_and,free]
  let b : ℝ := (RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card
  have hraw := charge Z X yz room a dom fix
  have hs : |upperQuotientReading a y X Z/(X:ℝ)-b/(Z:ℝ)| ≤ η := by
    rw [←show (upperQuotientReading a y X Z-(X:ℝ)/Z*b)/(X:ℝ)=
        upperQuotientReading a y X Z/(X:ℝ)-b/Z by field_simp [hx.ne',hz.ne'],
      abs_div,abs_of_pos hx,div_le_iff₀ hx]
    exact hraw
  have bounds := smoothFraction_bounds (y:=y) zp
  have radius := stable_ratio bounds.1 bounds.2 ηp.le (min_le_right ..) hs
    (variation Z X yz top room a nn dom same)
  rw [abs_div,abs_of_pos hx,div_div_div_cancel_right₀ hx.ne'] at radius
  exact radius.trans (by linarith only [show η ≤ ε/4 from min_le_left ..])

end GaloisForLFunctions.RestrictedFactorizationCalculus
