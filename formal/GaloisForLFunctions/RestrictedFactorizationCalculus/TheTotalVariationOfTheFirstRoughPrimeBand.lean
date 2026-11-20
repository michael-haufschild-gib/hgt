import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeOnlyQuotientRowsOfTheRoughInterior
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheLogarithmicThresholdForRoughMobiusCharge
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSmoothProportionAtEveryInteriorQuotientCut

/-!
# Positive charge and total variation of the first rough prime band

Through the square of the deletion threshold the positive part of the
rough Möbius prefix is either zero or one. All large quotients see the
unit coefficient. The prime number theorem pays for the unobserved part
of the positive mass. Subtracting the known signed charge then recovers
the negative mass and the total variation of the same arithmetic row.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical Topology
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev roughPrefix (y m : ℕ) := coprimeMoebiusSum (primorial y) m

/-- Total positive mass of the quotient coefficients with nonnegative input weights. -/
def positivePrimeBandMass (a : ArithmeticFunction ℝ) (y X Z : ℕ) :=
  ∑ q∈Ioc (X/Z) X,a q*max (roughPrefix y (X/q)) 0

/-- Sum of the absolute weighted quotient coefficients. -/
def primeBandVariation (a : ArithmeticFunction ℝ) (y X Z : ℕ) :=
  ∑ q∈Ioc (X/Z) X,|a q*roughPrefix y (X/q)|

private theorem unit_prefix {y m : ℕ} (hm : 0 < m) (hle : m ≤ y) : roughPrefix y m=1 := by
  change coprimeMoebiusSum (primorial y) m = 1
  rw [rough_prefix_before_composites hm (hle.trans (Nat.le_self_pow (by decide : 2≠0) y))]
  have hz : RHTower.Sieve.bigPrimeSet y m=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hm,_⟩ := mem_filter.mp hi
    have := mem_Icc.mp hm
    omega
  simp [hz]

private theorem positive_sandwich (a : ArithmeticFunction ℝ) {y Z X : ℕ}
    (hpos : 0 < y) (hyZ : y ≤ Z) (hpre : ∀ m : ℕ,0 < m → m ≤ Z → roughPrefix y m ≤ 1) (ha : ∀ n,0 ≤ a n) :
    (∑ q∈Ioc (X/y) X,a q) ≤ positivePrimeBandMass a y X Z ∧
      positivePrimeBandMass a y X Z ≤ ∑ q∈Ioc (X/Z) X,a q := by
  have hZpos := hpos.trans_le hyZ
  have hsub : Ioc (X/y) X⊆Ioc (X/Z) X :=
    Ioc_subset_Ioc_left (Nat.div_le_div_left hyZ hpos)
  constructor
  · calc _ = ∑ q∈Ioc (X/y) X,a q*max (roughPrefix y (X/q)) 0 := by
           apply sum_congr rfl
           intro q hq
           obtain ⟨hl,hu⟩ := mem_Ioc.mp hq
           have hq' : 0 < q := (Nat.zero_le _).trans_lt hl
           have hlt := (Nat.div_lt_iff_lt_mul hpos).mp hl
           have hfloor : X/q < y := (Nat.div_lt_iff_lt_mul hq').mpr (by simpa only [Nat.mul_comm] using hlt)
           simp only [unit_prefix (Nat.div_pos hu hq') hfloor.le,max_eq_left zero_le_one,mul_one]
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => mul_nonneg (ha q) (le_max_right _ _))
  · apply sum_le_sum
    intro q hq
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hq
    have hq' : 0 < q := (Nat.zero_le _).trans_lt hl
    have hlt := (Nat.div_lt_iff_lt_mul hZpos).mp hl
    have hfloor : X/q < Z := (Nat.div_lt_iff_lt_mul hq').mpr (by simpa only [Nat.mul_comm] using hlt)
    have hmax := max_le (hpre (X/q) (Nat.div_pos hu hq') hfloor.le) (zero_le_one : (0:ℝ) ≤ 1)
    exact (mul_le_mul_of_nonneg_left hmax (ha q)).trans_eq (mul_one _)

/-- Below the square of the prime wall the prefix is at most one. Beyond
that square it is strictly negative throughout any fixed polynomial range. -/
theorem one_sided_rough_prefix_on_polynomial_ranges (j : ℕ) :
    ∀ᶠ y : ℕ in atTop,∀ m : ℕ,0 < m → m ≤ y^j →
      coprimeMoebiusSum (primorial y) m ≤ 1 ∧
        (y^2 < m → coprimeMoebiusSum (primorial y) m < 0) := by
  obtain ⟨c,hc,L,_,hcharge⟩ := negative_charge_of_every_polynomial_rough_cutoff j
  filter_upwards [eventually_ge_atTop L] with y hy
  intro m hm hsize
  have hneg (hbig : y^2 < m) : roughPrefix y m < 0 := by
    have hLy : L*y ≤ m := (Nat.mul_le_mul_right y hy).trans (by simpa only [pow_two] using hbig.le)
    have hmain := hcharge y m hy hLy hsize
    have hm' : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
    have strict := hmain.trans_lt (neg_neg_of_pos (mul_pos hc hm'))
    by_contra! h
    exact (not_lt_of_ge (mul_nonneg (Real.log_natCast_nonneg _) h)) strict
  refine ⟨?_,hneg⟩
  rcases le_or_gt m (y^2) with h|h
  · rw [rough_prefix_before_composites hm h]
    exact sub_le_self _ (Nat.cast_nonneg _)
  · exact (hneg h).le.trans zero_le_one

private theorem interval_error {x P L U a b ε : ℝ} (hx : 0 < x) (he : 0 ≤ ε)
    (low : |L - (x-a)| ≤ ε/2*x) (high : |U - (x-b)| ≤ ε/2*x)
    (hL : L ≤ P) (hU : P ≤ U) (ha : a ≤ x*(ε/2)) (hb : 0 ≤ b) :
    |P/x-1| ≤ ε := by
  apply abs_le.mpr
  constructor
  · apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ hx).mpr
    nlinarith only [(abs_le.mp low).1, hL, ha]
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hx).mpr
    nlinarith only [(abs_le.mp high).2, hU, hb, mul_nonneg he hx.le]

/-- The positive mass per unit X tends uniformly to one throughout every
fixed polynomial range in the prime wall. -/
theorem positive_charge_through_polynomial_band (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop,∀ Z X : ℕ,y ≤ Z → Z ≤ y^j → y*Z ≤ X → ∀ a : ArithmeticFunction ℝ,
      (∀ q,0 ≤ a q) → (∀ q,|a q| ≤ vonMangoldt q) → (∀ p,p.Prime → a p=roughMangoldtWeight y p) →
      |positivePrimeBandMass a y X Z/(X:ℝ)-1| ≤ ε := by
  obtain ⟨N,_,hcost⟩ := ordinary_prime_interval_price (half_pos hε)
  have hinv : Tendsto (fun y : ℕ => (y:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop N,eventually_ge_atTop 1,hinv.eventually_lt_const (half_pos hε),
    one_sided_rough_prefix_on_polynomial_ranges j] with y hN hyp hsmall hpre
  intro Z X hyZ hZ hroom a ha hdom hpr
  have hzp := hyp.trans hyZ
  have hyK : y ≤ X/Z := (Nat.le_div_iff_mul_le hzp).mpr hroom
  have hK : X/Z ≤ X/y := Nat.div_le_div_left hyZ hyp
  have hp : 0 < (X:ℝ) := Nat.cast_pos.mpr ((hyp.trans hyK).trans (Nat.div_le_self X Z))
  have low := hcost y (X/y) (hyK.trans hK) ((hN.trans hyK).trans hK) a hdom hpr (X:ℝ)
    (Nat.cast_le.mpr (Nat.div_le_self ..))
  have high := hcost y (X/Z) hyK (hN.trans hyK) a hdom hpr (X:ℝ)
    (Nat.cast_le.mpr (Nat.div_le_self ..))
  rw [Nat.floor_natCast] at low high
  obtain ⟨hlo,hhi⟩ := positive_sandwich a hyp hyZ (fun m hm hle => (hpre m hm (hle.trans hZ)).1) ha
  have hratio : ((X/y:ℕ):ℝ) ≤ (X:ℝ)*(ε/2) := by
    have hb : ((X/y:ℕ):ℝ)*(y:ℝ) ≤ X := by exact_mod_cast Nat.div_mul_le_self X y
    have hr := (le_div_iff₀ (Nat.cast_pos.mpr hyp : 0 < (y:ℝ))).mpr hb
    rw [div_eq_mul_inv] at hr
    exact hr.trans (mul_le_mul_of_nonneg_left hsmall.le hp.le)
  exact interval_error hp hε.le low high hlo hhi hratio (Nat.cast_nonneg _)

private theorem total_as_positive_minus_signed (a : ArithmeticFunction ℝ) (y X Z : ℕ) (ha : ∀ n,0 ≤ a n) :
    primeBandVariation a y X Z = 2*positivePrimeBandMass a y X Z-upperQuotientReading a y X Z := by
  rw [primeBandVariation,positivePrimeBandMass,upperQuotientReading,mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro q _
  rw [abs_mul,abs_of_nonneg (ha q)]
  by_cases hp : 0 ≤ roughPrefix y (X/q)
  · rw [abs_of_nonneg hp,max_eq_left hp];ring
  · rw [abs_of_neg (lt_of_not_ge hp),max_eq_right (le_of_not_ge hp)];ring

private theorem variation_error {P S u ε : ℝ} (hp : |P-1| ≤ ε/3) (hs : |S-u| ≤ ε/3) :
    |2*P-S-(2-u)| ≤ ε := by
  exact abs_le.mpr ⟨by linarith only [(abs_le.mp hp).1,(abs_le.mp hs).2],
    by linarith only [(abs_le.mp hp).2,(abs_le.mp hs).1]⟩

/-- For any cutoff through the first prime band the unsigned row has
profile 1+log(log Z/log y), uniformly in the observation X. -/
theorem total_variation_through_first_prime_band {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop,∀ Z X : ℕ,y ≤ Z → Z ≤ y^2 → y*Z ≤ X → ∀ a : ArithmeticFunction ℝ,
      (∀ q,0 ≤ a q) → (∀ q,|a q| ≤ vonMangoldt q) → (∀ p,p.Prime → a p=roughMangoldtWeight y p) →
      |primeBandVariation a y X Z/(X:ℝ)-(1+Real.log (Real.log Z/Real.log y))| ≤ ε := by
  have hp : 0 < ε/3 := by positivity
  filter_upwards [positive_charge_through_polynomial_band 2 hp,signed_profile_through_the_first_prime_band hp] with y hpos hsig
  intro Z X hyZ hZ hr a ha hd hs
  have h₁ := hpos Z X hyZ hZ hr a ha hd hs
  have h₂ := hsig Z X hyZ hZ hr a hd hs
  rw [total_as_positive_minus_signed _ _ _ _ ha,sub_div,mul_div_assoc]
  have price := variation_error h₁ h₂
  rwa [show 2-(1-Real.log (Real.log Z/Real.log y))=1+Real.log (Real.log Z/Real.log y) by ring] at price

/-- Across any fixed polynomial cofactor range, the unsigned mass per unit
X equals two minus the smooth proportion, with a uniformly vanishing error. -/
theorem total_variation_and_smooth_proportion (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop,∀ Z X : ℕ,y ≤ Z → Z ≤ y^j → y*Z ≤ X → ∀ a : ArithmeticFunction ℝ,
      (∀ q,0 ≤ a q) → (∀ q,|a q| ≤ vonMangoldt q) → (∀ p,p.Prime → a p=roughMangoldtWeight y p) →
      |primeBandVariation a y X Z/(X:ℝ)-
        (2-((RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card:ℝ)/(Z:ℝ))| ≤ ε := by
  have hp : 0 < ε/3 := by positivity
  filter_upwards [positive_charge_through_polynomial_band j hp,
    raw_prime_profile_at_every_interior_cut hp,eventually_ge_atTop 1] with y hpos hraw hy
  intro Z X hyZ hZ hr a ha hdom hs
  have hagree (p : ℕ) (hpp : p.Prime) : a p=roughOrdinaryPrimeWeight y p := by
    rw [hs p hpp,roughMangoldtWeight,roughRestriction_apply,vonMangoldt_apply_prime hpp]
    have hfree : IsFree (RoughReading.banned y) p ↔ y < p := by
      simpa only [RoughReading.banned,Set.mem_setOf_eq,not_le] using isFree_prime (RoughReading.banned y) hpp
    change _=(if p.Prime ∧ y < p then Real.log p else 0)
    simp only [hpp,true_and,hfree]
  have h₁ := hpos Z X hyZ hZ hr a ha hdom hs
  have h₂ := hraw Z X hyZ hr a hdom hagree
  have hx : 0 < (X:ℝ) := Nat.cast_pos.mpr ((Nat.mul_pos hy (hy.trans hyZ)).trans_le hr)
  have hz : 0 < (Z:ℝ) := Nat.cast_pos.mpr (hy.trans hyZ)
  let b : ℝ := (RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card
  have hnorm : |upperQuotientReading a y X Z/(X:ℝ)-b/(Z:ℝ)| ≤ ε/3 := by
    rw [←show (upperQuotientReading a y X Z-(X:ℝ)/Z*b)/(X:ℝ)=
        upperQuotientReading a y X Z/(X:ℝ)-b/Z by field_simp [hx.ne',hz.ne'],
      abs_div,abs_of_pos hx,div_le_iff₀ hx]
    exact h₂
  rw [total_as_positive_minus_signed _ _ _ _ ha,sub_div,mul_div_assoc]
  change |2*(positivePrimeBandMass a y X Z/(X:ℝ))-upperQuotientReading a y X Z/(X:ℝ)-(2-b/Z)| ≤ ε
  exact variation_error h₁ hnorm

#print axioms one_sided_rough_prefix_on_polynomial_ranges
#print axioms positive_charge_through_polynomial_band
#print axioms total_variation_and_smooth_proportion
#print axioms total_variation_through_first_prime_band
end GaloisForLFunctions.RestrictedFactorizationCalculus
