import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SquareAndSixthPowerSamplesOfTheReciprocalPrimeOctave
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.FiniteWeakMomentComparison

/-!
# Counting integer power comparisons on the gcd grid

A deficit of at least log(2)/j is the integer comparison
G^j ≤ 2^((j-1)X). Dyadic j up to 2K suffice on a prefix of length K.
Smaller deficits together cost at most log(2). The finite weak first
moment bounds the full deficit with the harmonic factor H_K.
-/

noncomputable section
open Finset Filter GaloisForLFunctions.FiniteWeakMoment
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Positive part of the normalized shortfall in one gcd row. -/
def gcdRowDeficit (r m : ℕ) : ℝ :=
  max (Real.log 2 - Real.log (octaveGcdProduct (m^r) (m^(r+1))) / (m:ℝ)^(r+1)) 0

/-- Rows whose gcd product falls below the indicated integer power threshold. -/
def gcdPowerFailures (r K j : ℕ) : Finset ℕ :=
  (Icc 1 K).filter fun m => (octaveGcdProduct (m^r) (m^(r+1)))^j ≤ 2^((j-1)*m^(r+1))

/-- A positive logarithmic cutoff can be tested by comparing natural powers. -/
theorem gcd_power_failure_iff (r : ℕ) {m j : ℕ} (hm : 0 < m) (hj : 0 < j) :
    (octaveGcdProduct (m^r) (m^(r+1)))^j ≤ 2^((j-1)*m^(r+1)) ↔
      Real.log 2/(j:ℝ) ≤ gcdRowDeficit r m := by
  let G := octaveGcdProduct (m^r) (m^(r+1))
  change G^j ≤ _ ↔ _
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj' : 0 < (j:ℝ) := Nat.cast_pos.mpr hj
  have hX : 0 < (m:ℝ)^(r+1) := pow_pos (Nat.cast_pos.mpr hm) _
  rw [gcdRowDeficit,le_max_iff,or_iff_left (not_le.mpr (div_pos hlog hj'))]
  change _ ↔ Real.log 2/j ≤ Real.log 2-Real.log G/(m:ℝ)^(r+1)
  by_cases hG : G=0
  · rw [hG,zero_pow hj.ne',Nat.cast_zero,Real.log_zero,zero_div,sub_zero]
    exact iff_of_true (Nat.zero_le _) (div_le_self hlog.le (by exact_mod_cast hj))
  have hG' : 0 < (G:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hG)
  have hcast : G^j ≤ 2^((j-1)*m^(r+1)) ↔ (G:ℝ)^j ≤ (2:ℝ)^((j-1)*m^(r+1)) := by norm_cast
  rw [hcast,←Real.log_le_log_iff (pow_pos hG' _) (by positivity),Real.log_pow,Real.log_pow,
    Nat.cast_mul,Nat.cast_sub (show 1 ≤ j by omega),Nat.cast_one,Nat.cast_pow]
  rw [le_sub_comm,div_le_iff₀ hX,sub_mul (Real.log 2) (Real.log 2/(j:ℝ)),div_mul_eq_mul_div,le_sub_comm,div_le_iff₀ hj']
  constructor <;> intro h <;> linarith only [h]

/-- Only dyadically many integer thresholds occur up to K. -/
def subpowerGcdPowerCounts (r : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 0 ≤ A ∧ ∃ᶠ K : ℕ in atTop,
    ∀ k : ℕ, 2^k ≤ 2*K → ((gcdPowerFailures r K (2^k)).card:ℝ) ≤ (2:ℝ)^k*A*(K:ℝ)^δ

private theorem failures_paid (r K : ℕ) {j : ℕ} (hj : 0 < j) :
    ((gcdPowerFailures r K j).card:ℝ)*(Real.log 2/(j:ℝ)) ≤ powerGridGcdDeficit r K := by
  rw [←nsmul_eq_mul,←sum_const]
  apply (sum_le_sum (fun m hm => (gcd_power_failure_iff r (mem_Icc.mp (mem_filter.mp hm).1).1 hj).mp
    (mem_filter.mp hm).2)).trans
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => le_max_right _ _

private theorem row_le_log (r m : ℕ) : gcdRowDeficit r m ≤ Real.log 2 := by
  unfold gcdRowDeficit
  exact max_le (sub_le_self _ (div_nonneg (Real.log_natCast_nonneg _) (by positivity)))
    (Real.log_nonneg (by norm_num))

private theorem weak_levels_paid (r : ℕ) {K : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ k : ℕ, 2^k ≤ 2*K → ((gcdPowerFailures r K (2^k)).card:ℝ) ≤ (2:ℝ)^k*B)
    (i : ℕ) :
    levelMass (Icc 1 K) (gcdRowDeficit r) i ≤ Real.log 2*(1+2*B) := by
  let f := gcdRowDeficit r
  let S := (Icc 1 K).filter fun m => f i ≤ f m
  change f i*(S.card:ℝ) ≤ _
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf : 0 ≤ f i := le_max_right _ _
  have hc : S.card ≤ K := by
    have hx := card_le_card (filter_subset (fun m => f i ≤ f m) (Icc 1 K))
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hx
  by_cases hs : f i*(K:ℝ) ≤ Real.log 2
  · have hx := (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hc : (S.card:ℝ) ≤ K) hf).trans hs
    linarith only [hx,mul_nonneg hlog.le hB]
  have hfi : 0 < f i := lt_of_le_of_ne hf (fun he => by simp [←he,hlog.le] at hs)
  have hr : 1 ≤ Real.log 2/f i := (one_le_div hfi).mpr (row_le_log r i)
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near hr (show (1:ℝ)<2 by norm_num)
  have hscale := (le_div_iff₀ hfi).mp hlo
  have hk : (2:ℝ)^k ≤ K := hlo.trans ((div_le_iff₀ hfi).mpr (by linarith only [lt_of_not_ge hs]))
  have hcut : 2^(k+1) ≤ 2*K := by
    rw [pow_succ]; exact_mod_cast (show (2:ℝ)^k*2 ≤ 2*K by linarith only [hk])
  have hp : 0 < (2:ℝ)^(k+1) := by positivity
  have hlev : Real.log 2/(2:ℝ)^(k+1) ≤ f i := (div_le_iff₀ hp).mpr (by
    have hh := (div_lt_iff₀ hfi).mp hhi
    linarith only [hh])
  have hsub : S ⊆ gcdPowerFailures r K (2^(k+1)) := by
    intro m hm
    obtain ⟨hm',hd⟩ := mem_filter.mp hm
    refine mem_filter.mpr ⟨hm',(gcd_power_failure_iff r (mem_Icc.mp hm').1 (by positivity)).mpr ?_⟩
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hlev.trans hd
  have hb := (Nat.cast_le.mpr (card_le_card hsub) : (S.card:ℝ) ≤ _).trans (h (k+1) hcut)
  have hx := mul_le_mul_of_nonneg_left hb hf
  have hy := mul_le_mul_of_nonneg_right hscale hB
  rw [pow_succ] at hx
  linarith only [hx,hy,hlog.le]

/-- The full gcd deficit and the counts of failures at logarithmically many
integer thresholds have exactly the same cofinal subpower criterion. -/
theorem subpower_counts_iff_gcd_grid (r : ℕ) : subpowerGcdPowerCounts r ↔ subpowerGcdGrid r := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro ht δ hδ
    let d := δ/2
    have hd : 0 < d := half_pos hδ
    obtain ⟨A,hA,hfreq⟩ := ht d hd
    refine ⟨Real.log 2*(1+2*A)*(1+1/d),(hfreq.and_eventually (eventually_ge_atTop 1)).mono ?_⟩
    rintro K ⟨h,hK⟩
    have hK' : 0 < (K:ℝ) := Nat.cast_pos.mpr hK
    have hx := Real.one_le_rpow (Nat.one_le_cast.mpr hK : (1:ℝ) ≤ K) hd.le
    let x := (K:ℝ)^d
    have hx₁ : 1 ≤ x := hx
    have hlevels := weak_levels_paid r (mul_nonneg hA (zero_le_one.trans hx₁))
      (fun k hk => (h k hk).trans_eq (mul_assoc ..))
    have hs := sum_le_harmonic (Icc 1 K) (gcdRowDeficit r) _ (fun _ _ => le_max_right _ _) (fun i _ => hlevels i)
    rw [Nat.card_Icc,Nat.add_sub_cancel] at hs
    have hh := harmonic_le_one_add_log K
    have hlog' := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hK' d)
    rw [Real.log_rpow hK'] at hlog'
    have hlogK : Real.log K ≤ x/d := (le_div_iff₀ hd).mpr (by linarith only [hlog'])
    have hh' : (harmonic K:ℝ) ≤ (1+1/d)*x := by
      exact (hh.trans (add_le_add hx₁ hlogK)).trans_eq (by ring)
    have hrow : Real.log 2*(1+2*(A*x)) ≤ (Real.log 2*(1+2*A))*x := by
      linarith only [mul_le_mul_of_nonneg_left hx₁ hlog.le]
    have he : (K:ℝ)^δ=x*x := by rw [show δ=d+d by dsimp [d]; ring, Real.rpow_add hK']
    calc powerGridGcdDeficit r K ≤ _ := hs
         _ ≤ ((1+1/d)*x)*((Real.log 2*(1+2*A))*x) :=
           mul_le_mul hh' hrow (by positivity) (by positivity)
         _ = _ := by rw [he]; ring
  · intro hg δ hδ
    obtain ⟨A,h⟩ := hg δ hδ
    refine ⟨max A 0/Real.log 2,div_nonneg (le_max_right _ _) hlog.le,h.mono ?_⟩
    intro K hK k _
    have hp : 0 < (2:ℝ)^k := by positivity
    have hmass := (failures_paid r K (j:=2^k) (by positivity)).trans (hK.trans
      (mul_le_mul_of_nonneg_right (le_max_left A 0) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    rw [Nat.cast_pow,Nat.cast_ofNat,←mul_div_assoc,div_le_iff₀ hp] at hmass
    exact ((le_div_iff₀ hlog).mpr hmass).trans_eq (by ring)

/-- RH is equivalent to a bound on counts of integer power comparisons on
the square/cube gcd grid. The threshold exponent ranges over powers of two. -/
theorem rh_iff_dyadic_gcd_power_counts : RiemannHypothesis ↔ subpowerGcdPowerCounts 2 :=
  riemannHypothesis_iff_square_cube_gcd_deficit.trans (subpower_counts_iff_gcd_grid 2).symm

/-- The same integer counts on the sixth-power grid characterize the
eleven-thirds bound at every conductor endpoint. -/
theorem sixth_power_counts_iff_eleven_thirds :
    subpowerGcdPowerCounts 6 ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |seventeenNinthsConductorPrefix N| ≤ C*(N:ℝ)^(11/3:ℝ) :=
  (subpower_counts_iff_gcd_grid 6).trans sixth_seventh_gcd_iff_eleven_thirds

#print axioms subpower_counts_iff_gcd_grid
#print axioms rh_iff_dyadic_gcd_power_counts
#print axioms sixth_power_counts_iff_eleven_thirds

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
