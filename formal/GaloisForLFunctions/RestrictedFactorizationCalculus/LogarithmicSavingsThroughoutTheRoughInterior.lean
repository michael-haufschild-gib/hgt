import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeReadingsBeyondTheHyperbola
import GaloisForLFunctions.BezoutValuationIncidence.TheBalancedStatisticIsTheQuasiRiemannHypothesis
import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability
import GaloisForLFunctions.RHTower.ShortWindowNoGo

/-!
# Arbitrary logarithmic savings in the rough prime-power interior

Opening the deleted Euler factors gives ordinary Möbius prefixes at
smooth quotients. Long prefixes inherit the zero-free-region saving.
The number of short prefixes is bounded by Rankin's smooth-number
estimate. Both bounds are uniform in the observation endpoint and in
all deletion walls up to the log-square wall.
-/
noncomputable section
open Finset Filter ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence
open scoped Classical Topology
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev row (y t : ℕ) := coprimeMoebiusSum (primorial y) t
private abbrev smooth (y t : ℕ) := _root_.RHTower.Sieve.smoothUpTo (Nat.primesLE y) t

private theorem ordinary_eq_mertens (n : ℕ) :
    coprimeMoebiusSum 1 n = _root_.RHTower.Sieve.mertensM n := by
  simpa [coprimeMoebiusSum,coprimeMoebiusIndicator,moebiusReal] using sum_Icc_moebiusReal_eq_mertensM n

private theorem cutoff_price :
    ∀ᶠ X : ℕ in atTop, ∀ y ≤ logSquareCutoff X,
      deletionPrice (3/4) y ≤ (X:ℝ)^(1/16:ℝ) := by
  filter_upwards [log_square_deletion_cost (by norm_num : (1:ℝ)/2 < 3/4)
    (by norm_num : (0:ℝ) < 1/16)] with X hx
  intro y hy
  let z := logSquareCutoff X
  have h := deletionPrice_one_le (by norm_num : (0:ℝ) < 3/4) z
  have hh : deletionPrice (3/4) z ≤ (deletionPrice (3/4) z)^2 := by nlinarith only [h,sq_nonneg (deletionPrice (3/4) z-1)]
  have hc : (deletionPrice (3/4) z)^2 ≤ ((z:ℝ)+1)*(deletionPrice (3/4) z)^2 :=
    le_mul_of_one_le_left (sq_nonneg _) (by have := Nat.cast_nonneg (α:=ℝ) z; linarith)
  exact (deletionPrice_mono (by norm_num : (0:ℝ) < 3/4) hy).trans (hh.trans (hc.trans hx))

private theorem long_prefix {t X d K p : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ n ≥ K, |_root_.RHTower.Sieve.mertensM n| ≤ B*(n:ℝ)/Real.log n^p)
    (hl : 0 < Real.log X) (hX : 0 < (X:ℝ)) (hK : (K:ℝ) ≤ (X:ℝ)^(1/16:ℝ))
    (ht : t ≤ X) (hd : 0 < d) (hv : (X:ℝ)^(1/16:ℝ) ≤ ((t/d:ℕ):ℝ)) :
    |coprimeMoebiusSum 1 (t/d)| ≤ B*16^p*(X:ℝ)/Real.log X^p * (1/(d:ℝ)) := by
  let v := t/d
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hX _) hv
  rw [Real.log_rpow hX] at hlog
  have hlv : 0 < Real.log (v:ℝ) := lt_of_lt_of_le (mul_pos (by norm_num) hl) hlog
  have hden := pow_le_pow_left₀ hl.le (show Real.log X ≤ 16*Real.log v by linarith only [hlog]) p
  rw [mul_pow] at hden
  have hn : K ≤ v := by exact_mod_cast hK.trans hv
  have hdiv : (v:ℝ)*d ≤ X := by exact_mod_cast (Nat.div_mul_le_self t d).trans ht
  rw [ordinary_eq_mertens]
  apply (hM v hn).trans
  rw [one_div,←div_eq_mul_inv,div_div]
  apply (div_le_div_iff₀ (pow_pos hlv _) (mul_pos (pow_pos hl _) (Nat.cast_pos.mpr hd))).mpr
  calc B*(v:ℝ)*(Real.log X^p*d) = (B*((v:ℝ)*d))*Real.log X^p := by ring
       _ ≤ (B*(X:ℝ))*(16^p * Real.log v^p) :=
         mul_le_mul (mul_le_mul_of_nonneg_left hdiv hB) hden (pow_nonneg hl.le _)
           (mul_nonneg hB hX.le)
       _ = _ := by ring

/-- All frozen rough Möbius prefixes below the observation scale have
arbitrary inverse-logarithmic savings, uniformly in every smaller prime wall. -/
theorem uniform_log_savings_for_rough_prefixes (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, ∀ y ≤ logSquareCutoff X, ∀ t ≤ X,
      |coprimeMoebiusSum (primorial y) t| * Real.log X^p ≤ C*(X:ℝ) := by
  obtain ⟨B,hB,hM⟩ := _root_.RHTower.Sieve.deningerMertensM_log_pow_rate (p+1)
  obtain ⟨K,hK⟩ := eventually_atTop.mp hM
  let A := B*16^(p+1)
  have hA : 0 ≤ A := mul_nonneg hB (by positivity)
  refine ⟨1+2*A,by positivity,?_⟩
  have grow := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/16)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have loggrow := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [cutoff_price,grow.eventually_ge_atTop (K:ℝ),loggrow.eventually_ge_atTop 1,
    eventually_ge_atTop 1,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
      (_root_.RHTower.burnolEventually_log_pow_le_rpow (by norm_num : (0:ℝ) < 1/8) p)]
    with X hprice hKX hlog hX hpoly
  intro y hy t ht
  let S := smooth y t
  let H := (X:ℝ)^(1/16:ℝ)
  let L := Real.log (X:ℝ)
  change 1 ≤ L at hlog
  let G := A*(X:ℝ)/L^(p+1)
  have hx : 0 < (X:ℝ) := Nat.cast_pos.mpr hX
  have hl : 0 < L := zero_lt_one.trans_le hlog
  have hG : 0 ≤ G := div_nonneg (mul_nonneg hA hx.le) (pow_nonneg hl.le _)
  have hcap : (S.card:ℝ)*H ≤ (X:ℝ)^(7/8:ℝ) := by
    have pop := smooth_population_le_deletion_price (by norm_num : (0:ℝ) < 3/4) y t
    have hb := mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg t) (Nat.cast_le.mpr ht)
        (by norm_num : (0:ℝ) ≤ 3/4)) (hprice y hy)
        (zero_le_one.trans (deletionPrice_one_le (by norm_num : (0:ℝ) < 3/4) y))
        (Real.rpow_nonneg hx.le _)
    apply (mul_le_mul_of_nonneg_right (pop.trans hb) (Real.rpow_nonneg hx.le _)).trans_eq
    rw [←Real.rpow_add hx,←Real.rpow_add hx]
    norm_num
  have hsum : ∑ d∈S,(1/(d:ℝ)) ≤ 1+L := by
    apply le_trans _ (_root_.RHTower.harmonic_Icc_le_one_add_log X hX)
    exact sum_le_sum_of_subset_of_nonneg (fun d hd => by
      obtain ⟨⟨hp,hu⟩,_⟩ := _root_.RHTower.Sieve.mem_smoothUpTo.mp hd
      exact mem_Icc.mpr ⟨hp,hu.trans ht⟩) (fun d _ _ => by positivity)
  have individual (d : ℕ) (hd : d∈S) :
      |coprimeMoebiusSum 1 (t/d)| ≤ H+G*(1/(d:ℝ)) := by
    have dp := (_root_.RHTower.Sieve.mem_smoothUpTo.mp hd).1.1
    rcases le_total ((t/d:ℕ):ℝ) H with h|h
    · exact ((abs_coprimeMoebiusSum_le 1 _).trans h).trans (le_add_of_nonneg_right (mul_nonneg hG (by positivity)))
    · exact (long_prefix hB hK hl hx hKX ht dp h).trans (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))
  have hrow : |row y t| ≤ (X:ℝ)^(7/8:ℝ)+G*(1+L) := by
    rw [row,←smooth_lift_of_the_full_prefix,smoothLiftedPrefix]
    apply (abs_sum_le_sum_abs ..).trans ((sum_le_sum individual).trans ?_)
    rw [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum]
    exact add_le_add hcap (mul_le_mul_of_nonneg_left hsum hG)
  have hlow : (X:ℝ)^(7/8:ℝ)*L^p ≤ X := by
    apply (mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg hx.le _)).trans_eq
    rw [←Real.rpow_add hx];norm_num
  have hhigh : G*(1+L)*L^p ≤ 2*A*X := by
    have hh := mul_le_mul_of_nonneg_left (show 1+L ≤ 2*L by linarith only [hlog]) hG
    apply (mul_le_mul_of_nonneg_right hh (pow_nonneg hl.le _)).trans_eq
    dsimp only [G]
    rw [pow_succ]
    field_simp [hl.ne']
  have hb := mul_le_mul_of_nonneg_right hrow (pow_nonneg hl.le p)
  rw [add_mul] at hb
  exact hb.trans ((add_le_add hlow hhigh).trans_eq (by ring))

private abbrev weighted (y t : ℕ) := weightedFrozenPrefix (fun n => Real.log n) y t

private theorem log_mono_nat : Monotone (fun k : ℕ => Real.log k) := by
  intro k m h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa only [Nat.cast_zero,Real.log_zero] using Real.log_natCast_nonneg m
  exact Real.log_le_log (Nat.cast_pos.mpr hk) (Nat.cast_le.mpr h)

/-- Finite Abel summation charges at most one copy of the logarithmic
variation in addition to the endpoint term. -/
private theorem weighted_price (y t : ℕ) {H : ℝ}
    (cap : ∀ n ≤ t, |row y n| ≤ H) : |weighted y t| ≤ 2*H*Real.log t := by
  have variation (m : ℕ) (hm : m ≤ t) :
      |row y m*Real.log m-weighted y m| ≤ H*Real.log m := by
    induction m with
    | zero => simp [weighted,weightedFrozenPrefix]
    | succ m ih =>
      have hmt := (Nat.le_succ m).trans hm
      have row_step : row y (m+1)=row y m+coprimeMoebiusIndicator (primorial y) (m+1) :=
        sum_Icc_succ_top (by omega) _
      have weight_step : weighted y (m+1)=weighted y m+
          coprimeMoebiusIndicator (primorial y) (m+1)*Real.log (m+1:ℕ) := sum_Icc_succ_top (by omega) _
      have hdiff := sub_nonneg.mpr (log_mono_nat (Nat.le_succ m))
      have term := mul_le_mul_of_nonneg_right (cap m hmt) hdiff
      rw [row_step,weight_step,show
        (row y m+coprimeMoebiusIndicator (primorial y) (m+1))*Real.log (m+1:ℕ)-
            (weighted y m+coprimeMoebiusIndicator (primorial y) (m+1)*Real.log (m+1:ℕ)) =
          (row y m*Real.log m-weighted y m)+row y m*(Real.log (m+1:ℕ)-Real.log m) by ring]
      apply (abs_add_le ..).trans
      rw [abs_mul,abs_of_nonneg hdiff]
      linarith only [ih hmt,term]
  have main := abs_sub (row y t*Real.log t) (row y t*Real.log t-weighted y t)
  rw [sub_sub_cancel,abs_mul,abs_of_nonneg (Real.log_natCast_nonneg t)] at main
  linarith only [main,variation t le_rfl,mul_le_mul_of_nonneg_right (cap t le_rfl) (Real.log_natCast_nonneg t)]

private theorem natural_head (y t : ℕ) (hy : 0 < y) :
    quotientReading (roughFloorCoefficient y (roughMangoldtWeight y)) t= -weighted y t := by
  rw [roughFloorCoefficient,←rough_action_as_a_coefficient_prefix y t,full_rough_reading hy]
  unfold roughLogarithmicHead weighted weightedFrozenPrefix
  congr 1
  exact sum_congr rfl (fun n hn => congrArg (fun z : ℝ => z*Real.log n)
    (primorial_indicator_eq_deleted_mobius y n (mem_Icc.mp hn).1).symm)

/-- The complete signed Mangoldt interior has every inverse-logarithmic
saving, uniformly in the removed head and all positive lower prime walls. -/
theorem uniform_log_savings_for_mangoldt_interiors (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, ∀ y : ℕ, 0 < y → y ≤ logSquareCutoff X →
      ∀ T : ℕ, |roughInteriorReading (roughMangoldtWeight y) y X T| * Real.log X^p ≤ C*(X:ℝ) := by
  obtain ⟨B,hB,hrough⟩ := uniform_log_savings_for_rough_prefixes (p+1)
  refine ⟨4*B,by positivity,?_⟩
  filter_upwards [hrough,eventually_ge_atTop 2] with X hX hx
  intro y hy wall T
  let L := Real.log (X:ℝ)
  let H := B*(X:ℝ)/L^(p+1)
  have hl : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hH : 0 ≤ H := div_nonneg (mul_nonneg hB (Nat.cast_nonneg X)) (pow_nonneg hl.le _)
  have head (t : ℕ) (ht : t ≤ X) : |weighted y t| ≤ 2*H*L := by
    apply (weighted_price y t (fun n hn => (le_div_iff₀ (pow_pos hl _)).mpr (hX y wall n (hn.trans ht)))).trans
    exact mul_le_mul_of_nonneg_left (log_mono_nat ht) (by positivity)
  have hsplit := rough_head_and_interior (roughMangoldtWeight y) y X T
  rw [rough_action_as_a_coefficient_prefix] at hsplit
  change quotientReading (roughFloorCoefficient y (roughMangoldtWeight y)) X =
    roughInteriorReading (roughMangoldtWeight y) y X T +
    quotientReading (roughFloorCoefficient y (roughMangoldtWeight y)) (min X T) at hsplit
  rw [natural_head _ _ hy,natural_head _ _ hy] at hsplit
  have eq : roughInteriorReading (roughMangoldtWeight y) y X T=weighted y (min X T)-weighted y X := by
    linarith only [hsplit]
  have upper := (abs_sub ..).trans (add_le_add (head (min X T) (min_le_left X T)) (head X le_rfl))
  rw [eq]
  apply (mul_le_mul_of_nonneg_right upper (pow_nonneg hl.le p)).trans_eq
  dsimp only [H]
  rw [pow_succ]
  field_simp [hl.ne']
  ring

/-- In particular every exponent, including four sevenths, has a signed
reading smaller than X by any prescribed logarithmic power. -/
theorem log_savings_at_every_head_exponent (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, ∀ α : ℝ,
      |primePowerInteriorAtExponent α X| * Real.log X^p ≤ C*(X:ℝ) := by
  obtain ⟨C,hC,h⟩ := uniform_log_savings_for_mangoldt_interiors p
  refine ⟨C,hC,?_⟩
  filter_upwards [h,logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1] with X hx hy
  exact fun α => hx _ hy le_rfl ⌊(X:ℝ)^α⌋₊

end GaloisForLFunctions.RestrictedFactorizationCalculus
