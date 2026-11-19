import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCriticalEulerPriceOfTheLogSquareCutoff
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCriticalMassOfTheOmittedPrimePowers
import GaloisForLFunctions.RHTower.Sieve.MoebiusDoubleLogRealCutoff
import GaloisForLFunctions.RHTower.WeilPositivityMertensConstantObstruction

/-!
# Prime and proper-power mass at the log-square wall

Scaling the prime wall by a fixed factor has an explicit square-root cost.
The omitted proper powers contribute one half of the endpoint logarithm.
-/
noncomputable section
open Finset Filter
open scoped Classical Topology
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev L (n : ℕ) := Real.log (n:ℝ)
private abbrev wall := logSquareCutoff
private abbrev rho (n : ℕ) := ∑ p ∈ Nat.primesLE n,Real.log p/Real.sqrt p
private abbrev mass (y X : ℕ) := ∑ d ∈ Icc 1 X,roughProperPowerWeight y d/Real.sqrt d

private theorem log_square_wall_root_ratio :
    Tendsto (fun X : ℕ => Real.sqrt (wall X)/L X) atTop (𝓝 1) := by
  have logtop : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have tiny : Tendsto (fun n : ℕ => (L n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp logtop
  have low := (tendsto_const_nhds (x := (1:ℝ))).sub tiny
  have high := (tendsto_const_nhds (x := (1:ℝ))).add tiny
  rw [sub_zero] at low
  rw [add_zero] at high
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low high
  all_goals
    filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    have np : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
    have n1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have lp : 0<L n := Real.log_pos (by exact_mod_cast (by omega : 1<n))
    let k := ⌊Real.log ((n:ℝ)+1)⌋₊
    have eq : Real.sqrt (wall n)=k := by
      change Real.sqrt ((k^2:ℕ):ℝ)=k
      rw [Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg _)]
    rw [eq]
  · have h := Real.log_le_log np (by linarith : (n:ℝ) ≤ n+1)
    have round : Real.log ((n:ℝ)+1)<(k:ℝ)+1 := Nat.lt_floor_add_one _
    apply (le_div_iff₀ lp).mpr
    change (1-(L n)⁻¹)*L n ≤ _
    rw [sub_mul,one_mul,inv_mul_cancel₀ lp.ne']
    linarith only [h,round]
  · have log2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have up := Real.log_le_log (show 0<(n:ℝ)+1 by positivity) (show (n:ℝ)+1 ≤ 2*n by linarith only [n1])
    rw [Real.log_mul (by norm_num) np.ne'] at up
    have floor : (k:ℝ) ≤ Real.log ((n:ℝ)+1) := Nat.floor_le (Real.log_nonneg (by linarith only [n1]))
    apply (div_le_iff₀ lp).mpr
    change _ ≤ (1+(L n)⁻¹)*L n
    rw [add_mul,one_mul,inv_mul_cancel₀ lp.ne']
    linarith only [floor,up,log2]

private theorem sqrt_wall_of_scaled_cut {λ : ℝ} (hλ : 1 ≤ λ) :
    Tendsto (fun n : ℕ => Real.sqrt (⌊λ*(n:ℝ)⌋₊:ℕ)/Real.sqrt n) atTop (𝓝 (Real.sqrt λ)) := by
  have h : Tendsto (fun n : ℕ => (⌊λ*(n:ℝ)⌋₊:ℝ)/(n:ℝ)) atTop (𝓝 λ) :=
    (tendsto_nat_floor_mul_div_atTop (zero_le_one.trans hλ)).comp tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def,Real.sqrt_div (Nat.cast_nonneg _)] using Real.continuous_sqrt.continuousAt.tendsto.comp h

/-- The exact critical mass of the additional ordinary primes in one multiplicative window. -/
theorem critical_mass_of_a_scaled_prime_window {λ : ℝ} (hλ : 1 ≤ λ) :
    Tendsto (fun n : ℕ => (∑ p ∈ (Nat.primesLE ⌊λ*(n:ℝ)⌋₊).filter (n<·),Real.log p/Real.sqrt p)/
      Real.sqrt n) atTop (𝓝 (2*(Real.sqrt λ-1))) := by
  let z := fun n : ℕ => ⌊λ*(n:ℝ)⌋₊
  have large (n : ℕ) : n ≤ z n := Nat.le_floor (le_mul_of_one_le_left (Nat.cast_nonneg n) hλ)
  have ztop : Tendsto z atTop atTop := tendsto_atTop.mpr (fun k => (eventually_ge_atTop k).mono
    (fun n h => h.trans (large n)))
  have upper := (limit_log_weighted_roots_of_primes.comp ztop).mul (sqrt_wall_of_scaled_cut hλ)
  have dif := upper.sub limit_log_weighted_roots_of_primes
  rw [show (2:ℝ)*Real.sqrt λ-2=2*(Real.sqrt λ-1) by ring] at dif
  apply dif.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n np
  let S := Nat.primesLE (z n)
  let T := Nat.primesLE n
  have sub : T ⊆ S := fun p hp => Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans (large _),
    (Nat.mem_primesLE.mp hp).2⟩
  have eq : S.filter (n<·)=S \ T := by
    ext p
    simp only [S,T,mem_filter,mem_sdiff,Nat.mem_primesLE]
    omega
  change rho (z n)/Real.sqrt (z n)*(Real.sqrt (z n)/Real.sqrt n)-rho n/Real.sqrt n=
    (∑ p ∈ S.filter (n<·),Real.log p/Real.sqrt p)/Real.sqrt n
  rw [eq,sum_sdiff_eq_sub sub]
  field_simp [(Real.sqrt_pos.mpr (Nat.cast_pos.mpr np)).ne',
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (np.trans (large n)))).ne']

private theorem log_of_the_wall_is_sublinear :
    Tendsto (fun X : ℕ => Real.log (wall X)/L X) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    exact ha.trans_le (div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))
  · intro a ha
    filter_upwards [log_square_deletion_cost (by norm_num : (1:ℝ)/2<1) (half_pos ha),
      logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,eventually_ge_atTop (2:ℕ)] with X cost yp xp
    have lp : 0<L X := Real.log_pos (by exact_mod_cast (by omega : 1<X))
    have e1 := deletionPrice_one_le (s := 1) zero_lt_one (wall X)
    have low := le_mul_of_one_le_right (by positivity : 0 ≤ (wall X:ℝ)+1) (one_le_pow₀ e1 (n := 2))
    have bound : (wall X:ℝ) ≤ (X:ℝ)^(a/2) := (by linarith : (wall X:ℝ) ≤ wall X+1).trans (low.trans cost)
    have up := Real.log_le_log (Nat.cast_pos.mpr yp) bound
    rw [Real.log_rpow (Nat.cast_pos.mpr (by omega : 0<X))] at up
    apply (div_lt_iff₀ lp).mpr
    linarith only [up,mul_pos ha lp]

private theorem proper_powers_use_half_the_log :
    Tendsto (fun X : ℕ => mass (wall X) X/L X) atTop (𝓝 (1/2)) := by
  have logtop : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have sqtop := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have high0 := (RHTower.Sieve.tendsto_log_natFloor_div_log_one.comp sqtop).mul_const (1/2:ℝ)
  rw [one_mul] at high0
  have high : Tendsto (fun X : ℕ => Real.log X.sqrt/L X) atTop (𝓝 (1/2)) := by
    apply high0.congr'
    filter_upwards [eventually_ge_atTop (2:ℕ)] with X pos
    change Real.log (⌊Real.sqrt (X:ℝ)⌋₊:ℝ)/Real.log (Real.sqrt (X:ℝ))*(1/2)=_
    rw [RHTower.floor_sqrt_eq_sqrt_floor (Nat.cast_nonneg _),Nat.floor_natCast,Real.log_sqrt (Nat.cast_nonneg _)]
    ring
  obtain ⟨K,hK,price⟩ := sharp_logarithmic_length_of_the_omitted_powers
  have fee := (tendsto_inv_atTop_zero.comp logtop).const_mul K
  rw [mul_zero] at fee
  have bound := high.add fee
  have low := (high.sub log_of_the_wall_is_sublinear).sub fee
  rw [add_zero] at bound; rw [sub_zero,sub_zero] at low
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low bound
  all_goals
    filter_upwards [logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,eventually_ge_atTop (2:ℕ)] with X yp xp
    have lp : 0<L X := Real.log_pos (by exact_mod_cast (by omega : 1<X))
    let y := wall X
    have mp : 1 ≤ X.sqrt := Nat.le_sqrt.mpr (by omega)
    have m0 := Real.log_nonneg (Nat.one_le_cast.mpr (le_min yp mp))
    have mup := Real.log_le_log (Nat.cast_pos.mpr (le_min yp mp)) (Nat.cast_le.mpr (min_le_left y X.sqrt))
    have both := abs_le.mp (price y X yp (by omega))
  · change Real.log X.sqrt/L X-Real.log y/L X-K*(L X)⁻¹ ≤ mass y X/L X
    have eq : Real.log X.sqrt/L X-Real.log y/L X-K*(L X)⁻¹=(Real.log X.sqrt-Real.log y-K)/L X := by ring
    rw [eq]; exact div_le_div_of_nonneg_right (by linarith only [both.1,mup]) lp.le
  · change mass y X/L X ≤ Real.log X.sqrt/L X+K*(L X)⁻¹
    rw [show Real.log X.sqrt/L X+K*(L X)⁻¹=(Real.log X.sqrt+K)/L X by ring]
    exact div_le_div_of_nonneg_right (by linarith only [both.2,m0]) lp.le

/-- The threshold for simultaneously omitting proper powers and ordinary
primes through a multiple of the frozen log-square cutoff. -/
theorem limiting_mass_of_the_combined_omission {λ : ℝ} (hλ : 1 ≤ λ) :
    Tendsto (fun X : ℕ => let y := wall X
      (mass y X+(∑ p ∈ (Nat.primesLE ⌊λ*(y:ℝ)⌋₊).filter (y<·),Real.log p/Real.sqrt p))/L X)
      atTop (𝓝 (1/2+2*(Real.sqrt λ-1))) := by
  have shell := ((critical_mass_of_a_scaled_prime_window hλ).comp logSquareCutoff_tendsto_atTop).mul log_square_wall_root_ratio
  rw [mul_one] at shell
  apply (proper_powers_use_half_the_log.add shell).congr'
  filter_upwards [logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1] with X yp
  let S := ∑ p ∈ (Nat.primesLE ⌊λ*(wall X:ℝ)⌋₊).filter (wall X<·),Real.log p/Real.sqrt p
  change mass (wall X) X/L X+(S/Real.sqrt (wall X))*(Real.sqrt (wall X)/L X)=_
  field_simp [(Real.sqrt_pos.mpr (Nat.cast_pos.mpr yp)).ne']

#print axioms critical_mass_of_a_scaled_prime_window
#print axioms limiting_mass_of_the_combined_omission
end GaloisForLFunctions.RestrictedFactorizationCalculus
