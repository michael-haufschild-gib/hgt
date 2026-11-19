import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCriticalMassOfTheOmittedPrimePowers
import GaloisForLFunctions.RestrictedFactorizationCalculus.InvertingAWeightedReadingAtAMovingPrimeCutoff

/-!
# Inverting the ordinary-prime reading at square root

A prime-square kernel uses half the available logarithm. All higher
powers and the logarithmic variation of smaller frozen rows cost a
bounded multiple of their square-root price. The other half closes the
diagonal induction even with a general increasing endpoint allowance.
-/

noncomputable section

open Finset Filter
open scoped Classical
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev M (y X : ℕ) := coprimeMoebiusSum (primorial y) X
private abbrev E (y : ℕ) := deletionPrice (1/2) y

/-- The uncentered ordinary-prime charge retains the full integral
floor contribution of the smooth population. -/
def ordinaryPrimeCharge (y X : ℕ) := centeredOrdinaryPrimeRemainder y X+
    (y:ℝ)*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) (X/y)).card

/-- Removing the floor center recovers the literal ordinary-prime sum. -/
theorem ordinary_prime_charge_as_a_quotient_sum (y X : ℕ) :
    ordinaryPrimeCharge y X=∑ m ∈ RoughReading.freeSet y (X/y),
      RoughReading.row y m*ordinaryPrimeReading y (X/m) := by
  have floors := smooth_population_as_a_rough_floor_sum y ((X:ℝ)/y)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [Nat.floor_div_natCast,Nat.floor_natCast] at floors
  rw [ordinaryPrimeCharge,centeredOrdinaryPrimeRemainder,←floors,mul_sum,←sum_add_distrib]
  exact sum_congr rfl (fun m _ => by ring)

private theorem proper_power_correction (y X : ℕ) (xp : 0<X) {H : ℝ} (hH : 0 ≤ H)
    (smaller : ∀ k,k<X → |M y k| ≤ H*Real.sqrt k) :
    |∑ d ∈ Icc 1 X,roughProperPowerWeight y d*M y (X/d)| ≤
      H*Real.sqrt X*(∑ d ∈ Icc 1 X,roughProperPowerWeight y d/Real.sqrt d) := by
  rw [mul_sum]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro d hd
  by_cases ok : 1<d ∧ y<d ∧ ¬d.Prime ∧ RHTower.CoprimeMobius.IsFree (RoughReading.banned y) d
  · have w0 : 0 ≤ roughProperPowerWeight y d := by
      rw [roughProperPowerWeight,if_pos ok]; exact ArithmeticFunction.vonMangoldt_nonneg
    have dp := (mem_Icc.mp hd).1
    have d0 := (Nat.cast_pos (α := ℝ)).mpr dp
    have frac : ((X/d:ℕ):ℝ) ≤ (X:ℝ)/d :=
      (le_div_iff₀ d0).mpr (by exact_mod_cast Nat.div_mul_le_self X d)
    have root := Real.sqrt_le_sqrt frac
    rw [Real.sqrt_div (Nat.cast_nonneg _)] at root
    have cap := (smaller _ (Nat.div_lt_self xp ok.1)).trans (mul_le_mul_of_nonneg_left root hH)
    rw [abs_mul,abs_of_nonneg w0]
    exact (mul_le_mul_of_nonneg_left cap w0).trans_eq (by ring)
  · simp only [roughProperPowerWeight,if_neg ok,zero_mul,abs_zero,zero_div,mul_zero,le_refl]

/-- All errors in the local ordinary-prime equation use strictly smaller
endpoints. Their critical norm has leading coefficient one half. -/
theorem ordinary_prime_reading_on_smaller_frozen_rows :
    ∃ K : ℝ,0 ≤ K ∧ ∀ y X : ℕ,0<y → 0<X → ∀ H : ℝ,0 ≤ H →
      (∀ k,k<X → |M y k| ≤ H*Real.sqrt k) →
      |M y X*Real.log X+ordinaryPrimeCharge y X| ≤ H*Real.sqrt X*(Real.log X/2+K) := by
  obtain ⟨K,hK,mass⟩ := half_logarithmic_price_of_proper_powers
  refine ⟨K+2,by linarith only [hK],fun y X hy hx H hH rows => ?_⟩
  have bound := (proper_power_correction y X hx hH rows).trans (mul_le_mul_of_nonneg_left
    (mass y X hx) (mul_nonneg hH (Real.sqrt_nonneg _)))
  have shift := critical_variation_of_the_frozen_logarithmic_row y X hH rows
  have logeq : weightedFrozenPrefix (fun k => Real.log k) y X=
      ∑ n ∈ Icc 1 X,RoughReading.row y n*Real.log n :=
    sum_congr rfl (fun n hn => congrArg (fun a : ℝ => a*Real.log n)
      (primorial_indicator_eq_deleted_mobius y n (mem_Icc.mp hn).1))
  rw [logeq] at shift
  let W := ∑ n ∈ Icc 1 X,RoughReading.row y n*Real.log n
  let T := ∑ d ∈ Icc 1 X,roughProperPowerWeight y d*M y (X/d)
  have iden := exact_centered_ordinary_prime_reading hy X
  have eq : M y X*Real.log X+ordinaryPrimeCharge y X=M y X*Real.log X-W-T := by
    unfold ordinaryPrimeCharge; linarith only [iden]
  rw [eq]
  exact (abs_sub ..).trans ((add_le_add shift bound).trans_eq (by ring))

/-- A single ordinary-prime reading of size v(X)√X log X controls
every higher frozen row of size v(X)√X with one Euler product. -/
theorem critical_inversion_of_the_ordinary_prime_reading (b : ℕ → ℕ) (hb : Monotone b)
    (active : ∀ᶠ n : ℕ in atTop,0<b n) (v : ℕ → ℝ) (hv : Monotone v) (v1 : ∀ n,1 ≤ v n)
    {B : ℝ} (hB : 0 ≤ B)
    (reading : ∀ᶠ n : ℕ in atTop,|ordinaryPrimeCharge (b n) n| ≤ B*v n*Real.sqrt n*Real.log n) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ n y : ℕ,b n ≤ y → |M y n| ≤ C*v n*E y*Real.sqrt n := by
  obtain ⟨K,hK,localBound⟩ := ordinary_prime_reading_on_smaller_frozen_rows
  have top := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N,late⟩ := eventually_atTop.mp (reading.and (active.and (top.eventually_ge_atTop (4*(K+1)))))
  let C := max (N:ℝ) (4*B)
  have c0 : 0 ≤ C := (Nat.cast_nonneg N).trans (le_max_left ..)
  let A := fun n => C*v n
  have a0 (n : ℕ) : 0 ≤ A n := mul_nonneg c0 (zero_le_one.trans (v1 n))
  have inc : Monotone A := fun _ _ h => mul_le_mul_of_nonneg_left (hv h) c0
  have sp : 0<(1/2:ℝ) := by norm_num
  refine ⟨C,c0,fun n y hy => ?_⟩
  rw [Real.sqrt_eq_rpow]
  apply induction_above_a_moving_prime_cutoff b hb A inc a0 sp _ n y hy
  intro t ht ih
  let y := b t
  let H := A t*E y
  let Z := H*Real.sqrt t
  let L := Real.log (t:ℝ)
  have e1 : 1 ≤ E y := deletionPrice_one_le sp _
  have H0 : 0 ≤ H := mul_nonneg (a0 t) (zero_le_one.trans e1)
  have z0 : 0 ≤ Z := mul_nonneg H0 (Real.sqrt_nonneg _)
  have root1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr ht)
  change |M y t| ≤ H*(t:ℝ)^(1/2:ℝ)
  rw [←Real.sqrt_eq_rpow]
  by_cases early : t<N
  · apply (abs_coprimeMoebiusSum_le _ _).trans
    have c := (Nat.cast_le (α := ℝ)).mpr early.le
    exact (c.trans (le_max_left ..)).trans (((le_mul_of_one_le_right c0 (v1 t)).trans
      (le_mul_of_one_le_right (a0 t) e1)).trans (le_mul_of_one_le_right H0 root1))
  obtain ⟨observed,positive,high⟩ := late t (le_of_not_gt early)
  have lp : 0<L := by linarith only [high,hK]
  have rows (k : ℕ) (lt : k<t) : |M y k| ≤ H*Real.sqrt k := by
    have h := ih k lt
    rw [←Real.sqrt_eq_rpow] at h
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (inc lt.le) (zero_le_one.trans e1))
      (Real.sqrt_nonneg _))
  have err := localBound y t positive ht H H0 rows
  have scale : 4*(B*v t*Real.sqrt t) ≤ Z := by
    have fromB := mul_le_mul_of_nonneg_right (le_max_right (N:ℝ) (4*B)) (zero_le_one.trans (v1 t))
    have fee := le_mul_of_one_le_right (a0 t) e1
    exact (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_right (fromB.trans fee) (Real.sqrt_nonneg _))
  have tri := abs_sub (M y t*L+ordinaryPrimeCharge y t) (ordinaryPrimeCharge y t)
  rw [add_sub_cancel_right,abs_mul,abs_of_pos lp] at tri
  apply le_of_mul_le_mul_right _ lp
  change |M y t| *L ≤ Z*L
  change |M y t*L+ordinaryPrimeCharge y t| ≤ Z*(L/2+K) at err
  linarith only [tri,err,observed,mul_le_mul_of_nonneg_right scale lp.le,
    mul_le_mul_of_nonneg_left high z0,z0]

/-- One additional Euler product restores every integer in the sharp prefix. -/
theorem critical_full_prefix_from_the_ordinary_prime_reading (b : ℕ → ℕ) (hb : Monotone b)
    (active : ∀ᶠ n : ℕ in atTop,0<b n) (v : ℕ → ℝ) (hv : Monotone v) (v1 : ∀ n,1 ≤ v n)
    {B : ℝ} (hB : 0 ≤ B)
    (reading : ∀ᶠ n : ℕ in atTop,|ordinaryPrimeCharge (b n) n| ≤ B*v n*Real.sqrt n*Real.log n) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ X : ℕ,|coprimeMoebiusSum 1 X| ≤ C*v X*(E (b X))^2*Real.sqrt X := by
  obtain ⟨C,hC,rows⟩ := critical_inversion_of_the_ordinary_prime_reading b hb active v hv v1 hB reading
  refine ⟨C,hC,fun X => ?_⟩
  let y := b X
  have sp : 0<(1/2:ℝ) := by norm_num
  have e0 := zero_le_one.trans (deletionPrice_one_le sp y)
  have cap (k : ℕ) (hk : k ≤ X) : |M y k| ≤ (C*v X*E y)*(k:ℝ)^(1/2:ℝ) := by
    rw [←Real.sqrt_eq_rpow]
    exact (rows k y (hb hk)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hv hk) hC) e0) (Real.sqrt_nonneg _))
  have h := restore_full_row_from_prime_cutoff sp X y (mul_nonneg (mul_nonneg hC (zero_le_one.trans (v1 X))) e0) cap
  change |M 0 X| ≤ _ at h
  rw [show M 0 X=coprimeMoebiusSum 1 X by simp [M],←Real.sqrt_eq_rpow] at h
  exact h.trans_eq (by dsimp only [y,E]; ring)

/-- Conversely, a bound for the full Mertens prefix controls the actual
ordinary-prime reading at every fixed cutoff, at the first Euler price. -/
theorem ordinary_prime_readings_from_the_full_prefix (v : ℕ → ℝ) (hv : Monotone v)
    (v0 : ∀ n,0 ≤ v n) {C : ℝ} (hC : 0 ≤ C)
    (full : ∀ n,|coprimeMoebiusSum 1 n| ≤ C*v n*Real.sqrt n) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ X y : ℕ,0<X → 0<y →
      |ordinaryPrimeCharge y X| ≤ C*v X*E y*Real.sqrt X*(3*Real.log X/2+K) := by
  let A := fun n => C*v n
  have inc : Monotone A := fun _ _ h => mul_le_mul_of_nonneg_left (hv h) hC
  have a0 (n : ℕ) : 0 ≤ A n := mul_nonneg hC (v0 n)
  have sp : 0<(1/2:ℝ) := by norm_num
  have frozen (n y : ℕ) : |M y n| ≤ A n*E y*Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    apply induction_above_a_moving_prime_cutoff (fun _ => 0) (fun _ _ _ => le_rfl)
      A inc a0 sp _ n y (Nat.zero_le _)
    intro k _ _
    change |M 0 k| ≤ A k*E 0*(k:ℝ)^(1/2:ℝ)
    simpa [M,E,A,deletionPrice,←Real.sqrt_eq_rpow] using full k
  obtain ⟨K,hK,price⟩ := ordinary_prime_reading_on_smaller_frozen_rows
  refine ⟨K,hK,fun X y hx hy => ?_⟩
  let H := A X*E y
  have e0 := zero_le_one.trans (deletionPrice_one_le sp y)
  have cap (k : ℕ) (hk : k ≤ X) : |M y k| ≤ H*Real.sqrt k :=
    (frozen k y).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (inc hk) e0) (Real.sqrt_nonneg _))
  have err := price y X hy hx H (mul_nonneg (a0 X) e0) (fun k hk => cap k hk.le)
  have lx := Real.log_nonneg (Nat.one_le_cast.mpr hx)
  have tri := abs_sub (M y X*Real.log X+ordinaryPrimeCharge y X) (M y X*Real.log X)
  rw [add_sub_cancel_left,abs_mul,abs_of_nonneg lx] at tri
  change _ ≤ H*Real.sqrt X*(3*Real.log X/2+K)
  exact tri.trans ((add_le_add err (mul_le_mul_of_nonneg_right (cap X le_rfl) lx)).trans_eq (by ring))

#print axioms ordinary_prime_readings_from_the_full_prefix
#print axioms ordinary_prime_charge_as_a_quotient_sum
#print axioms ordinary_prime_reading_on_smaller_frozen_rows
#print axioms critical_full_prefix_from_the_ordinary_prime_reading

end GaloisForLFunctions.RestrictedFactorizationCalculus
