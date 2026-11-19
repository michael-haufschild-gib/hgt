import GaloisForLFunctions.RestrictedFactorizationCalculus.InvertingTheOrdinaryPrimeReadingAtSquareRoot
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCriticalEulerPriceOfTheLogSquareCutoff

/-!
# The Mertens criterion on one ordinary-prime reading

The same prime wall is used for every cofactor at each sharp endpoint.
One or two powers of the critical Euler price suffice to transfer any
increasing square-root allowance. This preserves both the family of
square-root-plus-epsilon bounds and the finer critical Euler scale.
-/

noncomputable section

open Finset Filter
open scoped Classical
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev b := logSquareCutoff
private abbrev E (X : ℕ) := deletionPrice (1/2) (b X)
private abbrev R (X : ℕ) := centeredOrdinaryPrimeRemainder (b X) X
private abbrev U (X : ℕ) := ordinaryPrimeCharge (b X) X
private abbrev M := coprimeMoebiusSum 1

/-- Cost of restoring the critical Euler factors and the logarithmic endpoint. -/
def criticalLogSquarePrice (X : ℕ) := ((b X:ℝ)+1)*(E X)^2

private abbrev P := criticalLogSquarePrice
private theorem e1 (X : ℕ) : 1 ≤ E X := deletionPrice_one_le (by norm_num) _
private theorem b1 (X : ℕ) : 1 ≤ (b X:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) (b X); linarith
private theorem p1 (X : ℕ) : 1 ≤ P X := one_le_mul_of_one_le_of_one_le (b1 _) (one_le_pow₀ (e1 _))
private theorem product_mono : Monotone P := by
  intro j k jk
  have e := deletionPrice_mono (by norm_num : 0<(1/2:ℝ)) (logSquareCutoff_mono jk)
  exact mul_le_mul (add_le_add_right (Nat.cast_le.mpr (logSquareCutoff_mono jk)) _)
    (pow_le_pow_left₀ (zero_le_one.trans (e1 j)) e 2) (sq_nonneg _) (zero_le_one.trans (b1 k))

/-- A sharp square-root estimate with the specified multiplicative allowance. -/
def squareRootAllowance (v f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ,0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,|f n| ≤ C*v n*Real.sqrt n

private theorem full_from_eventual {v : ℕ → ℝ} (v1 : ∀ n,1 ≤ v n) (h : squareRootAllowance v M) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ n,|M n| ≤ C*v n*Real.sqrt n := by
  obtain ⟨D,hD,pay⟩ := h
  obtain ⟨N,large⟩ := eventually_atTop.mp pay
  let C := max D (N:ℝ)
  have c0 : 0 ≤ C := hD.trans (le_max_left ..)
  refine ⟨C,c0,fun n => ?_⟩
  by_cases late : N ≤ n
  · exact (large n late).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left ..)
      (zero_le_one.trans (v1 _))) (Real.sqrt_nonneg _))
  rcases Nat.eq_zero_or_pos n with z | np
  · simp [z,M,coprimeMoebiusSum]
  · have bound := (abs_coprimeMoebiusSum_le 1 n).trans (Nat.cast_le.mpr (le_of_not_ge late))
    exact (bound.trans (le_max_right ..)).trans ((le_mul_of_one_le_right c0 (v1 n)).trans
      (le_mul_of_one_le_right (mul_nonneg c0 (zero_le_one.trans (v1 n))) (Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr np))))

private theorem center_price (X : ℕ) : |U X-R X| ≤ P X*Real.sqrt X := by
  let y := b X
  let S := RHTower.Sieve.smoothUpTo (Nat.primesLE y) (X/y)
  have root := Real.sqrt_le_sqrt ((Nat.cast_le (α := ℝ)).mpr (Nat.div_le_self X y))
  have e0 := zero_le_one.trans (e1 X)
  have bound := smooth_population_le_deletion_price (by norm_num : 0<(1/2:ℝ)) y (X/y)
  rw [←Real.sqrt_eq_rpow] at bound
  have sm : (S.card:ℝ) ≤ Real.sqrt X*E X := bound.trans (mul_le_mul_of_nonneg_right root e0)
  change |(R X+(y:ℝ)*S.card)-R X| ≤ _
  rw [add_sub_cancel_left,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  have square : E X ≤ (E X)^2 := by nlinarith only [e1 X,sq_nonneg (E X-1)]
  have cost : (y:ℝ)*E X ≤ P X := mul_le_mul (by linarith : (y:ℝ) ≤ y+1) square e0 (by positivity)
  exact (mul_le_mul_of_nonneg_left sm (Nat.cast_nonneg _)).trans
    ((le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_right cost (Real.sqrt_nonneg _)))

private theorem shift_center {v f g : ℕ → ℝ} (v1 : ∀ n,1 ≤ v n) (dif : ∀ n,|f n-g n| ≤ P n*Real.sqrt n)
    (h : squareRootAllowance v g) : squareRootAllowance (fun n => v n*P n) f := by
  obtain ⟨C,hC,room⟩ := h
  refine ⟨C+1,by linarith only [hC],?_⟩
  filter_upwards [room] with X hx
  have tri := abs_sub_le (f X) (g X) 0
  simp only [sub_zero] at tri
  have cost := le_mul_of_one_le_left (zero_le_one.trans (p1 X)) (v1 X)
  have keep := le_mul_of_one_le_right (mul_nonneg hC (zero_le_one.trans (v1 X))) (p1 X)
  apply tri.trans ((add_le_add (dif X) hx).trans ?_)
  dsimp only
  linarith only [mul_le_mul_of_nonneg_right cost (Real.sqrt_nonneg X),
    mul_le_mul_of_nonneg_right keep (Real.sqrt_nonneg X)]

private theorem log_le_wall (X : ℕ) (xp : 0<X) : Real.log X ≤ (b X:ℝ)+1 := by
  let t := Real.log ((X:ℝ)+1)
  have relate := Real.log_le_log (Nat.cast_pos.mpr xp) (by linarith : (X:ℝ) ≤ X+1)
  have sq := Nat.le_self_pow (by decide : 2 ≠ 0) ⌊t⌋₊
  exact relate.trans ((Nat.lt_floor_add_one t).le.trans (add_le_add_right (Nat.cast_le.mpr sq) _))

private theorem allowance_mono {v w f : ℕ → ℝ} (le : ∀ᶠ n : ℕ in atTop,v n ≤ w n)
    (h : squareRootAllowance v f) : squareRootAllowance w f := by
  obtain ⟨C,hC,room⟩ := h
  exact ⟨C,hC,le.and room |>.mono (fun n hh => hh.2.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh.1 hC) (Real.sqrt_nonneg n)))⟩

/-- Every increasing allowance transfers from the single ordinary-prime
reading to the full prefix at one critical price, and conversely. -/
theorem uncentered_ordinary_prime_transfer (v : ℕ → ℝ) (hv : Monotone v) (v1 : ∀ n,1 ≤ v n) :
    (squareRootAllowance v U → squareRootAllowance (fun n => v n*P n) M) ∧
    (squareRootAllowance v M → squareRootAllowance (fun n => v n*P n) U) := by
  have act := logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1
  have logs := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  constructor
  · rintro ⟨B,hB,h⟩
    have read : ∀ᶠ n : ℕ in atTop,|U n| ≤ B*v n*Real.sqrt n*Real.log n := by
      filter_upwards [h,logs.eventually_ge_atTop 1] with n hn wall
      exact hn.trans (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hB (zero_le_one.trans (v1 n)))
        (Real.sqrt_nonneg n)) wall)
    obtain ⟨C,hC,full⟩ := critical_full_prefix_from_the_ordinary_prime_reading b logSquareCutoff_mono act v hv v1 hB read
    refine ⟨C,hC,Eventually.of_forall (fun X => ?_)⟩
    have cheap := le_mul_of_one_le_left (sq_nonneg (E X)) (b1 X)
    exact (full X).trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left cheap (mul_nonneg hC (zero_le_one.trans (v1 _)))) (Real.sqrt_nonneg _)).trans_eq (by ring))
  · intro h
    obtain ⟨C,hC,full⟩ := full_from_eventual v1 h
    obtain ⟨K,hK,read⟩ := ordinary_prime_readings_from_the_full_prefix v hv
      (fun n => zero_le_one.trans (v1 n)) hC full
    refine ⟨C*(2+K),mul_nonneg hC (by linarith only [hK]),?_⟩
    filter_upwards [act,eventually_ge_atTop (1:ℕ)] with n wall pos
    have lower := b1 n
    have scaled := le_mul_of_one_le_right hK lower
    have room : 3*Real.log n/2+K ≤ (2+K)*((b n:ℝ)+1) := by
      linarith only [log_le_wall n pos,scaled,lower]
    have square : E n ≤ (E n)^2 := by nlinarith only [e1 n,sq_nonneg (E n-1)]
    have gain := mul_le_mul square room
      (show 0 ≤ 3*Real.log n/2+K by have := Real.log_nonneg (Nat.one_le_cast.mpr pos); linarith only [this,hK])
      (sq_nonneg _)
    have base := mul_nonneg (mul_nonneg hC (zero_le_one.trans (v1 n))) (Real.sqrt_nonneg n)
    apply (read n (b n) pos wall).trans
    calc _ = (C*v n*Real.sqrt n)*(E n*(3*Real.log n/2+K)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left gain base
         _ = _ := by dsimp only [P,criticalLogSquarePrice]; ring

private theorem product_is_subpower {η : ℝ} (hη : 0<η) : ∀ᶠ X : ℕ in atTop,P X ≤ (X:ℝ)^η := by
  obtain ⟨C,_,price⟩ := critical_deletion_at_the_log_square_cutoff
  have logs := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [price,(Real.tendsto_log_atTop.comp logs).eventually_ge_atTop (C/η),
    (Real.tendsto_log_atTop.comp logs).eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)] with X cost late large pos
  have lx := Real.log_nonneg (Nat.one_le_cast.mpr pos)
  have lpos := zero_lt_one.trans_le large
  have fe := (div_le_iff₀ hη).mp late
  have budget : C*Real.log X/Real.log (Real.log X) ≤ Real.log X*η := (div_le_iff₀ lpos).mpr (by
    linarith only [mul_le_mul_of_nonneg_right fe lx])
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr pos)]
  exact cost.2.trans (Real.exp_le_exp.mpr budget)

private def powerWeight (η : ℝ) (n : ℕ) := (max 1 (n:ℝ))^η
private theorem power_weight_mono {η : ℝ} (hη : 0 ≤ η) : Monotone (powerWeight η) :=
  fun _ _ h => Real.rpow_le_rpow (by positivity) (max_le_max_left _ (Nat.cast_le.mpr h)) hη
private theorem power_weight_one {η : ℝ} (hη : 0 ≤ η) (n : ℕ) : 1 ≤ powerWeight η n :=
  Real.one_le_rpow (le_max_left ..) hη

private theorem power_allowance {η : ℝ} (hη : 0<η) {f : ℕ → ℝ} (zero : f 0=0) :
    squareRootAllowance (powerWeight η) f ↔ PrefixPower (1/2+η) f := by
  have eq (n : ℕ) (hn : 1 ≤ n) : powerWeight η n*Real.sqrt n=(n:ℝ)^(1/2+η) := by
    rw [powerWeight,max_eq_right (Nat.one_le_cast.mpr hn),Real.sqrt_eq_rpow,←Real.rpow_add (Nat.cast_pos.mpr hn)]
    congr 1; ring
  constructor
  · rintro ⟨C,_,bound⟩
    apply prefixPower_of_eventual (C := C) zero (by linarith only [hη])
    filter_upwards [bound,eventually_ge_atTop (1:ℕ)] with n hn pos
    simpa only [mul_assoc,eq n pos] using hn
  · rintro ⟨C,hC,bound⟩
    refine ⟨C,hC,?_⟩
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n pos
    simpa only [mul_assoc,eq n pos] using bound n

private theorem stable_under_one_price {f g : ℕ → ℝ} (f0 : f 0=0) (g0 : g 0=0)
    (transfer : ∀ v : ℕ → ℝ,Monotone v → (∀ n,1 ≤ v n) →
      squareRootAllowance v f → squareRootAllowance (fun n => v n*P n) g)
    (h : ∀ η : ℝ,0<η → PrefixPower (1/2+η) f) : ∀ η : ℝ,0<η → PrefixPower (1/2+η) g := by
  intro η hη
  have half := half_pos hη
  have pay := transfer _ (power_weight_mono half.le) (power_weight_one half.le)
    ((power_allowance half f0).mpr (h _ half))
  apply (power_allowance hη g0).mp
  apply allowance_mono _ pay
  filter_upwards [product_is_subpower half,eventually_ge_atTop (1:ℕ)] with X cost pos
  simp only [powerWeight,max_eq_right (Nat.one_le_cast.mpr pos)]
  exact (mul_le_mul_of_nonneg_left cost (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq
    (by rw [←Real.rpow_add (Nat.cast_pos.mpr pos)]; congr 1; ring)

/-- The actual Mertens square-root criterion can be tested on one
ordinary-prime quotient sum, either with or without its floor center. -/
theorem square_root_iff_one_ordinary_prime_reading :
    let sharp := fun f : ℕ → ℝ => ∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) f
    (sharp (fun X => ordinaryPrimeCharge (logSquareCutoff X) X) ↔ sharp (coprimeMoebiusSum 1)) ∧
    (sharp (fun X => centeredOrdinaryPrimeRemainder (logSquareCutoff X) X) ↔ sharp (coprimeMoebiusSum 1)) := by
  have m0 : M 0=0 := by simp [M,coprimeMoebiusSum]
  have u0 : U 0=0 := by rw [U,ordinary_prime_charge_as_a_quotient_sum]; simp [RoughReading.freeSet]
  have r0 : R 0=0 := by simp [R,centeredOrdinaryPrimeRemainder,RoughReading.freeSet]
  have both := Iff.intro
    (stable_under_one_price u0 m0 (fun v hv h1 => (uncentered_ordinary_prime_transfer v hv h1).1))
    (stable_under_one_price m0 u0 (fun v hv h1 => (uncentered_ordinary_prime_transfer v hv h1).2))
  refine ⟨both,Iff.trans ?_ both⟩
  exact ⟨stable_under_one_price r0 u0 (fun _ _ h1 => shift_center h1 center_price),
    stable_under_one_price u0 r0 (fun _ _ h1 => shift_center h1 (fun n => by rw [abs_sub_comm]; exact center_price n))⟩

/-- The finite-power Euler scale is exactly square root times
exp(O(log X/log log X)), including all sufficiently large endpoints. -/
theorem critical_euler_allowances_in_logarithmic_coordinates (f : ℕ → ℝ) :
    (∃ j : ℕ,squareRootAllowance (fun X => P X^j) f) ↔
      ∃ A C : ℝ,0 ≤ A ∧ 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop,
        |f X| ≤ C*Real.exp (A*Real.log X/Real.log (Real.log X))*Real.sqrt X := by
  obtain ⟨D,hD,price⟩ := critical_deletion_at_the_log_square_cutoff
  have logs := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  constructor
  · rintro ⟨j,C,hC,bound⟩
    refine ⟨j*D,C,mul_nonneg (Nat.cast_nonneg _) hD.le,hC,?_⟩
    filter_upwards [price,bound] with X paid good
    have pp := zero_lt_one.trans_le (p1 X)
    have le := Real.log_le_log pp paid.2
    rw [Real.log_exp] at le
    have cap : P X^j ≤ Real.exp (j*D*Real.log X/Real.log (Real.log X)) := by
      apply (Real.log_le_log_iff (pow_pos pp _) (Real.exp_pos _)).mp
      rw [Real.log_pow,Real.log_exp]
      exact (mul_le_mul_of_nonneg_left le (Nat.cast_nonneg _)).trans_eq (by ring)
    exact good.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cap hC) (Real.sqrt_nonneg _))
  · rintro ⟨A,C,hA,hC,bound⟩
    obtain ⟨j,hj⟩ := exists_nat_ge (32*A)
    refine ⟨j,C,hC,?_⟩
    filter_upwards [price,bound,logs.eventually_ge_atTop 1,(Real.tendsto_log_atTop.comp logs).eventually_ge_atTop 1]
      with X cost good log1 ll1
    let L := Real.log (X:ℝ)
    have pp := zero_lt_one.trans_le (p1 X)
    have llp : 0<Real.log L := zero_lt_one.trans_le ll1
    have es : E X ≤ (E X)^2 := by nlinarith only [e1 X,sq_nonneg (E X-1)]
    have ep : E X ≤ P X := es.trans (le_mul_of_one_le_left (sq_nonneg _) (b1 X))
    have lo := cost.1.trans (mul_le_mul_of_nonneg_right (Real.log_le_log (zero_lt_one.trans_le (e1 X)) ep) llp.le)
    have coef : A ≤ (j:ℝ)*(1/32) := by linarith only [hj]
    have cap : Real.exp (A*L/Real.log L) ≤ P X^j := by
      apply (Real.log_le_log_iff (Real.exp_pos _) (pow_pos pp j)).mp
      rw [Real.log_exp,Real.log_pow,div_le_iff₀ llp]
      linarith only [mul_le_mul_of_nonneg_left lo (Nat.cast_nonneg (α := ℝ) j),
        mul_le_mul_of_nonneg_right coef (zero_le_one.trans log1)]
    exact good.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cap hC) (Real.sqrt_nonneg _))

private theorem stable_at_the_critical_euler_scale {f g : ℕ → ℝ}
    (transfer : ∀ v : ℕ → ℝ,Monotone v → (∀ n,1 ≤ v n) →
      squareRootAllowance v f → squareRootAllowance (fun n => v n*P n) g)
    (h : ∃ j : ℕ,squareRootAllowance (fun X => P X^j) f) :
    ∃ j : ℕ,squareRootAllowance (fun X => P X^j) g := by
  obtain ⟨j,cap⟩ := h
  exact ⟨j+1,by simpa only [pow_succ] using transfer _ (fun a _ hab =>
    pow_le_pow_left₀ (zero_le_one.trans (p1 a)) (product_mono hab) j) (fun n => one_le_pow₀ (p1 n)) cap⟩

/-- The ordinary-prime criterion preserves the finer physical scale
sqrt X exp(O(log X/log log X)), for both the raw and centered readings. -/
theorem critical_scale_iff_one_ordinary_prime_reading :
    let bound := fun f : ℕ → ℝ => ∃ A C : ℝ,0 ≤ A ∧ 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop,
      |f X| ≤ C*Real.exp (A*Real.log X/Real.log (Real.log X))*Real.sqrt X
    (bound (fun X => ordinaryPrimeCharge (logSquareCutoff X) X) ↔ bound (coprimeMoebiusSum 1)) ∧
    (bound (fun X => centeredOrdinaryPrimeRemainder (logSquareCutoff X) X) ↔ bound (coprimeMoebiusSum 1)) := by
  dsimp only
  rw [←critical_euler_allowances_in_logarithmic_coordinates U,
    ←critical_euler_allowances_in_logarithmic_coordinates M,←critical_euler_allowances_in_logarithmic_coordinates R]
  have both := Iff.intro
    (stable_at_the_critical_euler_scale (fun v hv h1 => (uncentered_ordinary_prime_transfer v hv h1).1))
    (stable_at_the_critical_euler_scale (fun v hv h1 => (uncentered_ordinary_prime_transfer v hv h1).2))
  refine ⟨both,Iff.trans ?_ both⟩
  exact ⟨stable_at_the_critical_euler_scale (fun _ _ h1 => shift_center h1 center_price),
    stable_at_the_critical_euler_scale (fun _ _ h1 => shift_center h1 (fun n => by rw [abs_sub_comm]; exact center_price n))⟩

#print axioms critical_scale_iff_one_ordinary_prime_reading
#print axioms uncentered_ordinary_prime_transfer
#print axioms square_root_iff_one_ordinary_prime_reading

end GaloisForLFunctions.RestrictedFactorizationCalculus
