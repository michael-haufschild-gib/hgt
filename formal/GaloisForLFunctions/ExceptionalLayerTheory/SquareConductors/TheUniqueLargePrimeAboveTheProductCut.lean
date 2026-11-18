import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheCenteredMangoldtTailOfTheProduct

/-!
# A short cofactor cap in the long product

Thinning the original cap at a power of the conductor costs an explicit
amount on every terminal interval, independently of the product cutoff.
Beyond the product of the new cap and the conductor, the first prime
exceeds the conductor and is the unique large prime divisor.
-/

noncomputable section
open Finset ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem centered_power_cap_error {d : ℝ} (hd : d ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n → ∀ U : ℕ,
      |centeredProductReading U n-cappedUpperProductReading U ⌊(n:ℝ)^d⌋₊ n| ≤
        C*conductorLog n*(n:ℝ)^(1-d) := by
  obtain ⟨A,hA,ha⟩ := capped_centered_product_error
  obtain ⟨T,hT,hwin⟩ := successorSquare_window_bound
  obtain ⟨D,_,hD,_,hdiff⟩ := sampledSpline_differences
  obtain ⟨J,hJ,hlog⟩ := splineHorizon_conductorLog
  have hT0 := zero_le_one.trans hT
  refine ⟨T^2*A*J*(T+T^2)*D,by positivity,fun {n} hn U => ?_⟩
  let L := splineHorizon n
  let b := ⌊(n:ℝ)^d⌋₊
  let H := conductorLog n
  let E := (n:ℝ)^(1-d)
  let Y (k : ℕ) := max (productLower 1 k) U
  let g (k : ℕ) := centeredProductTail k (Y k) - ordinaryFactorTail 4 k (cappedCoprimeSlice 1 1 k (Y k) b)
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have he : 1 ≤ E := Real.one_le_rpow (by exact_mod_cast hn) (sub_nonneg.mpr hd)
  have he₀ := zero_le_one.trans he
  have hH : 0 ≤ H := zero_le_one.trans (conductorLog_one_le n)
  have hL : (L:ℝ) ≤ (T*n)^2 := hwin hn
  have heq : (n:ℝ)*E*(n:ℝ)^d=(n:ℝ)^2 := by
    dsimp only [E]; rw [mul_assoc,←Real.rpow_add hn',sub_add_cancel,Real.rpow_one,sq]
  have hfloor : (n:ℝ)^d ≤ ((b+1:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one ((n:ℝ)^d)).le
  have hrow (k : ℕ) (hk : k ∈ Icc 1 L) :
      |g k| ≤ A*(J*H)*((T+T^2)*n*E) := by
    obtain ⟨hk₁,hkL⟩ := mem_Icc.mp hk
    have hk' := (Nat.cast_le.mpr hkL : (k:ℝ) ≤ L).trans hL
    have hroot := Real.sqrt_le_sqrt hk'
    rw [Real.sqrt_sq (mul_nonneg hT0 hn'.le)] at hroot
    have hq : ((k/(b+1):ℕ):ℝ) ≤ T^2*n*E := by
      apply Nat.cast_div_le.trans
      apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos b) : (0:ℝ)<(b+1:ℕ))).mpr
      calc (k:ℝ) ≤ (T*n)^2 := hk'
           _ = T^2*n*E*(n:ℝ)^d := by rw [mul_pow,←heq]; ring
           _ ≤ _ := mul_le_mul_of_nonneg_left hfloor (by positivity)
    have hw := (hroot.trans (le_mul_of_one_le_right (mul_nonneg hT0 hn'.le) he))
    have hs : Real.sqrt k+((k/(b+1):ℕ):ℝ) ≤ (T+T^2)*n*E := (add_le_add hw hq).trans_eq (by ring)
    have hl := Real.log_le_log (Nat.cast_pos.mpr hk₁) (Nat.cast_le.mpr hkL : (k:ℝ) ≤ L)
    exact (ha hk₁ (Y k) b).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left ((add_le_add_left hl 1).trans (hlog hn)) hA) hs
      (by positivity) (by positivity))
  unfold centeredProductReading cappedUpperProductReading splineCountReading
  rw [←sum_sub_distrib]
  simp_rw [←sub_mul]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _k ∈ Icc 1 L, (A*(J*H)*((T+T^2)*n*E))*(D/(n:ℝ)^3) := by
           apply sum_le_sum
           intro k hk
           rw [abs_mul]
           exact mul_le_mul (hrow k hk) ((hdiff hn k).1) (abs_nonneg _) (by positivity)
       _ ≤ (T*n)^2*((A*(J*H)*((T+T^2)*n*E))*(D/(n:ℝ)^3)) := by
           rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
           exact mul_le_mul_of_nonneg_right hL (by positivity)
       _ = _ := by change _ = _*H*E; field_simp

/-- Price of all omitted cofactors on every fragment of the original signed
sum. The product cutoff is arbitrary, including a different integer in
every conductor. -/
theorem power_cofactor_cap_fragment {d : ℝ} (hd : d ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : ℕ → ℕ) (J M : ℕ), 0 < M →
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading (U n) n n -
        cappedUpperProductReading (U n) ⌊(n:ℝ)^d⌋₊ n)| ≤ C*(M:ℝ)^(4-d)*conductorLog M := by
  obtain ⟨A,hA,ha⟩ := centered_power_cap_error hd
  obtain ⟨B,hB,hb⟩ := capped_centered_reading_error
  refine ⟨B+A,add_nonneg hB hA,fun U J M hM => ?_⟩
  have hM' : (0:ℝ) < M := Nat.cast_pos.mpr hM
  let E := (M:ℝ)^(1-d)
  let H := conductorLog M
  have he₁ : 1 ≤ E := Real.one_le_rpow (by exact_mod_cast hM) (sub_nonneg.mpr hd)
  have hE := zero_le_one.trans he₁
  have hH : 0 ≤ H := zero_le_one.trans (conductorLog_one_le M)
  let V (n : ℕ) := cappedUpperProductReading (U n) n n
  let W (n : ℕ) := cappedUpperProductReading (U n) ⌊(n:ℝ)^d⌋₊ n
  let R (n : ℕ) := centeredProductReading (U n) n
  have hrow (n : ℕ) (hn : n ∈ Ioc J M) : |(n:ℝ)^2*(V n-W n)| ≤ (M:ℝ)^2*((B+A)*H*E) := by
    obtain ⟨hjn,hnm⟩ := mem_Ioc.mp hn
    have hn₀ := (Nat.zero_le J).trans_lt hjn
    have hi := conductorLog_mono hn₀ hnm
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg n) (Nat.cast_le.mpr hnm) (sub_nonneg.mpr hd)
    have hleft : |V n-R n| ≤ B*H*E := by
      rw [abs_sub_comm]
      exact (hb hn₀ (U n)).trans ((mul_le_mul_of_nonneg_left hi hB).trans
        (le_mul_of_one_le_right (mul_nonneg hB hH) he₁))
    have hright : |R n-W n| ≤ A*H*E := (ha hn₀ (U n)).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hi hA) hp (Real.rpow_nonneg (Nat.cast_nonneg n) _) (mul_nonneg hA hH))
    have h := abs_add_le (V n-R n) (R n-W n)
    rw [sub_add_sub_cancel] at h
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg n) (Nat.cast_le.mpr hnm) 2)
      (h.trans ((add_le_add hleft hright).trans_eq (by ring))) (abs_nonneg _) (sq_nonneg _)
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _n ∈ Ioc J M, (M:ℝ)^2*((B+A)*H*E) := sum_le_sum hrow
       _ ≤ M*((M:ℝ)^2*((B+A)*H*E)) := by
         rw [sum_const,Nat.card_Ioc,nsmul_eq_mul]
         exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M J)) (by positivity)
       _ = _ := by
         rw [show 4-d=3+(1-d) by ring,Real.rpow_add hM',Real.rpow_natCast _ 3]
         dsimp only [E,H]; ring

/-- The square-root cofactor cutoff costs only exponent 7/2 with one log,
uniformly at the seventeen-ninths product boundary. -/
theorem seventeenNinths_square_root_cofactor_cap :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J M : ℕ, 0 < M →
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ ⌊Real.sqrt n⌋₊ n)| ≤
          C*(M:ℝ)^(7/2:ℝ)*conductorLog M := by
  obtain ⟨C,hC,h⟩ := power_cofactor_cap_fragment (d := 1/2) (by norm_num)
  refine ⟨C,hC,fun J M hM => ?_⟩
  simpa only [Real.sqrt_eq_rpow,show (4:ℝ)-1/2=7/2 by norm_num] using
    h (fun n => ⌊(n:ℝ)^(17/9:ℝ)⌋₊) J M hM

/-- With complementary exponents d and 1+d the first prime exceeds the
conductor. In particular every eligible product has a unique large prime
and the coprimality test is automatic. -/
theorem unique_prime_beyond_conductor {d : ℝ} (hd : d ≤ 1) {n k p v : ℕ} (hn : 0<n) (hp : p.Prime)
    (hv : v ∈ Ioc (max (productLower 1 k) ⌊(n:ℝ)^(1+d)⌋₊ /p) (min (k/p) ⌊(n:ℝ)^d⌋₊)) :
    n < p ∧ p.Coprime v ∧ ∃! r : ℕ, r.Prime ∧ r ∣ p*v ∧ ⌊(n:ℝ)^d⌋₊ < r := by
  let b := ⌊(n:ℝ)^d⌋₊
  let U := ⌊(n:ℝ)^(1+d)⌋₊
  have hn' := Nat.cast_pos.mpr (α := ℝ) hn
  have hb : (b:ℝ) ≤ (n:ℝ)^d := Nat.floor_le (Real.rpow_nonneg hn'.le _)
  have hbn : b ≤ n := Nat.cast_le.mp (hb.trans ((Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hn) hd).trans_eq (Real.rpow_one _)))
  have hnb : n*b ≤ U := by
    apply Nat.le_floor
    rw [Nat.cast_mul,Real.rpow_add hn',Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hb hn'.le
  have hq := (capped_upper_ranges hp.pos hv).1
  have hvb := (mem_Ioc.mp hv).2.trans (min_le_right _ _)
  have hbig : n < p := lt_of_not_ge fun hh => hq.not_ge ((Nat.mul_le_mul hh hvb).trans hnb)
  have hs : b^2 ≤ U := (show b^2 ≤ n*b by simpa only [sq] using Nat.mul_le_mul_right b hbn).trans hnb
  exact ⟨hbig,capped_upper_unique_large_prime hp hs hq hvb⟩

#print axioms power_cofactor_cap_fragment
#print axioms seventeenNinths_square_root_cofactor_cap
#print axioms unique_prime_beyond_conductor
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
