import GaloisForLFunctions.ExceptionalLayerTheory.CancellationOnRepeatedPrimeFactors
import GaloisForLFunctions.ExceptionalLayerTheory.PrimeCountsOnAdjustableProductIntervals

/-!
# Coprime ordinary prime factors at both Vaughan widths

At every divided horizon the first factor can be restricted to ordinary
primes coprime to their complementary factor. Both factor cutoffs grow
as a positive power of the horizon at each target exponent.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem positive_interval (L X : ℕ) : Ioc L X = (Icc 1 X).filter (fun n => L < n) := by
  ext n
  simp only [mem_Ioc,mem_filter,mem_Icc]
  omega

/-- Reversing the high product interval keeps the exact first-factor and
quotient endpoints. The inner coefficient already vanishes through D. -/
theorem adjustable_product_slices (D R X : ℕ) :
    adjustableProductRow D R X = ∑ u ∈ Ioc D X, vonMangoldt u*factorSlice D R X (productLower D X) u := by
  let Y := productLower D X
  let f (u v : ℕ) := if D<u ∧ Y<u*v then vonMangoldt u*innerJump D v*centeredPrimeWeight R (X/(u*v)) else 0
  have hi : adjustableProductRow D R X = ∑ n ∈ Icc 1 X, ∑ q ∈ n.divisorsAntidiagonal, f q.1 q.2 := by
    unfold adjustableProductRow
    rw [positive_interval,sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hy : Y<n
    · rw [if_pos hy,balancedProduct,sum_mul,sum_filter]
      apply sum_congr rfl
      intro q hq
      have he := (Nat.mem_divisorsAntidiagonal.mp hq).1
      dsimp only [f]; rw [he]
      by_cases hu : D<q.1
      · rw [if_pos (show D<q.1 ∧ Y<n from ⟨hu,hy⟩)]
        by_cases hv : D<q.2
        · rw [if_pos (show D<q.1 ∧ D<q.2 from ⟨hu,hv⟩)]
        · rw [if_neg (fun h : D<q.1 ∧ D<q.2 => hv h.2),innerJump_small (Nat.le_of_not_gt hv),mul_zero,zero_mul]
      · simp [hu]
    · rw [if_neg hy]
      symm
      apply sum_eq_zero
      intro q hq
      simp [f,(Nat.mem_divisorsAntidiagonal.mp hq).1,hy]
  rw [hi,Sieve.sum_Icc_divisorsAntidiagonal_swap f,positive_interval D X,sum_filter]
  apply sum_congr rfl
  intro u hu
  have hu₁ := (mem_Icc.mp hu).1
  by_cases hd : D<u
  · rw [if_pos hd,factorSlice,positive_interval,sum_filter,mul_sum]
    apply sum_congr rfl
    intro v _
    have he : Y/u<v ↔ Y<u*v := by rw [Nat.div_lt_iff_lt_mul hu₁,Nat.mul_comm v u]
    dsimp only [f]
    by_cases hy : Y/u<v
    · rw [if_pos ⟨hd,he.mp hy⟩,if_pos hy,Nat.div_div_eq_div_mul]; ring
    · rw [if_neg (fun hh => hy (he.mpr hh.2)),if_neg hy,mul_zero]
  · rw [if_neg hd]
    exact sum_eq_zero fun v _ => by simp [f,hd]

private theorem initial_factor_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {D R X : ℕ} {H : ℝ}, 1 ≤ D → 1 ≤ R → 1 ≤ H → (D : ℝ) ≤ H → (R : ℝ) ≤ H →
      |adjustableProductRow D R X-longFactorRow D R X (productLower D X)| ≤ K*H^3*Real.sqrt X := by
  obtain ⟨C,hC,h⟩ := factor_slice_bounds
  refine ⟨56*C,by positivity,?_⟩
  intro D R X H hD hR hH hd hr
  let Y := productLower D X
  let U := 2*(D+1)
  let S := (Ioc D X).filter (fun u => u ≤ U)
  let a := fun u => vonMangoldt u*factorSlice D R X Y u
  have htail : (Ioc D X).filter (fun u => ¬u ≤ U) = Ioc U X := by
    ext u
    simp only [mem_filter,mem_Ioc,not_le]
    dsimp [U]; omega
  have he := sum_filter_add_sum_filter_not (Ioc D X) (fun u => u≤U) a
  rw [htail] at he
  rw [adjustable_product_slices]
  change |(∑ u ∈ Ioc D X, a u)-(∑ u ∈ Ioc U X, a u)| ≤ _
  rw [←he,add_sub_cancel_right]
  let A := C*((D+1 : ℕ) : ℝ)*R*Real.sqrt X
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs := (h hD hR X Y).1
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ u ∈ S, A*vonMangoldt u := by
            apply sum_le_sum
            intro u hu
            have hu₁ := (mem_Ioc.mp (mem_filter.mp hu).1).1
            have hroot : 1 ≤ Real.sqrt u := by
              simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ u by exact_mod_cast (by omega : 1 ≤ u))
            dsimp only [a]
            rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg,mul_comm]
            exact mul_le_mul_of_nonneg_right ((hs u).trans (div_le_self hA hroot)) vonMangoldt_nonneg
       _ ≤ A*(7*U) := by
            rw [←mul_sum]
            apply mul_le_mul_of_nonneg_left _ hA
            apply le_trans _ (chebyshevPsi_le_seven U)
            apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => vonMangoldt_nonneg)
            intro u hu
            obtain ⟨hi,hle⟩ := mem_filter.mp hu
            exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hi).1; omega,hle⟩
       _ ≤ _ := by
            have hd₁ : ((D+1 : ℕ) : ℝ) ≤ 2*H := by push_cast; linarith only [hH,hd]
            have hU : (U : ℝ) ≤ 4*H := by dsimp [U]; push_cast at hd₁ ⊢; linarith only [hd₁]
            have hh := mul_le_mul (mul_le_mul hd₁ hr (Nat.cast_nonneg R) (by positivity)) hU
              (Nat.cast_nonneg U) (by positivity)
            dsimp [A]
            linarith only [mul_le_mul_of_nonneg_left hh (mul_nonneg hC (Real.sqrt_nonneg (X : ℝ)))]

/-- Quantitative transfer to coprime prime factors, uniform in the two
cutoffs, the integer horizon, and its logarithm. -/
theorem coprime_prime_row_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {D R X : ℕ} {H : ℝ}, 1 ≤ X → 1 ≤ D → 1 ≤ R → 1 ≤ H →
      (D : ℝ) ≤ H → (R : ℝ) ≤ H → Real.log X ≤ H →
      |(Chebyshev.psi X-X)-coprimePrimeRow D R X (productLower D X)| ≤ K*H^5*Real.sqrt X := by
  obtain ⟨C,hC,h₁⟩ := adjustable_product_bound
  obtain ⟨A,hA,h₂⟩ := initial_factor_bound
  obtain ⟨B,hB,h₃⟩ := repeated_prime_factors_bound
  refine ⟨C+A+4*B,by positivity,?_⟩
  intro D R X H hx hD hR hH hd hr hlog
  let Y := productLower D X
  let T := H^5*Real.sqrt X
  have h32 : H^3*Real.sqrt X ≤ T := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH (by norm_num : 3≤5)) (Real.sqrt_nonneg _)
  have hrep := h₃ hD hR hx Y
  have hprod := mul_le_mul (mul_le_mul (show ((D+1 : ℕ) : ℝ) ≤ 2*H by push_cast; linarith only [hH,hd]) hr
    (Nat.cast_nonneg R) (by positivity)) (show 1+Real.log X ≤ 2*H by linarith only [hlog,hH])
    (by have := Real.log_natCast_nonneg X; positivity) (by positivity)
  have hrep' : |longFactorRow D R X Y-coprimePrimeRow D R X Y| ≤ 4*B*T := by
    apply hrep.trans
    linarith only [mul_le_mul_of_nonneg_left hprod (mul_nonneg hB (Real.sqrt_nonneg (X : ℝ))),
      mul_le_mul_of_nonneg_left h32 (show 0 ≤ 4*B by positivity)]
  have ht : (Chebyshev.psi X-X)-coprimePrimeRow D R X Y =
      ((Chebyshev.psi X-X)-adjustableProductRow D R X)+(adjustableProductRow D R X-longFactorRow D R X Y)+
        (longFactorRow D R X Y-coprimePrimeRow D R X Y) := by ring
  rw [ht]
  apply (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
  have hh : |(Chebyshev.psi X-X)-adjustableProductRow D R X| ≤ C*T := by
    simpa only [T,mul_assoc] using h₁ hx hR hH hd hr hlog
  have hs : |adjustableProductRow D R X-longFactorRow D R X Y| ≤ A*T := by
    have hl := h₂ (X := X) hD hR hH hd hr
    rw [mul_assoc A] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left h32 hA)
  rw [mul_assoc (C+A+4*B)]
  change _ ≤ (C+A+4*B)*T
  linarith only [hh,hs,hrep']

/-- Both endpoints of the product window and the coprimality restriction
can be imposed directly in the finite prime sum. -/
theorem coprime_prime_support {R : ℕ} (hR : 1 ≤ R) (D X Y : ℕ) :
    coprimePrimeRow D R X Y =
      ∑ p ∈ (Ioc (2*(D+1)) X).filter Nat.Prime, Real.log p*
        ∑ v ∈ Ioc (max D (Y/p)) (X/p/R) with p.Coprime v,
          innerJump D v*centeredPrimeWeight R (X/p/v) := by
  unfold coprimePrimeRow
  apply sum_congr rfl
  intro p hp
  rw [vonMangoldt_apply_prime (mem_filter.mp hp).2]
  congr 1
  unfold coprimeSlice
  symm
  apply sum_subset
  · intro v hv
    obtain ⟨hh,hc⟩ := mem_filter.mp hv
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hh
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(le_max_right ..).trans_lt hl,hu.trans (Nat.div_le_self ..)⟩,hc⟩
  · intro v hv hout
    obtain ⟨hh,hc⟩ := mem_filter.mp hv
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hh
    by_cases hd : v ≤ D
    · rw [innerJump_small hd,zero_mul]
    · have hgt : X/p/R < v := by
        by_contra! hle
        exact hout (mem_filter.mpr ⟨mem_Ioc.mpr ⟨max_lt (by omega) hl,hle⟩,hc⟩)
      have hv₁ : 0 < v := by omega
      have hlt : X/p/v < R := (Nat.div_lt_iff_lt_mul hv₁).mpr
        (by simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hR).mp hgt)
      rw [centeredPrimeWeight_small ((Nat.one_le_div_iff hv₁).mpr hu) hlt,mul_zero]

/-- Cutoffs growing at a positive power of each individual divided horizon. -/
def coprimeHorizon (δ : ℝ) (X : ℕ) : ℝ :=
  let D := ⌊(X : ℝ)^δ⌋₊
  coprimePrimeRow D D X (productLower D X)

/-- A nondecreasing error bound at divided horizons costs at most the
total absolute mass of the truncated Vaughan coefficients. -/
theorem cofactor_sum_majorant (f g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n)
    (hmono : ∀ x n : ℕ, 1 ≤ x → x ≤ n → g x ≤ g n)
    (h : ∀ x : ℕ, 1 ≤ x → |f x| ≤ g x) (V W N : ℕ) :
    |∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*f (N/d)| ≤
      (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*g N := by
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ d ∈ Icc 1 (min N W), |Sieve.typeIIShort V d| * g N := by
            apply sum_le_sum
            intro d hd
            obtain ⟨hd₁,hd₂⟩ := mem_Icc.mp hd
            have hx := (Nat.one_le_div_iff hd₁).mpr (hd₂.trans (min_le_left ..))
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left ((h _ hx).trans (hmono _ _ hx (Nat.div_le_self N d))) (abs_nonneg _)
       _ ≤ _ := by
            rw [←sum_mul]
            exact mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (min_le_right N W))
              (fun _ _ _ => abs_nonneg _)) (hg N)

/-- A nondecreasing bound on every divided horizon transfers with the total
absolute mass of the truncated Vaughan coefficients. -/
theorem cofactor_transfer_majorant (f g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n)
    (hmono : ∀ x n : ℕ, 1 ≤ x → x ≤ n → g x ≤ g n)
    (h : ∀ x : ℕ, 1 ≤ x → |(Chebyshev.psi x-x)-f x| ≤ g x) (V W N : ℕ) :
    |cofactorCountError V W N-∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*f (N/d)| ≤
      (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*g N := by
  rw [cofactorCountError_eq,←sum_sub_distrib]
  simp_rw [←mul_sub]
  exact cofactor_sum_majorant _ g hg hmono h V W N

/-- One fixed coprime row works at square-root precision up to five
logarithms, simultaneously at all horizons and Vaughan widths. -/
theorem logarithmic_coprime_cofactors :
    let row := fun X : ℕ =>
      let D := ⌊1+Real.log X⌋₊
      coprimePrimeRow D D X (productLower D X)
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V W N : ℕ,
      |cofactorCountError V W N-∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*row (N/d)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*(1+Real.log N)^5*Real.sqrt N) := by
  intro row
  obtain ⟨K,hK,h⟩ := coprime_prime_row_bound
  refine ⟨K,hK,cofactor_transfer_majorant row (fun N => K*(1+Real.log N)^5*Real.sqrt N)
    (fun n => by have := Real.log_natCast_nonneg n; positivity) ?_ ?_⟩
  · intro x n hx hxn
    have hlog := Real.log_le_log (by exact_mod_cast hx : (0 : ℝ)<x) (by exact_mod_cast hxn : (x : ℝ) ≤ n)
    have hz := Real.log_natCast_nonneg x
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl (1 : ℝ)) hlog) 5) hK)
      (Real.sqrt_le_sqrt (by exact_mod_cast hxn)) (Real.sqrt_nonneg _) (by have := Real.log_natCast_nonneg n; positivity)
  · intro x hx
    let H := 1+Real.log x
    have hz := Real.log_natCast_nonneg x
    have hH : 1 ≤ H := by dsimp [H]; linarith
    have hD := (Nat.one_le_floor_iff H).mpr hH
    have hd := Nat.floor_le (zero_le_one.trans hH)
    exact h hx hD hD hH hd hd (show Real.log x ≤ 1+Real.log x by linarith)

/-- The approximation costs a strictly smaller power than any prescribed
target above one half, at both Vaughan widths and every integer horizon. -/
theorem coprime_prime_cofactors {b : ℝ} (hb : 1/2 < b) :
    let δ := (b-1/2)/10
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V W N : ℕ,
      |cofactorCountError V W N-∑ d ∈ Icc 1 (min N W), Sieve.typeIIShort V d*coprimeHorizon δ (N/d)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*(N : ℝ)^((b+1/2)/2)) := by
  intro δ
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hb]
  let c := 1+1/δ
  have hc : 1 ≤ c := by dsimp [c]; linarith only [one_div_pos.mpr hδ]
  obtain ⟨C,hC,h⟩ := coprime_prime_row_bound
  let K := C*c^5
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  have row (X : ℕ) (hX : 1 ≤ X) :
      |(Chebyshev.psi X-X)-coprimeHorizon δ X| ≤ K*(X : ℝ)^((b+1/2)/2) := by
    let t := (X : ℝ)^δ
    let D := ⌊t⌋₊
    let H := c*t
    have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hx0 := zero_lt_one.trans_le hx
    have ht : 1 ≤ t := Real.one_le_rpow hx hδ.le
    have hD : 1 ≤ D := (Nat.one_le_floor_iff _).mpr ht
    have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hc ht
    have hd : (D : ℝ) ≤ H := (Nat.floor_le (zero_le_one.trans ht)).trans (le_mul_of_one_le_left (zero_le_one.trans ht) hc)
    have hl : Real.log X ≤ H := (Real.log_le_rpow_div hx0.le hδ).trans (by
      change t/δ ≤ (1+1/δ)*t
      rw [add_mul,one_mul]
      exact (show t/δ = (1/δ)*t by ring).le.trans (le_add_of_nonneg_left (zero_le_one.trans ht)))
    apply (h hX hD hD hH hd hd hl).trans_eq
    have he : t^5*Real.sqrt X = (X : ℝ)^((b+1/2)/2) := by
      dsimp [t]
      rw [←Real.rpow_natCast _ 5,←Real.rpow_mul hx0.le,Real.sqrt_eq_rpow,←Real.rpow_add hx0]
      congr 1
      dsimp [δ]; norm_num; ring
    dsimp only [K,H]
    rw [mul_pow,←he]; ring
  exact cofactor_transfer_majorant (coprimeHorizon δ) (fun n => K*(n : ℝ)^((b+1/2)/2))
    (fun _ => by positivity) (fun x n _ hxn => mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hxn) (by linarith only [hb])) hK) row

#print axioms coprime_prime_support
#print axioms coprime_prime_row_bound
#print axioms logarithmic_coprime_cofactors
#print axioms coprime_prime_cofactors
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
