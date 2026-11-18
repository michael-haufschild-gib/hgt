import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CappedConductorPrefixes

/-!
# The centered Mangoldt measure inside an arbitrary product window

After restoring all first factors, the logarithmic factorial identity identifies
the cumulative product coefficient with the prime error up to one logarithm.
The complementary cap, repeated primes and proper powers have square-root
cost on the conductor mesh. Both sharp product endpoints can vary.
-/

noncomputable section
open Finset ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem positive_cut (Y k : ℕ) : Ioc Y k = (Icc 1 k).filter (Y < ·) := by
  ext t
  simp only [mem_Ioc,mem_Icc,mem_filter]
  omega

/-- The full two-factor coefficient against any function of the product. -/
private theorem balanced_window (Y k : ℕ) (f : ℕ → ℝ) :
    (∑ q ∈ Ioc Y k, balancedProduct 1 q * f q) =
      ∑ u ∈ Ioc 1 k, vonMangoldt u * ∑ v ∈ Ioc (Y/u) (k/u), innerJump 1 v * f (u*v) := by
  let F (u v : ℕ) := if 1 < u ∧ Y < u*v then vonMangoldt u * innerJump 1 v * f (u*v) else 0
  have hn (q : ℕ) :
      (if Y < q then balancedProduct 1 q * f q else 0) = ∑ z ∈ q.divisorsAntidiagonal, F z.1 z.2 := by
    by_cases hy : Y < q
    · rw [if_pos hy, balancedProduct, sum_mul, sum_filter]
      apply sum_congr rfl
      intro z hz
      have he := (Nat.mem_divisorsAntidiagonal.mp hz).1
      by_cases hu : 1 < z.1 <;> by_cases hv : 1 < z.2
      · simp [F, he, hu, hv, hy]
      · simp [F, he, hu, hv, hy, innerJump_small (Nat.le_of_not_gt hv)]
      · simp [F, he, hu, hv, hy]
      · simp [F, he, hu, hv, hy]
    · rw [if_neg hy]
      exact (sum_eq_zero fun z hz => by simp [F, (Nat.mem_divisorsAntidiagonal.mp hz).1, hy]).symm
  rw [positive_cut Y k, sum_filter, sum_congr rfl (fun q _ => hn q),
    _root_.RHTower.Sieve.sum_Icc_divisorsAntidiagonal_swap F, positive_cut 1 k, sum_filter]
  apply sum_congr rfl
  intro u hu
  have hpos := (mem_Icc.mp hu).1
  by_cases h : 1 < u
  · rw [if_pos h, positive_cut, sum_filter, mul_sum]
    apply sum_congr rfl
    intro v _
    have he : Y/u < v ↔ Y < u*v := by rw [Nat.div_lt_iff_lt_mul hpos, Nat.mul_comm v u]
    by_cases hv : Y < u*v <;> simp [F, h, he, hv, mul_assoc]
  · rw [if_neg h]
    exact sum_eq_zero fun _ _ => by simp [F, h]

private theorem balanced_discrepancy :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k t : ℕ, t ≤ k →
      |∑ v ∈ Ioc 0 t, (vonMangoldt v - balancedProduct 1 v - 1)| ≤ C*(1+Real.log k) := by
  let C := mass 2*(5+Real.log 4)+(1+mass 2)*7
  have hmass := (abs_nonneg _).trans (abs_prefix_le_mass (R := 2) (by decide) 0)
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hnC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hnC,fun k t htk => ?_⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp only [Ioc_self,sum_empty,abs_zero]
    exact mul_nonneg hnC (zero_le_one.trans (le_add_of_nonneg_right (Real.log_natCast_nonneg k)))
  have hI : Ioc 0 t = Icc 1 t := by ext i; simp only [mem_Icc,mem_Ioc]; omega
  have hpsi : ∑ v ∈ Icc 1 t, vonMangoldt v = Chebyshev.psi t := by
    unfold Chebyshev.psi
    rw [Nat.floor_natCast]
    rfl
  rw [hI, sum_sub_distrib, sum_sub_distrib, hpsi, sum_balancedProduct, sum_const,
    Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one, sub_right_comm]
  apply (abs_error_sub_middle (R := 2) (by decide) ht 1).trans
  have hl := Real.log_le_log (by exact_mod_cast ht : (0:ℝ) < t) (by exact_mod_cast htk : (t:ℝ) ≤ k)
  have hk := Real.log_natCast_nonneg k
  dsimp only [C]
  norm_num only [Nat.reduceMul,Nat.cast_ofNat,one_mul,mul_one]
  nlinarith only [mul_le_mul_of_nonneg_left hl hmass, mul_nonneg hmass hk,
    mul_nonneg (mul_nonneg hmass hlog) hk, hk, hmass]

/-- The centered one-factor measure on exactly the same sharp product interval. -/
def centeredProductTail (k Y : ℕ) : ℝ :=
  ∑ q ∈ Ioc Y k, (vonMangoldt q - 1) * centeredPrimeWeight 1 (k/q)

private theorem balanced_tail_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k Y : ℕ,
      |centeredProductTail k Y - ∑ q ∈ Ioc Y k, balancedProduct 1 q * centeredPrimeWeight 1 (k/q)| ≤
        C*(1+Real.log k)*Real.sqrt k := by
  obtain ⟨A,hA,ha⟩ := balanced_discrepancy
  obtain ⟨F,hF,hf⟩ := centeredPrimeWeight_uniform
  refine ⟨4*A*F,by positivity,fun k Y => ?_⟩
  have hH : 0 ≤ 1+Real.log k := by have := Real.log_natCast_nonneg k; positivity
  have ht := abs_truncated_quotient_pair (N := k) Y (fun q => vonMangoldt q-balancedProduct 1 q-1)
    (centeredPrimeWeight 1) (mul_nonneg hA hH) hF (ha k) (by simpa only [Nat.cast_one,mul_one] using hf (R := 1) le_rfl)
  have he : centeredProductTail k Y - ∑ q ∈ Ioc Y k, balancedProduct 1 q * centeredPrimeWeight 1 (k/q) =
      ∑ q ∈ Ioc Y k, (vonMangoldt q-balancedProduct 1 q-1)*centeredPrimeWeight 1 (k/q) := by
    rw [centeredProductTail, ←sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  have hroot : (k.sqrt:ℝ) ≤ Real.sqrt k :=
    (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
      (by exact_mod_cast (show k.sqrt^2 ≤ k by simpa only [sq] using Nat.sqrt_le k))
  rw [he]
  exact ht.trans ((mul_le_mul_of_nonneg_left hroot (by positivity)).trans_eq (by ring))

private theorem small_first_factors :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k Y : ℕ,
      |(∑ q ∈ Ioc Y k, balancedProduct 1 q * centeredPrimeWeight 1 (k/q)) - longFactorRow 1 1 k Y| ≤
        C*Real.sqrt k := by
  obtain ⟨K,hK,h⟩ := factor_slice_bounds
  refine ⟨56*K,by positivity,fun k Y => ?_⟩
  rw [balanced_window]
  simp only [← Nat.div_div_eq_div_mul]
  let S := (Ioc 1 k).filter (· ≤ 4)
  let f := fun u => vonMangoldt u * factorSlice 1 1 k Y u
  have he : (Ioc 1 k).filter (fun u => ¬u ≤ 4) = Ioc 4 k := by
    ext u; simp only [mem_filter,mem_Ioc]; omega
  have hs := sum_filter_add_sum_filter_not (Ioc 1 k) (fun u => u ≤ 4) f
  rw [he] at hs
  change |(∑ u ∈ Ioc 1 k, f u) - ∑ u ∈ Ioc 4 k, f u| ≤ _
  rw [← hs,add_sub_cancel_right]
  let A := 2*K*Real.sqrt k
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc _ ≤ ∑ u ∈ S, vonMangoldt u * A := by
          apply (abs_sum_le_sum_abs _ _).trans
          apply sum_le_sum
          intro u hu
          have hu1 : 1 ≤ u := (mem_Ioc.mp (mem_filter.mp hu).1).1.le
          have hr : 1 ≤ Real.sqrt u := by simpa only [Real.sqrt_one] using
               (Real.sqrt_le_sqrt (by exact_mod_cast hu1 : (1:ℝ) ≤ u))
          have hb : |factorSlice 1 1 k Y u| ≤ A / Real.sqrt u := by
            simpa only [A,Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one,mul_one,mul_comm K 2] using
              (h (D := 1) (R := 1) le_rfl le_rfl k Y).1 u
          dsimp only [f]
          rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
          exact mul_le_mul_of_nonneg_left (hb.trans (div_le_self hA hr)) vonMangoldt_nonneg
       _ ≤ (7*4)*A := by
          rw [←sum_mul]
          apply mul_le_mul_of_nonneg_right _ hA
          refine le_trans ?_ (_root_.RHTower.chebyshevPsi_le_seven 4)
          apply sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => vonMangoldt_nonneg
          intro u hu
          exact mem_Icc.mpr ⟨(mem_Ioc.mp (mem_filter.mp hu).1).1.le,(mem_filter.mp hu).2⟩
       _ = _ := by dsimp [A]; ring

/-- Uniform comparison with the centered prime-only product measure. The first
term pays the factorial discrepancy, repeated primes and proper powers. The
second pays the cofactor cap. No restriction on the lower endpoint is needed. -/
theorem capped_centered_product_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}, 1 ≤ k → ∀ Y b : ℕ,
      |centeredProductTail k Y - ordinaryFactorTail 4 k (cappedCoprimeSlice 1 1 k Y b)| ≤
        C*(1+Real.log k)*(Real.sqrt k + (k/(b+1) : ℕ)) := by
  obtain ⟨A,hA,ha⟩ := balanced_tail_error
  obtain ⟨B,hB,hb⟩ := small_first_factors
  obtain ⟨D,hD,hd⟩ := repeated_prime_factors_bound
  obtain ⟨E,hE,he⟩ := large_complement_bound
  refine ⟨A+B+2*D+2*E,by positivity,fun {k} hk Y b => ?_⟩
  let S := ∑ q ∈ Ioc Y k, balancedProduct 1 q * centeredPrimeWeight 1 (k/q)
  let G := longFactorRow 1 1 k Y
  let P := coprimePrimeRow 1 1 k Y
  let T := ordinaryFactorTail 4 k (cappedCoprimeSlice 1 1 k Y b)
  have hdec : centeredProductTail k Y - T =
      (centeredProductTail k Y-S)+(S-G)+(G-P)+(P-T) := by ring
  have h₁ := ha k Y
  have h₂ := hb k Y
  have h₃ := hd (D := 1) (R := 1) le_rfl le_rfl hk Y
  have h₄ := he (D := 1) (R := 1) (F := 4) le_rfl le_rfl hk (by decide) Y b
  simp only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one,mul_one] at h₃ h₄
  change |G-P| ≤ _ at h₃
  change |P-T| ≤ _ at h₄
  change |centeredProductTail k Y-S| ≤ _ at h₁
  change |S-G| ≤ _ at h₂
  rw [show ordinaryFactorTail 4 k (cappedCoprimeSlice 1 1 k Y b) = T from rfl,hdec]
  apply (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add h₁ h₂)) h₃)) h₄).trans _)
  let H := 1+Real.log k
  have hH : 1 ≤ H := le_add_of_nonneg_right (Real.log_natCast_nonneg k)
  have hR := Real.sqrt_nonneg (k:ℝ)
  have hQ := Nat.cast_nonneg (α := ℝ) (k/(b+1))
  have hR' : H*Real.sqrt k ≤ H*(Real.sqrt k + (k/(b+1) : ℕ)) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hQ) (zero_le_one.trans hH)
  have hQ' : H*(k/(b+1) : ℕ) ≤ H*(Real.sqrt k + (k/(b+1) : ℕ)) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hR) (zero_le_one.trans hH)
  have hb' := mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left hR hH).trans hR') hB
  dsimp only [H] at hb' hR' hQ'
  linarith only [hb',mul_le_mul_of_nonneg_left hR' hA,mul_le_mul_of_nonneg_left hR' hD,
    mul_le_mul_of_nonneg_left hQ' hE]

/-- The compensated single-factor sum uses the same moving lower endpoint
and the same finite spline. -/
def centeredProductReading (U n : ℕ) : ℝ :=
  splineCountReading n (fun k => centeredProductTail k (max (productLower 1 k) U))

/-- Lifting the cofactor cap and inverting the complete divisor coefficient
cost one logarithm per conductor, uniformly in the sharp product cutoff. -/
theorem capped_centered_reading_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n → ∀ U : ℕ,
      |centeredProductReading U n - cappedUpperProductReading U n n| ≤ C*conductorLog n := by
  obtain ⟨A,hA,ha⟩ := capped_centered_product_error
  obtain ⟨T,hT,hwin⟩ := successorSquare_window_bound
  obtain ⟨D,_,hD,_,hdiff⟩ := sampledSpline_differences
  obtain ⟨J,hJ,hlog⟩ := splineHorizon_conductorLog
  have hT0 := zero_le_one.trans hT
  refine ⟨T^2*A*J*(T+T^2)*D,by positivity,fun {n} hn U => ?_⟩
  let L := splineHorizon n
  let H := conductorLog n
  let Y (k : ℕ) := max (productLower 1 k) U
  let g (k : ℕ) := centeredProductTail k (Y k) - ordinaryFactorTail 4 k (cappedCoprimeSlice 1 1 k (Y k) n)
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hH : 0 ≤ H := zero_le_one.trans (conductorLog_one_le n)
  have hL : (L:ℝ) ≤ (T*n)^2 := hwin hn
  have hrow (k : ℕ) (hk : k ∈ Icc 1 L) : |g k| ≤ A*(J*H)*((T+T^2)*n) := by
    obtain ⟨hk1,hkL⟩ := mem_Icc.mp hk
    have hk' := (Nat.cast_le.mpr hkL : (k:ℝ) ≤ L).trans hL
    have hroot := Real.sqrt_le_sqrt hk'
    rw [Real.sqrt_sq (mul_nonneg hT0 hn'.le)] at hroot
    have hquot : ((k/(n+1) : ℕ) : ℝ) ≤ T^2*n := by
      apply Nat.cast_div_le.trans
      apply (div_le_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
      push_cast
      nlinarith only [hk',mul_nonneg (sq_nonneg T) hn'.le]
    have hlog' := Real.log_le_log (by exact_mod_cast hk1 : (0:ℝ) < k)
      (by exact_mod_cast hkL : (k:ℝ) ≤ L)
    apply (ha hk1 (Y k) n).trans
    apply mul_le_mul (mul_le_mul_of_nonneg_left
      ((add_le_add (le_refl (1:ℝ)) hlog').trans (hlog hn)) hA) _ (by positivity) (by positivity)
    rw [add_mul]
    exact add_le_add hroot hquot
  unfold centeredProductReading cappedUpperProductReading splineCountReading
  rw [←sum_sub_distrib]
  simp_rw [←sub_mul]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _k ∈ Icc 1 L, (A*(J*H)*((T+T^2)*n))*(D/(n:ℝ)^3) := by
           apply sum_le_sum
           intro k hk
           rw [abs_mul]
           exact mul_le_mul (hrow k hk) ((hdiff hn k).1) (abs_nonneg _) (by positivity)
       _ ≤ (T*n)^2 * ((A*(J*H)*((T+T^2)*n))*(D/(n:ℝ)^3)) := by
           rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
           exact mul_le_mul_of_nonneg_right hL (by positivity)
       _ = _ := by change _ = _*H; field_simp; ring

/-- Uniform cubic-logarithmic transfer through every terminal, also for a
partial block and for product cutoffs chosen independently at each conductor. -/
theorem partial_prefix_centered_product_transfer :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : ℕ → ℕ) (L M : ℕ),
      |∑ n ∈ Ioc L M, (n:ℝ)^2*(centeredProductReading (U n) n -
        cappedUpperProductReading (U n) n n)| ≤ C*(M:ℝ)^3*conductorLog M := by
  obtain ⟨C,hC,h⟩ := capped_centered_reading_error
  refine ⟨C,hC,fun U L M => ?_⟩
  have hH := zero_le_one.trans (conductorLog_one_le M)
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _n ∈ Ioc L M, (M:ℝ)^2*(C*conductorLog M) := by
          apply sum_le_sum
          intro n hn
          obtain ⟨hl,hm⟩ := mem_Ioc.mp hn
          have hpos := (Nat.zero_le L).trans_lt hl
          rw [abs_mul,abs_of_nonneg (sq_nonneg (n:ℝ))]
          exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hm) 2)
            ((h hpos _).trans (mul_le_mul_of_nonneg_left (conductorLog_mono hpos hm) hC))
            (abs_nonneg _) (sq_nonneg _)
       _ ≤ M*((M:ℝ)^2*(C*conductorLog M)) := by
          rw [sum_const,nsmul_eq_mul,Nat.card_Ioc]
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M L)) (by positivity)
       _ = _ := by ring

#print axioms partial_prefix_centered_product_transfer
#print axioms capped_centered_reading_error
#print axioms capped_centered_product_error
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
