import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFiniteMeshAtAnOrdinaryFirstPrime
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.OnePrimeCutForEveryConductorInTheFragment
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ConductorSmoothingBeyondTheSplineKnots

/-!
# Restoring lower products for a fixed set of ordinary primes

A common cutoff on the first prime leaves a coefficient depending only on
the product. The divisor logarithm bounds this coefficient uniformly in
the cutoff. Each low product sees a single interval of conductors.
-/

noncomputable section
open Finset ArithmeticFunction Filter
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Transposition of the restored products, with their sharp moving upper bound. -/
theorem lower_product_exchange {w : ℕ → ℕ} (hw : Monotone w) (P N M : ℕ) :
    (∑ n ∈ Ioc N M, ∑ q ∈ Ioc 0 (w n), firstPrimeProductCoefficient P q * positiveProductPair n q) =
      ∑ q ∈ Ioc 0 (w M), firstPrimeProductCoefficient P q *
        ∑ n ∈ Ioc N M with q ≤ w n, positiveProductPair n q := by
  let S := Ioc 0 (w M)
  let f (n q : ℕ) := firstPrimeProductCoefficient P q * positiveProductPair n q
  have hr (n : ℕ) (hn : n ∈ Ioc N M) :
      (∑ q ∈ Ioc 0 (w n), f n q) = ∑ q ∈ S, if q ≤ w n then f n q else 0 := by
    rw [←sum_filter]
    have hi : S.filter (· ≤ w n) = Ioc 0 (w n) := by
      ext q
      simp only [S,mem_filter,mem_Ioc]
      exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.trans (hw (mem_Ioc.mp hn).2)⟩,h.2⟩⟩
    rw [hi]
  change (∑ n ∈ Ioc N M, ∑ q ∈ Ioc 0 (w n), f n q) = _
  rw [sum_congr rfl hr,sum_comm]
  apply sum_congr rfl
  intro q _
  rw [←sum_filter,mul_sum]

/-- Restoring every product below a monotone detached cutoff costs the
conductor-smoothed mesh bound, uniformly over all fixed first-prime cuts. -/
theorem restored_lower_products_octave :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w : ℕ → ℕ}, Monotone w →
      ∀ {N M : ℕ}, 0 < N → N ≤ M → M ≤ 2*N →
      8*(w M:ℝ) < Real.exp (-8)*(N:ℝ)^2 → ∀ P : ℕ,
      |∑ n ∈ Ioc N M, ∑ q ∈ Ioc 0 (w n),
        firstPrimeProductCoefficient P q * positiveProductPair n q| ≤
          C*Real.log (w M)*((w M:ℝ)^9/(N:ℝ)^14+(w M:ℝ)^8/(N:ℝ)^13+(w M:ℝ)^5/(N:ℝ)^8) := by
  obtain ⟨A,hA,hcoeff⟩ := firstPrimeProductCoefficient_bound
  obtain ⟨K,hK,hcond⟩ := conductor_interval_horizonPair_bound
  refine ⟨A*K,mul_nonneg hA hK,fun {w} hw {N M} hN hNM hM2 hbirth P => ?_⟩
  let W := w M
  let E (q : ℕ) := (q:ℝ)^8/(N:ℝ)^14+(q:ℝ)^7/(N:ℝ)^13+(q:ℝ)^4/(N:ℝ)^8
  have hm : Monotone E := by
    intro q r hqr
    have hp (m d : ℕ) : (q:ℝ)^m/(N:ℝ)^d ≤ (r:ℝ)^m/(N:ℝ)^d :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hqr) _) (by positivity)
    exact add_le_add (add_le_add (hp 8 14) (hp 7 13)) (hp 4 8)
  rw [lower_product_exchange hw]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _q ∈ Ioc 0 W, (A*Real.log W)*(K*E W) := by
            apply sum_le_sum
            intro q hq
            obtain ⟨hq0,hqW⟩ := mem_Ioc.mp hq
            have hq' : 8*(q:ℝ) < Real.exp (-8)*(N:ℝ)^2 :=
              (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hqW) (by norm_num : (0:ℝ)≤8)).trans_lt hbirth
            have hz (n : ℕ) (hn : n ∈ Ioc N M) : sampledSpline n q=0 := by
              have hnN := (mem_Ioc.mp hn).1
              apply sampledSpline_eq_zero_before (hN.trans hnN)
              have hs := mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (Nat.cast_nonneg N) (Nat.cast_le.mpr hnN.le) 2) (Real.exp_pos (-8)).le
              linarith only [hq',hs,Nat.cast_nonneg (α := ℝ) q]
            obtain ⟨a,d,ha,had,hd,he⟩ := monotone_shell_conductors (u := fun _ => 0)
              monotone_const hw hNM q 0
            simp only [Nat.zero_le,true_and,hq0] at he
            have heq : (∑ n ∈ Ioc N M with q ≤ w n, positiveProductPair n q) =
                ∑ n ∈ Ico a d, (n:ℝ)^2*unitHorizonPair n q := by
              rw [←he]
              exact sum_congr rfl fun n hn => by rw [positiveProductPair,hz n (mem_filter.mp hn).1,add_zero]
            rw [abs_mul,heq]
            exact mul_le_mul ((hcoeff P q).trans (mul_le_mul_of_nonneg_left
              (Real.log_le_log (Nat.cast_pos.mpr hq0) (Nat.cast_le.mpr hqW)) hA))
              ((hcond hN ha had (hd.trans (Nat.succ_le_succ hM2)) hq0 hq').trans
                (mul_le_mul_of_nonneg_left (hm hqW) hK))
              (abs_nonneg _) (mul_nonneg hA (Real.log_natCast_nonneg W))
       _ = _ := by
          rw [sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul]
          dsimp only [E,W]
          ring

/-- The sharp seventeen-ninths lower products have cubic-logarithmic price on every
sufficiently late partial octave, with one constant for every common prime cut. -/
theorem restored_seventeen_ninths_late_octaves :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ {M : ℕ}, N ≤ M → M ≤ 2*N → ∀ P : ℕ,
      |∑ n ∈ Ioc N M, ∑ q ∈ Ioc 0 ⌊(n:ℝ)^(17/9:ℝ)⌋₊,
          firstPrimeProductCoefficient P q * positiveProductPair n q| ≤ C*(N:ℝ)^3*conductorLog N := by
  obtain ⟨K,hK,h⟩ := restored_lower_products_octave
  let a := (17/9:ℝ)
  let w (n : ℕ) := ⌊(n:ℝ)^a⌋₊
  have ha : 0≤a := by norm_num [a]
  have hw : Monotone w := fun _ _ hn => Nat.floor_mono
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hn) ha)
  have ht : Tendsto (fun N : ℕ => (N:ℝ)^(1/9:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/9)).comp tendsto_natCast_atTop_atTop
  refine ⟨6*K*4^9,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ),ht.eventually_gt_atTop (32*Real.exp 8)] with N hN hg
  intro M hNM hM2 P
  have hpos : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hN1 : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  let X := (N:ℝ)^a
  let W := w M
  have hX : 0<X := Real.rpow_pos_of_pos hpos _
  have hMf : (W:ℝ) ≤ (M:ℝ)^a := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg M) _)
  have hM : (M:ℝ)≤2*N := by exact_mod_cast hM2
  have hW : (W:ℝ)≤4*X := by
    apply (hMf.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) hM ha)).trans
    rw [Real.mul_rpow (by norm_num) hpos.le]
    exact mul_le_mul_of_nonneg_right ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (by norm_num [a] : a≤2)).trans_eq (by norm_num [Real.rpow_two])) hX.le
  have hpow : X*(N:ℝ)^(1/9:ℝ)=(N:ℝ)^2 := by
    dsimp only [X]; rw [←Real.rpow_add hpos,show a+1/9=2 by norm_num [a],Real.rpow_two]
  have hborn : 8*(W:ℝ)<Real.exp (-8)*(N:ℝ)^2 := by
    rw [Real.exp_neg,inv_mul_eq_div,lt_div_iff₀ (Real.exp_pos 8),←hpow]
    have h₁ := mul_le_mul_of_nonneg_right hW (Real.exp_pos 8).le
    linarith only [h₁,mul_lt_mul_of_pos_left hg hX]
  have hW1 : 1 ≤ W := Nat.le_floor (Real.one_le_rpow (Nat.one_le_cast.mpr (hN.trans hNM)) ha)
  have hlog : Real.log W ≤ 2*conductorLog N := by
    have hlarge : (1:ℝ)≤2*N := by linarith only [hN1]
    have hh := Real.log_le_log (Nat.cast_pos.mpr hW1)
      (hMf.trans ((Real.rpow_le_rpow (Nat.cast_nonneg _) hM ha).trans
        ((Real.rpow_le_rpow_of_exponent_le hlarge (by norm_num [a] : a≤2)).trans_eq
          (Real.rpow_two _))))
    rw [Real.log_pow] at hh
    dsimp only [conductorLog]
    linarith only [hh]
  have term (m k : ℕ) (hm : m≤9) (he : a*m-k≤3) :
      (W:ℝ)^m/(N:ℝ)^k ≤ 4^9*(N:ℝ)^3 := by
    have hconst : (4:ℝ)^m ≤ 4^9 := pow_le_pow_right₀ (by norm_num) hm
    have hh := div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg W) hW m)
      (pow_nonneg hpos.le k)
    apply hh.trans
    rw [mul_pow,mul_div_assoc]
    have heq : X^m/(N:ℝ)^k=(N:ℝ)^(a*m-k) := by
      dsimp only [X]
      rw [Real.rpow_sub hpos,Real.rpow_mul hpos.le,Real.rpow_natCast,Real.rpow_natCast]
    rw [heq]
    exact mul_le_mul hconst ((Real.rpow_le_rpow_of_exponent_le hN1 he).trans_eq
      (Real.rpow_natCast _ 3)) (Real.rpow_nonneg hpos.le _) (by norm_num)
  have hs := add_le_add (add_le_add (term 9 14 le_rfl (by norm_num [a]))
    (term 8 13 (by decide) (by norm_num [a]))) (term 5 8 (by decide) (by norm_num [a]))
  have hlog0 := zero_le_one.trans (conductorLog_one_le N)
  have hE : 0 ≤ (W:ℝ)^9/(N:ℝ)^14+(W:ℝ)^8/(N:ℝ)^13+(W:ℝ)^5/(N:ℝ)^8 := by positivity
  exact (h hw hN hNM hM2 hborn P).trans ((mul_le_mul
    (mul_le_mul_of_nonneg_left hlog hK) hs hE (by positivity :
      0 ≤ K*(2*conductorLog N))).trans_eq (by ring))

/-- Restoring all products through the original moving cutoff has one
cubic-logarithmic bound uniform in both conductor endpoints and the prime cut. -/
theorem restored_seventeen_ninths_fragments :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P J M : ℕ,
      |∑ n ∈ Ioc J M, ∑ q ∈ Ioc 0 ⌊(n:ℝ)^(17/9:ℝ)⌋₊,
        firstPrimeProductCoefficient P q * positiveProductPair n q| ≤ C*(M:ℝ)^3*conductorLog M := by
  obtain ⟨K,hK,h⟩ := restored_seventeen_ninths_late_octaves
  obtain ⟨k,hk⟩ := eventually_atTop.mp h
  obtain ⟨A,hA,ha⟩ := firstPrimeProductCoefficient_bound
  let w (n : ℕ) := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  let F (P n : ℕ) := ∑ q ∈ Ioc 0 (w n), firstPrimeProductCoefficient P q*positiveProductPair n q
  let g (n : ℕ) := ∑ q ∈ Ioc 0 (w n), A*Real.log q*|positiveProductPair n q|
  let D := ∑ n ∈ Ioc 0 (2*(k+1)), g n
  have hg (n : ℕ) : 0 ≤ g n := sum_nonneg fun q _ =>
    mul_nonneg (mul_nonneg hA (Real.log_natCast_nonneg q)) (abs_nonneg _)
  have hD : 0≤D := sum_nonneg fun n _ => hg n
  let C := D+K
  have hC : 0≤C := add_nonneg hD hK
  have hKC : K≤C := le_add_of_nonneg_left hD
  have early (P J M : ℕ) (hM : M≤2*(k+1)) : |∑ n ∈ Ioc J M, F P n| ≤ D := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ n ∈ Ioc J M, g n := by
              apply sum_le_sum
              intro n _
              apply (abs_sum_le_sum_abs _ _).trans
              apply sum_le_sum
              intro q _
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right (ha P q) (abs_nonneg _)
         _ ≤ D := sum_le_sum_of_subset_of_nonneg
           (fun n hn => mem_Ioc.mpr ⟨(Nat.zero_le J).trans_lt (mem_Ioc.mp hn).1,
             (mem_Ioc.mp hn).2.trans hM⟩) (fun n _ _ => hg n)
  refine ⟨C,hC,fun P J M => ?_⟩
  change |∑ n ∈ Ioc J M, F P n| ≤ _
  revert J
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro J
    by_cases hJM : J < M
    swap
    · rw [Ioc_eq_empty_of_le (le_of_not_gt hJM),sum_empty,abs_zero]
      exact mul_nonneg (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg _) _))
        (zero_le_one.trans (conductorLog_one_le _))
    have hM0 := (Nat.zero_le J).trans_lt hJM
    by_cases hb : M≤2*(k+1)
    · have hsc : 1 ≤ (M:ℝ)^3*conductorLog M := one_le_mul_of_one_le_of_one_le
        (one_le_pow₀ (Nat.one_le_cast.mpr hM0)) (conductorLog_one_le M)
      exact (early P J M hb).trans (((le_add_of_nonneg_right hK).trans
        (le_mul_of_one_le_right hC hsc)).trans_eq (by ring))
    let L := (M+1)/2
    have hkL : k ≤ L := by dsimp only [L]; omega
    have hL : 0<L := by dsimp only [L]; omega
    have hLM : L<M := by dsimp only [L]; omega
    have hML : M≤2*L := by dsimp only [L]; omega
    have monot {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) :
        K*(i:ℝ)^3*conductorLog i ≤ C*(j:ℝ)^3*conductorLog j := by
      exact mul_le_mul (mul_le_mul hKC (pow_le_pow_left₀ (Nat.cast_nonneg i) (Nat.cast_le.mpr hij) 3)
        (pow_nonneg (Nat.cast_nonneg i) 3) hC) (conductorLog_mono hi hij)
        (zero_le_one.trans (conductorLog_one_le i)) (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg j) 3))
    by_cases hJL : L ≤ J
    · exact (hk J (hkL.trans hJL) hJM.le (hML.trans (Nat.mul_le_mul_left 2 hJL)) P).trans
        (monot (hL.trans_le hJL) hJM.le)
    have hJL' := (lt_of_not_ge hJL).le
    rw [←sum_Ioc_consecutive (F P) hJL' hLM.le]
    have left := ih L hLM J
    have right := (hk L hkL hLM.le hML P).trans (monot hL le_rfl)
    have hr : (L:ℝ) ≤ (2/3:ℝ)*M := by
      have hn : 3*L≤2*M := by dsimp only [L]; omega
      have hn' : 3*(L:ℝ)≤2*M := by exact_mod_cast hn
      linarith only [hn']
    have hcube : 2*(L:ℝ)^3 ≤ (M:ℝ)^3 := by
      linarith only [pow_le_pow_left₀ (Nat.cast_nonneg L) hr 3,pow_nonneg (Nat.cast_nonneg (α := ℝ) M) 3]
    apply (abs_add_le _ _).trans ((add_le_add left right).trans _)
    calc _ = C*(2*(L:ℝ)^3)*conductorLog L := by ring
         _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hcube hC) (conductorLog_mono hL hLM.le)
           (zero_le_one.trans (conductorLog_one_le L)) (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg M) 3))

/-- Complete positive-quotient product sum with a common first-prime cutoff. -/
def wholeFirstPrimeProductReading (P n : ℕ) :=
  ∑ q ∈ Ioc 0 (splineHorizon n), firstPrimeProductCoefficient P q * positiveProductPair n q

private theorem original_cut_le_horizon {n : ℕ} (hn : 0<n) : ⌊(n:ℝ)^(17/9:ℝ)⌋₊ ≤ splineHorizon n := by
  have hN : (1:ℝ)≤n := Nat.one_le_cast.mpr hn
  have h := successorSquareWindowScale_bounds n
  have hs : (n:ℝ)^2 ≤ (splineHorizon n:ℝ) := by
    unfold splineHorizon
    push_cast
    linarith only [h.1,h.2.2,Nat.cast_nonneg (α := ℝ) (windowEnd ((2*n+1)^2+1))]
  exact Nat.cast_le.mp ((Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (17/9))).trans
    ((Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (17/9:ℝ)≤2)).trans ((Real.rpow_two _).le.trans hs)))

private theorem first_prime_reading_sub_whole {n : ℕ} (hn : 0<n) (P : ℕ) :
    (n:ℝ)^2*unrestrictedFirstPrimeReading P ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n - wholeFirstPrimeProductReading P n =
      -(∑ q ∈ Ioc 0 ⌊(n:ℝ)^(17/9:ℝ)⌋₊, firstPrimeProductCoefficient P q*positiveProductPair n q) := by
  rw [unrestrictedFirstPrimeReading,common_prime_positive_product_pairs,wholeFirstPrimeProductReading,
    ←sum_Ioc_consecutive (fun q => firstPrimeProductCoefficient P q*positiveProductPair n q)
      (Nat.zero_le _) (original_cut_le_horizon hn)]
  ring

/-- Every terminal fragment of the original signed conductor prefix agrees
up to cubic-logarithmic error with a complete product sum having a single
first-prime list and the positive first quotient endpoint. -/
theorem seventeen_ninths_whole_first_prime_fragments :
    ∃ C : ℝ, 0≤C ∧ ∀ (J M : ℕ), 0<M →
      |∑ n ∈ Ioc J M, ((n:ℝ)^2*cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        wholeFirstPrimeProductReading (commonFirstPrimeCut M) n)| ≤ C*(M:ℝ)^3*conductorLog M := by
  obtain ⟨A,hA,ha⟩ := common_cap_free_prime_fragments
  obtain ⟨B,hB,hb⟩ := restored_seventeen_ninths_fragments
  refine ⟨A+B,add_nonneg hA hB,fun J M hM => ?_⟩
  let P := commonFirstPrimeCut M
  let U (n : ℕ) := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  let H (n : ℕ) := (n:ℝ)^2*(cappedUpperProductReading (U n) n n-unrestrictedFirstPrimeReading P (U n) n)
  let R (n : ℕ) := ∑ q ∈ Ioc 0 (U n), firstPrimeProductCoefficient P q*positiveProductPair n q
  have he (n : ℕ) (hn : n ∈ Ioc J M) :
      (n:ℝ)^2*cappedUpperProductReading (U n) n n - wholeFirstPrimeProductReading P n = H n-R n := by
    have hrow := first_prime_reading_sub_whole ((Nat.zero_le J).trans_lt (mem_Ioc.mp hn).1) P
    dsimp only [H,U,R]
    linear_combination hrow
  rw [sum_congr rfl he,sum_sub_distrib]
  exact (abs_sub _ _).trans ((add_le_add (ha J M hM) (hb P J M)).trans_eq (by ring))

#print axioms seventeen_ninths_whole_first_prime_fragments
#print axioms restored_seventeen_ninths_fragments
#print axioms restored_seventeen_ninths_late_octaves
#print axioms lower_product_exchange
#print axioms restored_lower_products_octave
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
