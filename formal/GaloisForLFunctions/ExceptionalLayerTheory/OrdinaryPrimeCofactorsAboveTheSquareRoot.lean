import GaloisForLFunctions.ExceptionalLayerTheory.OrdinaryPrimeCancellationInTheSquareRootBand
import GaloisForLFunctions.ExceptionalLayerTheory.OrdinaryPrimesInTheFactorialInterval

/-!
# Ordinary prime cofactors above the square root

The exterior parity correction preserves the factorial pairing and the
square-root moment. Removing proper powers and the ordinary-prime band around
the square root leaves a single signed interval at each divided horizon.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def primeSum (R X L U : ℕ) : ℝ :=
  ∑ p ∈ (Ico L U).filter Nat.Prime, Real.log p*centeredPrimeWeight R (X/p)

private theorem full_row :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X →
      let R := ⌊(X : ℝ)^(1/100000 : ℝ)⌋₊
      |(Chebyshev.psi X-X)-primeSum R X 1 (X+1)| ≤ K*Real.sqrt X := by
  obtain ⟨C,hC,hm⟩ := mass_uniform
  obtain ⟨F,hF,hsize⟩ := centeredPrimeWeight_uniform
  obtain ⟨A,hA,hpowers⟩ := proper_powers_of_zero_moment hF
  refine ⟨420*(1+C)*16523+A,by positivity,fun X hX => ?_⟩
  intro R
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 := zero_lt_one.trans_le hx
  let T := (X : ℝ)^(1/4 : ℝ)
  have h1 : 1 ≤ T := Real.one_le_rpow hx (by norm_num)
  have hr : 1 ≤ R := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hx (by norm_num))
  have hR : (R : ℝ) ≤ (X : ℝ)^(1/100000 : ℝ) := Nat.floor_le (by positivity)
  have hR1 : (R : ℝ) ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
  have hR2 : (R : ℝ)^2 ≤ T := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg R) hR 2).trans
    rw [← Real.rpow_natCast _ 2,← Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hM : 1+mass R ≤ (1+C)*T := by
    have hh := (hm R hr).trans (mul_le_mul_of_nonneg_left hR1 hC)
    linarith only [hh,h1]
  have hlog : Real.log X ≤ 4*T := by
    have hl := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1/4)
    change Real.log X ≤ T/(1/4 : ℝ) at hl
    linarith only [hl]
  let a := 128*(128*R^2+1)
  have ha : Real.log (a : ℝ) ≤ 16512*T := by
    have ht := Real.log_le_sub_one_of_pos (show 0 < (a : ℝ) by dsimp [a]; positivity)
    dsimp [a] at ht ⊢
    push_cast at ht ⊢
    linarith only [ht,hR2,h1]
  have hL : 3+Real.log (a : ℝ)+2*Real.log X ≤ 16523*T := by linarith only [ha,hlog,h1]
  have hS : 0 ≤ 3+Real.log (a : ℝ)+2*Real.log X := by
    have := Real.log_natCast_nonneg a; have := Real.log_natCast_nonneg X; positivity
  have ht : T*T = Real.sqrt X := by
    rw [show T*T=(X : ℝ)^((1/4 : ℝ)+1/4) from (Real.rpow_add hx0 _ _).symm,Real.sqrt_eq_rpow]
    norm_num
  have hf := (centeredPrimeWeight_factorial hr hX).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num : (0 : ℝ) ≤ 420)) hL hS (by positivity))
  have hp := hpowers X X R hX le_rfl (hR.trans (Real.rpow_le_rpow_of_exponent_le hx (by norm_num)))
    (centeredPrimeWeight R) (hsize hr) (centered_weight_moment hr)
  have he : primeSum R X 1 (X+1) + (∑ m ∈ Ioc 0 X, centeredPrimeWeight R (X/m)*primePowerPart m) =
      ∑ m ∈ Icc 1 X, vonMangoldt m*centeredPrimeWeight R (X/m) := by
    have h₁ : Ico 1 (X+1) = Ioc 0 X := by ext n; simp only [mem_Ico,mem_Ioc]; omega
    have h₂ : Icc 1 X = Ioc 0 X := by ext n; simp only [mem_Icc,mem_Ioc]; omega
    rw [primeSum,h₁,h₂,sum_filter,← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    by_cases hh : p.Prime <;> simp [primePowerPart,hh,vonMangoldt_apply_prime,mul_comm]
  rw [← he,abs_le] at hf
  rw [abs_le] at hp ⊢
  rw [← ht] at hp ⊢
  constructor <;> linarith only [hf.1,hf.2,hp.1,hp.2]

/-- The ordinary-prime interval left at a single divided horizon. -/
def aboveSquareRoot (X : ℕ) : ℝ :=
  let R := ⌊(X : ℝ)^(1/100000 : ℝ)⌋₊
  let U := ⌊(X : ℝ)^(50001/100000 : ℝ)⌋₊
  ∑ p ∈ (Ioc U (X/R)).filter Nat.Prime, Real.log p*centeredPrimeWeight R (X/p)

private theorem primeSum_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (R X : ℕ) :
    primeSum R X a c = primeSum R X a b+primeSum R X b c := by
  simp only [primeSum,sum_filter]
  exact (sum_Ico_consecutive _ hab hbc).symm

/-- Each divided horizon has square-root error after removing all
ordinary primes through X to the power 50001/100000. -/
theorem ordinary_primes_above_sqrt_row :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X →
      |(Chebyshev.psi X-X)-aboveSquareRoot X| ≤ K*Real.sqrt X := by
  obtain ⟨C,hC,hfull⟩ := full_row
  obtain ⟨D,hD,hband⟩ := centered_prime_square_root_band
  obtain ⟨F,hF,hsize⟩ := centeredPrimeWeight_uniform
  refine ⟨C+D+14*F,by positivity,fun X hX => ?_⟩
  let R := ⌊(X : ℝ)^(1/100000 : ℝ)⌋₊
  let L := ⌈(X : ℝ)^(49999/100000 : ℝ)⌉₊
  let U := ⌊(X : ℝ)^(50001/100000 : ℝ)⌋₊+1
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 := zero_lt_one.trans_le hx
  have hr : 1 ≤ R := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hx (by norm_num))
  have hL : 1 ≤ L := Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos hx0 _)
  have hlu : L ≤ U := by
    apply Nat.ceil_le.mpr
    have ht := Nat.lt_floor_add_one ((X : ℝ)^(50001/100000 : ℝ))
    exact (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (49999/100000 : ℝ) ≤ 50001/100000)).trans
      (by exact_mod_cast ht.le)
  have huX : U ≤ X+1 := by
    apply Nat.add_le_add_right _ 1
    exact Nat.floor_le_of_le ((Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (50001/100000 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one _))
  have hR : (R : ℝ) ≤ (X : ℝ)^(1/100000 : ℝ) := Nat.floor_le (by positivity)
  have hl : (L : ℝ) ≤ 2*(X : ℝ)^(49999/100000 : ℝ) := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le (49999/100000 : ℝ))
    have h1 := Real.one_le_rpow hx (by norm_num : (0 : ℝ) ≤ 49999/100000)
    change (⌈(X : ℝ)^(49999/100000 : ℝ)⌉₊ : ℝ) ≤ _
    linarith only [h,h1]
  have hrl : (R : ℝ)*L ≤ 2*Real.sqrt X := by
    apply (mul_le_mul hR hl (Nat.cast_nonneg L) (by positivity)).trans_eq
    rw [mul_left_comm,← Real.rpow_add hx0,Real.sqrt_eq_rpow]; norm_num
  have hhead : |primeSum R X 1 L| ≤ 14*F*Real.sqrt X := by
    apply (centered_prime_absolute_bound hr hsize le_rfl).trans
    calc (F*R)*(7*L) = (7*F)*((R : ℝ)*L) := by ring
         _ ≤ (7*F)*(2*Real.sqrt X) := mul_le_mul_of_nonneg_left hrl (by positivity)
         _ = _ := by ring
  have hend : primeSum R X U (X+1) = aboveSquareRoot X := by
    unfold primeSum aboveSquareRoot
    apply (sum_subset ?_ ?_).symm
    · intro p hp
      obtain ⟨h,hh⟩ := mem_filter.mp hp
      obtain ⟨hl',hu'⟩ := mem_Ioc.mp h
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hl',(hu'.trans (Nat.div_le_self ..)).trans_lt (Nat.lt_succ_self _)⟩,hh⟩
    · intro p hp hex
      obtain ⟨h,hh⟩ := mem_filter.mp hp
      obtain ⟨hl',hu'⟩ := mem_Ico.mp h
      have hp0 : 0 < p := hh.pos
      have hgt : X/R < p := by
        by_contra! hle
        exact hex (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hl',hle⟩,hh⟩)
      have hlt : X/p < R := (Nat.div_lt_iff_lt_mul hp0).mpr (by
        simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hr).mp hgt)
      rw [centeredPrimeWeight_small ((Nat.one_le_div_iff hp0).mpr (by omega : p ≤ X)) hlt,mul_zero]
  have hf : |(Chebyshev.psi X-X)-primeSum R X 1 (X+1)| ≤ C*Real.sqrt X := hfull X hX
  have hb : |primeSum R X L U| ≤ D*Real.sqrt X := hband X hX
  rw [primeSum_split hL (hlu.trans huX),primeSum_split hlu huX,hend] at hf
  rw [abs_le] at hf hb hhead ⊢
  constructor <;> linarith only [hf.1,hf.2,hb.1,hb.2,hhead.1,hhead.2]

/-- The paired cofactor counts are carried by ordinary primes strictly
above the square-root band of their own divided horizon. -/
theorem ordinary_prime_cofactors_above_sqrt :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ V W N : ℕ, 1 ≤ N →
      |cofactorCountError V W N - ∑ d ∈ Icc 1 (min N W),
        Sieve.typeIIShort V d*aboveSquareRoot (N/d)| ≤
        (∑ d ∈ Icc 1 W, |Sieve.typeIIShort V d|)*(K*Real.sqrt N) := by
  obtain ⟨K,hK,h⟩ := ordinary_primes_above_sqrt_row
  refine ⟨K,hK,fun V W N _ => ?_⟩
  rw [cofactorCountError_eq,← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ d ∈ Icc 1 (min N W), |Sieve.typeIIShort V d| * (K*Real.sqrt N) := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro d hd
      obtain ⟨hl,hu⟩ := mem_Icc.mp hd
      have h1 := (Nat.one_le_div_iff hl).mpr (hu.trans (min_le_left ..))
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (h _ h1).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast Nat.div_le_self N d)) hK)
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg
        (Icc_subset_Icc_right (min_le_right N W)) (fun _ _ _ => abs_nonneg _)) (by positivity)

#print axioms ordinary_prime_cofactors_above_sqrt

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
