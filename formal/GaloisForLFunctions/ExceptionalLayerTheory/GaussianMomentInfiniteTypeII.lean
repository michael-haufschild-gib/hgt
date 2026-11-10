import GaloisForLFunctions.ExceptionalLayerTheory.GaussianMomentAllScales
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeSource
import GaloisForLFunctions.RHTower.Sieve.GallagherDyadicTail

/-!
# Uniform bounds for the complete Gaussian type-II moment

The retained Gaussian decay sums over all product scales. The resulting
bound is independent of the prime truncation and keeps the height saving.
An elementary coefficient bound proves absolute convergence before the
estimate passes to the complete arithmetic convolution.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory


private theorem exp_neg_four_pow_cube (j : ℕ) :
    Real.exp (-((4 : ℝ) ^ j)) ≤ 6 / (64 : ℝ) ^ j := by
  have h := Real.pow_div_factorial_le_exp ((4 : ℝ) ^ j) (by positivity) 3
  norm_num at h
  have hp : ((4 : ℝ) ^ j) ^ 3 = (64 : ℝ) ^ j := by
    rw [← pow_mul, mul_comm j 3, pow_mul]
    norm_num
  rw [hp] at h
  calc
    _ = 1 / Real.exp ((4 : ℝ) ^ j) := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / ((64 : ℝ) ^ j / 6) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) h
    _ = _ := by field_simp

private theorem sum_square_le_sum_diagonal (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (K : ℕ) :
    (∑ j ∈ range K, ∑ k ∈ range K, f (j + k)) ≤
      ∑ n ∈ range (2 * K), ((n : ℝ) + 1) * f n := by
  classical
  let a : ℕ → Finset (ℕ × ℕ) := Finset.HasAntidiagonal.antidiagonal
  have hsub : range K ×ˢ range K ⊆ (range (2 * K)).biUnion a := by
    intro p hp
    obtain ⟨hj, hk⟩ := mem_product.mp hp
    refine mem_biUnion.mpr ⟨p.1 + p.2, mem_range.mpr (by
      have := mem_range.mp hj
      have := mem_range.mp hk
      omega), ?_⟩
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
  have hdis : (↑(range (2 * K)) : Set ℕ).PairwiseDisjoint a := by
    intro n _ m _ hnm
    apply disjoint_left.mpr
    intro p hp hpm
    have hn := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hm := Finset.HasAntidiagonal.mem_antidiagonal.mp hpm
    exact hnm (hn.symm.trans hm)
  calc
    _ = ∑ p ∈ range K ×ˢ range K, f (p.1 + p.2) := (sum_product _ _ _).symm
    _ ≤ ∑ p ∈ (range (2 * K)).biUnion a, f (p.1 + p.2) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hf (p.1 + p.2))
    _ = ∑ n ∈ range (2 * K), ∑ p ∈ a n, f (p.1 + p.2) := sum_biUnion hdis
    _ = _ := by
      apply sum_congr rfl
      intro n _
      have he : (∑ p ∈ a n, f (p.1 + p.2)) = ∑ p ∈ a n, f n := by
        apply sum_congr rfl
        intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
      rw [he]
      simp [a]

/-- A geometric head and Gaussian tail bound a weighted dyadic sum uniformly in its truncation. -/
theorem sum_dyadic_gaussian_fourth_le {q α : ℝ}
    (hq : 1 < q) (hq2 : q ≤ 2) (hα : 0 ≤ α) (R N : ℕ)
    (hscale : 2 ≤ α * (4 : ℝ) ^ R) :
    ∑ n ∈ range N, q ^ n * ((n : ℝ) + 1) ^ 4 * Real.exp (-α * (4 : ℝ) ^ n / 2) ≤
      (1 / (q - 1) + 12) * q ^ R * ((R : ℝ) + 1) ^ 4 := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  let f := fun n : ℕ => q ^ n * ((n : ℝ) + 1) ^ 4 * Real.exp (-α * (4 : ℝ) ^ n / 2)
  have hf (n : ℕ) : 0 ≤ f n := by dsimp only [f]; positivity
  have hhead : ∑ n ∈ range R, f n ≤ (q ^ R / (q - 1)) * ((R : ℝ) + 1) ^ 4 := by
    calc
      _ ≤ ∑ n ∈ range R, q ^ n * ((R : ℝ) + 1) ^ 4 := by
        apply sum_le_sum
        intro n hn
        have hnR : (n : ℝ) + 1 ≤ (R : ℝ) + 1 := by exact_mod_cast (show n + 1 ≤ R + 1 by have := mem_range.mp hn; omega)
        have he : Real.exp (-α * (4 : ℝ) ^ n / 2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by
            have hh : 0 ≤ α * (4 : ℝ) ^ n / 2 := by positivity
            linarith only [hh])
        calc
          f n ≤ q ^ n * ((R : ℝ) + 1) ^ 4 * 1 := by dsimp only [f]; gcongr
          _ = _ := mul_one _
      _ = ((q ^ R - 1) / (q - 1)) * ((R : ℝ) + 1) ^ 4 := by
        rw [← sum_mul, geom_sum_eq hq.ne']
      _ ≤ _ := by gcongr; linarith only
  have htail (l : ℕ) : f (R + l) ≤
      6 * q ^ R * ((R : ℝ) + 1) ^ 4 * (1 / 2 : ℝ) ^ l := by
    have hpoly : (((R + l : ℕ) : ℝ) + 1) ^ 4 ≤ ((R : ℝ) + 1) ^ 4 * (16 : ℝ) ^ l := by
      have hsum : (((R + l : ℕ) : ℝ) + 1) ≤ ((R : ℝ) + 1) * ((l : ℝ) + 1) := by
        push_cast
        nlinarith only [mul_nonneg (Nat.cast_nonneg R : (0 : ℝ) ≤ R) (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
      have hl : (l : ℝ) + 1 ≤ (2 : ℝ) ^ l := by exact_mod_cast Nat.lt_two_pow_self (n := l)
      have hp : ((2 : ℝ) ^ l) ^ 4 = (16 : ℝ) ^ l := by
        rw [← pow_mul, mul_comm l 4, pow_mul]
        norm_num
      calc
        _ ≤ (((R : ℝ) + 1) * ((l : ℝ) + 1)) ^ 4 := by gcongr
        _ = ((R : ℝ) + 1) ^ 4 * ((l : ℝ) + 1) ^ 4 := mul_pow _ _ _
        _ ≤ ((R : ℝ) + 1) ^ 4 * ((2 : ℝ) ^ l) ^ 4 := by gcongr
        _ = _ := by rw [hp]
    have hexp : Real.exp (-α * (4 : ℝ) ^ (R + l) / 2) ≤ 6 / (64 : ℝ) ^ l := by
      apply (Real.exp_le_exp.mpr ?_).trans (exp_neg_four_pow_cube l)
      have hh := mul_le_mul_of_nonneg_right hscale (by positivity : 0 ≤ (4 : ℝ) ^ l)
      rw [pow_add]
      nlinarith only [hh]
    have hpow : q ^ (R + l) ≤ q ^ R * (2 : ℝ) ^ l := by rw [pow_add]; gcongr
    calc
      f (R + l) ≤ (q ^ R * (2 : ℝ) ^ l) * (((R : ℝ) + 1) ^ 4 * (16 : ℝ) ^ l) *
          (6 / (64 : ℝ) ^ l) := by dsimp only [f]; gcongr
      _ = 6 * q ^ R * ((R : ℝ) + 1) ^ 4 * (((2 : ℝ) ^ l * (16 : ℝ) ^ l) / (64 : ℝ) ^ l) := by ring
      _ = _ := by rw [← mul_pow, ← div_pow]; norm_num
  have ht : ∑ l ∈ range N, f (R + l) ≤ 12 * q ^ R * ((R : ℝ) + 1) ^ 4 := by
    have hg : ∑ l ∈ range N, (1 / 2 : ℝ) ^ l ≤ 2 := by
      have hI : Ico 0 N = range N := by ext n; simp
      simpa only [hI, pow_zero, show (1 : ℝ) / (1 - 1 / 2) = 2 by norm_num] using
        (geom_sum_Ico_le_of_lt_one (m := 0) (n := N) (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
    calc
      _ ≤ ∑ l ∈ range N, 6 * q ^ R * ((R : ℝ) + 1) ^ 4 * (1 / 2 : ℝ) ^ l := sum_le_sum fun l _ => htail l
      _ = (6 * q ^ R * ((R : ℝ) + 1) ^ 4) * ∑ l ∈ range N, (1 / 2 : ℝ) ^ l := (mul_sum _ _ _).symm
      _ ≤ (6 * q ^ R * ((R : ℝ) + 1) ^ 4) * 2 := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ range (R + N), f n :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun n _ _ => hf n)
    _ = (∑ n ∈ range R, f n) + ∑ l ∈ range N, f (R + l) := sum_range_add f R N
    _ ≤ (q ^ R / (q - 1)) * ((R : ℝ) + 1) ^ 4 + 12 * q ^ R * ((R : ℝ) + 1) ^ 4 :=
      add_le_add hhead ht
    _ = _ := by ring

private theorem dyadic_weight_factor (σ : ℝ) (j : ℕ) :
    (2 : ℝ) ^ j * ((2 : ℝ) ^ j) ^ (-σ) = ((2 : ℝ) ^ (1 - σ)) ^ j := by
  calc
    _ = ((2 : ℝ) ^ j) ^ (1 - σ) := by
      rw [sub_eq_add_neg, Real.rpow_add (by positivity), Real.rpow_one]
    _ = _ := by
      rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (j : ℝ),
        Real.rpow_mul_natCast (by norm_num)]

private theorem log_dyadic_le (j : ℕ) :
    1 + Real.log (2 * ((2 ^ j : ℕ) : ℝ)) ≤ 2 * ((j : ℝ) + 1) := by
  have hlog : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hj := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (j : ℝ) + 1)
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  nlinarith only [hj, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

private theorem sqrt_gaussianMomentRectangleEnergy_dyadic_le (σ α : ℝ) (j k : ℕ) :
    Real.sqrt (gaussianMomentRectangleEnergy σ α (2 ^ j) (2 ^ k)) ≤
      8 * ((2 : ℝ) ^ (1 - σ)) ^ (j + k) * ((j + k : ℕ) + 1 : ℝ) ^ 3 *
        Real.exp (-α * (4 : ℝ) ^ (j + k) / 2) := by
  have hW : (2 ^ j : ℝ) * (2 ^ k : ℝ) * (2 ^ j : ℝ) ^ (-σ) * (2 ^ k : ℝ) ^ (-σ) =
      ((2 : ℝ) ^ (1 - σ)) ^ (j + k) := by
    calc
      _ = ((2 : ℝ) ^ j * ((2 : ℝ) ^ j) ^ (-σ)) *
          ((2 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ (-σ)) := by ring
      _ = _ := by rw [dyadic_weight_factor, dyadic_weight_factor, pow_add]
  have hX : ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ (j + k) := by
    rw [← mul_pow, ← pow_add, ← pow_mul, mul_comm (j + k) 2, pow_mul]
    norm_num
  have hLD : 1 ≤ 1 + Real.log (2 * ((2 ^ j : ℕ) : ℝ)) := by
    have hh : 0 ≤ Real.log (2 * ((2 ^ j : ℕ) : ℝ)) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * 2 ^ j by have := Nat.one_le_two_pow (n := j); omega))
    linarith only [hh]
  have hLM : 0 ≤ 1 + Real.log (2 * ((2 ^ k : ℕ) : ℝ)) := by
    have hh : 0 ≤ Real.log (2 * ((2 ^ k : ℕ) : ℝ)) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * 2 ^ k by have := Nat.one_le_two_pow (n := k); omega))
    linarith only [hh]
  have hroot : Real.sqrt (1 + Real.log (2 * ((2 ^ j : ℕ) : ℝ))) ≤ 2 * ((j : ℝ) + 1) := by
    have hh : Real.sqrt (1 + Real.log (2 * ((2 ^ j : ℕ) : ℝ))) ≤
        1 + Real.log (2 * ((2 ^ j : ℕ) : ℝ)) := by
      apply (Real.sqrt_le_left (by positivity)).mpr
      nlinarith only [hLD]
    exact hh.trans (log_dyadic_le j)
  have he : Real.sqrt (Real.exp (-α * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ k) ^ 2)) =
      Real.exp (-α * (4 : ℝ) ^ (j + k) / 2) := by
    have hexp : Real.exp (-α * ((2 : ℝ) ^ j) ^ 2 * ((2 : ℝ) ^ k) ^ 2) =
        (Real.exp (-α * (4 : ℝ) ^ (j + k) / 2)) ^ 2 := by
      rw [show (Real.exp (-α * (4 : ℝ) ^ (j + k) / 2)) ^ 2 =
        Real.exp (-α * (4 : ℝ) ^ (j + k) / 2) * Real.exp (-α * (4 : ℝ) ^ (j + k) / 2) from pow_two _,
        ← Real.exp_add]
      congr 1
      rw [← hX]
      ring
    rw [hexp, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
  have henergy : Real.sqrt (gaussianMomentRectangleEnergy σ α (2 ^ j) (2 ^ k)) =
      ((2 : ℝ) ^ (1 - σ)) ^ (j + k) *
        Real.sqrt (1 + Real.log (2 * ((2 ^ j : ℕ) : ℝ))) *
        (1 + Real.log (2 * ((2 ^ k : ℕ) : ℝ))) ^ 2 *
          Real.exp (-α * (4 : ℝ) ^ (j + k) / 2) := by
    unfold gaussianMomentRectangleEnergy
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity),
      show (1 + Real.log (2 * ((2 ^ k : ℕ) : ℝ))) ^ 4 =
        ((1 + Real.log (2 * ((2 ^ k : ℕ) : ℝ))) ^ 2) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
    push_cast
    rw [hW, he]
  rw [henergy]
  have hLMle := log_dyadic_le k
  have hjk : ((j : ℝ) + 1) * ((k : ℝ) + 1) ^ 2 ≤ (((j + k : ℕ) : ℝ) + 1) ^ 3 := by
    have hj : (j : ℝ) + 1 ≤ (((j + k : ℕ) : ℝ) + 1) := by push_cast; linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hk : (k : ℝ) + 1 ≤ (((j + k : ℕ) : ℝ) + 1) := by push_cast; linarith only [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    calc
      _ ≤ ((((j + k : ℕ) : ℝ) + 1)) * ((((j + k : ℕ) : ℝ) + 1)) ^ 2 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ((2 : ℝ) ^ (1 - σ)) ^ (j + k) * (2 * ((j : ℝ) + 1)) *
        (2 * ((k : ℝ) + 1)) ^ 2 * Real.exp (-α * (4 : ℝ) ^ (j + k) / 2) := by gcongr
    _ = 8 * ((2 : ℝ) ^ (1 - σ)) ^ (j + k) * (((j : ℝ) + 1) * ((k : ℝ) + 1) ^ 2) *
        Real.exp (-α * (4 : ℝ) ^ (j + k) / 2) := by ring
    _ ≤ _ := by gcongr

/-- The retained rectangle envelopes sum uniformly in the dyadic truncation. -/
theorem sum_sqrt_gaussianMomentRectangleEnergy_le {σ α : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 ≤ α) (R K : ℕ)
    (hscale : 2 ≤ α * (4 : ℝ) ^ R) :
    (∑ j ∈ range K, ∑ k ∈ range K,
      Real.sqrt (gaussianMomentRectangleEnergy σ α (2 ^ j) (2 ^ k))) ≤
        8 * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) *
          ((2 : ℝ) ^ (1 - σ)) ^ R * ((R : ℝ) + 1) ^ 4 := by
  let q := (2 : ℝ) ^ (1 - σ)
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  have hq2 : q ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith only [hσ] : 1 - σ ≤ 1)
  let f := fun n : ℕ => q ^ n * ((n : ℝ) + 1) ^ 3 * Real.exp (-α * (4 : ℝ) ^ n / 2)
  have hf (n : ℕ) : 0 ≤ f n := by dsimp only [f, q]; positivity
  calc
    _ ≤ ∑ j ∈ range K, ∑ k ∈ range K, 8 * f (j + k) := by
      apply sum_le_sum
      intro j _
      apply sum_le_sum
      intro k _
      exact (sqrt_gaussianMomentRectangleEnergy_dyadic_le σ α j k).trans_eq (by dsimp only [f, q]; ring)
    _ = 8 * (∑ j ∈ range K, ∑ k ∈ range K, f (j + k)) := by simp_rw [← mul_sum]
    _ ≤ 8 * ∑ n ∈ range (2 * K), ((n : ℝ) + 1) * f n :=
      mul_le_mul_of_nonneg_left (sum_square_le_sum_diagonal f hf K) (by norm_num)
    _ = 8 * ∑ n ∈ range (2 * K), q ^ n * ((n : ℝ) + 1) ^ 4 * Real.exp (-α * (4 : ℝ) ^ n / 2) := by
      congr 1
      apply sum_congr rfl
      intro n _
      dsimp only [f]
      ring
    _ ≤ 8 * ((1 / (q - 1) + 12) * q ^ R * ((R : ℝ) + 1) ^ 4) :=
      mul_le_mul_of_nonneg_left (sum_dyadic_gaussian_fourth_le hq hq2 hα R (2 * K) hscale) (by norm_num)
    _ = _ := by ring

/-- The actual type-II convolution moment has an arithmetic bound independent
of both prime endpoints, at every dyadic scale dominating the damping radius. -/
theorem exists_gaussianVaughan_moment_uniform_typeII_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α ξ t : ℝ) (A B R U V : ℕ),
      0 ≤ σ → σ < 1 → 0 < ξ → 1 ≤ t → ξ / (2 * t) ≤ α → α ≤ ξ →
      1 ≤ A → 1 ≤ B → 2 ≤ α * (4 : ℝ) ^ R →
      128 * t * Real.log t ≤ Real.pi * U → 2 * t ≤ V →
      ‖(((α : ℂ) - ξ * I) / t) *
        (∑ n ∈ Ico A B, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
          gaussianPrimeWeight (σ - 2) α ξ t n)‖ ≤
        8 * Real.sqrt (C / t) * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) *
          ((2 : ℝ) ^ (1 - σ)) ^ R * ((R : ℝ) + 1) ^ 4 := by
  obtain ⟨C, hC, hb⟩ := exists_gaussianVaughan_moment_typeII_block_bound
  refine ⟨C, hC, ?_⟩
  intro σ α ξ t A B R U V hσ hσ1 hξ ht hlower hupper hA hB hscale hU hV
  have hα : 0 ≤ α := (by positivity : 0 ≤ ξ / (2 * t)).trans hlower
  have hBK : B ≤ 2 ^ B := (Nat.lt_two_pow_self (n := B)).le
  have he := sum_sqrt_gaussianMomentRectangleEnergy_le hσ hσ1 hα R B hscale
  refine (hb σ α ξ t A B B U V hσ hξ ht hlower hupper hA hB hBK hU hV).trans ?_
  exact (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)).trans_eq (by ring)


private theorem norm_typeII_convolution_le (U V n : ℕ) :
    ‖(((typeIILong U * typeIIShort V) n : ℝ) : ℂ)‖ ≤ 2 * (n : ℝ) ^ 2 := by
  rw [coe_mul_apply]
  calc
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal,
        ‖((typeIILong U p.1 : ℝ) : ℂ) * ((typeIIShort V p.2 : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, 2 * (n : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hp' := Nat.mem_divisorsAntidiagonal.mp hp
      have hp1 : 1 ≤ p.1 := by
        by_contra h
        have hz : p.1 = 0 := by omega
        rw [hz, zero_mul] at hp'
        exact hp'.2 hp'.1.symm
      have hp2 : 1 ≤ p.2 := by
        by_contra h
        have hz : p.2 = 0 := by omega
        rw [hz, mul_zero] at hp'
        exact hp'.2 hp'.1.symm
      have hlong : |typeIILong U p.1| ≤ (p.1 : ℝ) := by
        have hlog := Real.log_le_sub_one_of_pos (by exact_mod_cast hp1 : (0 : ℝ) < p.1)
        exact ((abs_vonMangoldt_sub_truncAF_le U p.1).trans ArithmeticFunction.vonMangoldt_le_log).trans
          (by linarith only [hlog])
      have hshort : |typeIIShort V p.2| ≤ 2 * (p.2 : ℝ) := by
        have hh := abs_one_sub_zeta_mul_moebius_le V p.2
        change |typeIIShort V p.2| ≤ 1 + (p.2.divisors.card : ℝ) at hh
        have hcard : (p.2.divisors.card : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast Nat.card_divisors_le_self p.2
        have hp2' : (1 : ℝ) ≤ p.2 := by exact_mod_cast hp2
        linarith only [hh, hcard, hp2']
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      refine (mul_le_mul hlong hshort (abs_nonneg _) (by positivity)).trans_eq ?_
      have hprod : (p.1 : ℝ) * p.2 = n := by exact_mod_cast hp'.1
      nlinarith only [hprod]
    _ = (n.divisors.card : ℝ) * (2 * n) := by simp [card_divisorsAntidiagonal]
    _ ≤ (n : ℝ) * (2 * n) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.card_divisors_le_self n
    _ = _ := by ring

/-- The norm of a Gaussian Dirichlet weight depends only on its real damping and abscissa. -/
theorem norm_gaussianPrimeWeight_exact (σ α ξ t : ℝ) (n : ℕ) :
    ‖gaussianPrimeWeight σ α ξ t n‖ =
      (n : ℝ) ^ (-σ) * Real.exp (-α * (n : ℝ) ^ 2) := by
  rw [gaussianPrimeWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  congr 1
  rw [gaussianPrimePhase, Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.natCast_re, Complex.natCast_im, pow_two, Complex.mul_im]
  ring

/-- Absolute convergence holds for the literal shifted arithmetic convolution. -/
theorem summable_gaussianVaughan_moment_typeII {σ α : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 < α) (ξ t : ℝ) (U V : ℕ) :
    Summable (fun n : ℕ => (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
      gaussianPrimeWeight (σ - 2) α ξ t n) := by
  apply ((RHTower.summable_pow_mul_exp_neg_nat_sq 4 hα).mul_left 2).of_norm_bounded
  intro n
  rw [norm_mul, norm_gaussianPrimeWeight_exact]
  have hc := norm_typeII_convolution_le U V n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : ‖(((typeIILong U * typeIIShort V) 0 : ℝ) : ℂ)‖ = 0 := by simp
    rw [hz, zero_mul]
    positivity
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hw : (n : ℝ) ^ (-(σ - 2)) ≤ (n : ℝ) ^ 2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hn1
        (by linarith only [hσ] : -(σ - 2) ≤ 2)
    calc
      _ ≤ (2 * (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 * Real.exp (-α * (n : ℝ) ^ 2)) := by gcongr
      _ = _ := by ring

/-- The infinite type-II moment retains the truncation-uniform arithmetic estimate. -/
theorem exists_gaussianVaughan_moment_infinite_typeII_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α ξ t : ℝ) (R U V : ℕ),
      0 ≤ σ → σ < 1 → 0 < ξ → 1 ≤ t → ξ / (2 * t) ≤ α → α ≤ ξ →
      2 ≤ α * (4 : ℝ) ^ R →
      128 * t * Real.log t ≤ Real.pi * U → 2 * t ≤ V →
      ‖(((α : ℂ) - ξ * I) / t) *
        (∑' n : ℕ, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
          gaussianPrimeWeight (σ - 2) α ξ t n)‖ ≤
        8 * Real.sqrt (C / t) * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) *
          ((2 : ℝ) ^ (1 - σ)) ^ R * ((R : ℝ) + 1) ^ 4 := by
  obtain ⟨C, hC, hb⟩ := exists_gaussianVaughan_moment_uniform_typeII_bound
  refine ⟨C, hC, ?_⟩
  intro σ α ξ t R U V hσ hσ1 hξ ht hlower hupper hscale hU hV
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hα : 0 < α := (by positivity : 0 < ξ / (2 * t)).trans_le hlower
  let f := fun n : ℕ => (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
    gaussianPrimeWeight (σ - 2) α ξ t n
  have hs : Summable f := summable_gaussianVaughan_moment_typeII hσ hα ξ t U V
  have hz : f 0 = 0 := by simp [f]
  have hlim := (hs.tendsto_sum_tsum_nat.const_mul (((α : ℂ) - ξ * I) / t)).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have he : (∑ n ∈ Ico 1 N, f n) = ∑ n ∈ range N, f n := by
    rw [sum_Ico_eq_sub _ hN, sum_range_one, hz, sub_zero]
  have hh := hb σ α ξ t 1 N R U V hσ hσ1 hξ ht hlower hupper le_rfl hN hscale hU hV
  change ‖(((α : ℂ) - ξ * I) / t) * (∑ n ∈ Ico 1 N, f n)‖ ≤ _ at hh
  rwa [he] at hh

/-- A dyadic scale just above a real damping scale costs only a constant
factor in length and a logarithm in the scale index. -/
theorem exists_gaussianMoment_physical_scale {σ α X : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 ≤ α) (hX : 1 ≤ X) (hscale : 2 ≤ α * X ^ 2) :
    ∃ R : ℕ, 2 ≤ α * (4 : ℝ) ^ R ∧
      ((2 : ℝ) ^ (1 - σ)) ^ R * ((R : ℝ) + 1) ^ 4 ≤
        2 * X ^ (1 - σ) * (2 + Real.log X / Real.log 2) ^ 4 := by
  obtain ⟨k, hlo, hhi⟩ := RHTower.Sieve.exists_dyadic_scale (W := 1) (by norm_num) hX
  simp only [mul_one] at hlo hhi
  refine ⟨k + 1, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith only [hX]) hhi.le 2) hα
    have hp : ((2 : ℝ) ^ (k + 1)) ^ 2 = (4 : ℝ) ^ (k + 1) := by
      rw [← pow_mul, mul_comm (k + 1) 2, pow_mul]
      norm_num
    rw [hp] at hh
    exact hscale.trans hh
  · have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ k) hlo
    rw [Real.log_pow] at hlog
    have hk : (k : ℝ) ≤ Real.log X / Real.log 2 :=
      (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog
    have hidx : ((k + 1 : ℕ) : ℝ) + 1 ≤ 2 + Real.log X / Real.log 2 := by
      push_cast
      linarith only [hk]
    have hlength : (2 : ℝ) ^ (k + 1) ≤ 2 * X := by
      rw [pow_succ]
      nlinarith only [hlo]
    have hq2 : (2 : ℝ) ^ (1 - σ) ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith only [hσ] : 1 - σ ≤ 1)
    have hp : ((2 : ℝ) ^ (1 - σ)) ^ (k + 1) ≤ 2 * X ^ (1 - σ) := by
      calc
        _ = ((2 : ℝ) ^ (k + 1)) ^ (1 - σ) := by
          rw [← Real.rpow_mul_natCast (by norm_num), mul_comm (1 - σ),
            Real.rpow_natCast_mul (by norm_num)]
        _ ≤ (2 * X) ^ (1 - σ) := Real.rpow_le_rpow (by positivity) hlength (by linarith only [hσ1])
        _ = (2 : ℝ) ^ (1 - σ) * X ^ (1 - σ) := Real.mul_rpow (by norm_num) (by linarith only [hX])
        _ ≤ _ := mul_le_mul_of_nonneg_right hq2 (Real.rpow_nonneg (by linarith only [hX]) _)
    exact mul_le_mul hp (pow_le_pow_left₀ (by positivity) hidx 4) (by positivity) (by positivity)

/-- A real physical scale gives a closed bound for the complete infinite
arithmetic type-II moment, with square-root-of-height saving. -/
theorem exists_gaussianVaughan_moment_physical_typeII_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α ξ t X : ℝ) (U V : ℕ),
      0 ≤ σ → σ < 1 → 0 < ξ → 1 ≤ t → ξ / (2 * t) ≤ α → α ≤ ξ →
      1 ≤ X → 2 ≤ α * X ^ 2 →
      128 * t * Real.log t ≤ Real.pi * U → 2 * t ≤ V →
      ‖(((α : ℂ) - ξ * I) / t) *
        (∑' n : ℕ, (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) *
          gaussianPrimeWeight (σ - 2) α ξ t n)‖ ≤
        16 * Real.sqrt (C / t) * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) *
          X ^ (1 - σ) * (2 + Real.log X / Real.log 2) ^ 4 := by
  obtain ⟨C, hC, hb⟩ := exists_gaussianVaughan_moment_infinite_typeII_bound
  refine ⟨C, hC, ?_⟩
  intro σ α ξ t X U V hσ hσ1 hξ ht hlower hupper hX hscale hU hV
  have hα : 0 ≤ α := (by positivity : 0 ≤ ξ / (2 * t)).trans hlower
  obtain ⟨R, hR, hbound⟩ := exists_gaussianMoment_physical_scale hσ hσ1 hα hX hscale
  have hq : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  have hf : 0 ≤ 8 * Real.sqrt (C / t) * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) := by positivity
  refine (hb σ α ξ t R U V hσ hσ1 hξ ht hlower hupper hR hU hV).trans ?_
  convert mul_le_mul_of_nonneg_left hbound hf using 1 <;> ring

/-- Every positive Gaussian damping has an admissible physical scale. -/
theorem gaussianMoment_physicalScale_admissible {α : ℝ} (hα : 0 < α) :
    1 ≤ max 1 (Real.sqrt (2 / α)) ∧
      2 ≤ α * (max 1 (Real.sqrt (2 / α))) ^ 2 := by
  refine ⟨le_max_left _ _, ?_⟩
  have hh := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right 1 (Real.sqrt (2 / α))) 2) hα.le
  rw [Real.sq_sqrt (by positivity), mul_div_cancel₀ _ hα.ne'] at hh
  exact hh

#print axioms sum_dyadic_gaussian_fourth_le
#print axioms exists_gaussianMoment_physical_scale
#print axioms norm_gaussianPrimeWeight_exact
#print axioms sum_sqrt_gaussianMomentRectangleEnergy_le
#print axioms exists_gaussianVaughan_moment_uniform_typeII_bound
#print axioms summable_gaussianVaughan_moment_typeII
#print axioms exists_gaussianVaughan_moment_infinite_typeII_bound
#print axioms exists_gaussianVaughan_moment_physical_typeII_bound
#print axioms gaussianMoment_physicalScale_admissible

end GaloisForLFunctions.ExceptionalLayerTheory
