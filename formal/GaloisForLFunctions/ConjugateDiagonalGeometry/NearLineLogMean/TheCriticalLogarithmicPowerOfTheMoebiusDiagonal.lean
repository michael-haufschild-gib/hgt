import GaloisForLFunctions.RHTower.SquarefreeLowerDensity
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.PSeries

/-!
# The critical logarithmic exponent of the Möbius diagonal

Every initial interval contains at least a quarter squarefree integers.
Abel summation preserves this fraction under every decreasing nonnegative
weight. Cauchy condensation therefore gives the exact convergence
boundary for the diagonals with fractional powers of log n.
-/

noncomputable section
open Finset Filter ArithmeticFunction
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def squareMass (n : ℕ) : ℝ := ((moebius n : ℤ):ℝ)^2

private theorem squareMass_nonneg (n : ℕ) : 0 ≤ squareMass n := sq_nonneg _

private theorem squareMass_eq (n : ℕ) : squareMass n = if Squarefree n then 1 else 0 := by
  classical
  rw [squareMass,←Int.cast_pow,moebius_sq]
  split <;> norm_num

private theorem squareMass_prefix (K : ℕ) :
    (K:ℝ) ≤ 4*(∑ n ∈ Icc 1 K, squareMass n) := by
  classical
  have h := RHTower.quarter_le_card_squarefree K
  have he : (∑ n ∈ Icc 1 K, squareMass n) = (((Icc 1 K).filter Squarefree).card:ℝ) := by
    simp only [squareMass_eq,←sum_filter,sum_const, nsmul_eq_mul,mul_one]
  rw [he]
  linarith only [h]

/-- Every finite decreasing nonnegative weight sees at least one quarter
of its mass on the support of the Möbius coefficients. -/
theorem squarefree_quarter_of_antitone_mass (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hm : Antitone f) (K : ℕ) :
    (∑ n ∈ Icc 1 K, f n) ≤ 4*∑ n ∈ Icc 1 K, ((moebius n : ℤ):ℝ)^2*f n := by
  let A (N : ℕ) := 4*(∑ n ∈ Icc 1 N, squareMass n)-(N:ℝ)
  have hA (N : ℕ) : 0 ≤ A N := sub_nonneg.mpr (squareMass_prefix N)
  have h (N : ℕ) : f (N+1)*A N ≤
      4*(∑ n ∈ Icc 1 N, squareMass n*f n)-(∑ n ∈ Icc 1 N, f n) := by
    induction N with
    | zero => simp [A]
    | succ N ih =>
      have he : A (N+1)=A N+4*squareMass (N+1)-1 := by
        simp only [A,sum_Icc_succ_top (by omega : 1 ≤ N+1),Nat.cast_add_one]; ring
      have hd := mul_le_mul_of_nonneg_right (hm (Nat.le_succ (N+1))) (hA (N+1))
      rw [he] at hd
      rw [he,sum_Icc_succ_top (by omega : 1 ≤ N+1),sum_Icc_succ_top (by omega : 1 ≤ N+1)]
      linarith only [hd,ih]
  exact sub_nonneg.mp ((mul_nonneg (hf _) (hA K)).trans (h K))

private theorem summable_squareMass_iff (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hm : Antitone f) :
    Summable (fun n => squareMass n*f n) ↔ Summable f := by
  constructor
  · intro hs
    apply summable_of_sum_range_le hf (c:=f 0+4*(∑' n, squareMass n*f n))
    intro K
    have hsub : range K ⊆ insert 0 (Icc 1 K) := by
      intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · exact mem_insert_self ..
      · exact mem_insert_of_mem (mem_Icc.mpr ⟨hp,(mem_range.mp hn).le⟩)
    have hu := sum_le_sum_of_subset_of_nonneg (f:=f) hsub (fun n _ _ => hf n)
    rw [sum_insert (by simp : 0 ∉ Icc 1 K)] at hu
    have hw := squarefree_quarter_of_antitone_mass f hf hm K
    have ht := hs.sum_le_tsum (Icc 1 K) (fun n _ => mul_nonneg (squareMass_nonneg n) (hf n))
    change (∑ n ∈ Icc 1 K, f n) ≤ 4*∑ n ∈ Icc 1 K, squareMass n*f n at hw
    linarith only [hu,hw,ht]
  · intro hs
    apply hs.of_nonneg_of_le (fun n => mul_nonneg (squareMass_nonneg n) (hf n))
    intro n
    rw [squareMass_eq]
    split <;> simp [hf]

private def logWeight (p : ℝ) (n : ℕ) : ℝ :=
  (max 2 (n:ℝ))⁻¹*(Real.log (max 2 (n:ℝ)))^(-p)

private theorem logWeight_nonneg (p : ℝ) (n : ℕ) : 0 ≤ logWeight p n :=
  mul_nonneg (inv_nonneg.mpr (le_max_of_le_left (by norm_num))) (Real.rpow_nonneg
    (Real.log_nonneg (le_max_of_le_left (by norm_num : (1:ℝ)≤2))) _)

private theorem logWeight_antitone {p : ℝ} (hp : 0 ≤ p) : Antitone (logWeight p) := by
  intro m n h
  have hm : (0:ℝ) < max 2 (m:ℝ) := lt_of_lt_of_le (by norm_num) (le_max_left ..)
  have hmn := max_le_max_left (2:ℝ) (Nat.cast_le.mpr h)
  have hl : 0 < Real.log (max 2 (m:ℝ)) := Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_left ..))
  exact mul_le_mul (inv_anti₀ hm hmn) (Real.rpow_le_rpow_of_nonpos hl
    (Real.log_le_log hm hmn) (neg_nonpos.mpr hp))
    (Real.rpow_nonneg (hl.le.trans (Real.log_le_log hm hmn)) _) (inv_nonneg.mpr hm.le)

private theorem logWeight_summable_iff {p : ℝ} (hp : 0 ≤ p) : Summable (logWeight p) ↔ 1 < p := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [←summable_condensed_iff_of_nonneg (logWeight_nonneg p) (fun _ _ _ h => logWeight_antitone hp h)]
  have he : (fun k : ℕ => (2:ℝ)^k*logWeight p (2^k)) =ᶠ[atTop]
      (fun k : ℕ => (Real.log 2)^(-p)*(k:ℝ)^(-p)) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
    have h₂ : (2:ℝ) ≤ (2:ℝ)^k := by simpa using pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hk
    rw [logWeight,Nat.cast_pow,Nat.cast_ofNat,max_eq_right h₂,Real.log_pow,
      Real.mul_rpow (Nat.cast_nonneg _) hlog.le,←mul_assoc,mul_inv_cancel₀ (by positivity),one_mul,mul_comm]
  rw [summable_congr_atTop he]
  have hc : (Real.log 2)^(-p) ≠ 0 := (Real.rpow_pos_of_pos hlog _).ne'
  constructor
  · intro h
    have h' := h.mul_left ((Real.log 2)^(-p))⁻¹
    simp only [←mul_assoc,inv_mul_cancel₀ hc,one_mul] at h'
    linarith only [Real.summable_nat_rpow.mp h']
  · intro h
    exact (Real.summable_nat_rpow.mpr (by linarith only [h] : -p < -1)).mul_left _

/-- The diagonal of the critical-line Möbius polynomial with a logarithmic
filter is summable exactly above power one. -/
theorem squarefree_logarithmic_diagonal_iff (p : ℝ) :
    Summable (fun n : ℕ => ((moebius n : ℤ):ℝ)^2 / (n:ℝ) * (Real.log n)^(-p)) ↔ 1 < p := by
  have he : (fun n : ℕ => ((moebius n : ℤ):ℝ)^2/(n:ℝ)*(Real.log n)^(-p)) =ᶠ[atTop]
      (fun n => squareMass n*logWeight p n) := by
    filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    simp only [squareMass,logWeight,max_eq_right (show (2:ℝ) ≤ n by exact_mod_cast hn),div_eq_mul_inv,mul_assoc]
  rw [summable_congr_atTop he]
  rcases le_or_gt 0 p with hp | hp
  · exact (summable_squareMass_iff _ (logWeight_nonneg p) (logWeight_antitone hp)).trans (logWeight_summable_iff hp)
  · refine iff_of_false ?_ (by linarith only [hp])
    intro hs
    have hm : (fun n => squareMass n*logWeight 1 n) ≤ᶠ[atTop] (fun n => squareMass n*logWeight p n) := by
      obtain ⟨N,hN⟩ := exists_nat_gt (Real.exp 1)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hlog : 1 ≤ Real.log (max 2 (n:ℝ)) := by
        rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (by norm_num) (le_max_left ..))]
        exact hN.le.trans ((Nat.cast_le.mpr hn).trans (le_max_right ..))
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hlog (by linarith only [hp] : -(1:ℝ) ≤ -p))
        (inv_nonneg.mpr (le_max_of_le_left (by norm_num)))) (sq_nonneg _)
    have h₁ : Summable (fun n => squareMass n*logWeight 1 n) := hs.of_norm_bounded_eventually_nat
      (hm.mono fun n hn => by rwa [Real.norm_of_nonneg (mul_nonneg (squareMass_nonneg n) (logWeight_nonneg 1 n))])
    exact (lt_irrefl (1:ℝ)) ((logWeight_summable_iff zero_le_one).mp
      ((summable_squareMass_iff _ (logWeight_nonneg 1) (logWeight_antitone zero_le_one)).mp h₁))


end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
