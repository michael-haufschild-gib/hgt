import GaloisForLFunctions.HTGeometry.ChronologicalTensor.SixPoint
import Mathlib.Analysis.MeanInequalities

/-!
# Exact capacity under independent repeated fusion

For `n` copies of the six-endpoint response and one shared variation budget,
multiplication by `n^(3*n)` gives capacity exactly `sixCapacity^n`.
The global bound follows from finite AM-GM; repeated scaled optimal probes attain
it. Repeated rational probes already attain `(10/9)^n`. The empty product is
included in the universal bound, and all nonempty products have explicit witnesses.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Finset

theorem mass_product_bound (n : ℕ) (x : Fin n → ℝ) :
    (n : ℝ)^n * (∏ i, |x i|) ≤ (∑ i, |x i|)^n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsum : (∑ _i : Fin n, (1 : ℝ)) = n := by simp
  have h := Real.geom_mean_le_arith_mean univ (fun _i : Fin n => (1 : ℝ))
    (fun i => |x i|) (by intros; positivity) (by rw [hsum]; exact hn0)
    (by intros; positivity)
  simp only [Real.rpow_one, one_mul, hsum] at h
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg
    (prod_nonneg (fun i _ => abs_nonneg (x i))) _) h n
  rw [Real.rpow_inv_natCast_pow (prod_nonneg (fun i _ => abs_nonneg (x i))) hn] at hp
  have hm := mul_le_mul_of_nonneg_left hp (le_of_lt (pow_pos hn0 n))
  have he : (n : ℝ)^n * ((∑ i, |x i|)/(n : ℝ))^n = (∑ i, |x i|)^n := by
    rw [← mul_pow]
    congr 1
    field_simp
  exact hm.trans_eq he

def blockCost (n : ℕ) (a b c d e : Fin n → ℝ) : ℝ :=
  ∑ i, sixCost (a i) (b i) (c i) (d i) (e i)

def fusedResponse (n : ℕ) (a b c d e : Fin n → ℝ) : ℝ :=
  (n : ℝ)^(3*n) * ∏ i, sixResponse (a i) (b i) (c i) (d i) (e i)

theorem fused_sharp_bound (n : ℕ) (a b c d e : Fin n → ℝ) :
    |fusedResponse n a b c d e| ≤ sixCapacity^n * blockCost n a b c d e ^ (3*n) := by
  have hc : ∀ i, 0 ≤ sixCost (a i) (b i) (c i) (d i) (e i) := by
    intro i; unfold sixCost; positivity
  have hp := prod_le_prod (fun i (_ : i ∈ (univ : Finset (Fin n))) =>
      abs_nonneg (sixResponse (a i) (b i) (c i) (d i) (e i)))
    (fun i _ => six_sharp_bound (a i) (b i) (c i) (d i) (e i))
  have hm := mass_product_bound n (fun i => sixCost (a i) (b i) (c i) (d i) (e i))
  simp only [abs_of_nonneg (hc _)] at hm
  have hm3 := pow_le_pow_left₀ (show 0 ≤ (n : ℝ)^n *
    ∏ i, sixCost (a i) (b i) (c i) (d i) (e i) by exact mul_nonneg (by positivity) (prod_nonneg (fun i _ => hc i))) hm 3
  calc
    _ = (n : ℝ)^(3*n) * ∏ i, |sixResponse (a i) (b i) (c i) (d i) (e i)| := by
      rw [fusedResponse, abs_mul, abs_of_nonneg (by positivity), Finset.abs_prod]
    _ ≤ (n : ℝ)^(3*n) * ∏ i, (sixCapacity * sixCost (a i) (b i) (c i) (d i) (e i)^3) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = sixCapacity^n * ((n : ℝ)^n * ∏ i, sixCost (a i) (b i) (c i) (d i) (e i))^3 := by
      rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow, mul_pow]
      simp only [← pow_mul]
      rw [Nat.mul_comm n 3]
      ring
    _ ≤ sixCapacity^n * ((∑ i, sixCost (a i) (b i) (c i) (d i) (e i))^n)^3 :=
      mul_le_mul_of_nonneg_left hm3 (pow_nonneg sixCapacity_nonneg _)
    _ = _ := by rw [← pow_mul, Nat.mul_comm n 3]; rfl

theorem six_scale (t a b c d e : ℝ) :
    sixResponse (t*a) (t*b) (t*c) (t*d) (t*e) = t^3 * sixResponse a b c d e := by
  unfold sixResponse separatedThree rainbowThree
  ring

theorem sixCost_scale (t a b c d e : ℝ) :
    sixCost (t*a) (t*b) (t*c) (t*d) (t*e) = |t| * sixCost a b c d e := by
  simp only [sixCost, abs_mul]
  ring

theorem fused_repeated_probe (n : ℕ) (a b c d e : ℝ) :
    blockCost (n+1) (fun _ => a/(n+1)) (fun _ => b/(n+1)) (fun _ => c/(n+1))
      (fun _ => d/(n+1)) (fun _ => e/(n+1)) = sixCost a b c d e ∧
    fusedResponse (n+1) (fun _ => a/(n+1)) (fun _ => b/(n+1)) (fun _ => c/(n+1))
      (fun _ => d/(n+1)) (fun _ => e/(n+1)) = (sixResponse a b c d e)^(n+1) := by
  have hn : (0 : ℝ) < n+1 := by positivity
  have hne : (n : ℝ)+1 ≠ 0 := ne_of_gt hn
  have hcost : sixCost (a/(n+1)) (b/(n+1)) (c/(n+1)) (d/(n+1)) (e/(n+1)) =
      sixCost a b c d e / (n+1) := by
    simp only [sixCost, abs_div, abs_of_pos hn]
    ring
  have hr : sixResponse (a/(n+1)) (b/(n+1)) (c/(n+1)) (d/(n+1)) (e/(n+1)) =
      sixResponse a b c d e / (n+1)^3 := by
    unfold sixResponse separatedThree rainbowThree
    field_simp
  constructor
  · simp only [blockCost, hcost, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    field_simp
  · simp only [fusedResponse, hr, prod_const, card_univ, Fintype.card_fin,
      Nat.cast_add, Nat.cast_one, div_pow, ← pow_mul]
    field_simp

theorem fused_attained (n : ℕ) :
    blockCost (n+1) (fun _ => ((1-peakPosition)/2)/(n+1)) (fun _ => 0)
      (fun _ => peakPosition/(n+1)) (fun _ => 0) (fun _ => ((1-peakPosition)/2)/(n+1)) = 1 ∧
    |fusedResponse (n+1) (fun _ => ((1-peakPosition)/2)/(n+1)) (fun _ => 0)
      (fun _ => peakPosition/(n+1)) (fun _ => 0) (fun _ => ((1-peakPosition)/2)/(n+1))| =
      sixCapacity^(n+1) := by
  have h := fused_repeated_probe n ((1-peakPosition)/2) 0 peakPosition 0 ((1-peakPosition)/2)
  simp only [zero_div] at h
  rw [h.1, h.2, abs_pow, six_attained.1, six_attained.2]
  exact ⟨rfl, rfl⟩

theorem fused_rational_amplification (n : ℕ) :
    blockCost (n+1) (fun _ => (1/3)/(n+1)) (fun _ => 0)
      (fun _ => (1/3)/(n+1)) (fun _ => 0) (fun _ => (1/3)/(n+1)) = 1 ∧
    fusedResponse (n+1) (fun _ => (1/3)/(n+1)) (fun _ => 0)
      (fun _ => (1/3)/(n+1)) (fun _ => 0) (fun _ => (1/3)/(n+1)) = (10/9 : ℝ)^(n+1) := by
  have h := fused_repeated_probe n (1/3) 0 (1/3) 0 (1/3)
  simp only [zero_div] at h
  rw [h.1, h.2, six_rational_witness.1, six_rational_witness.2]
  exact ⟨rfl, rfl⟩

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
