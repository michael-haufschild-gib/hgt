import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Amplification

/-!
# Reversal sensitivity surviving every finite enclosure depth

Enclosing a history adds a factor of its total signed displacement. For `n`
independent normalized reversal blocks and `k` enclosures, the monotone capacity
is exactly one. Repeated reversed probes have response magnitude
`(28/27)^n * (1/3)^k`. Bernoulli's inequality shows that `54*(k+1)` blocks retain
response at least three at every enclosure depth. The proof gives the exact
compositional law as well as the nonuniformity statement; no numerical power is
evaluated as an optimality certificate.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Finset

def totalDisplacement (n : ℕ) (a b c d e : Fin n → ℝ) : ℝ :=
  ∑ i, (a i + b i + c i + d i + e i)

def reversalProduct (n : ℕ) (a b c d e : Fin n → ℝ) : ℝ :=
  (n : ℝ)^(3*n) * ∏ i, reversalResponse (a i) (b i) (c i) (d i) (e i)

def enclosedReversal (n k : ℕ) (a b c d e : Fin n → ℝ) : ℝ :=
  totalDisplacement n a b c d e ^ k * reversalProduct n a b c d e

theorem reversalProduct_monotone_bound (n : ℕ) (a b c d e : Fin n → ℝ) :
    |reversalProduct n (fun i => |a i|) (fun i => |b i|) (fun i => |c i|)
      (fun i => |d i|) (fun i => |e i|)| ≤ blockCost n a b c d e ^ (3*n) := by
  have hc : ∀ i, 0 ≤ sixCost (a i) (b i) (c i) (d i) (e i) := by
    intro i; unfold sixCost; positivity
  have hp := prod_le_prod (fun i (_ : i ∈ (univ : Finset (Fin n))) =>
      abs_nonneg (reversalResponse |a i| |b i| |c i| |d i| |e i|))
    (fun i _ => monotone_reversal_bound (a i) (b i) (c i) (d i) (e i))
  have hm := mass_product_bound n (fun i => sixCost (a i) (b i) (c i) (d i) (e i))
  simp only [abs_of_nonneg (hc _)] at hm
  have hm3 := pow_le_pow_left₀ (show 0 ≤ (n : ℝ)^n *
    ∏ i, sixCost (a i) (b i) (c i) (d i) (e i) by
      exact mul_nonneg (by positivity) (prod_nonneg (fun i _ => hc i))) hm 3
  calc
    _ = (n : ℝ)^(3*n) * ∏ i, |reversalResponse |a i| |b i| |c i| |d i| (|e i|)| := by
      rw [reversalProduct, abs_mul, abs_of_nonneg (by positivity), Finset.abs_prod]
    _ ≤ (n : ℝ)^(3*n) * ∏ i, sixCost (a i) (b i) (c i) (d i) (e i)^(3 : ℕ) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((n : ℝ)^n * ∏ i, sixCost (a i) (b i) (c i) (d i) (e i))^(3 : ℕ) := by
      rw [prod_pow, mul_pow, ← pow_mul, Nat.mul_comm n 3]
    _ ≤ ((∑ i, sixCost (a i) (b i) (c i) (d i) (e i))^n)^(3 : ℕ) := hm3
    _ = _ := by rw [← pow_mul, Nat.mul_comm n 3]; rfl

theorem enclosed_monotone_bound (n k : ℕ) (a b c d e : Fin n → ℝ) :
    |enclosedReversal n k (fun i => |a i|) (fun i => |b i|) (fun i => |c i|)
      (fun i => |d i|) (fun i => |e i|)| ≤ blockCost n a b c d e ^ (k+3*n) := by
  have ht : 0 ≤ blockCost n a b c d e := by
    unfold blockCost sixCost
    positivity
  have hs : totalDisplacement n (fun i => |a i|) (fun i => |b i|) (fun i => |c i|)
      (fun i => |d i|) (fun i => |e i|) = blockCost n a b c d e := rfl
  rw [enclosedReversal, abs_mul, hs, abs_pow, abs_of_nonneg ht, pow_add]
  exact mul_le_mul_of_nonneg_left (reversalProduct_monotone_bound n a b c d e) (pow_nonneg ht _)

theorem reversalProduct_repeated (n : ℕ) (a b c d e : ℝ) :
    reversalProduct (n+1) (fun _ => a/(n+1)) (fun _ => b/(n+1)) (fun _ => c/(n+1))
      (fun _ => d/(n+1)) (fun _ => e/(n+1)) = (reversalResponse a b c d e)^(n+1) := by
  have hr : reversalResponse (a/(n+1)) (b/(n+1)) (c/(n+1)) (d/(n+1)) (e/(n+1)) =
      reversalResponse a b c d e / (n+1)^(3 : ℕ) := by
    unfold reversalResponse separatedThree rainbowThree
    field_simp
  simp only [reversalProduct, hr, prod_const, card_univ, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one, div_pow, ← pow_mul]
  field_simp

theorem totalDisplacement_repeated (n : ℕ) (a b c d e : ℝ) :
    totalDisplacement (n+1) (fun _ => a/(n+1)) (fun _ => b/(n+1)) (fun _ => c/(n+1))
      (fun _ => d/(n+1)) (fun _ => e/(n+1)) = a+b+c+d+e := by
  have hs : a/(n+1)+b/(n+1)+c/(n+1)+d/(n+1)+e/(n+1) = (a+b+c+d+e)/(n+1) := by ring
  simp only [totalDisplacement, hs, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem enclosed_monotone_attained (n k : ℕ) :
    blockCost (n+1) (fun _ => 0) (fun _ => 0) (fun _ => 1/(n+1)) (fun _ => 0) (fun _ => 0) = 1 ∧
    |enclosedReversal (n+1) k (fun _ => 0) (fun _ => 0) (fun _ => 1/(n+1))
      (fun _ => 0) (fun _ => 0)| = 1 := by
  have hc := (fused_repeated_probe n 0 0 1 0 0).1
  have hp := reversalProduct_repeated n 0 0 1 0 0
  have hs := totalDisplacement_repeated n 0 0 1 0 0
  simp only [zero_div] at hc hp hs
  constructor
  · simpa [sixCost] using hc
  · rw [enclosedReversal, hs, hp]
    simp [reversalResponse, separatedThree, rainbowThree, abs_pow]

theorem enclosed_reversed_witness (n k : ℕ) :
    blockCost (n+1) (fun _ => (1/3)/(n+1)) (fun _ => 0) (fun _ => (-1/3)/(n+1))
      (fun _ => 0) (fun _ => (1/3)/(n+1)) = 1 ∧
    |enclosedReversal (n+1) k (fun _ => (1/3)/(n+1)) (fun _ => 0) (fun _ => (-1/3)/(n+1))
      (fun _ => 0) (fun _ => (1/3)/(n+1))| = (28/27 : ℝ)^(n+1) * (1/3 : ℝ)^k := by
  have hc := (fused_repeated_probe n (1/3) 0 (-1/3) 0 (1/3)).1
  have hp := reversalProduct_repeated n (1/3) 0 (-1/3) 0 (1/3)
  have hs := totalDisplacement_repeated n (1/3) 0 (-1/3) 0 (1/3)
  simp only [zero_div] at hc hp hs
  constructor
  · rw [hc, reversal_advantage_witness.1]
  · rw [enclosedReversal, hs, hp, reversal_advantage_witness.2.1, abs_mul, abs_pow, abs_pow]
    have hsum : (1/3 : ℝ)+0+(-1/3)+0+1/3 = 1/3 := by ring
    rw [hsum, abs_of_nonneg (show (0 : ℝ) ≤ 1/3 by positivity),
      abs_of_nonpos (show (-28/27 : ℝ) ≤ 0 by linarith)]
    have hn : -(-28/27 : ℝ) = 28/27 := by ring
    rw [hn, mul_comm]

theorem enclosure_growth (k : ℕ) :
    (3 : ℝ) ≤ (28/27 : ℝ)^(54*(k+1)) * (1/3 : ℝ)^k := by
  have hb := one_add_mul_le_pow (a := (1/27 : ℝ)) (by linarith) 54
  have hb' : (3 : ℝ) ≤ (28/27 : ℝ)^(54 : ℕ) := by
    have hbase : (1 : ℝ)+1/27 = 28/27 := by ring
    have hleft : (1 : ℝ)+((54 : ℕ) : ℝ)*(1/27) = 3 := by ring
    rw [hbase, hleft] at hb
    exact hb
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ 3 by positivity) hb' (k+1)
  rw [← pow_mul] at hp
  have he : (3 : ℝ)^(k+1) * (1/3 : ℝ)^k = 3 := by
    rw [pow_succ]
    calc
      _ = 3 * ((3 : ℝ)*(1/3))^k := by rw [mul_pow]; ring
      _ = 3 := by rw [show (3 : ℝ)*(1/3)=1 by ring, one_pow, mul_one]
  calc
    (3 : ℝ) = (3 : ℝ)^(k+1) * (1/3 : ℝ)^k := he.symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)

theorem every_enclosure_depth_has_reversal_survivor (k : ℕ) :
    ∃ a b c d e : Fin (54*(k+1)) → ℝ,
      blockCost (54*(k+1)) a b c d e = 1 ∧
      3 ≤ |enclosedReversal (54*(k+1)) k a b c d e| := by
  have hn : 54*k+53+1 = 54*(k+1) := by ring
  have hw := enclosed_reversed_witness (54*k+53) k
  rw [hn] at hw
  refine ⟨_, _, _, _, _, hw.1, ?_⟩
  rw [hw.2]
  exact enclosure_growth k

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
