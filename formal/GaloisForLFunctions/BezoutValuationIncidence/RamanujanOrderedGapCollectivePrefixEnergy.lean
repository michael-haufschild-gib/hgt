import GaloisForLFunctions.BezoutValuationIncidence.OrderedPronicGapCellsAndCollectivePrefixEnergy
import GaloisForLFunctions.BezoutValuationIncidence.RamanujanDilationProfileResidueGapBudget

/-!
# Collective prefix bounds on the Ramanujan dilation carrier

The exact Möbius residue expansion transfers the ordered-gap estimate to the
original scaled primitives `X_p(n) = p * Re(A_(r+2)(n/p))`. For a chain of
base `P`, total gap length `H`, and `K` pre-overlap quotient levels, its signed
packet has prefix energy at most

`ramanujanDilationResidueBudget (r+2) * (8 * harmonic K + 2 * H/P) * sum a_i^2*h_i`.

Cofactor dilation enlarges the available prefix; every cofactor estimate is
restricted back to the same physical horizon `(K+1)*P`. The signed gap sum
is retained before taking energy. Cauchy is used only across the finite base
cofactors and to polarize the resulting estimate into a bilinear bound.

The existing floor-dilation mean identity shows the packet has exactly zero
global pronic mean. All public statements have data parameters only. These
bounds concern the stated prefix; the later signed tail is still unresolved.
-/

open Finset RHTower ArithmeticFunction
open scoped BigOperators
namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

private theorem gap_chain_pos (K m offset : ℕ) (h : ℕ → ℕ) (i : ℕ) :
    0 < pronicGapChainLower K m offset h i := by
  unfold pronicGapChainLower
  positivity

private theorem gap_chain_scaled (K m offset : ℕ) (h : ℕ → ℕ) (d : ℕ+) (i : ℕ) :
    pronicGapChainLower K m ((d : ℕ) * offset + ((d : ℕ) - 1))
      (fun j => (d : ℕ) * h j) i = (d : ℕ) * pronicGapChainLower K m offset h i := by
  unfold pronicGapChainLower
  simp only [← Finset.mul_sum]
  have hd : (d : ℕ) - 1 + 1 = (d : ℕ) := Nat.sub_add_cancel d.pos
  calc
    _ = (d : ℕ) * (K * (∑ j ∈ range m, h j) + offset + ∑ j ∈ range i, h j) +
        ((d : ℕ) - 1 + 1) := by ring
    _ = _ := by rw [hd]; ring

private theorem gap_chain_prefix_simple (K : ℕ+) (m offset : ℕ)
    (h : ℕ → ℕ) (a : ℕ → ℝ) :
    let P := pronicGapChainLower K m offset h 0
    (∑ n ∈ range (((K : ℕ) + 1) * P),
      (∑ i ∈ range m, a i *
        (((n % pronicGapChainLower K m offset h i : ℕ) : ℝ) -
          ((n % (pronicGapChainLower K m offset h i + h i) : ℕ) : ℝ))) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1))) ≤
      (8 * (harmonic (K : ℕ) : ℝ) + 2 * ((∑ i ∈ range m, h i : ℕ) : ℝ) / P) *
        ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
  have hb := pronicResidueGapChain_prefix_energy_le K m offset h a
  dsimp only at hb ⊢
  have hd : (∑ i ∈ range m, (a i) ^ 2 *
      ((h i : ℝ) * (harmonic (K : ℕ) : ℝ) -
        (K : ℝ) * (h i : ℝ) ^ 2 / pronicGapChainLower K m offset h i)) ≤
      (harmonic (K : ℕ) : ℝ) * ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    have hz : 0 ≤ (K : ℝ) * (h i : ℝ) ^ 2 / pronicGapChainLower K m offset h i := by
      positivity
    nlinarith [mul_nonneg (sq_nonneg (a i)) hz]
  simp only [mul_div_assoc] at hb hd ⊢
  nlinarith

/-- Positive cofactor dilation preserves the collective gap bound on the original prefix. -/
theorem pronicResidueGapChain_scaled_prefix_energy_le (K d : ℕ+) (m offset : ℕ)
    (h : ℕ → ℕ) (a : ℕ → ℝ) :
    let P := pronicGapChainLower K m offset h 0
    (∑ n ∈ range (((K : ℕ) + 1) * P),
      (∑ i ∈ range m, a i *
        (((n % ((d : ℕ) * pronicGapChainLower K m offset h i) : ℕ) : ℝ) -
          ((n % ((d : ℕ) * (pronicGapChainLower K m offset h i + h i)) : ℕ) : ℝ))) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1))) ≤
      (d : ℝ) *
        (8 * (harmonic (K : ℕ) : ℝ) + 2 * ((∑ i ∈ range m, h i : ℕ) : ℝ) / P) *
          ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
  let p (i : ℕ) := pronicGapChainLower K m offset h i
  let P := p 0
  let T := ((K : ℕ) + 1) * P
  let h' (i : ℕ) := (d : ℕ) * h i
  let offset' := (d : ℕ) * offset + ((d : ℕ) - 1)
  let p' (i : ℕ) := pronicGapChainLower K m offset' h' i
  let F (n : ℕ) := ∑ i ∈ range m, a i *
    (((n % ((d : ℕ) * p i) : ℕ) : ℝ) -
      ((n % ((d : ℕ) * (p i + h i)) : ℕ) : ℝ))
  have hp' (i : ℕ) : p' i = (d : ℕ) * p i := gap_chain_scaled K m offset h d i
  have hH : ((∑ i ∈ range m, h' i : ℕ) : ℝ) =
      (d : ℝ) * ((∑ i ∈ range m, h i : ℕ) : ℝ) := by
    simp only [h', ← Finset.mul_sum, Nat.cast_mul]
  have hA : (∑ i ∈ range m, (a i) ^ 2 * (h' i : ℝ)) =
      (d : ℝ) * ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    simp only [h', Nat.cast_mul]
    ring
  have hP' : (p' 0 : ℝ) = (d : ℝ) * P := by exact_mod_cast hp' 0
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hP0 : (P : ℝ) ≠ 0 := by
    have := gap_chain_pos K m offset h 0
    positivity
  have hb := gap_chain_prefix_simple K m offset' h' a
  change (∑ n ∈ range (((K : ℕ) + 1) * p' 0),
    (∑ i ∈ range m, a i * (((n % p' i : ℕ) : ℝ) -
      ((n % (p' i + h' i) : ℕ) : ℝ))) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ _ at hb
  have hF (n : ℕ) : (∑ i ∈ range m, a i * (((n % p' i : ℕ) : ℝ) -
      ((n % (p' i + h' i) : ℕ) : ℝ))) = F n := by
    simp only [hp', h', ← Nat.mul_add, F]
  simp_rw [hF] at hb
  rw [hH, hA, hP'] at hb
  have hbudget :
      (8 * (harmonic (K : ℕ) : ℝ) +
        2 * ((d : ℝ) * ((∑ i ∈ range m, h i : ℕ) : ℝ)) / ((d : ℝ) * P)) *
          ((d : ℝ) * ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ)) =
      (d : ℝ) * (8 * (harmonic (K : ℕ) : ℝ) +
        2 * ((∑ i ∈ range m, h i : ℕ) : ℝ) / P) *
          ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
    field_simp
  rw [hbudget] at hb
  have hT : T ≤ ((K : ℕ) + 1) * p' 0 := by
    calc
      T ≤ (d : ℕ) * T := by nlinarith [d.pos]
      _ = _ := by rw [hp']; dsimp only [T, P]; ring
  change (∑ n ∈ range T, (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ _
  calc
    _ ≤ ∑ n ∈ range (((K : ℕ) + 1) * p' 0),
        (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono hT)
      intro n _ _
      positivity
    _ ≤ _ := hb

/-- A signed chain of differences of the original scaled Ramanujan primitives. -/
def ramanujanGapChainPacket (r K m offset : ℕ) (h : ℕ → ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range m, a i *
    ((pronicGapChainLower K m offset h i : ℝ) *
      (pmRamanujanPrimitive (r + 2) (n / pronicGapChainLower K m offset h i)).re -
      ((pronicGapChainLower K m offset h i + h i : ℕ) : ℝ) *
        (pmRamanujanPrimitive (r + 2) (n / (pronicGapChainLower K m offset h i + h i))).re)

private theorem hasSum_scaled_primitive_mean (r p : ℕ) (hp : 0 < p) :
    HasSum (fun n : ℕ => (p : ℝ) * (pmRamanujanPrimitive (r + 2) (n / p)).re /
      ((n : ℝ) * ((n : ℝ) + 1))) (-vonMangoldt (r + 2)) := by
  let f (n : ℕ) := (pmRamanujanPrimitive (r + 2) n).re
  have hb (n : ℕ) : |f n| ≤ pmRamanujanPrimitiveBound (r + 2) :=
    (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le (by omega) _)
  have hf : f 0 = 0 := by simp [f, pmRamanujanPrimitive]
  have hfloor := pm_tsum_floor_dilation f
    (fun n => by simpa only [Real.norm_eq_abs] using hb n) hf hp
  have hsum : Summable (fun n : ℕ => f (n / p) / ((n : ℝ) * ((n : ℝ) + 1))) := by
    simpa only [cast_pronicSeq_eq] using summable_div_pronicSeq_of_bounded (fun n => hb (n / p))
  have hs := hsum.hasSum.mul_left (p : ℝ)
  have he : (p : ℝ) * (∑' n : ℕ, f (n / p) / ((n : ℝ) * ((n : ℝ) + 1))) =
      -vonMangoldt (r + 2) := by
    rw [hfloor, (hasSum_pmRamanujanPrimitive_reciprocal (by omega : 1 < r + 2)).tsum_eq]
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    field_simp
  rw [he] at hs
  exact hs.congr_fun (fun n => by dsimp only [f]; ring)

/-- The original signed dilation packet has exactly zero global pronic mean. -/
theorem hasSum_ramanujanGapChainPacket_zero (r K m offset : ℕ)
    (h : ℕ → ℕ) (a : ℕ → ℝ) :
    HasSum (fun n : ℕ => ramanujanGapChainPacket r K m offset h a n /
      ((n : ℝ) * ((n : ℝ) + 1))) 0 := by
  let p (i : ℕ) := pronicGapChainLower K m offset h i
  have hs : HasSum (fun n : ℕ => ∑ i ∈ range m, a i *
      ((p i : ℝ) * (pmRamanujanPrimitive (r + 2) (n / p i)).re -
        ((p i + h i : ℕ) : ℝ) *
          (pmRamanujanPrimitive (r + 2) (n / (p i + h i))).re) /
        ((n : ℝ) * ((n : ℝ) + 1))) (∑ i ∈ range m, (0 : ℝ)) := by
    apply hasSum_sum
    intro i _
    have hp : 0 < p i := gap_chain_pos K m offset h i
    have hq : 0 < p i + h i := by omega
    have ht := ((hasSum_scaled_primitive_mean r (p i) hp).sub
      (hasSum_scaled_primitive_mean r (p i + h i) hq)).mul_left (a i)
    simpa only [sub_self, mul_zero, sub_div, mul_sub, mul_div_assoc] using ht
  simpa only [sum_const_zero, ramanujanGapChainPacket, sum_div, p] using hs

private theorem gap_packet_residues (r K m offset : ℕ) (h : ℕ → ℕ)
    (a : ℕ → ℝ) (n : ℕ) :
    ramanujanGapChainPacket r K m offset h a n =
      -∑ x ∈ (r + 2).divisorsAntidiagonal, (moebius x.2 : ℝ) *
        ∑ i ∈ range m, a i *
          (((n % (x.1 * pronicGapChainLower K m offset h i) : ℕ) : ℝ) -
            ((n % (x.1 * (pronicGapChainLower K m offset h i + h i)) : ℕ) : ℝ)) := by
  let p (i : ℕ) := pronicGapChainLower K m offset h i
  have hd (i : ℕ) :
      (p i : ℝ) * (pmRamanujanPrimitive (r + 2) (n / p i)).re -
        ((p i + h i : ℕ) : ℝ) * (pmRamanujanPrimitive (r + 2) (n / (p i + h i))).re =
      -∑ x ∈ (r + 2).divisorsAntidiagonal, (moebius x.2 : ℝ) *
        (((n % (p i * x.1) : ℕ) : ℝ) - ((n % ((p i + h i) * x.1) : ℕ) : ℝ)) := by
    rw [scaled_pmRamanujanPrimitive_eq_residues, scaled_pmRamanujanPrimitive_eq_residues]
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
    ring
  change (∑ i ∈ range m, a i *
    ((p i : ℝ) * (pmRamanujanPrimitive (r + 2) (n / p i)).re -
      ((p i + h i : ℕ) : ℝ) * (pmRamanujanPrimitive (r + 2) (n / (p i + h i))).re)) = _
  simp_rw [hd, mul_neg, mul_sum]
  rw [sum_neg_distrib, sum_comm]
  congr 1
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro i _
  rw [Nat.mul_comm (p i) x.1, Nat.mul_comm (p i + h i) x.1]
  dsimp only [p]
  ring

/-- A collective bound on the actual Ramanujan dilation packet, with the physical prefix fixed. -/
theorem ramanujanGapChainPacket_prefix_energy_le (r : ℕ) (K : ℕ+) (m offset : ℕ)
    (h : ℕ → ℕ) (a : ℕ → ℝ) :
    let P := pronicGapChainLower K m offset h 0
    (∑ n ∈ range (((K : ℕ) + 1) * P), (ramanujanGapChainPacket r K m offset h a n) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))) ≤
      ramanujanDilationResidueBudget (r + 2) *
        (8 * (harmonic (K : ℕ) : ℝ) + 2 * ((∑ i ∈ range m, h i : ℕ) : ℝ) / P) *
          ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ) := by
  let P := pronicGapChainLower K m offset h 0
  let T := ((K : ℕ) + 1) * P
  let S := (r + 2).divisorsAntidiagonal
  let C := 8 * (harmonic (K : ℕ) : ℝ) + 2 * ((∑ i ∈ range m, h i : ℕ) : ℝ) / P
  let A := ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ)
  let R (d n : ℕ) := ∑ i ∈ range m, a i *
    (((n % (d * pronicGapChainLower K m offset h i) : ℕ) : ℝ) -
      ((n % (d * (pronicGapChainLower K m offset h i + h i)) : ℕ) : ℝ))
  have hpoint (n : ℕ) : (ramanujanGapChainPacket r K m offset h a n) ^ 2 ≤
      (S.card : ℝ) * ∑ x ∈ S, (moebius x.2 : ℝ) ^ 2 * (R x.1 n) ^ 2 := by
    rw [gap_packet_residues, neg_sq]
    have ht := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
      (fun x => (moebius x.2 : ℝ) * R x.1 n)
    simpa only [S, R, one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, mul_pow] using ht
  have hcofactor (x : ℕ × ℕ) (hx : x ∈ S) :
      (∑ n ∈ range T, (R x.1 n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ (x.1 : ℝ) * C * A := by
    have hx0 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
    exact pronicResidueGapChain_scaled_prefix_energy_le K ⟨x.1, hx0⟩ m offset h a
  change (∑ n ∈ range T, (ramanujanGapChainPacket r K m offset h a n) ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1))) ≤ ramanujanDilationResidueBudget (r + 2) * C * A
  calc
    _ ≤ ∑ n ∈ range T, ((S.card : ℝ) * ∑ x ∈ S,
        (moebius x.2 : ℝ) ^ 2 * (R x.1 n) ^ 2) / ((n : ℝ) * ((n : ℝ) + 1)) := by
      apply sum_le_sum
      intro n _
      exact div_le_div_of_nonneg_right (hpoint n) (by positivity)
    _ = (S.card : ℝ) * ∑ x ∈ S, (moebius x.2 : ℝ) ^ 2 *
        (∑ n ∈ range T, (R x.1 n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
      simp_rw [mul_div_assoc, sum_div]
      rw [← mul_sum, sum_comm]
      congr 1
      apply sum_congr rfl
      intro x _
      rw [mul_sum]
      simp only [mul_div_assoc]
    _ ≤ (S.card : ℝ) * ∑ x ∈ S, (moebius x.2 : ℝ) ^ 2 * ((x.1 : ℝ) * C * A) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hcofactor x hx) (sq_nonneg _)
    _ = _ := by
      unfold ramanujanDilationResidueBudget
      simp_rw [← mul_assoc]
      rw [← sum_mul, ← sum_mul]
      dsimp only [S]
      ring


private theorem pronic_bilinear_sq_le (T : ℕ) (f g : ℕ → ℝ) :
    (∑ n ∈ range T, f n * g n / ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 ≤
      (∑ n ∈ range T, (f n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) *
        ∑ n ∈ range T, (g n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  let w (n : ℕ) := (n : ℝ) * ((n : ℝ) + 1)
  have hw (n : ℕ) : 0 ≤ w n := by dsimp only [w]; positivity
  have hm (n : ℕ) : (f n / Real.sqrt (w n)) * (g n / Real.sqrt (w n)) =
      f n * g n / w n := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (hw n)]
  have hs (u : ℕ → ℝ) (n : ℕ) : (u n / Real.sqrt (w n)) ^ 2 = (u n) ^ 2 / w n := by
    rw [div_pow, Real.sq_sqrt (hw n)]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (range T)
    (fun n => f n / Real.sqrt (w n)) (fun n => g n / Real.sqrt (w n))
  simpa only [hm, hs, w] using hc

/-- Two independently signed dilation packets satisfy the corresponding bilinear prefix estimate. -/
theorem ramanujanGapChainPacket_bilinear_prefix_sq_le (r : ℕ) (K : ℕ+) (m offset : ℕ)
    (h : ℕ → ℕ) (a b : ℕ → ℝ) :
    let P := pronicGapChainLower K m offset h 0
    (∑ n ∈ range (((K : ℕ) + 1) * P),
      ramanujanGapChainPacket r K m offset h a n * ramanujanGapChainPacket r K m offset h b n /
        ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 ≤
      (ramanujanDilationResidueBudget (r + 2) *
        (8 * (harmonic (K : ℕ) : ℝ) + 2 * ((∑ i ∈ range m, h i : ℕ) : ℝ) / P)) ^ 2 *
          (∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ)) *
            ∑ i ∈ range m, (b i) ^ 2 * (h i : ℝ) := by
  let P := pronicGapChainLower K m offset h 0
  let T := ((K : ℕ) + 1) * P
  let C := ramanujanDilationResidueBudget (r + 2) *
    (8 * (harmonic (K : ℕ) : ℝ) + 2 * ((∑ i ∈ range m, h i : ℕ) : ℝ) / P)
  let A (c : ℕ → ℝ) := ∑ i ∈ range m, (c i) ^ 2 * (h i : ℝ)
  let E (c : ℕ → ℝ) := ∑ n ∈ range T, (ramanujanGapChainPacket r K m offset h c n) ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1))
  have he (c : ℕ → ℝ) : 0 ≤ E c := sum_nonneg fun n _ => by positivity
  have ha : E a ≤ C * A a := ramanujanGapChainPacket_prefix_energy_le r K m offset h a
  have hb : E b ≤ C * A b := ramanujanGapChainPacket_prefix_energy_le r K m offset h b
  have hc := pronic_bilinear_sq_le T (ramanujanGapChainPacket r K m offset h a)
    (ramanujanGapChainPacket r K m offset h b)
  change (∑ n ∈ range T,
    ramanujanGapChainPacket r K m offset h a n * ramanujanGapChainPacket r K m offset h b n /
      ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 ≤ C ^ 2 * A a * A b
  calc
    _ ≤ E a * E b := hc
    _ ≤ (C * A a) * (C * A b) := mul_le_mul ha hb (he b) ((he a).trans ha)
    _ = _ := by ring

end
end GaloisForLFunctions.BezoutValuationIncidence
