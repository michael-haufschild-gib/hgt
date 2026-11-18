import GaloisForLFunctions.ExceptionalLayerTheory.EveryFiniteCofactorSeesTheOrdinaryPrimeCount
import GaloisForLFunctions.RHTower.MobiusDiscretePacketEdgeEstimates

/-!
# One-sided oscillation of prime-count increments

For an increasing nonnegative weight, Abel summation is a positive combination
of suffix sums. A decreasing weight gives prefix sums. Thus the largest
one-sided increase is multiplied by at most the largest weight. Applying the
two statements to the prime logarithm and its reciprocal gives sharp local
comparisons for both signs of the centered ordinary count.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ExceptionalLayerTheory

private def intervalPrefix (a : ℕ → ℝ) (n : ℕ) := ∑ i ∈ range (n+1), a i

private theorem sum_Ioc_prefix_diff (a : ℕ → ℝ) {l u : ℕ} (hl : l≤u) :
    ∑ i ∈ Ioc l u, a i=intervalPrefix a u-intervalPrefix a l := by
  induction u, hl using Nat.le_induction with
  | base => simp
  | succ u hu ih =>
    rw [sum_Ioc_succ_top hu,ih]
    simp only [intervalPrefix,Finset.sum_range_succ _ (u+1)]
    ring

private theorem centered_parts (a w : ℕ → ℝ) {l u : ℕ} (hl : l<u) (c : ℝ) :
    ∑ i ∈ Ioc l u, w i*a i =
      w u*(intervalPrefix a u-c)-w (l+1)*(intervalPrefix a l-c)-
      ∑ i ∈ Ioc l (u-1), (w (i+1)-w i)*(intervalPrefix a i-c) := by
  have he := Finset.sum_Ioc_by_parts w a hl
  simp only [smul_eq_mul,← intervalPrefix] at he
  have ht := _root_.RHTower.DiscretePacket.sum_Ioc_telescope w (show l≤u-1 by omega)
  rw [Nat.sub_add_cancel (by omega : 1≤u)] at ht
  simp only [mul_sub _ _ c,sum_sub_distrib,← sum_mul,ht]
  rw [he]
  ring

/-- A nonnegative monotone weight multiplies a one-sided suffix bound by at
most its terminal value. -/
theorem sum_weighted_le_of_suffix_bounds {l u : ℕ} (hl : l<u) (a w : ℕ → ℝ) {B : ℝ}
    (hb : ∀ j : ℕ, l≤j → j≤u → ∑ i ∈ Ioc j u, a i≤B) (hw : 0≤w (l+1))
    (hm : ∀ i ∈ Ioc l (u-1), w i≤w (i+1)) :
    ∑ i ∈ Ioc l u, w i*a i≤w u*B := by
  have h (j : ℕ) (hj : l≤j) (hju : j≤u) : intervalPrefix a u-intervalPrefix a j≤B := by
    simpa only [sum_Ioc_prefix_diff a hju] using hb j hj hju
  have hs : (∑ i ∈ Ioc l (u-1), (w (i+1)-w i)*(intervalPrefix a u-intervalPrefix a i)) ≤
      (w u-w (l+1))*B := by
    calc
      _ ≤ ∑ i ∈ Ioc l (u-1), (w (i+1)-w i)*B := by
        refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
          (h i (mem_Ioc.mp hi).1.le ((mem_Ioc.mp hi).2.trans (Nat.sub_le ..))) (sub_nonneg.mpr (hm i hi))
      _ = _ := by rw [← sum_mul,_root_.RHTower.DiscretePacket.sum_Ioc_telescope w (by omega),
                        Nat.sub_add_cancel (by omega : 1≤u)]
  rw [centered_parts a w hl (intervalPrefix a u),sub_self,mul_zero,zero_sub]
  have hneg : (∑ i ∈ Ioc l (u-1), (w (i+1)-w i)*(intervalPrefix a i-intervalPrefix a u)) =
      -(∑ i ∈ Ioc l (u-1), (w (i+1)-w i)*(intervalPrefix a u-intervalPrefix a i)) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [hneg]
  linarith only [hs,mul_le_mul_of_nonneg_left (h l le_rfl hl.le) hw]

/-- A nonnegative decreasing weight multiplies a one-sided prefix bound by
at most its initial value. -/
theorem sum_weighted_le_of_prefix_bounds {l u : ℕ} (hl : l<u) (a w : ℕ → ℝ) {B : ℝ}
    (hb : ∀ j : ℕ, l≤j → j≤u → ∑ i ∈ Ioc l j, a i≤B) (hw : 0≤w u)
    (hm : ∀ i ∈ Ioc l (u-1), w (i+1)≤w i) :
    ∑ i ∈ Ioc l u, w i*a i≤w (l+1)*B := by
  have h (j : ℕ) (hj : l≤j) (hju : j≤u) : intervalPrefix a j-intervalPrefix a l≤B := by
    simpa only [sum_Ioc_prefix_diff a hj] using hb j hj hju
  have hs : (w u-w (l+1))*B ≤
      ∑ i ∈ Ioc l (u-1), (w (i+1)-w i)*(intervalPrefix a i-intervalPrefix a l) := by
    calc
      _ = ∑ i ∈ Ioc l (u-1), (w (i+1)-w i)*B := by
        rw [← sum_mul,_root_.RHTower.DiscretePacket.sum_Ioc_telescope w (by omega),
          Nat.sub_add_cancel (by omega : 1≤u)]
      _ ≤ _ := by
        refine sum_le_sum fun i hi => mul_le_mul_of_nonpos_left
          (h i (mem_Ioc.mp hi).1.le ((mem_Ioc.mp hi).2.trans (Nat.sub_le ..))) (sub_nonpos.mpr (hm i hi))
  rw [centered_parts a w hl (intervalPrefix a l),sub_self,mul_zero,sub_zero]
  linarith only [hs,mul_le_mul_of_nonneg_left (h u hl.le le_rfl) hw]

private def windowPairs (Y : ℕ) := (Icc Y (2*Y)) ×ˢ (Icc Y (2*Y))

private theorem windowPairs_nonempty (Y : ℕ) : (windowPairs Y).Nonempty :=
  ⟨(Y,Y),mem_product.mpr ⟨mem_Icc.mpr ⟨le_rfl,by omega⟩,mem_Icc.mpr ⟨le_rfl,by omega⟩⟩⟩

/-- Largest forward interval sum in an octave. Empty intervals contribute zero. -/
def largestForwardSum (a : ℕ → ℝ) (Y : ℕ) : ℝ :=
  (windowPairs Y).sup' (windowPairs_nonempty Y) (fun z => ∑ n ∈ Ioc z.1 z.2, a n)

private theorem le_forward (a : ℕ → ℝ) {Y h k : ℕ} (hh : h∈Icc Y (2*Y)) (hk : k∈Icc Y (2*Y)) :
    (∑ i ∈ Ioc h k, a i)≤largestForwardSum a Y :=
  Finset.le_sup' (f := fun z : ℕ × ℕ => ∑ i ∈ Ioc z.1 z.2, a i) (mem_product.mpr ⟨hh,hk⟩)

private theorem forward_nonneg (a : ℕ → ℝ) (Y : ℕ) : 0≤largestForwardSum a Y := by
  have hy : Y∈Icc Y (2*Y) := mem_Icc.mpr ⟨le_rfl,by omega⟩
  simpa using le_forward a hy hy

/-- Multiplying a signed centered prime count by the prime logarithm changes
its largest forward sum by factors between the two extreme local logarithms. -/
theorem forward_prime_logarithm_bounds (Y : ℕ) (hY : 2≤Y) (sign : ℝ) :
    let b := fun n : ℕ => sign*ordinaryPrimeCountWeight n
    let a := fun n : ℕ => Real.log n*b n
    Real.log (Y+1:ℕ)*largestForwardSum b Y≤largestForwardSum a Y ∧
      largestForwardSum a Y≤Real.log (2*Y:ℕ)*largestForwardSum b Y := by
  intro b a
  have hl (n : ℕ) (hn : Y≤n) : 0<Real.log n :=
    Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hmono {i j : ℕ} (hi : Y≤i) (hij : i≤j) : Real.log i≤Real.log j :=
    Real.log_le_log (by exact_mod_cast (show 0<i by omega)) (by exact_mod_cast hij)
  have hmid {h k : ℕ} (hh : h∈Icc Y (2*Y)) (hk : k∈Icc Y (2*Y)) {j : ℕ} (hj : h≤j) (hjk : j≤k) :
      j∈Icc Y (2*Y) := mem_Icc.mpr ⟨(mem_Icc.mp hh).1.trans hj,hjk.trans (mem_Icc.mp hk).2⟩
  constructor
  · have hstart := hl (Y+1) (by omega)
    rw [mul_comm,← le_div_iff₀ hstart]
    apply Finset.sup'_le
    rintro ⟨h,k⟩ hp
    obtain ⟨hh,hk⟩ := mem_product.mp hp
    by_cases hlk : h<k
    · have hinv (n : ℕ) (hn : n∈Ioc h k) : (Real.log n)⁻¹*a n=b n :=
        inv_mul_cancel_left₀ (hl n ((mem_Icc.mp hh).1.trans (mem_Ioc.mp hn).1.le)).ne' _
      rw [← sum_congr rfl hinv]
      have hw := sum_weighted_le_of_prefix_bounds hlk a (fun n => (Real.log n)⁻¹)
        (fun j hj hju => le_forward a hh (hmid hh hk hj hju)) (inv_nonneg.mpr (hl k (mem_Icc.mp hk).1).le)
        (fun i hi => inv_anti₀ (hl i ((mem_Icc.mp hh).1.trans (mem_Ioc.mp hi).1.le))
          (hmono ((mem_Icc.mp hh).1.trans (mem_Ioc.mp hi).1.le) (Nat.le_succ i)))
      exact hw.trans (by rw [div_eq_mul_inv,mul_comm (largestForwardSum a Y)]; exact mul_le_mul_of_nonneg_right
        (inv_anti₀ hstart (hmono (by omega) (Nat.succ_le_succ (mem_Icc.mp hh).1))) (forward_nonneg a Y))
    · rw [Ioc_eq_empty (le_of_not_gt hlk),sum_empty]
      exact div_nonneg (forward_nonneg a Y) hstart.le
  · apply Finset.sup'_le
    rintro ⟨h,k⟩ hp
    obtain ⟨hh,hk⟩ := mem_product.mp hp
    by_cases hlk : h<k
    · have hpre := sum_weighted_le_of_suffix_bounds hlk b (fun n => Real.log n)
        (fun j hj hju => le_forward b (hmid hh hk hj hju) hk) (hl _ (by have := (mem_Icc.mp hh).1; omega)).le
        (fun i hi => hmono ((mem_Icc.mp hh).1.trans (mem_Ioc.mp hi).1.le) (Nat.le_succ i))
      exact hpre.trans (mul_le_mul_of_nonneg_right (hmono (mem_Icc.mp hk).1 (mem_Icc.mp hk).2) (forward_nonneg b Y))
    · rw [Ioc_eq_empty (le_of_not_gt hlk),sum_empty]
      exact mul_nonneg (hl _ (by omega)).le (forward_nonneg b Y)

end GaloisForLFunctions.ExceptionalLayerTheory
