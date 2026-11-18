import GaloisForLFunctions.CountingHolography.Sections.MobiusInterpolationByIntegerFactorialDegrees
import GaloisForLFunctions.BezoutValuationIncidence.BezoutSelbergDiagonalCoercivityAndHalfDecorrelation
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorDilationChannels

/-! # Rounding the real degrees of the factorial interpolant

Möbius inversion over the multiples recovers each unrounded sample.
Passing to the next integer costs the Lipschitz constant times the square
of the support cutoff, divided by the square of the sample degree.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections
open Finset ArithmeticFunction BezoutValuationIncidence

/-- Möbius inverse of a cutoff test in the multiplicative argument. -/
def mobiusFactorialSample (W : ℝ → ℝ) (B u : ℝ) : ℝ :=
  ∑ d ∈ Icc 1 ⌊B/u⌋₊, moebiusReal d * W (d*u)

/-- The floor reading is the sum of the tails at the rounded multiples. -/
def roundedFactorialReading (W : ℝ → ℝ) (B y : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 ⌊B/y⌋₊, mobiusFactorialSample W B ⌈k*y⌉₊

theorem sum_mobiusFactorialSample (W : ℝ → ℝ) (B : ℝ) (hW : ∀ u, B < u → W u=0)
    {y : ℝ} (hy : 0 < y) :
    (∑ k ∈ Icc 1 ⌊B/y⌋₊, mobiusFactorialSample W B (k*y)) = W y := by
  let N := ⌊B/y⌋₊
  let F := fun d k : ℕ => moebiusReal d * W ((d*k:ℕ)*y)
  have inner (k : ℕ) : mobiusFactorialSample W B (k*y) = ∑ d ∈ Icc 1 (N/k), F d k := by
    rw [mobiusFactorialSample,mul_comm (k:ℝ) y,← div_div,Nat.floor_div_natCast]
    apply sum_congr rfl
    intro d _
    simp only [F,Nat.cast_mul]; ring_nf
  simp_rw [inner]
  rw [← _root_.RHTower.sum_hyperbola_swap_real N F,← _root_.RHTower.Sieve.sum_divisors_swap N F]
  have row (m : ℕ) (hm : m ∈ Icc 1 N) :
      (∑ d ∈ m.divisors, F d (m/d)) = if m=1 then W y else 0 := by
    have h : ∀ d ∈ m.divisors, F d (m/d)=moebiusReal d*W (m*y) := fun d hd => by
      rw [F,Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    rw [sum_congr rfl h,← sum_mul,sum_divisors_moebiusReal_eq_ite_one (mem_Icc.mp hm).1]
    split_ifs with h <;> simp [h]
  rw [sum_congr rfl row]
  by_cases h : 1 ≤ N
  · simp [h]
  · have hlt : B < y := (div_lt_one hy).mp (by
      by_contra! hb
      exact h (Nat.le_floor (by simpa only [Nat.cast_one] using hb)))
    simp [h,hW y hlt]

private theorem sample_enlarge {W : ℝ → ℝ} {B u : ℝ} (hu : 0 < u)
    (hW : ∀ x, B < x → W x=0) {N : ℕ} (hN : ⌊B/u⌋₊ ≤ N) :
    mobiusFactorialSample W B u = ∑ d ∈ Icc 1 N, moebiusReal d*W (d*u) := by
  apply sum_subset (Icc_subset_Icc_right hN)
  intro d hd hd'
  have hl : ⌊B/u⌋₊ < d := lt_of_not_ge fun h => hd' (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,h⟩)
  have hdu : B/u < d := by
    by_contra! h
    exact hl.not_ge (Nat.le_floor h)
  rw [hW _ ((div_lt_iff₀ hu).mp hdu),mul_zero]

/-- A unit-cell shift of a Möbius tail costs at most K B²/u². -/
theorem mobiusFactorialSample_rounding {W : ℝ → ℝ} {B L u v : ℝ} (hB : 0 ≤ B)
    (hL : 0 ≤ L) (hW : ∀ x, B < x → W x=0)
    (hLip : ∀ a b : ℝ, 0 < a → a ≤ b → |W b-W a| ≤ L*(b-a))
    (hu : 0 < u) (huv : u ≤ v) (hvu : v ≤ u+1) :
    |mobiusFactorialSample W B v-mobiusFactorialSample W B u| ≤ L*(B/u)^2 := by
  let N := ⌊B/u⌋₊
  have hN : (N:ℝ) ≤ B/u := Nat.floor_le (div_nonneg hB hu.le)
  rw [sample_enlarge (hu.trans_le huv) hW (Nat.floor_mono (div_le_div_of_nonneg_left hB hu huv)),
    mobiusFactorialSample,← sum_sub_distrib]
  have row (d : ℕ) (hd : d ∈ Icc 1 N) :
      |moebiusReal d*W (d*v)-moebiusReal d*W (d*u)| ≤ L*(B/u) := by
    have hd₀ : 0 < (d:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hd).1
    have hdN := (Nat.cast_le.mpr (mem_Icc.mp hd).2).trans hN
    have hμ : |moebiusReal d| ≤ 1 := by
      unfold moebiusReal
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    rw [← mul_sub,abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) hμ).trans
      ((hLip _ _ (mul_pos hd₀ hu) (mul_le_mul_of_nonneg_left huv hd₀.le)).trans ?_)
    apply mul_le_mul_of_nonneg_left _ hL
    rw [← mul_sub]
    exact (mul_le_of_le_one_right hd₀.le (by linarith only [hvu])).trans hdN
  exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum row).trans (by
    simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
    exact (mul_le_mul_of_nonneg_right hN (mul_nonneg hL (div_nonneg hB hu.le))).trans_eq (by ring)))

/-- At every positive integer degree the rounded interpolant is exact. -/
theorem roundedFactorialReading_nat (W : ℝ → ℝ) (B : ℝ) (hW : ∀ x, B < x → W x=0)
    {y : ℕ} (hy : 0 < y) : roundedFactorialReading W B y = W y := by
  unfold roundedFactorialReading
  have h (k : ℕ) : (⌈(k:ℝ)*y⌉₊:ℝ) = (k:ℝ)*y := by rw [← Nat.cast_mul,Nat.ceil_natCast,Nat.cast_mul]
  simp_rw [h]
  exact sum_mobiusFactorialSample W B hW (Nat.cast_pos.mpr hy)

private theorem telescoping_interval (b : ℕ → ℝ) {a n : ℕ} (h : a ≤ n+1) :
    (∑ j ∈ Icc a n, (b j-b (j+1))) = b a-b (n+1) := by
  induction n generalizing a with
  | zero => interval_cases a <;> simp
  | succ n ih =>
    by_cases ha : a = n+2
    · simp [ha]
    · have h' : a ≤ n+1 := by omega
      rw [sum_Icc_succ_top h',ih h']; ring

/-- Real-degree floor evaluation of the integer factorial presentation
with coefficients equal to successive differences of the Möbius tail. -/
theorem roundedFactorialReading_eq_floor_sum (W : ℝ → ℝ) {B y : ℝ} (hB : 0 ≤ B) (hy : 0 < y) :
    roundedFactorialReading W B y =
    ∑ j ∈ Icc 1 ⌊B⌋₊, (mobiusFactorialSample W B j - mobiusFactorialSample W B (j+1:ℕ)) *
      (⌊(j:ℝ)/y⌋₊:ℝ) := by
  classical
  let L := ⌊B⌋₊
  let N := ⌊B/y⌋₊
  let b := fun j : ℕ => mobiusFactorialSample W B j
  let c := fun j : ℕ => b j-b (j+1)
  have bz {j : ℕ} (hj : L < j) : b j = 0 := by
    have hj' : B < (j:ℝ) := by
      by_contra! h; exact hj.not_ge (Nat.le_floor h)
    have hq : ⌊B/(j:ℝ)⌋₊=0 := Nat.floor_eq_zero.mpr ((div_lt_one (hB.trans_lt hj')).mpr hj')
    simp [b,mobiusFactorialSample,hq]
  have count (j : ℕ) (hj : j ∈ Icc 1 L) :
      (∑ k ∈ Icc 1 N, if (k:ℝ)*y ≤ j then c j else 0) = c j*(⌊(j:ℝ)/y⌋₊:ℝ) := by
    have hjB := (Nat.cast_le.mpr (mem_Icc.mp hj).2).trans (Nat.floor_le hB)
    have hle : ⌊(j:ℝ)/y⌋₊ ≤ N := Nat.floor_mono (div_le_div_of_nonneg_right hjB hy.le)
    have he : (Icc 1 N).filter (fun k : ℕ => (k:ℝ)*y ≤ j) = Icc 1 ⌊(j:ℝ)/y⌋₊ := by
      ext k
      simp only [mem_filter,mem_Icc,← le_div_iff₀ hy,← Nat.le_floor_iff (div_nonneg (Nat.cast_nonneg j) hy.le)]
      omega
    rw [← sum_filter,he,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel,mul_comm]
  have col (k : ℕ) (hk : k ∈ Icc 1 N) :
      ∑ j ∈ Icc 1 L, (if (k:ℝ)*y ≤ j then c j else 0) = b ⌈k*y⌉₊ := by
    have hp := mul_pos (Nat.cast_pos.mpr (mem_Icc.mp hk).1 : 0 < (k:ℝ)) hy
    have hk' : 1 ≤ ⌈(k:ℝ)*y⌉₊ := Nat.ceil_pos.mpr hp
    have he : (Icc 1 L).filter (fun j : ℕ => (k:ℝ)*y ≤ j) = Icc ⌈k*y⌉₊ L := by
      ext j; simp only [mem_filter,mem_Icc,← Nat.ceil_le]; omega
    rw [← sum_filter,he]
    by_cases h : ⌈(k:ℝ)*y⌉₊ ≤ L+1
    · rw [show c = fun j => b j-b (j+1) from rfl,telescoping_interval b h,bz (Nat.lt_succ_self L),sub_zero]
    · rw [Icc_eq_empty_of_lt (by omega),sum_empty,bz (by omega)]
  change (∑ k ∈ Icc 1 N, b ⌈k*y⌉₊) = ∑ j ∈ Icc 1 L, c j*_
  rw [← sum_congr rfl col,sum_comm]
  exact sum_congr rfl count

private theorem reciprocal_square_sum (N : ℕ) : (∑ k ∈ Icc 1 N, 1/(k:ℝ)^2) ≤ 2 := by
  have h (n : ℕ) : (∑ k ∈ Icc 1 n, 1/(k:ℝ)^2) ≤ 2-2/((n:ℝ)+1) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [sum_Icc_succ_top (by omega),Nat.cast_succ]
      have ht := add_le_add_right ih (1/((n:ℝ)+1)^2)
      refine ht.trans ?_
      field_simp <;> nlinarith only [Nat.cast_nonneg (α := ℝ) n,sq_nonneg (n:ℝ)]
  exact (h N).trans (sub_le_self _ (by positivity))

/-- For W(y/X) the cutoff is BX and the Lipschitz constant is L/X,
giving a bound 2 L B² X/y². -/
theorem roundedFactorialReading_error {W : ℝ → ℝ} {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hW : ∀ x, B < x → W x=0)
    (hLip : ∀ a b : ℝ, 0 < a → a ≤ b → |W b-W a| ≤ L*(b-a)) {y : ℝ} (hy : 0 < y) :
    |roundedFactorialReading W B y - W y| ≤ 2*L*(B/y)^2 := by
  rw [roundedFactorialReading,← sum_mobiusFactorialSample W B hW hy,← sum_sub_distrib]
  have hrow (k : ℕ) (hk : k ∈ Icc 1 ⌊B/y⌋₊) :
      |mobiusFactorialSample W B ⌈k*y⌉₊-mobiusFactorialSample W B (k*y)| ≤ L*(B/y)^2*(1/(k:ℝ)^2) := by
    have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hk).1
    have hky := mul_pos hk' hy
    exact (mobiusFactorialSample_rounding hB hL hW hLip hky (Nat.le_ceil _) (Nat.ceil_lt_add_one hky.le).le).trans_eq (by field_simp; ring)
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hrow).trans ?_)
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left (reciprocal_square_sum _) (mul_nonneg hL (sq_nonneg _))).trans_eq (by ring)

end GaloisForLFunctions.CountingHolography.Sections
