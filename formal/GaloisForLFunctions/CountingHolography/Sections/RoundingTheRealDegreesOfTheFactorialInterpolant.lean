import GaloisForLFunctions.CountingHolography.Sections.MobiusInterpolationByIntegerFactorialDegrees
import GaloisForLFunctions.BezoutValuationIncidence.BezoutSelbergDiagonalCoercivityAndHalfDecorrelation
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.MonotoneErrorsInvertAtMertensPrecision
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
      dsimp only [F]
      rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    rw [sum_congr rfl h,← sum_mul,sum_divisors_moebiusReal_eq_ite_one (mem_Icc.mp hm).1]
    split_ifs with h <;> simp [h]
  rw [sum_congr rfl row]
  by_cases h : 1 ≤ N
  · simp [h]
  · have hlt : B < y := (div_lt_one hy).mp (by
      by_contra! hb
      exact h (Nat.le_floor (by simpa only [Nat.cast_one] using hb)))
    simp [hW y hlt]

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
      have ht := add_le_add ih (le_refl (1/((n:ℝ)+1)^2))
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
    exact (mobiusFactorialSample_rounding hB hL hW hLip hky (Nat.le_ceil _) (Nat.ceil_lt_add_one hky.le).le).trans_eq (by field_simp)
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hrow).trans ?_)
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left (reciprocal_square_sum _) (mul_nonneg hL (sq_nonneg _))).trans_eq (by ring)

open ArithmeticOfSquareRootPrecision Filter Topology

/-- Partial summation transfers a Mertens power bound to a compact
Lipschitz test, uniformly as its dilation varies over positive reals. -/
theorem mobiusFactorialSample_mertens_bound {W : ℝ → ℝ} {B L C σ : ℝ}
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hW : ∀ x, B < x → W x=0)
    (hLip : ∀ a b : ℝ, 0 < a → a ≤ b → |W b-W a| ≤ L*(b-a))
    (hM : ∀ n : ℕ, 0 < n → |mertens n| ≤ C*(n:ℝ)^σ) {u : ℝ} (hu : 0 < u) :
    |mobiusFactorialSample W B u| ≤ (C*L*B)*(B/u)^σ := by
  let N := ⌊B/u⌋₊
  let f := fun k : ℕ => W (k*u)
  have hN : (N:ℝ) ≤ B/u := Nat.floor_le (div_nonneg hB hu.le)
  have htop : f (N+1)=0 := by
    apply hW
    apply (div_lt_iff₀ hu).mp
    exact_mod_cast Nat.lt_floor_add_one (B/u)
  have hI : Icc 1 N=Ioc 0 N := by ext d; simp only [mem_Icc,mem_Ioc]; omega
  have he := sum_moebius_mul_eq f N
  rw [htop,mul_zero,zero_add] at he
  rw [mobiusFactorialSample,show ⌊B/u⌋₊=N from rfl,hI]
  change |∑ d ∈ Ioc 0 N, (moebius d:ℝ)*f d| ≤ _
  rw [he]
  have row (k : ℕ) (hk : k ∈ Ioc 0 N) :
      |mertens k*(f k-f (k+1))| ≤ C*(B/u)^σ*(L*u) := by
    have hk₀ := (mem_Ioc.mp hk).1
    have hkN := (Nat.cast_le.mpr (mem_Ioc.mp hk).2).trans hN
    have hd := hLip ((k:ℝ)*u) ((k:ℝ)*u+u) (mul_pos (Nat.cast_pos.mpr hk₀) hu)
      (le_add_of_nonneg_right hu.le)
    have hg : |f k-f (k+1)| ≤ L*u := by
      rw [abs_sub_comm]
      simpa only [f,Nat.cast_succ,add_mul,one_mul,add_sub_cancel_left] using hd
    rw [abs_mul]
    exact mul_le_mul ((hM k hk₀).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg k) hkN hσ) hC)) hg (abs_nonneg _)
      (mul_nonneg hC (Real.rpow_nonneg (div_nonneg hB hu.le) _))
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum row).trans ?_)
  simp only [sum_const,nsmul_eq_mul,Nat.card_Ioc,Nat.sub_zero]
  refine (mul_le_mul_of_nonneg_right hN (by positivity)).trans_eq ?_
  field_simp [hu.ne']

private theorem weighted_derivative_zero {W W' : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hW : ∀ x, B < x → W x=0) (hD : ∀ x, 0 < x → HasDerivAt W (W' x) x) :
    ∀ v, B < v → v*W' v=0 := by
  intro v hv
  have hl : W =ᶠ[𝓝 v] fun _ => 0 :=
    eventually_of_mem (Ioi_mem_nhds hv) fun x hx => hW _ hx
  have hd := (hD v (hB.trans_lt hv)).congr_of_eventuallyEq hl.symm
  rw [hd.unique (hasDerivAt_const v 0),mul_zero]

/-- Differentiation in the dilation variable replaces the test by v W'(v)
and divides the resulting Möbius sum by the argument. -/
theorem hasDerivAt_mobiusFactorialSample {W W' : ℝ → ℝ} {B u : ℝ} (hB : 0 ≤ B) (hu : 0 < u)
    (hW : ∀ x, B < x → W x=0) (hD : ∀ x, 0 < x → HasDerivAt W (W' x) x) :
    HasDerivAt (mobiusFactorialSample W B)
      (mobiusFactorialSample (fun v => v*W' v) B u / u) u := by
  let N := ⌊B/(u/2)⌋₊
  let S := Icc 1 N
  have hhalf := half_pos hu
  have expand (v : ℝ) (hv : u/2 < v) : mobiusFactorialSample W B v =
      ∑ d ∈ S, moebiusReal d * W (d*v) :=
    sample_enlarge (hhalf.trans hv) hW (Nat.floor_mono (div_le_div_of_nonneg_left hB hhalf hv.le))
  have hzero := weighted_derivative_zero hB hW hD
  have hd (d : ℕ) (hd : d ∈ S) :
      HasDerivAt (fun x : ℝ => moebiusReal d * W (d*x)) (moebiusReal d*(W' (d*u)*d)) u :=
    ((hD _ (mul_pos (Nat.cast_pos.mpr (mem_Icc.mp hd).1) hu)).comp u
      (by simpa only [id_eq,mul_one] using (hasDerivAt_id u).const_mul (d:ℝ))).const_mul _
  have hf := (HasDerivAt.fun_sum hd).congr_of_eventuallyEq
    (eventually_of_mem (Ioi_mem_nhds (half_lt_self hu)) fun x hx => expand _ hx)
  have hvalue : mobiusFactorialSample (fun v => v*W' v) B u/u =
      ∑ d ∈ S, moebiusReal d*(W' (d*u)*d) := by
    rw [sample_enlarge hu hzero (Nat.floor_mono (div_le_div_of_nonneg_left hB hhalf (half_le_self hu.le))),
      sum_div]
    exact sum_congr rfl fun d _ => by field_simp [hu.ne'] <;> ring
  rw [hvalue]
  exact hf

/-- Partial summation applied to v W'(v) bounds the change across a
unit interval by the Mertens power divided by its left endpoint. -/
theorem mobiusFactorialSample_mertens_step {W W' : ℝ → ℝ} {B L C σ : ℝ}
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hW : ∀ x, B < x → W x=0) (hD : ∀ x, 0 < x → HasDerivAt W (W' x) x)
    (hLip : ∀ a b : ℝ, 0 < a → a ≤ b → |b*W' b-a*W' a| ≤ L*(b-a))
    (hM : ∀ n : ℕ, 0 < n → |mertens n| ≤ C*(n:ℝ)^σ) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hvu : v ≤ u+1) :
    |mobiusFactorialSample W B v-mobiusFactorialSample W B u| ≤ C*L*B*(B/u)^σ/u := by
  let D := C*L*B*(B/u)^σ/u
  have hd (x : ℝ) (hx : x ∈ Set.Icc u v) := hasDerivAt_mobiusFactorialSample hB (hu.trans_le hx.1) hW hD
  have hbound (x : ℝ) (hx : x ∈ Set.Icc u v) : ‖deriv (mobiusFactorialSample W B) x‖ ≤ D := by
    have hx₀ := hu.trans_le hx.1
    rw [(hd _ hx).deriv,Real.norm_eq_abs,abs_div,abs_of_pos hx₀]
    have h := mobiusFactorialSample_mertens_bound hB hL hC hσ (weighted_derivative_zero hB hW hD) hLip hM hx₀
    have hpow := Real.rpow_le_rpow (div_nonneg hB hx₀.le) (div_le_div_of_nonneg_left hB hu hx.1) hσ
    exact (div_le_div_of_nonneg_right
      (h.trans (mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hC hL) hB))) hx₀.le).trans
      (div_le_div_of_nonneg_left (by positivity) hu hx.1)
  have h := (convex_Icc u v).norm_image_sub_le_of_norm_deriv_le (fun x hx => (hd x hx).differentiableAt)
    hbound (Set.left_mem_Icc.mpr huv) (Set.right_mem_Icc.mpr huv)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr huv)] at h
  exact h.trans (mul_le_of_le_one_right (by dsimp only [D]; positivity) (by linarith only [hvu]))

/-- Positive-degree reciprocal power sum for the rounding error. -/
def factorialInterpolationPSeries (σ : ℝ) := ∑' k : ℕ, ((k:ℝ)^(1+σ))⁻¹

private theorem sum_unit_rounding {b : ℝ → ℝ} {D B σ y : ℝ} (hD : 0 ≤ D)
    (hB : 0 ≤ B) (hσ : 0 < σ) (hy : 0 < y)
    (h : ∀ u v, 0 < u → u ≤ v → v ≤ u+1 → |b v-b u| ≤ D*(B/u)^σ/u)
    (v : ℕ → ℝ) (hv : ∀ k : ℕ, (k:ℝ)*y ≤ v k ∧ v k ≤ k*y+1) (N : ℕ) :
    (∑ k ∈ Icc 1 N, |b (v k)-b (k*y)|) ≤ factorialInterpolationPSeries σ*(D*(B/y)^σ/y) := by
  let E := D*(B/y)^σ/y
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hs := (Real.summable_nat_rpow_inv.mpr (by linarith only [hσ] : 1 < 1+σ))
  have row (k : ℕ) (hk : k ∈ Icc 1 N) : |b (v k)-b (k*y)| ≤ ((k:ℝ)^(1+σ))⁻¹*E := by
    have hk₀ : 0 < (k:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hk).1
    refine (h _ _ (mul_pos hk₀ hy) (hv k).1 (hv k).2).trans_eq ?_
    rw [show B/((k:ℝ)*y)=(B/y)/k by ring,Real.div_rpow (div_nonneg hB hy.le) hk₀.le,Real.rpow_add hk₀,Real.rpow_one]
    dsimp only [E]; ring
  refine (sum_le_sum row).trans ?_
  rw [← sum_mul]
  exact mul_le_mul_of_nonneg_right (hs.sum_le_tsum _ fun k _ => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE

/-- The rounded floor response preserves every positive Mertens exponent
with a tail of order y to the minus one minus that exponent. -/
theorem roundedFactorialReading_mertens_error {W W' : ℝ → ℝ} {B L C σ : ℝ}
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 0 ≤ C) (hσ : 0 < σ)
    (hW : ∀ x, B < x → W x=0) (hD : ∀ x, 0 < x → HasDerivAt W (W' x) x)
    (hLip : ∀ a b : ℝ, 0 < a → a ≤ b → |b*W' b-a*W' a| ≤ L*(b-a))
    (hM : ∀ n : ℕ, 0 < n → |mertens n| ≤ C*(n:ℝ)^σ) {y : ℝ} (hy : 0 < y) :
    |roundedFactorialReading W B y-W y| ≤ factorialInterpolationPSeries σ*(C*L*B*(B/y)^σ/y) := by
  rw [roundedFactorialReading,← sum_mobiusFactorialSample W B hW hy,← sum_sub_distrib]
  have hh := @mobiusFactorialSample_mertens_step W W' B L C σ hB hL hC hσ.le hW hD hLip hM
  exact (abs_sum_le_sum_abs _ _).trans (sum_unit_rounding (mul_nonneg (mul_nonneg hC hL) hB) hB hσ hy
    (fun u v => hh (u := u) (v := v)) (fun k => (⌈(k:ℝ)*y⌉₊:ℝ))
    (fun k => ⟨Nat.le_ceil _,(Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg _) hy.le)).le⟩) _)

/-- When the unit sample vanishes, balance cancels the full linear
part of every floor; its fractional part costs at most one coefficient. -/
theorem roundedFactorialReading_balanced_bound (W : ℝ → ℝ) {B y : ℝ} (hB : 0 ≤ B)
    (hy : 0 < y) (hW : ∀ x, B < x → W x=0) (h₁ : W 1=0) :
    |roundedFactorialReading W B y| ≤
      ∑ j ∈ Icc 1 ⌊B⌋₊, |mobiusFactorialSample W B j-mobiusFactorialSample W B (j+1:ℕ)| := by
  let c := fun j : ℕ => mobiusFactorialSample W B j-mobiusFactorialSample W B (j+1:ℕ)
  let I := Icc 1 ⌊B⌋₊
  have hbal : (∑ j ∈ I, c j*(j:ℝ)) = 0 := by
    have h := roundedFactorialReading_eq_floor_sum W hB (Nat.cast_pos.mpr Nat.one_pos : (0:ℝ) < (1:ℕ))
    rw [roundedFactorialReading_nat W B hW Nat.one_pos] at h
    simpa only [Nat.cast_one,h₁,div_one,Nat.floor_natCast] using h.symm
  have hzero : (∑ j ∈ I, c j*((j:ℝ)/y)) = 0 := by
    simp_rw [← mul_div_assoc]
    rw [← sum_div,hbal,zero_div]
  rw [roundedFactorialReading_eq_floor_sum W hB hy]
  change |∑ j ∈ I, c j*(⌊(j:ℝ)/y⌋₊:ℝ)| ≤ _
  rw [← sub_zero (∑ j ∈ I, c j*(⌊(j:ℝ)/y⌋₊:ℝ)),← hzero,← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [← mul_sub,abs_mul,abs_sub_comm (↑⌊(j:ℝ)/y⌋₊) ((j:ℝ)/y),
    abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le (div_nonneg (Nat.cast_nonneg j) hy.le)))]
  exact mul_le_of_le_one_right (abs_nonneg _) (by linarith only [Nat.lt_floor_add_one ((j:ℝ)/y)])

/-- Uniform bound at all small degrees for a balanced compact test
under the same Mertens hypothesis. -/
theorem roundedFactorialReading_mertens_small {W W' : ℝ → ℝ} {B L C σ : ℝ}
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 0 ≤ C) (hσ : 0 < σ)
    (hW : ∀ x, B < x → W x=0) (hD : ∀ x, 0 < x → HasDerivAt W (W' x) x)
    (hLip : ∀ a b : ℝ, 0 < a → a ≤ b → |b*W' b-a*W' a| ≤ L*(b-a))
    (hM : ∀ n : ℕ, 0 < n → |mertens n| ≤ C*(n:ℝ)^σ) (hsmall : ∀ x, 0 < x → x ≤ 1 → W x = 0)
    {y : ℝ} (hy : 0 < y) (hy₁ : y ≤ 1) :
    |roundedFactorialReading W B y-W y| ≤ factorialInterpolationPSeries σ*(C*L*B*B^σ) := by
  have hh := @mobiusFactorialSample_mertens_step W W' B L C σ hB hL hC hσ.le hW hD hLip hM
  have h := sum_unit_rounding (mul_nonneg (mul_nonneg hC hL) hB) hB hσ zero_lt_one
    (fun u v => hh (u := u) (v := v)) (fun k => ((k+1:ℕ):ℝ))
    (fun k => by push_cast; simp) ⌊B⌋₊
  rw [hsmall y hy hy₁,sub_zero]
  refine (roundedFactorialReading_balanced_bound W hB hy hW (hsmall 1 one_pos le_rfl)).trans ?_
  simpa only [mul_one,div_one,abs_sub_comm] using h

end GaloisForLFunctions.CountingHolography.Sections
