import GaloisForLFunctions.ExceptionalLayerTheory.EveryFiniteCofactorSeesTheOrdinaryPrimeCount
import GaloisForLFunctions.RHTower.MobiusDiscretePacketEdgeEstimates
import GaloisForLFunctions.ExceptionalLayerTheory.QuadratureOfTwoConsecutivePrimeIntervals

/-!
# One-sided oscillation of prime-count increments

For an increasing nonnegative weight, Abel summation is a positive combination
of suffix sums. A decreasing weight gives prefix sums. Thus the largest
one-sided increase is multiplied by at most the largest weight. Applying the
two statements to the prime logarithm and its reciprocal gives sharp local
comparisons for both signs of the centered ordinary count.
-/

noncomputable section

open Finset Filter Topology

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
  simp only [smul_eq_mul] at he
  change (∑ i ∈ Ioc l u, w i*a i) =
    w u*intervalPrefix a u-w (l+1)*intervalPrefix a l-
    ∑ i ∈ Ioc l (u-1), (w (i+1)-w i)*intervalPrefix a i at he
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
    (∑ i ∈ Ioc h k, a i)≤largestForwardSum a Y := by
  have hp : (h,k) ∈ windowPairs Y := mem_product.mpr ⟨hh,hk⟩
  exact Finset.le_sup' (f := fun z : ℕ × ℕ => ∑ i ∈ Ioc z.1 z.2, a i) hp

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
  have hmono {i j : ℕ} (hi : Y ≤ i) (hij : i≤j) : Real.log i≤Real.log j :=
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

/-- Freezing the logarithm at the initial cutoff costs at most its relative
variation times the largest absolute suffix sum, for either sign. -/
theorem prime_interval_freeze_log {l u : ℕ} (hl : 2 ≤ l) (hlu : l < u) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ j : ℕ, l ≤ j → j ≤ u →
      |∑ n ∈ Ioc j u, Real.log n * ordinaryPrimeCountWeight n| ≤ B) :
    |(∑ n ∈ Ioc l u, Real.log n * ordinaryPrimeCountWeight n) -
      Real.log l * ∑ n ∈ Ioc l u, ordinaryPrimeCountWeight n| ≤
      ((Real.log u-Real.log l)/Real.log l)*B := by
  let a (n : ℕ) := Real.log n*ordinaryPrimeCountWeight n
  let w (n : ℕ) := 1-Real.log l/Real.log n
  have hlog {n : ℕ} (hn : l ≤ n) : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hmono {i j : ℕ} (hi : l ≤ i) (hj : i ≤ j) :
      Real.log i ≤ Real.log j :=
    Real.log_le_log (by exact_mod_cast (show 0 < i by omega)) (by exact_mod_cast hj)
  have hw {n : ℕ} (hn : l ≤ n) : 0 ≤ w n := sub_nonneg.mpr ((div_le_one (hlog hn)).mpr (hmono le_rfl hn))
  have hinc (i : ℕ) (hi : i ∈ Ioc l (u-1)) : w i ≤ w (i+1) :=
    sub_le_sub_left (div_le_div_of_nonneg_left (hlog le_rfl).le (hlog (mem_Ioc.mp hi).1.le)
      (hmono (mem_Ioc.mp hi).1.le (Nat.le_succ i))) 1
  have hsum : (∑ n ∈ Ioc l u, w n*a n) =
      (∑ n ∈ Ioc l u, Real.log n*ordinaryPrimeCountWeight n)-
        Real.log l*∑ n ∈ Ioc l u, ordinaryPrimeCountWeight n := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    dsimp only [w,a]
    field_simp [(hlog (mem_Ioc.mp hn).1.le).ne']
  rw [← hsum,abs_le]
  have hpos := sum_weighted_le_of_suffix_bounds hlu a w
    (fun j hj hju => (abs_le.mp (h j hj hju)).2) (hw (Nat.le_succ _)) hinc
  have hneg := sum_weighted_le_of_suffix_bounds hlu (fun n => -a n) w
    (fun j hj hju => by rw [Finset.sum_neg_distrib]; exact neg_le.mpr (abs_le.mp (h j hj hju)).1)
    (hw (Nat.le_succ _)) hinc
  simp only [mul_neg,Finset.sum_neg_distrib] at hneg
  have hu : w u ≤ (Real.log u-Real.log l)/Real.log l := by
    rw [show w u = (Real.log u-Real.log l)/Real.log u by
      dsimp only [w]; rw [sub_div,div_self (hlog hlu.le).ne']]
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr (hmono le_rfl hlu.le)) (hlog le_rfl) (hmono le_rfl hlu.le)
  exact ⟨neg_le.mp (hneg.trans (mul_le_mul_of_nonneg_right hu hB)),
    hpos.trans (mul_le_mul_of_nonneg_right hu hB)⟩

/-- The log-weighted centered count is exactly the increment of θ(x)−x
at integer endpoints. -/
theorem centered_prime_log_interval {l u : ℕ} (hl : 1 ≤ l) (hlu : l ≤ u) :
    (∑ n ∈ Ioc l u, Real.log n*ordinaryPrimeCountWeight n) =
      (Chebyshev.theta u-u)-(Chebyshev.theta l-l) := by
  let f (n : ℕ) : ℝ := if n.Prime then Real.log n else 0
  have hp (n : ℕ) : (∑ k ∈ Icc 1 n, f k) = Chebyshev.theta n := by
    rw [Chebyshev.theta_eq_sum_primesLE_log,Nat.primesLE_eq_filter_Icc_one,sum_filter]
  have he : Icc 1 u = Icc 1 l ∪ Ioc l u := by
    ext n
    simp only [mem_Icc,mem_union,mem_Ioc]
    omega
  have hd : Disjoint (Icc 1 l) (Ioc l u) := Finset.disjoint_left.mpr
    fun _ h h' => (mem_Ioc.mp h').1.not_ge (mem_Icc.mp h).2
  have hθ := hp u
  rw [he,sum_union hd,hp] at hθ
  have ha (n : ℕ) (hn : n ∈ Ioc l u) : Real.log n*ordinaryPrimeCountWeight n = f n-1 := by
    have hn' := (mem_Ioc.mp hn).1
    have hh := Real.log_pos (show (1:ℝ) < n by exact_mod_cast (show 1<n by omega))
    change Real.log n*((if n.Prime then 1 else 0)-(Real.log n)⁻¹)=_
    rw [mul_sub,mul_inv_cancel₀ hh.ne']
    split <;> simp_all [f]
  rw [sum_congr rfl ha,sum_sub_distrib]
  simp only [sum_const,nsmul_eq_mul,mul_one,Nat.card_Ioc,Nat.cast_sub hlu]
  linarith only [hθ]

/-- Rounding both endpoints costs less than one in a centered interval. -/
theorem centered_prime_log_interval_real {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    |(∑ n ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, Real.log n*ordinaryPrimeCountWeight n)-
      ((Chebyshev.theta y-y)-(Chebyshev.theta x-x))| ≤ 1 := by
  rw [centered_prime_log_interval ((Nat.one_le_floor_iff x).mpr hx) (Nat.floor_mono hxy),
    ← Chebyshev.theta_eq_theta_coe_floor,← Chebyshev.theta_eq_theta_coe_floor,abs_le]
  have h₁ := Nat.floor_le (zero_le_one.trans hx)
  have h₂ := Nat.floor_le ((zero_le_one.trans hx).trans hxy)
  have h₃ := Nat.lt_floor_add_one x
  have h₄ := Nat.lt_floor_add_one y
  constructor <;> linarith only [h₁,h₂,h₃,h₄]

/-- At every sufficiently large integer base the largest centered prime
count in either direction has size at least a constant times Y^β/log(2Y). -/
theorem singleQuartet_signed_prime_octave {ρ : ℂ} (hq : ExclusionOfTheCriticalState.HasSingleOffLineQuartet ρ) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ Y : ℕ in atTop, ∀ ε : ℝ, |ε|=1 →
      c*(Y:ℝ)^ρ.re ≤ Real.log (2*Y:ℕ)*largestForwardSum (fun n => ε*ordinaryPrimeCountWeight n) Y := by
  obtain ⟨C,hC,h⟩ := singleQuartet_signed_theta_octave hq
  have hβ : 0<ρ.re := by linarith only [hq.1]
  have hp : Tendsto (fun Y : ℕ => (Y:ℝ)^ρ.re) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop
  refine ⟨C/2,half_pos hC,?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h,hp.eventually_ge_atTop (2/C),
    eventually_ge_atTop 2] with Y hY hpow h2
  intro ε hε
  obtain ⟨l,u,hl,hlu,hu,hs⟩ := hY ε hε
  have hy : (1:ℝ)≤Y := by exact_mod_cast (show 1≤Y by omega)
  have hfl : Y≤⌊l⌋₊ := Nat.le_floor hl
  have hfu : ⌊u⌋₊≤2*Y := by
    have he := (Nat.floor_le ((zero_le_one.trans hy).trans (hl.trans hlu))).trans hu
    exact_mod_cast he
  have he := centered_prime_log_interval_real (hy.trans hl) hlu
  let S := ∑ n ∈ Ioc ⌊l⌋₊ ⌊u⌋₊, Real.log n*ordinaryPrimeCountWeight n
  let E := (Chebyshev.theta u-u)-(Chebyshev.theta l-l)
  have he' : |ε*(S-E)|≤1 := by rw [abs_mul,hε,one_mul]; exact he
  have hf := Nat.floor_mono hlu
  have hI := le_forward (fun n => Real.log n*(ε*ordinaryPrimeCountWeight n))
    (mem_Icc.mpr ⟨hfl,hf.trans hfu⟩) (mem_Icc.mpr ⟨hfl.trans hf,hfu⟩)
  have hsum : (∑ n ∈ Ioc ⌊l⌋₊ ⌊u⌋₊, Real.log n*(ε*ordinaryPrimeCountWeight n))= ε*S := by
    dsimp only [S]; rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  rw [hsum] at hI
  have hpow' := (div_le_iff₀ hC).mp (show 2/C≤(Y:ℝ)^ρ.re from hpow)
  have hd := (abs_le.mp he').1
  change C*(Y:ℝ)^ρ.re ≤ ε*E at hs
  exact (show C/2*(Y:ℝ)^ρ.re ≤ ε*S by linarith only [hpow',hd,hs]).trans
    (hI.trans (forward_prime_logarithm_bounds Y h2 ε).2)

/-- Freezing the prime logarithm on any interval inside one octave has
error O(l^β/log l), uniformly in its upper endpoint. -/
theorem singleQuartet_prime_interval_freeze_log {ρ : ℂ} (hq : ExclusionOfTheCriticalState.HasSingleOffLineQuartet ρ) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ l : ℕ in atTop, ∀ u : ℕ, l≤u → u≤2*l →
      |(∑ n ∈ Ioc l u, Real.log n*ordinaryPrimeCountWeight n)-
        Real.log l*∑ n ∈ Ioc l u, ordinaryPrimeCountWeight n| ≤ K*(l:ℝ)^ρ.re/Real.log l := by
  obtain ⟨L,hL,h⟩ := singleQuartet_theta_error_power hq
  obtain ⟨X,hX⟩ := eventually_atTop.mp h
  let B := 2*L*(2:ℝ)^ρ.re
  have hB : 0≤B := by dsimp only [B]; positivity
  refine ⟨Real.log 2*B,mul_nonneg (Real.log_nonneg (by norm_num)) hB,?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop X,eventually_ge_atTop 2] with l hl h2
  have hp : (1:ℝ)<l := by exact_mod_cast (show 1<l by omega)
  have hlog := Real.log_pos hp
  have hβ : 0≤ρ.re := by linarith only [hq.1]
  have hLpow := Real.rpow_nonneg (Nat.cast_nonneg l) ρ.re
  intro u hlu hu
  rcases hlu.eq_or_lt with rfl | hlu
  · simp only [Ioc_self,sum_empty,mul_zero,sub_zero,abs_zero]
    positivity
  have hb (v : ℕ) (hv : l≤v) (hvu : v≤2*l) :
      |Chebyshev.theta v-v| ≤ L*((2:ℝ)^ρ.re*(l:ℝ)^ρ.re) := by
    have hv' : (l:ℝ)≤v := by exact_mod_cast hv
    apply (hX v (hl.trans hv')).trans
    rw [← Real.mul_rpow (by norm_num) (Nat.cast_nonneg l)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg v) (by exact_mod_cast hvu) hβ) hL
  have hs := prime_interval_freeze_log h2 hlu (mul_nonneg hB hLpow) (fun j hj hju => by
    rw [centered_prime_log_interval (by omega) hju]
    exact ((abs_sub _ _).trans (add_le_add (hb u hlu.le hu) (hb j hj (hju.trans hu)))).trans_eq (by
      dsimp only [B]; ring))
  have hlogu : Real.log u ≤ Real.log 2+Real.log l := by
    rw [← Real.log_mul (by norm_num) (zero_lt_one.trans hp).ne']
    exact Real.log_le_log (by exact_mod_cast (show 0<u by omega)) (by exact_mod_cast hu)
  apply hs.trans
  have ht := div_le_div_of_nonneg_right (show Real.log u-Real.log l≤Real.log 2 by linarith only [hlogu]) hlog.le
  exact (mul_le_mul_of_nonneg_right ht (mul_nonneg hB hLpow)).trans_eq (by ring)

end GaloisForLFunctions.ExceptionalLayerTheory
