import GaloisForLFunctions.ExceptionalLayerTheory.FiniteDilationsOfArithmeticKernels
import GaloisForLFunctions.ExceptionalLayerTheory.TheAlternatingDivisorCountHasSquareRootError
import GaloisForLFunctions.RHTower.CarrierLineSup

/-!
# A positive weight balancing the two signs of the prime error

For the test `g(v) = log v + (1/v-1)/2` above one, its alternating
divisor sum has logarithmic slope between one sixth and three quarters.
Abel summation then supplies positive weights comparable to the harmonic
weights whose signed prime error is bounded at square-root scale.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Continuous test supported above one. -/
def primeMeanTest (v : ℝ) : ℝ := if 1 ≤ v then Real.log v + (v⁻¹-1)/2 else 0

private theorem test_of_one_le {v : ℝ} (hv : 1 ≤ v) :
    primeMeanTest v = Real.log v+(v⁻¹-1)/2 := if_pos hv

private theorem test_zero {x : ℝ} (hx : x ≤ 1) : primeMeanTest x = 0 := by
  rcases hx.lt_or_eq with h | rfl
  · simp [primeMeanTest,not_le.mpr h]
  · norm_num [primeMeanTest]

/-- Positive logarithmic increments arise from the alternating divisor row. -/
def primeMeanKernel := arithmeticKernel alternatingDivisorCoeff primeMeanTest

/-- No divisor contributes before the first cutoff, including its endpoint. -/
theorem primeMeanKernel_eq_zero {x : ℝ} (hx : x ≤ 1) : primeMeanKernel x = 0 := by
  unfold primeMeanKernel arithmeticKernel
  apply sum_eq_zero
  intro n hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [test_zero ((div_le_one (zero_lt_one.trans_le hn1)).mpr (hx.trans hn1)),smul_zero]

private abbrev firstMoment (N : ℕ) := ∑ n ∈ Icc 1 N, (n:ℝ)*alternatingDivisorCoeff n

private theorem alternating_pair (k : ℕ) :
    alternatingDivisorCoeff (2*k+1) = 1 ∧ alternatingDivisorCoeff (2*k+2) = -1 := by
  have hd (j : ℕ) : alternatingDivisorCoeff (j+1) =
      (((j+1)%2 : ℕ):ℝ) - ((j%2 : ℕ):ℝ) := by
    have he := prefix_alternatingDivisorCoeff (j+1)
    rw [sum_Icc_succ_top (by omega : 1 ≤ j+1),prefix_alternatingDivisorCoeff] at he
    linarith only [he]
  constructor
  · rw [hd,show (2*k+1)%2=1 by omega,show (2*k)%2=0 by omega]
    norm_num
  · rw [show 2*k+2=(2*k+1)+1 by omega,hd,
      show (2*k+1+1)%2=0 by omega,show (2*k+1)%2=1 by omega]
    norm_num

private theorem firstMoment_pair (k : ℕ) :
    firstMoment (2*k) = -(k:ℝ) ∧ firstMoment (2*k+1) = k+1 := by
  have hs (n : ℕ) : firstMoment (n+1) = firstMoment n + (n+1)*alternatingDivisorCoeff (n+1) := by
    simp only [firstMoment,sum_Icc_succ_top (show 1 ≤ n+1 by omega),Nat.cast_add,Nat.cast_one]
  have he (k : ℕ) : firstMoment (2*k) = -(k:ℝ) := by
    induction k with
    | zero => simp [firstMoment]
    | succ k ih =>
      rw [show 2*(k+1)=2*k+1+1 by omega,hs,hs,ih,(alternating_pair k).1,(alternating_pair k).2]
      push_cast
      ring
  exact ⟨he k,by rw [hs,he,(alternating_pair k).1]; push_cast; ring⟩

/-- Reciprocal slope of the logarithmic mean, with the two endpoint bounds. -/
private theorem reciprocal_log_slope {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    ∃ r : ℝ, 0 ≤ r ∧ x*r ≤ 1 ∧ 1 ≤ y*r ∧
      x⁻¹-y⁻¹ = r*(Real.log y-Real.log x) := by
  have hy := hx.trans hxy
  let L := Real.log y-Real.log x
  have hL : 0 < L := sub_pos.mpr (Real.log_lt_log hx hxy)
  have hlow := Real.log_le_sub_one_of_pos (div_pos hx hy)
  have hhigh := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hx.ne' hy.ne'] at hlow
  rw [Real.log_div hy.ne' hx.ne'] at hhigh
  refine ⟨(x⁻¹-y⁻¹)/L,div_nonneg (sub_nonneg.mpr (inv_anti₀ hx hxy.le)) hL.le,?_,?_,
    (div_mul_cancel₀ _ hL.ne').symm⟩
  · rw [← mul_div_assoc,div_le_one hL,mul_sub,mul_inv_cancel₀ hx.ne',← div_eq_mul_inv]
    dsimp only [L]
    linarith only [hlow]
  · rw [← mul_div_assoc,le_div_iff₀ hL,one_mul,mul_sub,mul_inv_cancel₀ hy.ne',← div_eq_mul_inv]
    exact hhigh

private theorem kernel_cell_difference {n : ℕ} (hn : 1 ≤ n) {x y : ℝ}
    (hx : (n:ℝ) ≤ x) (hxy : x ≤ y) (hy : y ≤ (n:ℝ)+1) :
    primeMeanKernel y - primeMeanKernel x =
      ((n%2:ℕ):ℝ)*(Real.log y-Real.log x) + firstMoment n*((y⁻¹-x⁻¹)/2) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hx0 := hn0.trans_le hx
  have hy0 := hx0.trans_le hxy
  rw [primeMeanKernel,arithmeticKernel_on_unit_interval _ _ (test_zero le_rfl) (hx.trans hxy) hy,
    arithmeticKernel_on_unit_interval _ _ (test_zero le_rfl) hx (hxy.trans hy),← sum_sub_distrib,
    ← prefix_alternatingDivisorCoeff,firstMoment,sum_mul,sum_mul,← sum_add_distrib]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
  have hdx : (d:ℝ) ≤ x := (show (d:ℝ) ≤ n by exact_mod_cast (mem_Icc.mp hd).2).trans hx
  rw [test_of_one_le ((one_le_div hd0).mpr (hdx.trans hxy)),test_of_one_le ((one_le_div hd0).mpr hdx),
    Real.log_div hx0.ne' hd0.ne',Real.log_div hy0.ne' hd0.ne']
  simp only [smul_eq_mul,inv_div]
  simp only [div_eq_mul_inv]
  ring

private theorem cell_slope_bounds {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r)
    (hlo : (n:ℝ)*r ≤ 1) (hhi : 1 ≤ ((n:ℝ)+1)*r) :
    1/6 ≤ ((n%2:ℕ):ℝ) - firstMoment n*r/2 ∧
      ((n%2:ℕ):ℝ) - firstMoment n*r/2 ≤ 3/4 := by
  let k := n/2
  rcases (show n = 2*k ∨ n = 2*k+1 by dsimp only [k]; omega) with he | ho
  · have hk : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    rw [he,(firstMoment_pair k).1,show (2*k)%2=0 by omega,Nat.cast_zero]
    rw [he,Nat.cast_mul,Nat.cast_ofNat] at hlo hhi
    have hh := le_mul_of_one_le_left hr hk
    constructor <;> nlinarith only [hlo,hhi,hh]
  · rw [ho,(firstMoment_pair k).2,show (2*k+1)%2=1 by omega,Nat.cast_one]
    rw [ho,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] at hlo hhi
    have hkr := mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) hr
    constructor <;> nlinarith only [hlo,hhi,hkr]

/-- The alternating test has positive increments comparable to logarithmic distance. -/
theorem primeMeanKernel_increment_bounds {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (Real.log y-Real.log x)/6 ≤ primeMeanKernel y-primeMeanKernel x ∧
      primeMeanKernel y-primeMeanKernel x ≤ 3*(Real.log y-Real.log x)/4 := by
  apply of_adjacent_unit_intervals (P := fun u v =>
    (Real.log v-Real.log u)/6 ≤ primeMeanKernel v-primeMeanKernel u ∧
    primeMeanKernel v-primeMeanKernel u ≤ 3*(Real.log v-Real.log u)/4) _ _ hx hxy
  · intro n hn u v hnu huv hvn
    rcases huv.lt_or_eq with hlt | rfl
    · have hu : 0 < u := lt_of_lt_of_le (by exact_mod_cast hn : (0:ℝ) < n) hnu
      obtain ⟨r,hr,hur,hvr,hrec⟩ := reciprocal_log_slope hu hlt
      have hbounds := cell_slope_bounds hn hr
        ((mul_le_mul_of_nonneg_right hnu hr).trans hur)
        (hvr.trans (mul_le_mul_of_nonneg_right hvn hr))
      have hlog := (Real.log_lt_log hu hlt).le
      rw [kernel_cell_difference hn hnu hlt.le hvn,show v⁻¹-u⁻¹ = -(r*(Real.log v-Real.log u)) by linarith only [hrec]]
      constructor <;> nlinarith only [mul_le_mul_of_nonneg_right hbounds.1 (sub_nonneg.mpr hlog),
        mul_le_mul_of_nonneg_right hbounds.2 (sub_nonneg.mpr hlog)]
    · simp
  · intro u v z huv hvz
    constructor <;> linarith only [huv.1,huv.2,hvz.1,hvz.2]

/-- Difference of the positive kernel at consecutive integer divisors. -/
def primeMeanWeight (N n : ℕ) : ℝ :=
  primeMeanKernel ((N:ℝ)/n) - primeMeanKernel ((N:ℝ)/(n+1))

private theorem log_dilation_gap {N n : ℕ} (hn : 1 ≤ n) (hnN : n < N) :
    1/(n+1:ℝ) ≤ Real.log ((N:ℝ)/n)-Real.log ((N:ℝ)/(n+1)) ∧
      Real.log ((N:ℝ)/n)-Real.log ((N:ℝ)/(n+1)) ≤ 1/n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs : 0 < (n:ℝ)+1 := by positivity
  rw [Real.log_div hN0.ne' hn0.ne',Real.log_div hN0.ne' hs.ne']
  have hl := Real.log_le_sub_one_of_pos (div_pos hn0 hs)
  have hu := Real.log_le_sub_one_of_pos (div_pos hs hn0)
  rw [Real.log_div hn0.ne' hs.ne',show (n:ℝ)/(n+1)-1= -(1/(n+1)) by field_simp; ring] at hl
  rw [Real.log_div hs.ne' hn0.ne',show ((n:ℝ)+1)/n-1=1/n by field_simp; ring] at hu
  constructor <;> linarith only [hl,hu]

private theorem cutoff_ratios {N n : ℕ} (hn : 1 ≤ n) (hnN : n < N) :
    1 ≤ (N:ℝ)/(n+1) ∧ (N:ℝ)/(n+1) < (N:ℝ)/n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact ⟨(one_le_div (by positivity)).mpr (by exact_mod_cast hnN),
    div_lt_div_of_pos_left hN0 hn0 (by linarith)⟩

/-- Strictly positive harmonic-size weights at all interior divisors. -/
theorem primeMeanWeight_bounds {N n : ℕ} (hn : 1 ≤ n) (hnN : n < N) :
    (1/(n+1:ℝ))/6 ≤ primeMeanWeight N n ∧ primeMeanWeight N n ≤ (3/4)*(1/n) := by
  have ⟨hx,hy⟩ := cutoff_ratios hn hnN
  have hb := primeMeanKernel_increment_bounds hx hy.le
  have hl := log_dilation_gap hn hnN
  unfold primeMeanWeight
  constructor <;> linarith only [hb.1,hb.2,hl.1,hl.2]

private theorem abs_test_increment_le {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    |primeMeanTest ((N:ℝ)/n)-primeMeanTest ((N:ℝ)/(n+1))| ≤ 1/n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rcases hnN.lt_or_eq with h | rfl
  · let x := (N:ℝ)/(n+1)
    let y := (N:ℝ)/n
    obtain ⟨hx,hy⟩ := cutoff_ratios hn h
    change 1 ≤ x at hx
    change x < y at hy
    obtain ⟨r,hr,hxr,-,he⟩ := reciprocal_log_slope (zero_lt_one.trans_le hx) hy
    have hr1 : r ≤ 1 := (le_mul_of_one_le_left hr hx).trans hxr
    have hlog : 0 ≤ Real.log y-Real.log x := sub_nonneg.mpr (Real.log_lt_log (zero_lt_one.trans_le hx) hy).le
    have hmul := mul_le_mul_of_nonneg_right hr1 hlog
    have hpos := mul_nonneg hr hlog
    have hre : x⁻¹-y⁻¹ = r*(Real.log y-Real.log x) := he
    change |primeMeanTest y-primeMeanTest x| ≤ _
    rw [test_of_one_le (hx.trans hy.le),test_of_one_le hx]
    rw [abs_of_nonneg (by linarith only [hre,hmul,hlog])]
    have hupper : Real.log y-Real.log x ≤ 1/n := (log_dilation_gap hn h).2
    linarith only [hre,hpos,hupper]
  · rw [div_self hn0.ne',test_zero le_rfl,test_zero (by rw [div_le_one (by positivity)]; linarith),
      sub_zero,abs_zero]
    positivity

/-- The signed prime error against these positive weights has square-root size. -/
theorem abs_primeMeanWeight_sum_le (N : ℕ) :
    |∑ n ∈ Icc 1 N, (Chebyshev.psi n - n)*primeMeanWeight N n| ≤
      2*(75+2*|Real.eulerMascheroniConstant|)*Real.sqrt N := by
  let B := 75+2*|Real.eulerMascheroniConstant|
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have he : arithmeticKernel alternatingPrimeExcess primeMeanTest N =
      ∑ n ∈ Icc 1 N, (Chebyshev.psi n - n)*primeMeanWeight N n := by
    rw [alternatingPrimeExcess,mul_comm,arithmeticKernel_mul]
    change arithmeticKernel (vonMangoldt-(zeta : ArithmeticFunction ℝ)) primeMeanKernel (N:ℝ) = _
    rw [arithmeticKernel_eq_prefix_differences _ primeMeanKernel (fun _ h => primeMeanKernel_eq_zero h)]
    simp only [sum_vonMangoldt_sub_zeta,smul_eq_mul,primeMeanWeight]
  rw [← he,arithmeticKernel_eq_prefix_differences _ _ (fun _ h => test_zero h)]
  simp only [smul_eq_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc 1 N, B*(n:ℝ)^(-(1/2:ℝ)) := by
      refine sum_le_sum fun n hn => ?_
      have h1 := (mem_Icc.mp hn).1
      have hp : 0 < (n:ℝ) := by exact_mod_cast h1
      rw [abs_mul]
      apply (mul_le_mul (abs_prefix_alternatingPrimeExcess n)
        (abs_test_increment_le h1 (mem_Icc.mp hn).2) (abs_nonneg _) (mul_nonneg hB (Real.sqrt_nonneg _))).trans_eq
      change B*Real.sqrt n*(1/n) = _
      rw [mul_assoc,Real.sqrt_eq_rpow,one_div (n:ℝ),← div_eq_mul_inv,← Real.rpow_sub_one hp.ne',
        show (1/2:ℝ)-1 = -(1/2) by ring]
    _ ≤ _ := by
      rw [← mul_sum]
      have hb := mul_le_mul_of_nonneg_left (_root_.RHTower.sum_rpow_neg_half_le N) hB
      exact hb.trans_eq (by dsimp only [B]; ring)

#print axioms abs_primeMeanWeight_sum_le
#print axioms primeMeanWeight_bounds
#print axioms primeMeanKernel_increment_bounds

end GaloisForLFunctions.ExceptionalLayerTheory
