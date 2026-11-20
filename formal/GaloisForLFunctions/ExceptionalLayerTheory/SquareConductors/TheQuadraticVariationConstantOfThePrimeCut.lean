import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFineVariationOfTheCenteredPrimeCut
import GaloisForLFunctions.RHTower.PrimeRpowLogSumAsymptotic

/-!
# The leading constant of the quadratic variation of the prime cut

On the full integer mesh in the linear part of the conductor spline, the
squared increments of the centered tail have leading term λ² K³ log K / 3.
The additional logarithm comes from the prime jumps. Replacing one prime
logarithm by log K costs only O(K³), uniformly in the conductor.
-/

noncomputable section
open Filter Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def primeStepLog (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

private def cutPrimeSecondMoment (K : ℕ) : ℝ :=
  ∑ k ∈ range K, (↑(k+1):ℝ)^2*primeStepLog (k+1)

private theorem prime_second_moment_limit :
    Tendsto (fun K : ℕ => cutPrimeSecondMoment K/(K:ℝ)^3) atTop (𝓝 (1/3:ℝ)) := by
  let f (n : ℕ) : ℝ := (n:ℝ)^2*primeStepLog n
  let b := ∑ n ∈ range 3, f n
  have prime := (_root_.RHTower.tendsto_primeRpowLogSumIoc (by norm_num : (0:ℝ)<3)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have grow : Tendsto (fun n : ℕ => (n:ℝ)^(3:ℕ)) atTop atTop := by
    simpa only [Function.comp_def,Real.rpow_natCast] using
      ((tendsto_rpow_atTop (show (0:ℝ)<(3:ℕ) by norm_num)).comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have small : Tendsto (fun n : ℕ => b/(n:ℝ)^3) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using grow.inv_tendsto_atTop.const_mul b
  have main : Tendsto (fun n : ℕ => _root_.RHTower.primeRpowLogSumIoc 3 n/(n:ℝ)^3)
      atTop (𝓝 (1/3:ℝ)) := by
    simpa only [Function.comp_def,show (3:ℝ)=((3:ℕ):ℝ) by norm_num,Real.rpow_natCast] using prime
  apply (show Tendsto (fun n : ℕ => _root_.RHTower.primeRpowLogSumIoc 3 n/(n:ℝ)^3+b/(n:ℝ)^3)
    atTop (𝓝 (1/3:ℝ)) by simpa only [add_zero] using main.add small).congr'
  filter_upwards [eventually_ge_atTop 2] with K hk
  have whole : Ioc 2 K ∪ range 3=range (K+1) := by
    ext n
    simp only [mem_union,mem_Ioc,mem_range]
    omega
  have apart : Disjoint (Ioc 2 K) (range 3) := by
    apply disjoint_left.mpr
    intro n h j
    have := (mem_Ioc.mp h).1
    have := mem_range.mp j
    omega
  have high : _root_.RHTower.primeRpowLogSumIoc 3 K=∑ n ∈ Ioc 2 K,f n := by
    rw [_root_.RHTower.primeRpowLogSumIoc,Nat.floor_natCast]
    refine sum_congr rfl fun n _ => ?_
    dsimp only [f,primeStepLog]
    rw [show (3:ℝ)-1=2 by norm_num,Real.rpow_two]
    split_ifs <;> simp
  have all := sum_union (f:=f) apart
  rw [whole,sum_range_succ',show f 0=0 by simp [f],add_zero] at all
  rw [←add_div,high]
  exact congrArg (fun x : ℝ => x/(K:ℝ)^3) all.symm

-- The log gap costs at most K/n, which absorbs one missing prime logarithm.
private theorem square_jump_remainder {n K : ℕ} (hn : 0<n) (hnK : n≤K) :
    |(n:ℝ)^2*(1-primeStepLog n)^2-Real.log K*((n:ℝ)^2*primeStepLog n)|≤
      (K:ℝ)^2*(1+3*primeStepLog n) := by
  have np : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have nk : (n:ℝ)≤K := Nat.cast_le.mpr hnK
  have kp := np.trans_le nk
  have n2 := pow_le_pow_left₀ np.le nk 2
  by_cases hp : n.Prime
  · rw [primeStepLog,if_pos hp]
    have w := Real.log_natCast_nonneg n
    have left := Real.log_le_log np nk
    have step := Real.log_le_sub_one_of_pos (div_pos kp np)
    rw [Real.log_div kp.ne' np.ne'] at step
    have cap := (le_div_iff₀ np).mp (step.trans (sub_le_self _ zero_le_one))
    have down : (n:ℝ)^2*(Real.log K-Real.log n)≤(K:ℝ)^2 := calc
      _ = (n:ℝ)*((Real.log K-Real.log n)*n) := by ring
      _ ≤ n*K := mul_le_mul_of_nonneg_left cap np.le
      _ ≤ _ := by simpa only [sq] using mul_le_mul_of_nonneg_right nk kp.le
    have main := mul_le_mul_of_nonneg_right down w
    have sign := mul_nonneg (mul_nonneg (sq_nonneg (n:ℝ)) (sub_nonneg.mpr left)) w
    have small := mul_le_mul_of_nonneg_right n2 w
    apply abs_le.mpr
    constructor <;> linarith only [main,sign,small,n2,sq_nonneg (n:ℝ),
      mul_nonneg (sq_nonneg (n:ℝ)) w,mul_nonneg (sq_nonneg (K:ℝ)) w]
  · simpa only [primeStepLog,if_neg hp,sub_zero,one_pow,mul_one,mul_zero,add_zero,abs_of_nonneg (sq_nonneg _)] using n2

/-- Replacing one prime logarithm by the cutoff logarithm in the squared
mesh increments has a uniform cubic cost in the entire first spline segment. -/
theorem centered_cut_square_log_remainder {N K : ℕ} (hN : 0<N)
    (hk : (K:ℝ)≤Real.exp (-8)*(N:ℝ)^2) :
    |(∑ k ∈ range K, ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖^2)-
      innerPrimeSlope^2*(Real.log K*cutPrimeSecondMoment K)|≤
      innerPrimeSlope^2*(1+3*Real.log 4)*(K:ℝ)^3 := by
  let f (k : ℕ) : ℝ := (↑(k+1):ℝ)^2*(1-primeStepLog (k+1))^2
  let g (k : ℕ) : ℝ := (↑(k+1):ℝ)^2*primeStepLog (k+1)
  have mesh : (∑ k ∈ range K, ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖^2)=
      innerPrimeSlope^2*(∑ k ∈ range K,f k) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hm => ?_
    have hi := Nat.succ_le_of_lt (mem_range.mp hm)
    rw [centered_fixed_cut_step hN ((Nat.cast_le.mpr hi).trans hk),Complex.norm_real,Real.norm_eq_abs,sq_abs]
    dsimp only [f,innerCutIncrement,primeStepLog]
    ring
  have mass : (∑ k ∈ range K,primeStepLog (k+1))≤(K:ℝ)*Real.log 4 := by
    have full : (∑ n ∈ range (K+1),primeStepLog n)=∑ k ∈ range K,primeStepLog (k+1) := by
      rw [sum_range_succ',show primeStepLog 0=0 by simp [primeStepLog],add_zero]
    rw [←full,primeStepLog,←sum_filter]
    exact _root_.RHTower.Sieve.sum_log_primesLE_le K
  have approx : |(∑ k ∈ range K,f k)-Real.log K*(∑ k ∈ range K,g k)|≤
      (1+3*Real.log 4)*(K:ℝ)^3 := by
    rw [mul_sum,←sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    apply (sum_le_sum (s:=range K) (fun k hk => square_jump_remainder (Nat.succ_pos k)
      (Nat.succ_le_of_lt (mem_range.mp hk)))).trans
    rw [←mul_sum,sum_add_distrib,sum_const,card_range,nsmul_eq_mul,mul_one,←mul_sum]
    linarith only [mul_le_mul_of_nonneg_left mass (sq_nonneg (K:ℝ))]
  rw [mesh,←mul_sub,abs_mul,abs_of_nonneg (sq_nonneg _),mul_assoc]
  exact mul_le_mul_of_nonneg_left approx (sq_nonneg _)

/-- At the prescribed cutoff the unnormalized quadratic variation is
asymptotic to λ² K³ log K / 3. -/
theorem seventeen_ninths_cut_square_variation_constant :
    Tendsto (fun N : ℕ => let K := ⌊(N:ℝ)^(17/9:ℝ)⌋₊
      (∑ k ∈ range K, ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖^2)/
        ((K:ℝ)^3*Real.log K)) atTop (𝓝 (innerPrimeSlope^2/3)) := by
  let K (N : ℕ) := ⌊(N:ℝ)^(17/9:ℝ)⌋₊
  have grow : Tendsto K atTop atTop := tendsto_atTop_mono' atTop
    (seventeen_ninths_inside_first_knot.mono fun _ h => h.1) tendsto_id
  have main := (prime_second_moment_limit.comp grow).const_mul (innerPrimeSlope^2)
  have loggrow := Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow)
  let C := innerPrimeSlope^2*(1+3*Real.log 4)
  have small : Tendsto (fun N : ℕ => C/Real.log (K N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using loggrow.inv_tendsto_atTop.const_mul C
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have half := half_pos hε
  filter_upwards [seventeen_ninths_inside_first_knot,eventually_ge_atTop 2,
    Metric.tendsto_nhds.mp main (ε/2) half,small.eventually_lt_const half] with N geo hn close err
  have two : 2≤K N := hn.trans geo.1
  have x : 1<(K N:ℝ) := by exact_mod_cast (show 1<K N from two)
  have lg := Real.log_pos x
  have cube := pow_pos (zero_lt_one.trans x) 3
  have bound := centered_cut_square_log_remainder (by omega : 0<N) geo.2
  let v := ∑ k ∈ range (K N), ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖^2
  let m := innerPrimeSlope^2*(cutPrimeSecondMoment (K N)/(K N:ℝ)^3)
  have id : v/((K N:ℝ)^3*Real.log (K N))-m=
      (v-innerPrimeSlope^2*(Real.log (K N)*cutPrimeSecondMoment (K N)))/((K N:ℝ)^3*Real.log (K N)) := by
    dsimp only [m]
    field_simp [cube.ne',lg.ne']
  have near : |v/((K N:ℝ)^3*Real.log (K N))-m|≤C/Real.log (K N) := by
    rw [id,abs_div,abs_of_pos (mul_pos cube lg),div_le_div_iff₀ (mul_pos cube lg) lg]
    exact (mul_le_mul_of_nonneg_right bound lg.le).trans_eq (by dsimp only [C]; ring)
  change dist m (innerPrimeSlope^2*(1/3))<ε/2 at close
  rw [show innerPrimeSlope^2*(1/3)=innerPrimeSlope^2/3 by ring] at close
  rw [Real.dist_eq] at close ⊢
  change |v/((K N:ℝ)^3*Real.log (K N))-innerPrimeSlope^2/3|<ε
  have triangle := abs_sub_le (v/((K N:ℝ)^3*Real.log (K N))) m (innerPrimeSlope^2/3)
  linarith only [triangle,near,close,err]

#print axioms centered_cut_square_log_remainder
#print axioms seventeen_ninths_cut_square_variation_constant
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
