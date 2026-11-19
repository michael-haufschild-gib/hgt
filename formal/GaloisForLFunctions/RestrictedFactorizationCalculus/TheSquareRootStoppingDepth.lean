import GaloisForLFunctions.RestrictedFactorizationCalculus.TheExplicitLogSquareRoughSet
import GaloisForLFunctions.RHTower.Sieve.AlmostPrimeGlobalCount
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorProduct

/-!
# The square-root stopping depth of least-prime expansion

A sharp prefix can discard every squarefree vertex with at least
half log X / log log X factors at square-root-plus-epsilon cost.
A growing positive Euler weight controls all terminal signs together.
-/

noncomputable section

open Filter Finset
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Terminal squarefree vertices of prime-factor depth at least k. -/
def terminalAtDepth (k X : ℕ) := (squarefreeOf (Icc 1 X)).filter (fun n => k ≤ n.primeFactors.card)

/-- A positive exponential moment for every terminal depth and every
sharp cutoff, with the true reciprocal prime sum in its exponent. -/
theorem terminal_depth_euler_bound {z : ℝ} (hz : 1 ≤ z) (k X : ℕ) :
    ((terminalAtDepth k X).card:ℝ)*z^k ≤ (X:ℝ)*Real.exp (z*RHTower.Sieve.mertensS X) := by
  let P := Nat.primesLE X
  let M := ∏ p ∈ P,p
  let S := terminalAtDepth k X
  let f := fun n : ℕ => ∏ p ∈ n.primeFactors, z/(p:ℝ)
  have z0 : 0 ≤ z := zero_le_one.trans hz
  have pos (n : ℕ) : 0 ≤ f n := prod_nonneg (fun _ _ => div_nonneg z0 (Nat.cast_nonneg _))
  have prime (p : ℕ) (hp : p ∈ P) := Nat.prime_of_mem_primesLE hp
  have sub : S ⊆ M.divisors := by
    intro n hn
    obtain ⟨hi,_⟩ := mem_filter.mp hn
    obtain ⟨hit,sq⟩ := mem_filter.mp hi
    have nn := (mem_Icc.mp hit).1
    have inc : n.primeFactors ⊆ P := fun p hp => Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_dvd nn (Nat.dvd_of_mem_primeFactors hp)).trans (mem_Icc.mp hit).2,Nat.prime_of_mem_primeFactors hp⟩
    have dvd := prod_dvd_prod_of_subset _ _ id inc
    rw [Nat.prod_primeFactors_of_squarefree sq] at dvd
    exact Nat.mem_divisors.mpr ⟨dvd,(prod_pos (fun p hp => (prime p hp).pos)).ne'⟩
  have point (n : ℕ) (hn : n ∈ S) : z^k ≤ (X:ℝ)*f n := by
    obtain ⟨hi,deep⟩ := mem_filter.mp hn
    obtain ⟨hit,sq⟩ := mem_filter.mp hi
    have small := (Nat.cast_le (α := ℝ)).mpr (mem_Icc.mp hit).2
    have hsum : f n=z^n.primeFactors.card/(n:ℝ) := by
      simp only [f,prod_div_distrib,prod_const,←Nat.cast_prod,Nat.prod_primeFactors_of_squarefree sq]
    rw [hsum,mul_div_assoc',le_div_iff₀ (Nat.cast_pos.mpr (mem_Icc.mp hit).1)]
    exact (mul_le_mul (pow_le_pow_right₀ hz deep) small (Nat.cast_nonneg _) (pow_nonneg z0 _)).trans_eq (mul_comm ..)
  have counted := sum_le_sum point
  simp only [sum_const,nsmul_eq_mul,←mul_sum] at counted
  have whole := RHTower.Sieve.sum_divisors_prod_primes_eq_prod prime (fun p => z/(p:ℝ))
  change (∑ n ∈ M.divisors,f n)=_ at whole
  have bigger := sum_le_sum_of_subset_of_nonneg sub (fun n _ _ => pos n)
  rw [whole] at bigger
  have step (p : ℕ) (_ : p ∈ P) : z/(p:ℝ)+1 ≤ Real.exp (z*(1/p)) := by
    simpa only [mul_one_div] using Real.add_one_le_exp (z/(p:ℝ))
  have euler := Finset.prod_le_prod (fun p (_ : p ∈ P) => add_nonneg (div_nonneg z0 (Nat.cast_nonneg p)) zero_le_one) step
  rw [←Real.exp_sum,←mul_sum] at euler
  exact counted.trans (mul_le_mul_of_nonneg_left (bigger.trans euler) (Nat.cast_nonneg X))

/-- Depth as a fraction of log X / log log X. -/
def stoppingDepth (α : ℝ) (X : ℕ) := ⌈α*Real.log X/Real.log (Real.log X)⌉₊

private theorem price_of_growing_weight {t η : ℝ} (ht : t<1) (hη : 0<η) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop,L^t*(Real.log L+C) ≤ η*L := by
  let r := (1-t)/2
  have hr : 0<r := by dsimp only [r]; linarith only [ht]
  let K := 1/r+|C|
  have growth := (tendsto_rpow_atTop hr).eventually_ge_atTop (K/η)
  filter_upwards [growth,eventually_ge_atTop (1:ℝ)] with L g hL
  have h0 := zero_lt_one.trans_le hL
  have pow1 : 1 ≤ L^r := Real.one_le_rpow hL hr.le
  have bound : Real.log L+C ≤ K*L^r := by
    have h := Real.log_le_rpow_div h0.le hr
    have hh := mul_le_mul_of_nonneg_left pow1 (abs_nonneg C)
    dsimp only [K]; rw [add_mul]; linarith only [h,le_abs_self C,hh]
  have h := (div_le_iff₀ hη).mp g
  have hi := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg h0.le (t+r))
  have eq : t+r+r=1 := by dsimp only [r]; ring
  calc
    L^t*(Real.log L+C) ≤ L^t*(K*L^r) := mul_le_mul_of_nonneg_left bound (Real.rpow_nonneg h0.le _)
    _ = K*L^(t+r) := by rw [Real.rpow_add h0]; ring
    _ ≤ η*(L^(t+r)*L^r) := by linarith only [hi]
    _ = η*L := by rw [←Real.rpow_add h0,eq,Real.rpow_one]

/-- Above any fixed positive fraction α of log X / log log X, the
actual terminal population through X is eventually at most X^(1-a)
for every a<α. -/
theorem terminal_depth_power_saving {α a : ℝ} (hα : 0<α) (ha : 0<a) (hlt : a<α) :
    ∀ᶠ X : ℕ in atTop,((terminalAtDepth (stoppingDepth α X) X).card:ℝ) ≤ (X:ℝ)^(1-a) := by
  let t := (α+a)/(2*α)
  let η := (α-a)/2
  have ht0 : 0<t := div_pos (add_pos hα ha) (by positivity)
  have ht : t<1 := (div_lt_one (by positivity : (0:ℝ)<2*α)).mpr (by linarith only [hlt])
  have hη : 0<η := by dsimp only [η]; linarith only [hlt]
  have calib : t*α=a+η := by dsimp only [t,η]; field_simp; ring
  have logs : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [logs (price_of_growing_weight ht hη RHTower.Sieve.mertensUpperConst),
    logs.eventually_ge_atTop 2,eventually_ge_atTop (2:ℕ)] with X price hL hX
  let L := Real.log (X:ℝ)
  let k := stoppingDepth α X
  have L1 : 1<L := by linarith only [hL]
  have L0 := zero_lt_one.trans L1
  have lpos := Real.log_pos L1
  have X0 : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  let z := L^t
  have z1 : 1 ≤ z := Real.one_le_rpow L1.le ht0.le
  have z0 := zero_lt_one.trans_le z1
  have cost := (mul_le_mul_of_nonneg_left (RHTower.Sieve.mertensS_le_logLog_add hX) z0.le).trans price
  have num := (terminal_depth_euler_bound z1 k X).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr cost) X0.le)
  have den0 := (div_le_iff₀ lpos).mp (Nat.le_ceil (α*L/Real.log L))
  have dk : (a+η)*L ≤ Real.log z*(k:ℝ) := by
    rw [←calib]
    change (t*α)*L ≤ Real.log (L^t)*(k:ℝ)
    rw [Real.log_rpow L0]
    linarith only [mul_le_mul_of_nonneg_left den0 ht0.le]
  have den : Real.exp ((a+η)*L) ≤ z^k := by
    rw [←Real.rpow_natCast,Real.rpow_def_of_pos z0]; exact Real.exp_le_exp.mpr dk
  have weighted := (mul_le_mul_of_nonneg_left den (Nat.cast_nonneg (terminalAtDepth k X).card)).trans num
  apply (mul_le_mul_iff_left₀ (Real.exp_pos ((a+η)*L))).mp
  apply weighted.trans_eq
  calc (X:ℝ)*Real.exp (η*L) = Real.exp L*Real.exp (η*L) := by rw [Real.exp_log X0]
       _ = (X:ℝ)^(1-a)*Real.exp ((a+η)*L) := by
         rw [Real.rpow_def_of_pos X0,←Real.exp_add,←Real.exp_add]
         congr 1
         dsimp only [L]; ring

/-- The exact signed sum of vertices reached before the stopping depth. -/
def shallowSignedPrefix (X : ℕ) :=
  ∑ n ∈ (squarefreeOf (Icc 1 X)).filter (fun n => n.primeFactors.card<stoppingDepth (1/2) X),(μ n:ℝ)

/-- Stopping at half the maximal prime-factor order incurs at most a
square-root-plus-epsilon unsigned error. Only the signed shallow exits
remain to be estimated in the full Mertens criterion. -/
theorem square_root_tail_of_the_least_prime_depth :
    (∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (fun X => ((terminalAtDepth (stoppingDepth (1/2) X) X).card:ℝ))) ∧
    (∀ X,|coprimeMoebiusSum 1 X-shallowSignedPrefix X| ≤
      (terminalAtDepth (stoppingDepth (1/2) X) X).card) := by
  constructor
  · intro ε hε
    let η := min ε (1/4)
    have hp : 0<η := lt_min hε (by norm_num)
    have hq : 0<(1:ℝ)/2-η := by
      have h := min_le_right ε (1/4 : ℝ); dsimp only [η]; linarith only [h]
    apply prefixPower_of_eventual (C := 1) (by simp [terminalAtDepth,squarefreeOf]) (by positivity)
    filter_upwards [terminal_depth_power_saving (by norm_num : (0:ℝ)<1/2) hq (by linarith only [hp]),
      eventually_ge_atTop (1:ℕ)] with X hx hX
    rw [one_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    exact hx.trans (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hX)
      (by linarith only [min_le_left ε (1/4:ℝ)]))
  intro X
  let S := squarefreeOf (Icc 1 X)
  let k := stoppingDepth (1/2) X
  have full : coprimeMoebiusSum 1 X=∑ n ∈ S,(μ n:ℝ) := by
    simp only [coprimeMoebiusSum,coprimeMoebiusIndicator,Nat.coprime_one_left,if_true]
    symm
    apply sum_subset (filter_subset ..)
    intro n hn absent
    rw [moebius_eq_zero_of_not_squarefree (fun h => absent (mem_filter.mpr ⟨hn,h⟩)),Int.cast_zero]
  have eq := sum_filter_add_sum_filter_not S (fun n => n.primeFactors.card<k) (fun n => (μ n:ℝ))
  simp only [not_lt] at eq
  change shallowSignedPrefix X+(∑ n ∈ terminalAtDepth k X,(μ n:ℝ))=_ at eq
  rw [full,←eq,add_sub_cancel_left]
  apply (abs_sum_le_sum_abs ..).trans
  exact (sum_le_sum (fun n (_ : n ∈ terminalAtDepth k X) =>
    (show |(μ n:ℝ)| ≤ 1 by exact_mod_cast (abs_moebius_le_one (n := n))))).trans_eq (by simp)

#print axioms terminal_depth_euler_bound
#print axioms terminal_depth_power_saving
#print axioms square_root_tail_of_the_least_prime_depth

end GaloisForLFunctions.RestrictedFactorizationCalculus
