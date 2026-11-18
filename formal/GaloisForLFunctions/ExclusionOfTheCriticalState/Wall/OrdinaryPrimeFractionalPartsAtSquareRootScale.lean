import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.TheFractionalPartAverageOfTheMangoldtMeasure
import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.TheLogarithmicFloorKernelOnTheCriticalStrip
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.DilatingTheOrdinaryPrimeMeasure
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheProperPrimePowersInThePrimeWave
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.LogarithmicMangoldtTail
import GaloisForLFunctions.HTGeometry.ReflectionIntegral
import GaloisForLFunctions.RHTower.ZetaGateProductAFEMainTermInputs
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap

/-!
# Fractional parts over ordinary primes at square-root scale

The factorial remainder of the full Mangoldt measure costs only a logarithm.
Upon removing the higher powers, prime squares produce a signed secondary
term of square-root size. Its coefficient is the real value of zeta at one half.
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset ArithmeticFunction
open scoped FourierTransform
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticOfSquareRootPrecision HTGeometry ArithmeticHodgeTheoryOfDegenerations
  CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri _root_.RHTower

/-- Natural cutoff of the polar-subtracted ordinary-prime fractional-part sum. -/
def ordinaryFractionalPrimeError (x Y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 0 ⌊Y⌋₊, if n.Prime then Real.log n*Int.fract (x/n) else 0) -
    x*(Real.log Y-Real.log x+1-Real.eulerMascheroniConstant)

private def omittedPower (x : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then 0 else vonMangoldt n*Int.fract (x/n)

private theorem fract_le_arg {u : ℝ} (hu : 0 ≤ u) : Int.fract u ≤ u := by
  rw [Int.fract]; exact sub_le_self _ (by exact_mod_cast Int.floor_nonneg.mpr hu)

private theorem omittedPower_summable {x : ℝ} (hx : 0 ≤ x) : Summable (omittedPower x) := by
  apply Summable.of_nonneg_of_le _ _ (RenormalizedIntersectionArithmeticCounts.summable_nonprime_mangoldt_reciprocal.mul_left x)
  · intro n; unfold omittedPower; split_ifs
    · exact le_rfl
    · exact mul_nonneg vonMangoldt_nonneg (Int.fract_nonneg _)
  · intro n
    by_cases h : n.Prime
    · simp only [omittedPower,if_pos h,mul_zero,le_refl]
    · simp only [omittedPower,if_neg h]
      exact (mul_le_mul_of_nonneg_left (fract_le_arg (div_nonneg hx (Nat.cast_nonneg n))) vonMangoldt_nonneg).trans_eq (by ring)

/-- The limit at a fixed observation point after subtracting all proper prime powers. -/
def ordinaryFractionalPrimeLimit (x : ℝ) : ℝ :=
  stirlingMain x-Real.log ((⌊x⌋₊).factorial : ℕ)-∑' n, omittedPower x n

/-- The linear coefficient in the summatory logarithm of the radical counts repeated prime factors. -/
theorem ordinaryFractionalPrimeLimit_one :
    ordinaryFractionalPrimeLimit 1 = -1-∑' n : ℕ, if n.Prime then (0:ℝ) else vonMangoldt n/n := by
  have h (n : ℕ) : omittedPower 1 n = if n.Prime then 0 else vonMangoldt n/(n:ℝ) := by
    by_cases hp : n.Prime
    · simp only [omittedPower,if_pos hp]
    by_cases hn : 2 ≤ n
    · have hn1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      rw [omittedPower,if_neg hp,if_neg hp,Int.fract_eq_self.mpr
        ⟨by positivity,(div_lt_one (zero_lt_one.trans hn1)).mpr hn1⟩]
      ring
    · rcases (show n=0 ∨ n=1 by omega) with rfl | rfl <;> simp [omittedPower]
  rw [ordinaryFractionalPrimeLimit,tsum_congr h]
  norm_num [stirlingMain]

theorem tendsto_ordinaryFractionalPrimeError {x : ℝ} (hx : 1 ≤ x) :
    Tendsto (ordinaryFractionalPrimeError x) atTop (𝓝 (ordinaryFractionalPrimeLimit x)) := by
  have h := (omittedPower_summable (zero_le_one.trans hx)).hasSum.tendsto_sum_nat
  have hcut : Tendsto (fun Y : ℝ => ⌊Y⌋₊+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop
  apply ((tendsto_fractionalMangoldtError hx).1.sub (h.comp hcut)).congr' (Eventually.of_forall fun Y => ?_)
  have hset : range (⌊Y⌋₊+1) = Finset.Icc 0 ⌊Y⌋₊ := by
    ext n; simp only [Finset.mem_range,Nat.lt_succ_iff,Finset.mem_Icc,Nat.zero_le,true_and]
  change fractionalMangoldtError x Y-(∑ n ∈ range (⌊Y⌋₊+1), omittedPower x n)=_
  unfold fractionalMangoldtError ordinaryFractionalPrimeError
  rw [hset,sub_right_comm,← sum_sub_distrib]
  apply congrArg (· - x*(Real.log Y-Real.log x+1-Real.eulerMascheroniConstant))
  refine sum_congr rfl fun n _ => ?_
  by_cases hp : n.Prime
  · simp only [omittedPower,if_pos hp,sub_zero,vonMangoldt_apply_prime hp]
  · simp only [omittedPower,if_neg hp,sub_self]

/-- Prime squares sample this test on the rescaled prime axis. -/
private def squareFract (u : ℝ) : ℝ := Int.fract (u⁻¹^2)

private theorem squareFract_continuous_ae :
    ∀ᵐ u ∂volume.restrict (Set.Ioi (0:ℝ)), ContinuousAt squareFract u := by
  have hskip : ∀ᵐ u ∂(volume : Measure ℝ), ∀ n : ℤ, u ≠ (Real.sqrt (n:ℝ))⁻¹ :=
    ae_all_iff.mpr fun _ => by rw [ae_iff]; simp
  filter_upwards [ae_restrict_of_ae hskip,ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hskip hu
  have hu0 : 0 < u := hu
  apply (Int.continuousAt_fract (x := u⁻¹^2) ?_).comp (by fun_prop (disch := positivity))
  intro h
  apply hskip ⌊u⁻¹^2⌋
  rw [← h,Real.sqrt_sq (inv_nonneg.mpr hu0.le),inv_inv]

private theorem squareFract_bound (u : ℝ) (hu : 0 ≤ u) : |squareFract u| ≤ 2/(1+u^2) := by
  rw [squareFract,abs_of_nonneg (Int.fract_nonneg _)]
  rcases le_or_gt u 1 with h | h
  · apply (Int.fract_lt_one _).le.trans
    rw [le_div_iff₀ (by positivity),one_mul]
    linarith only [pow_le_pow_left₀ hu h 2,one_pow 2]
  · apply (fract_le_arg (sq_nonneg _)).trans
    rw [inv_pow,inv_eq_one_div,div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [sq_nonneg (u-1),h]

/-- The test has Mellin mass minus zeta at one half. -/
private theorem integral_squareFract : (∫ u in Set.Ici (0:ℝ), squareFract u) = -(riemannZeta (1/2)).re := by
  let f := weightedFloorDiscrepancy (1/2)
  have hF := fourier_weightedFloorDiscrepancy (σ := 1/2) (by norm_num) (by norm_num) 0
  have hfreq : (∫ v, (f v:ℂ))=2*riemannZeta (1/2) := by
    simpa [f,Real.fourier_real_eq_integral_exp_smul,div_eq_mul_inv,mul_comm] using hF
  have hf : (∫ v, f v) = 2*(riemannZeta (1/2)).re := by
    rw [integral_complex_ofReal] at hfreq
    simpa using congrArg Complex.re hfreq
  rw [integral_Ici_eq_integral_Ioi,HTGeometry.integral_Ioi_comp_exp]
  have hpt (v : ℝ) : Real.exp v*squareFract (Real.exp v) = -f ((-2)*v) := by
    rw [squareFract, show (Real.exp v)⁻¹^2 = Real.exp ((-2)*v) by
      rw [← Real.exp_neg,pow_two,← Real.exp_add]; congr 1; ring]
    dsimp only [f,weightedFloorDiscrepancy]
    rw [neg_mul,neg_neg,show -(1/2:ℝ)*((-2)*v)=v by ring]
  simp_rw [hpt,integral_neg,Measure.integral_comp_mul_left,hf,smul_eq_mul]
  norm_num
  <;> ring

private theorem square_prime_fractional_limit :
    Tendsto (fun y : ℝ => (∑' p : Nat.Primes, Real.log (p:ℕ)*Int.fract ((y/(p:ℕ))^2))/y)
      atTop (𝓝 (-(riemannZeta (1/2)).re)) := by
  have h := tendsto_dilated_ordinary_prime_sum_ae
    (g := squareFract) (measurable_fract.comp (by fun_prop)) squareFract_continuous_ae
    (by norm_num : (0:ℝ) ≤ 2) squareFract_bound
  simpa only [integral_squareFract,squareFract,inv_div] using h

private abbrev highIndex (j : Nat.Primes × ℕ) := (j.1:ℕ)^(j.2+3)

private theorem omitted_at_power (y : ℝ) (j : Nat.Primes × ℕ) :
    omittedPower (y^2) (properPrimePowerIndex j) =
      vonMangoldt (properPrimePowerIndex j)*Int.fract (y^2/(properPrimePowerIndex j:ℕ)) :=
  if_neg (Nat.Prime.not_prime_pow (by omega : 2 ≤ j.2+2))

private theorem power_partition (y : ℝ) :
    (∑' n, omittedPower (y^2) n) =
      (∑' p : Nat.Primes, Real.log (p:ℕ)*Int.fract ((y/(p:ℕ))^2))+
      ∑' j : Nat.Primes × ℕ, vonMangoldt (highIndex j)*Int.fract (y^2/(highIndex j:ℕ)) := by
  let a := omittedPower (y^2)
  let f := fun j : Nat.Primes × ℕ => a (properPrimePowerIndex j)
  have ha : Summable a := omittedPower_summable (sq_nonneg y)
  have hc : Summable (fun n => (a n:ℂ)) := Complex.ofRealCLM.hasSum ha.hasSum |>.summable
  have hs := tsum_eq_ordinary_primes_add_proper_powers hc (fun n hn => by
    by_contra hz
    apply hn
    dsimp only [a,omittedPower]
    rw [vonMangoldt_eq_zero_iff.mpr hz,zero_mul,ite_self,Complex.ofReal_zero])
  have hp (p : Nat.Primes) : a p=0 := if_pos p.property
  simp only [hp,Complex.ofReal_zero,tsum_zero,zero_add,← Complex.ofReal_tsum] at hs
  have htotal : (∑' n, a n) = ∑' j, f j := Complex.ofReal_injective hs
  have hshift : Function.Injective (fun j : Nat.Primes × ℕ => (j.1,j.2+1)) := by
    rintro ⟨p,l⟩ ⟨q,k⟩ h
    exact Prod.ext (congrArg Prod.fst h) (Nat.succ.inj (congrArg Prod.snd h))
  have hf : Summable f := (ha.comp_injective eulerPrimePowerNat_injective).comp_injective hshift
  have hg := hf.comp_injective hshift
  have hhead := hf.comp_injective (i := fun p : Nat.Primes => (p,0)) (fun _ _ h => congrArg Prod.fst h)
  have hsplit (p : Nat.Primes) : (∑' j, f (p,j))=f (p,0)+∑' j, f (p,j+1) :=
    (hf.comp_injective (i := fun j : ℕ => (p,j)) (fun _ _ h => congrArg Prod.snd h)).tsum_eq_zero_add
  have hsq (p : Nat.Primes) : f (p,0)=Real.log (p:ℕ)*Int.fract ((y/(p:ℕ))^2) := by
    rw [show f (p,0)=_ from omitted_at_power y (p,0)]
    change vonMangoldt ((p:ℕ)^2)*Int.fract (y^2/(((p:ℕ)^2:ℕ):ℝ))=_
    rw [vonMangoldt_apply_pow (by decide),vonMangoldt_apply_prime p.property,Nat.cast_pow,div_pow]
  have hl (j : Nat.Primes × ℕ) : f (j.1,j.2+1)=
      vonMangoldt (highIndex j)*Int.fract (y^2/(highIndex j:ℕ)) := omitted_at_power y (j.1,j.2+1)
  change (∑' n, a n)=_
  rw [htotal,hf.tsum_prod]
  simp_rw [hsplit]
  rw [hhead.tsum_add hg.prod,← hg.tsum_prod]
  exact congrArg₂ HAdd.hAdd (tsum_congr hsq) (tsum_congr hl)

private theorem higher_powers_vanish :
    Tendsto (fun y : ℝ =>
      (∑' j : Nat.Primes × ℕ, vonMangoldt (highIndex j)*Int.fract (y^2/(highIndex j:ℕ)))/y)
      atTop (𝓝 0) := by
  let v := fun (y : ℝ) (j : Nat.Primes × ℕ) =>
    vonMangoldt (highIndex j)*Int.fract (y^2/(highIndex j:ℕ))/y
  have ha : Summable (fun j : Nat.Primes × ℕ => |vonMangoldtAtom (highIndex j)|) := by
    have h := (summable_xiPrimeLogHigherValuationThreePlus_term (s := 1/2-0)
      (by norm_num : (1:ℝ)/3 < ((1:ℂ)/2-0).re)).norm
    refine h.congr fun j => ?_
    rw [← vonMangoldtAtom_mul_cexp_eq_term 0]
    simp only [zero_mul,Complex.exp_zero,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have hlim (j : Nat.Primes × ℕ) : Tendsto (fun y => v y j) atTop (𝓝 0) := by
    have hu : Tendsto (fun y : ℝ => vonMangoldt (highIndex j)/y) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero' ((eventually_gt_atTop (0:ℝ)).mono fun y hy =>
      div_nonneg (mul_nonneg vonMangoldt_nonneg (Int.fract_nonneg _)) hy.le) ?_ hu
    filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right vonMangoldt_nonneg (Int.fract_lt_one _).le) hy.le
  have hdom : ∀ᶠ y : ℝ in atTop, ∀ j : Nat.Primes × ℕ, ‖v y j‖ ≤ |vonMangoldtAtom (highIndex j)| := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    intro j
    let n := highIndex j
    have hn2 : 2 ≤ n := j.1.property.two_le.trans (Nat.le_self_pow (by omega : j.2+3≠0) _)
    have hn : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
    have hroot := Real.sqrt_pos.mpr hn
    let w := y/Real.sqrt n
    have hw : 0 ≤ w := div_nonneg hy.le hroot.le
    have hh : Int.fract (w^2) ≤ w := by
      rcases le_or_gt w 1 with h | h
      · exact (fract_le_arg (sq_nonneg w)).trans (by nlinarith only [mul_nonneg hw (sub_nonneg.mpr h)])
      · exact (Int.fract_lt_one _).le.trans h.le
    have he : w^2=y^2/n := by rw [show w=y/Real.sqrt n from rfl,div_pow,Real.sq_sqrt hn.le]
    rw [he] at hh
    change ‖vonMangoldt n*Int.fract (y^2/n)/y‖ ≤ |vonMangoldtAtom n|
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (mul_nonneg vonMangoldt_nonneg (Int.fract_nonneg _)) hy.le),
      vonMangoldtAtom,if_pos hn2,abs_of_nonneg (div_nonneg vonMangoldt_nonneg hroot.le)]
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh vonMangoldt_nonneg) hy.le).trans_eq
    dsimp only [w]; field_simp [hy.ne',hroot.ne']
  have h := tendsto_tsum_of_dominated_convergence (f := v) (g := fun _ => (0:ℝ)) ha hlim hdom
  simpa only [v,tsum_div_const,tsum_zero] using h

/-- After ordinary-prime truncation tends to infinity, the full
square-root secondary term is ζ(1/2). The only surviving layer is prime squares. -/
theorem tendsto_ordinaryFractionalPrimeLimit_div_sqrt :
    Tendsto (fun x : ℝ => ordinaryFractionalPrimeLimit x/Real.sqrt x) atTop
      (𝓝 (riemannZeta (1/2)).re) := by
  have hpow : Tendsto (fun y : ℝ => (∑' n, omittedPower (y^2) n)/y) atTop
      (𝓝 (-(riemannZeta (1/2)).re)) := by
    have h := square_prime_fractional_limit.add higher_powers_vanish
    simpa only [power_partition,add_div,add_zero] using h
  have hs : Tendsto (fun y : ℝ => (stirlingMain (y^2)-Real.log ((⌊y^2⌋₊).factorial : ℕ))/y)
      atTop (𝓝 0) := by
    have hlog : Tendsto (fun y : ℝ => Real.log y/y) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h1 : Tendsto (fun y : ℝ => 1/y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have hbound : Tendsto (fun y : ℝ => 1/y+2*(Real.log y/y)) atTop (𝓝 0) := by
      simpa only [mul_zero,add_zero] using h1.add (hlog.const_mul 2)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hbound
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    rw [abs_div,abs_of_pos (zero_lt_one.trans_le hy)]
    have hh := (tendsto_fractionalMangoldtError (one_le_pow₀ hy (n := 2))).2
    rw [Real.log_pow] at hh
    exact (div_le_div_of_nonneg_right hh (zero_le_one.trans hy)).trans_eq (by push_cast; ring)
  have h := (hs.sub hpow).comp Real.tendsto_sqrt_atTop
  rw [zero_sub,neg_neg] at h
  apply h.congr' ((eventually_ge_atTop (0:ℝ)).mono fun x hx => ?_)
  change (stirlingMain ((Real.sqrt x)^2)-_)/_ - _ /_ = _
  rw [Real.sq_sqrt hx,ordinaryFractionalPrimeLimit,sub_div]

/-- Ordinary primes give a strictly negative renormalized sum at every sufficiently large point. -/
theorem eventually_ordinaryFractionalPrimeLimit_neg :
    ∀ᶠ x : ℝ in atTop, ordinaryFractionalPrimeLimit x < 0 := by
  have hζ : (riemannZeta (1/2)).re < 0 := by
    simpa using (_root_.RHTower.re_riemannZeta_ofReal_neg (σ := 1/2) (by norm_num) (by norm_num))
  filter_upwards [tendsto_ordinaryFractionalPrimeLimit_div_sqrt.eventually_lt_const hζ,
    eventually_gt_atTop (0:ℝ)] with x hx hx0
  have h := (div_lt_iff₀ (Real.sqrt_pos.mpr hx0)).mp hx
  simpa only [zero_mul] using h

/-- Sum of the logarithms of the distinct prime factors, counted once for each integer up to N. -/
def summatoryLogRadical (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ p ∈ m.primeFactors, Real.log p

private theorem log_radical_floor_sum (N M : ℕ) (hNM : N ≤ M) :
    (∑ p ∈ Finset.Icc 0 M, if p.Prime then Real.log p*((N/p:ℕ):ℝ) else 0) =
      summatoryLogRadical N := by
  let w := fun p : ℕ => if p.Prime then Real.log p else 0
  have hd (m : ℕ) : (∑ p ∈ m.primeFactors, Real.log p) = ∑ p ∈ m.divisors, w p := by
    rw [Nat.primeFactors_eq_to_filter_divisors_prime,Finset.sum_filter]
  have hI : Finset.Icc 1 N ⊆ Finset.Icc 0 M :=
    fun _ hp => Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Icc.mp hp).2.trans hNM⟩
  calc _ = ∑ p ∈ Finset.Icc 0 M, w p*((N/p:ℕ):ℝ) := by
             refine Finset.sum_congr rfl fun p _ => ?_
             by_cases hp : p.Prime <;> simp [w,hp]
    _ = ∑ p ∈ Finset.Icc 1 N, w p*((N/p:ℕ):ℝ) := by
             symm
             apply Finset.sum_subset hI
             intro p _ hp
             rcases Nat.eq_zero_or_pos p with rfl | hpos
             · simp
             have hlt : N < p := lt_of_not_ge fun h => hp (Finset.mem_Icc.mpr ⟨hpos,h⟩)
             rw [Nat.div_eq_of_lt hlt,Nat.cast_zero,mul_zero]
    _ = summatoryLogRadical N := by
             unfold summatoryLogRadical
             simp_rw [hd]
             rw [_root_.RHTower.Sieve.sum_divisors_swap N (fun p _ => w p)]
             apply Finset.sum_congr rfl fun p _ => ?_
             simp [Nat.card_Icc,mul_comm]

/-- Subtraction at one eliminates the reciprocal-prime term at every common cutoff. -/
theorem ordinaryFractionalPrimeLimit_nat {N : ℕ} (hN : 1 ≤ N) :
    ordinaryFractionalPrimeLimit N =
      (N:ℝ)*(Real.log N+ordinaryFractionalPrimeLimit 1)-summatoryLogRadical N := by
  have hlim := ((tendsto_ordinaryFractionalPrimeError (by exact_mod_cast hN : (1:ℝ) ≤ N)).sub
    ((tendsto_ordinaryFractionalPrimeError (x := 1) le_rfl).const_mul (N:ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hpoint (M : ℕ) (hM : N ≤ M) :
      ordinaryFractionalPrimeError N M-(N:ℝ)*ordinaryFractionalPrimeError 1 M =
        (N:ℝ)*Real.log N-summatoryLogRadical N := by
    have hp (p : ℕ) :
        (if p.Prime then Real.log p*Int.fract ((N:ℝ)/p) else 0)-
          (N:ℝ)*(if p.Prime then Real.log p*Int.fract (1/(p:ℝ)) else 0) =
        -(if p.Prime then Real.log p*((N/p:ℕ):ℝ) else 0) := by
      by_cases h : p.Prime
      · have hp1 : (1:ℝ) < p := by exact_mod_cast h.one_lt
        rw [if_pos h,if_pos h,if_pos h,Int.fract_eq_self.mpr
          ⟨by positivity, (div_lt_one (zero_lt_one.trans hp1)).mpr hp1⟩,
          Int.fract,← natCast_floor_eq_intCast_floor (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg p)),
          Nat.floor_div_natCast,Nat.floor_natCast]
        ring
      · simp [h]
    have hsum : (∑ p ∈ Finset.Icc 0 M, if p.Prime then Real.log p*Int.fract ((N:ℝ)/p) else 0)-
        (N:ℝ)*(∑ p ∈ Finset.Icc 0 M, if p.Prime then Real.log p*Int.fract (1/(p:ℝ)) else 0) =
        -summatoryLogRadical N := by
      rw [Finset.mul_sum,← Finset.sum_sub_distrib]
      simp_rw [hp]
      rw [Finset.sum_neg_distrib,log_radical_floor_sum N M hM]
    simp only [ordinaryFractionalPrimeError,Nat.floor_natCast,Real.log_one,sub_zero,one_mul]
    linear_combination hsum
  have he := tendsto_nhds_unique hlim ((tendsto_const_nhds : Tendsto
    (fun _ : ℕ => (N:ℝ)*Real.log N-summatoryLogRadical N) atTop _).congr'
      ((eventually_ge_atTop N).mono fun M hM => (hpoint M hM).symm))
  change ordinaryFractionalPrimeLimit N-(N:ℝ)*ordinaryFractionalPrimeLimit 1 = _ at he
  linarith only [he]

/-- The sharp summatory logarithm of the radical has a positive square-root secondary term. -/
theorem tendsto_summatoryLogRadical_secondary :
    Tendsto (fun N : ℕ =>
      (summatoryLogRadical N-(N:ℝ)*(Real.log N+ordinaryFractionalPrimeLimit 1))/Real.sqrt N)
      atTop (𝓝 (-(riemannZeta (1/2)).re)) := by
  refine (tendsto_ordinaryFractionalPrimeLimit_div_sqrt.neg.comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  change -(ordinaryFractionalPrimeLimit N/Real.sqrt N) = _
  rw [ordinaryFractionalPrimeLimit_nat hN]
  ring

#print axioms tendsto_summatoryLogRadical_secondary
#print axioms eventually_ordinaryFractionalPrimeLimit_neg
#print axioms tendsto_ordinaryFractionalPrimeLimit_div_sqrt
#print axioms tendsto_ordinaryFractionalPrimeError
#print axioms square_prime_fractional_limit
end GaloisForLFunctions.ExclusionOfTheCriticalState
