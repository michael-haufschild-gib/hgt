import GaloisForLFunctions.RestrictedFactorizationCalculus.SmoothCofactorsInEveryQuotientInterval

/-!
# The factorial upper bound for the smooth population

The divisor expansion of log n preserves smooth cofactors at every
small dilation. Above the prime wall only proper powers survive and
their total reciprocal Mangoldt weight is bounded. Iteration divides
by a new factor j on passing the wall y^j.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.Sieve
open scoped Topology Classical
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev smooth (y Z : ℕ) := smoothUpTo (Nat.primesLE y) Z
private abbrev remWeight := RHTower.Mertens.notPrimeVonMangoldt

private theorem rem_nonneg (n : ℕ) : 0 ≤ remWeight n := by
  unfold remWeight RHTower.Mertens.notPrimeVonMangoldt
  split <;> first | exact le_rfl | exact vonMangoldt_nonneg

private def price (y d m : ℕ) : ℝ :=
  (if d ≤ y ∧ m.primeFactors ⊆ Nat.primesLE y then vonMangoldt d else 0)+remWeight d

private theorem price_nonneg (y d m : ℕ) : 0 ≤ price y d m := by
  unfold price
  split <;> first | exact add_nonneg vonMangoldt_nonneg (rem_nonneg _) | simpa using rem_nonneg d

private theorem weight_on_smooth {n y Z : ℕ} (hn : n ∈ smooth y Z) {d m : ℕ} (mul : d*m=n) :
    vonMangoldt d ≤ price y d m := by
  obtain ⟨⟨np,_⟩,factors⟩ := mem_smoothUpTo.mp hn
  have nz : n ≠ 0 := Nat.ne_of_gt np
  have d_dvd : d ∣ n := mul ▸ dvd_mul_right ..
  have m_dvd : m ∣ n := mul ▸ dvd_mul_left ..
  have sub : m.primeFactors ⊆ Nat.primesLE y := by
    intro p hp
    exact factors (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.dvd_of_mem_primeFactors hp).trans m_dvd,nz⟩)
  by_cases small : d ≤ y
  · rw [price,if_pos ⟨small,sub⟩]
    exact le_add_of_nonneg_right (rem_nonneg _)
  · have nonprime : ¬d.Prime := fun prime => small (Nat.mem_primesLE.mp
      (factors (Nat.mem_primeFactors.mpr ⟨prime,d_dvd,nz⟩))).1
    simp only [price,small,false_and,if_false,remWeight,RHTower.Mertens.notPrimeVonMangoldt,
      nonprime,zero_add,le_rfl]

private theorem count_row (y Z d : ℕ) :
    (∑ m∈Icc 1 (Z/d),price y d m) =
      (if d ≤ y then vonMangoldt d*((smooth y (Z/d)).card:ℝ) else 0)+remWeight d*((Z/d:ℕ):ℝ) := by
  by_cases h : d ≤ y
  · simp only [price,h,true_and,if_true,sum_add_distrib,←sum_filter,sum_const,nsmul_eq_mul,
      smoothUpTo,Nat.card_Icc,Nat.add_sub_cancel]
    ring
  · simp only [price,h,false_and,if_false,zero_add,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel,mul_comm]

private theorem log_sum_bound (y Z : ℕ) (yz : y ≤ Z) :
    (∑ n∈smooth y Z,Real.log n) ≤
      (∑ d∈Icc 1 y,vonMangoldt d*((smooth y (Z/d)).card:ℝ))+
        (Z:ℝ)*(8+RHTower.Mertens.mertensTail) := by
  have lt := calc
    (∑ n∈smooth y Z,Real.log n) = ∑ n∈smooth y Z,∑ x∈n.divisorsAntidiagonal,vonMangoldt x.1 := by
      apply sum_congr rfl
      intro n _
      rw [Nat.sum_divisorsAntidiagonal (fun d _ => vonMangoldt d),vonMangoldt_sum]
    _ ≤ ∑ n∈smooth y Z,∑ x∈n.divisorsAntidiagonal,price y x.1 x.2 := by
      apply sum_le_sum
      intro n hn
      exact sum_le_sum (fun x hx => weight_on_smooth hn (Nat.mem_divisorsAntidiagonal.mp hx).1)
    _ ≤ ∑ n∈Icc 1 Z,∑ x∈n.divisorsAntidiagonal,price y x.1 x.2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun n _ _ => sum_nonneg fun _ _ => price_nonneg ..)
    _ = _ := sum_Icc_divisorsAntidiagonal_swap (price y) Z
  simp_rw [count_row] at lt
  rw [sum_add_distrib,←sum_filter] at lt
  have cut : (Icc 1 Z).filter (· ≤ y)=Icc 1 y := by
    ext d;simp only [mem_filter,mem_Icc];omega
  rw [cut] at lt
  refine lt.trans (add_le_add le_rfl ?_)
  calc
    _ ≤ ∑ d∈Icc 1 Z,(Z:ℝ)*(remWeight d/d) := sum_le_sum (fun d _ =>
      (mul_le_mul_of_nonneg_left Nat.cast_div_le (rem_nonneg d)).trans_eq (by ring))
    _ ≤ _ := by rw [←mul_sum];exact mul_le_mul_of_nonneg_left (RHTower.Mertens.tail_bounded Z) (Nat.cast_nonneg _)

/-- Uniform one-step inequality. Only the cofactors at dilations up to
the prime wall require any population estimate. -/
theorem smooth_logarithmic_recurrence :
    ∃ C : ℝ,0 < C ∧ ∀ y Z : ℕ,1 ≤ y → y ≤ Z → ∀ A : ℝ,0 ≤ A →
      (∀ d∈Icc 1 y, ((smoothUpTo (Nat.primesLE y) (Z/d)).card:ℝ) ≤ A*((Z/d:ℕ):ℝ)) →
      ((smoothUpTo (Nat.primesLE y) Z).card:ℝ)*Real.log Z ≤
        (Z:ℝ)*(A*(Real.log y+C)+C) := by
  let P := Real.log 4+4
  let L := 8+RHTower.Mertens.mertensTail
  have lp : 0 ≤ L := by
    simpa only [Icc_eq_empty_of_lt (by decide : 0<1),sum_empty] using RHTower.Mertens.tail_bounded 0
  have pp : 0 ≤ P := by dsimp only [P];positivity
  refine ⟨P+L+1,by positivity,?_⟩
  intro y Z yp yz A A0 lower
  have summed := sum_le_sum (s:=Icc 1 y) (fun d hd =>
    mul_le_mul_of_nonneg_left ((lower d hd).trans (mul_le_mul_of_nonneg_left
      (Nat.cast_div_le (α:=ℝ) (m:=Z) (n:=d)) A0)) (show 0 ≤ vonMangoldt d from vonMangoldt_nonneg))
  have eq (d : ℕ) : vonMangoldt d*(A*((Z:ℝ)/d))=(Z*A)*(vonMangoldt d/d) := by ring
  simp_rw [eq] at summed
  rw [←mul_sum] at summed
  have hb := (abs_le.mp (RHTower.Mertens.mertens_first y yp)).2
  have M : (∑ d∈Icc 1 y,vonMangoldt d/(d:ℝ)) ≤ Real.log y+P := by dsimp only [P]; linarith only [hb]
  have prime := summed.trans (mul_le_mul_of_nonneg_left M (mul_nonneg (Nat.cast_nonneg _) A0))
  have diff : (∑ n∈smooth y Z, (Real.log Z-Real.log n)) ≤ Z := by
    have big := sum_le_sum_of_subset_of_nonneg (f:=fun n : ℕ => Real.log Z-Real.log n)
      (show smooth y Z ⊆ Icc 1 Z from filter_subset ..) (fun n hi _ => sub_nonneg.mpr
        (Real.log_le_log (Nat.cast_pos.mpr (mem_Icc.mp hi).1) (Nat.cast_le.mpr (mem_Icc.mp hi).2)))
    simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel] at big ⊢
    linarith only [big,RHTower.Mertens.sum_log_ge Z]
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul] at diff
  have h := log_sum_bound y Z yz
  change _ ≤ _+(Z:ℝ)*L at h
  have psmall : A*(Real.log y+P) ≤ A*(Real.log y+(P+L+1)) := mul_le_mul_of_nonneg_left (by linarith) A0
  have grow := mul_le_mul_of_nonneg_left psmall (Nat.cast_nonneg (α:=ℝ) Z)
  have extra := mul_nonneg (Nat.cast_nonneg (α:=ℝ) Z) pp
  linarith only [h,diff,prime,grow,extra]

/-- Uniform upper density beyond each power of the prime wall. The
factor j! is independent of the smooth cutoff and observation. -/
theorem smooth_density_beyond_each_power (j : ℕ) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ y : ℕ in atTop,∀ Z : ℕ,y^j ≤ Z →
      ((smoothUpTo (Nat.primesLE y) Z).card:ℝ) ≤ (1/(j.factorial:ℝ)+ε)*Z := by
  induction j generalizing ε with
  | zero =>
    filter_upwards with y
    intro Z _
    have c := card_le_card (filter_subset (fun n : ℕ => n.primeFactors ⊆ Nat.primesLE y) (Icc 1 Z))
    rw [Nat.card_Icc,Nat.add_sub_cancel] at c
    simp only [Nat.factorial_zero,Nat.cast_one,div_one]
    have c' : ((smooth y Z).card:ℝ) ≤ (Z:ℝ) := by exact_mod_cast c
    exact c'.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith))
  | succ j ih =>
    obtain ⟨C,hC,step⟩ := smooth_logarithmic_recurrence
    let A := 1/(j.factorial:ℝ)+ε/2
    have A0 : 0 ≤ A := by dsimp only [A];positivity
    have grow := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    filter_upwards [ih (half_pos ep),grow.eventually_ge_atTop ((A*C+C)/(ε/2)),
      eventually_ge_atTop (2:ℕ)] with y pop pay hy
    intro Z room
    have yp : 0 < y := by omega
    have yz : y ≤ Z := (Nat.le_self_pow (Nat.succ_ne_zero j) y).trans room
    have recu := step y Z yp yz A A0 (by
      intro d hd
      obtain ⟨dp,dy⟩ := mem_Icc.mp hd
      apply pop
      exact (Nat.le_div_iff_mul_le dp).mpr ((Nat.mul_le_mul_left (y^j) dy).trans ((pow_succ y j).symm.le.trans room)))
    have lp : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have lz := Real.log_le_log (Nat.cast_pos.mpr (Nat.pow_pos yp : 0 < y^(j+1))) (Nat.cast_le.mpr room)
    rw [Nat.cast_pow,Real.log_pow] at lz
    have payment := (div_le_iff₀ (half_pos ep)).mp pay
    have absorb : A*(Real.log y+C)+C ≤ (1/(j.factorial:ℝ)+ε)*Real.log y := by
      change A*C+C ≤ Real.log y*(ε/2) at payment
      dsimp only [A] at payment ⊢
      linarith only [payment]
    have top := recu.trans (mul_le_mul_of_nonneg_left absorb (Nat.cast_nonneg Z))
    have low := mul_le_mul_of_nonneg_left lz (Nat.cast_nonneg (α:=ℝ) (smooth y Z).card)
    have market : ((smooth y Z).card:ℝ)*(j+1:ℕ) ≤ (Z:ℝ)*(1/(j.factorial:ℝ)+ε) := by
      apply (mul_le_mul_iff_left₀ lp).mp
      linarith only [low,top]
    have fac : 0 < (j.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have jf : 0 < ((j+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
    apply (mul_le_mul_iff_left₀ jf).mp
    rw [Nat.factorial_succ,Nat.cast_mul]
    have split : (1/(((j+1:ℕ):ℝ)*(j.factorial:ℝ))+ε)*(Z:ℝ)*((j+1:ℕ):ℝ)=
      (Z:ℝ)*(1/(j.factorial:ℝ))+(Z:ℝ)*ε*((j+1:ℕ):ℝ) := by field_simp [fac.ne',jf.ne']
    rw [split]
    exact market.trans (by
      have u : 1 ≤ ((j+1:ℕ):ℝ) := Nat.one_le_cast.mpr (Nat.succ_pos j)
      have v := le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg (α:=ℝ) Z) ep.le) u
      linarith only [v])

end GaloisForLFunctions.RestrictedFactorizationCalculus
