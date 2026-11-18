import GaloisForLFunctions.ExceptionalLayerTheory.TheFiniteOddQuotientMeanOfProperPrimePowers

/-!
# A power saving at every cutoff of the odd-quotient prime count

Small divisors cost their unsigned square-root mass. Transposing the
remaining divisors gives signed prefixes at the quotient cutoffs. Balancing
the two estimates gives exponent 1/(3−2b) from a prefix exponent b.
-/

noncomputable section
open Finset ArithmeticFunction
open _root_.RHTower _root_.RHTower.Sieve
namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev u := properPowerLatticeWeight
private abbrev alt := alternatingDivisorCoeff
private abbrev mass (f : ArithmeticFunction ℝ) (N : ℕ) := ∑ n ∈ Icc 1 N, f n

private theorem trunc_weighted (f : ArithmeticFunction ℝ) (N Y : ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, truncAF f Y d*w d) = ∑ d ∈ Icc 1 (min N Y), f d*w d := by
  have he : (Icc 1 N).filter (· ≤ Y) = Icc 1 (min N Y) := by
    ext d
    simp only [mem_filter,mem_Icc,le_min_iff]
    tauto
  simp only [truncAF_apply,ite_mul,zero_mul]
  rw [← sum_filter,he]

private theorem abs_alt (j : ℕ) : |alt j| ≤ 1 := by
  rcases j with _ | j
  · simp
  have he : Icc 1 (j+1) = insert (j+1) (Icc 1 j) := by
    ext k
    simp only [mem_Icc,mem_insert]
    omega
  have ht := prefix_alternatingDivisorCoeff (j+1)
  rw [he,sum_insert (by simp),prefix_alternatingDivisorCoeff] at ht
  have h (m : ℕ) : ((m%2:ℕ):ℝ) ≤ 1 := by exact_mod_cast (show m%2 ≤ 1 by omega)
  rw [abs_le]
  constructor <;> linarith only [ht,h j,h (j+1),Nat.cast_nonneg (α := ℝ) (j%2),
    Nat.cast_nonneg (α := ℝ) ((j+1)%2)]

/-- The exact cutoff where the divisor sum is transposed can be chosen freely. -/
private theorem hyperbola {b K : ℝ} (hb : 0 < b) (hb' : b < 1/2) (hK : 0 ≤ K)
    (h : ∀ x : ℝ, 1 ≤ x → |properPowerDiscrepancy x| ≤ K*x^b)
    {N Y : ℕ} (hY : 1 ≤ Y) (hYN : Y ≤ N) :
    |oddQuotientPowerCount N| ≤ (K+6)*(Y:ℝ)^(1/2:ℝ)+
      2*(K+2)*(N:ℝ)^b*((N/(Y+1):ℕ):ℝ)^(1-b)/(1-b) := by
  let J := N/(Y+1)
  let tail : ArithmeticFunction ℝ := u-truncAF u Y
  have htail (m : ℕ) : mass tail m = mass u m-mass u (min m Y) := by
    dsimp only [mass,tail]
    simp only [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply,
      sum_add_distrib,sum_neg_distrib]
    rw [show (∑ d ∈ Icc 1 m, truncAF u Y d)=∑ d ∈ Icc 1 (min m Y), u d by
      simpa only [mul_one] using trunc_weighted u m Y (fun _ => 1)]
  have htrans : oddQuotientPowerCount N =
      mass (truncAF u Y*alt) N + mass (alt*tail) N := by
    have he : (truncAF u Y*alt+alt*tail : ArithmeticFunction ℝ)=u*alt := by dsimp only [tail]; ring
    unfold oddQuotientPowerCount
    rw [← show mass (u*alt) N = ∑ d ∈ Icc 1 N, u d*((N/d%2:ℕ):ℝ) by
      rw [mass,sum_Icc_mul_apply]; simp_rw [prefix_alternatingDivisorCoeff]]
    rw [← he]
    simp only [mass,ArithmeticFunction.add_apply,sum_add_distrib]
  have hshort : |mass (truncAF u Y*alt) N| ≤ (K+6)*(Y:ℝ)^(1/2:ℝ) := by
    rw [mass,sum_Icc_mul_apply]
    simp_rw [prefix_alternatingDivisorCoeff]
    rw [trunc_weighted,min_eq_right hYN]
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum ?_).trans (properPowerLatticeWeight_sum_abs hb.le hb'.le hK h hY)
    intro d _
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (N/d%2))]
    exact mul_le_of_le_one_right (abs_nonneg _) (by exact_mod_cast (show N/d%2 ≤ 1 by omega))
  have hrestrict : mass (alt*tail) N = ∑ j ∈ Icc 1 J, alt j*mass tail (N/j) := by
    rw [mass,sum_Icc_mul_apply]
    symm
    apply sum_subset (Icc_subset_Icc_right (Nat.div_le_self N (Y+1)))
    intro j hj hnot
    have hjp := (mem_Icc.mp hj).1
    have hjgt : J < j := lt_of_not_ge fun he => hnot (mem_Icc.mpr ⟨hjp,he⟩)
    have hsmall : N/j ≤ Y := by
      by_contra! hl
      have hm := (Nat.le_div_iff_mul_le hjp).mp hl
      exact (not_le_of_gt hjgt) ((Nat.le_div_iff_mul_le (Nat.succ_pos Y)).mpr (by simpa [mul_comm] using hm))
    change alt j*mass tail (N/j)=0
    rw [htail,min_eq_left hsmall,sub_self,mul_zero]
  have hl (j : ℕ) (hj : j ∈ Icc 1 J) :
      |alt j*mass tail (N/j)| ≤ 2*(K+2)*(N:ℝ)^b*(j:ℝ)^(-b) := by
    have hjp := (mem_Icc.mp hj).1
    have hprod := (Nat.le_div_iff_mul_le (Nat.succ_pos Y)).mp (mem_Icc.mp hj).2
    have hyj : Y+1 ≤ N/j := (Nat.le_div_iff_mul_le hjp).mpr (by simpa [mul_comm] using hprod)
    have hp := properPowerLatticeWeight_abs_sum hb.le h (n := N/j) (by omega)
    have hy := properPowerLatticeWeight_abs_sum hb.le h hY
    have hyord : (Y:ℝ) ≤ ((N/j:ℕ):ℝ) := by exact_mod_cast (show Y≤N/j by omega)
    have hpow := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg Y) hyord hb.le) (by linarith only [hK] : 0 ≤ K+2)
    have hq : ((N/j:ℕ):ℝ)^b ≤ ((N:ℝ)/j)^b :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le hb.le
    rw [abs_mul,htail,min_eq_right (by omega : Y ≤ N/j)]
    have h₁ := mul_le_mul_of_nonneg_right (abs_alt j) (abs_nonneg (mass u (N/j)-mass u Y))
    rw [one_mul] at h₁
    apply h₁.trans
    apply (abs_sub _ _).trans
    have h₂ := mul_le_mul_of_nonneg_left hq (by linarith only [hK] : 0 ≤ 2*(K+2))
    rw [Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),div_eq_mul_inv] at h₂
    rw [Real.rpow_neg (Nat.cast_nonneg j)]
    have hboth := add_le_add hp (hy.trans hpow)
    apply hboth.trans
    convert h₂ using 1 <;> ring
  have hs : (∑ j ∈ Icc 1 J, (j:ℝ)^(-b)) ≤ (J:ℝ)^(1-b)/(1-b) := by
    rw [← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,add_comm (1:ℝ)] using
      _root_.RHTower.sum_range_rpow_neg_le b hb (by linarith only [hb']) J
  have hlarge : |mass (alt*tail) N| ≤ 2*(K+2)*(N:ℝ)^b*(J:ℝ)^(1-b)/(1-b) := by
    rw [hrestrict]
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum hl).trans
    rw [← mul_sum,mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  rw [htrans]
  exact (abs_add_le _ _).trans (add_le_add hshort hlarge)

/-- A prefix exponent b for proper prime powers gives exponent 1/(3−2b)
for the actual odd-quotient count at every integer, without averaging. -/
theorem oddQuotientPowerCount_hyperbola_bound {b K : ℝ} (hb : 0 < b) (hb' : b < 1/2) (hK : 0 ≤ K)
    (h : ∀ x : ℝ, 1 ≤ x → |properPowerDiscrepancy x| ≤ K*x^b) {N : ℕ} (hn : 1 ≤ N) :
    |oddQuotientPowerCount N| ≤ (K+6+2*(K+2)/(1-b))*(N:ℝ)^(1/(3-2*b)) := by
  have hd : 0 < 3-2*b := by linarith only [hb']
  let a := 2/(3-2*b)
  have ha : 0 ≤ a := (div_pos (by norm_num) hd).le
  have ha' : a ≤ 1 := (div_le_one hd).mpr (by linarith only [hb'])
  have hN : (1:ℝ) ≤ N := by exact_mod_cast hn
  have hN0 := zero_lt_one.trans_le hN
  let Y := ⌊(N:ℝ)^a⌋₊
  have hY : 1 ≤ Y := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hN ha)
  have hy := Nat.floor_le (Real.rpow_nonneg hN0.le a)
  have hyN : Y ≤ N := by
    have hyreal : (Y:ℝ)≤(N:ℝ) := hy.trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN ha')
    exact_mod_cast hyreal
  have hJ : ((N/(Y+1):ℕ):ℝ) ≤ (N:ℝ)^(1-a) := by
    have hcut : (N:ℝ)^a ≤ (Y:ℝ)+1 := (Nat.lt_floor_add_one _).le
    rw [Real.rpow_sub hN0,Real.rpow_one]
    apply (show ((N/(Y+1):ℕ):ℝ) ≤ (N:ℝ)/(↑(Y+1):ℝ) from Nat.cast_div_le).trans
    rw [Nat.cast_succ]
    exact div_le_div_of_nonneg_left hN0.le (Real.rpow_pos_of_pos hN0 a) hcut
  have hs := Real.rpow_le_rpow (Nat.cast_nonneg Y) hy (by norm_num : (0:ℝ) ≤ 1/2)
  have ht := Real.rpow_le_rpow (Nat.cast_nonneg (N/(Y+1))) hJ (by linarith only [hb'] : 0 ≤ 1-b)
  rw [← Real.rpow_mul hN0.le,show a*(1/2)=1/(3-2*b) by dsimp [a]; ring] at hs
  rw [← Real.rpow_mul hN0.le] at ht
  have hex : (N:ℝ)^b*(N:ℝ)^((1-a)*(1-b)) = (N:ℝ)^(1/(3-2*b)) := by
    rw [← Real.rpow_add hN0]
    congr 1
    apply (eq_div_iff hd.ne').mpr
    have had : a*(3-2*b)=2 := div_mul_cancel₀ _ hd.ne'
    linear_combination (b-1)*had
  apply (hyperbola hb hb' hK h hY hyN).trans
  have hs' := mul_le_mul_of_nonneg_left hs (by linarith only [hK] : 0 ≤ K+6)
  have ht' := mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hN0.le b)
  rw [hex] at ht'
  have hc := mul_le_mul_of_nonneg_left ht' (show 0 ≤ 2*(K+2)/(1-b) by
    apply div_nonneg (by positivity); linarith only [hb'])
  convert add_le_add hs' hc using 1 <;> ring

/-- An unconditional exponent strictly below one half for the sharp
ordinary-prime, factorial, square and cube count. -/
theorem oddQuotientPowerCount_eight_seventeenths :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → |oddQuotientPowerCount N| ≤ C*(N:ℝ)^(8/17:ℝ) := by
  obtain ⟨K,hK,h⟩ := properPowerDiscrepancy_from_zero_free_strip (by norm_num : (20999/48000:ℝ) < 7/16)
  refine ⟨K+6+2*(K+2)/(1-7/16),by positivity,fun _ hn => ?_⟩
  simpa only [show 1/(3-2*(7/16:ℝ))=8/17 by norm_num] using
    oddQuotientPowerCount_hyperbola_bound (by norm_num) (by norm_num) hK h hn

private theorem unaveraged_exponents {a c : ℝ} (ha : 0 ≤ a) (ha' : a < 1/2)
    (h : ∀ b : ℝ, a < b → b < 1/2 → ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : ℝ, 1 ≤ x → |properPowerDiscrepancy x| ≤ K*x^b)
    (hc : 1/(3-2*a) < c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |oddQuotientPowerCount N| ≤ C*(N:ℝ)^c := by
  have hd : 0 < 3-2*a := by linarith only [ha']
  have hc0 := (one_div_pos.mpr hd).trans hc
  have hprod := (div_lt_iff₀ hd).mp hc
  have hinv : 1/c < 3-2*a := (div_lt_iff₀ hc0).mpr (by linarith only [hprod])
  obtain ⟨b,hab,hb⟩ := exists_between (lt_min ha' (by linarith only [hinv] : a < (3-1/c)/2))
  have hhalf := (lt_min_iff.mp hb).1
  have hgap := (lt_min_iff.mp hb).2
  obtain ⟨K,hK,hp⟩ := h b hab hhalf
  let C := K+6+2*(K+2)/(1-b)
  have hC : 0 ≤ C := by
    dsimp only [C]
    have : 0 < 1-b := by linarith only [hhalf]
    positivity
  refine ⟨C,hC,fun N hn => ?_⟩
  apply (oddQuotientPowerCount_hyperbola_bound (ha.trans_lt hab) hhalf hK hp hn).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
  apply (div_le_iff₀ (by linarith only [hhalf] : 0 < 3-2*b)).mpr
  have hx : 1/c ≤ 3-2*b := by linarith only [hgap]
  linarith only [(div_le_iff₀ hc0).mp hx]

/-- All exponents above the hyperbola threshold supplied by the
unconditional zero-free strip hold at every integer cutoff. -/
theorem oddQuotientPowerCount_sub_half {c : ℝ} (hc : 24000/51001 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → |oddQuotientPowerCount N| ≤ C*(N:ℝ)^c := by
  apply unaveraged_exponents (a := 20999/48000) (by norm_num) (by norm_num)
    (fun _ hb _ => properPowerDiscrepancy_from_zero_free_strip hb)
  norm_num at hc ⊢
  exact hc

/-- On RH the sharp count satisfies every exponent above two fifths. -/
theorem oddQuotientPowerCount_two_fifths_of_rh (hRH : RiemannHypothesis) {c : ℝ} (hc : 2/5 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → |oddQuotientPowerCount N| ≤ C*(N:ℝ)^c := by
  apply unaveraged_exponents (a := 1/4) (by norm_num) (by norm_num)
    (riemannHypothesis_iff_properPowerDiscrepancy_quarter.mp hRH)
  norm_num at hc ⊢
  exact hc

end GaloisForLFunctions.ExceptionalLayerTheory
