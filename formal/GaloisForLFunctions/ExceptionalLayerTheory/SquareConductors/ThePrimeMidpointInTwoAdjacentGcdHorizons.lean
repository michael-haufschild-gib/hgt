import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheGcdProductOnOneMangoldtOctave
import GaloisForLFunctions.ExceptionalLayerTheory.EveryRightZeroForcesBothSignsOfThePrimeError
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheSeventeenNinthsConductorPrefix
import GaloisForLFunctions.ExceptionalLayerTheory.GrowingQuotientBandsInBinomialCarries
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Two gcd horizons and the Chebyshev midpoint

On (2n,4n] the two product horizons 4n and 6n have only two cofactor
cells. Their signed log price is the difference between the adjacent
prime intervals (2n,3n] and (3n,4n]. Strict concavity transfers one
upper bound for this local difference to the entire Chebyshev error.
-/

noncomputable section
open Finset ArithmeticFunction Filter Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The twice-minus-three log price at the two adjacent product horizons. -/
def adjacentGcdPrice (n : ℕ) : ℝ :=
  2*Real.log (octaveGcdProduct (2*n) (6*n))-3*Real.log (octaveGcdProduct (2*n) (4*n))

private theorem psi_interval {a b : ℕ} (hab : a ≤ b) :
    (∑ d ∈ Ioc a b,vonMangoldt d)=Chebyshev.psi b-Chebyshev.psi a := by
  simp only [Chebyshev.psi,Nat.floor_natCast]
  linarith only [sum_Ioc_consecutive (fun d => vonMangoldt d) (Nat.zero_le a) hab]

/-- Each included divisor has signed multiplicity +1 through 3n and -1
above 3n. The middle endpoint belongs to the first interval. -/
theorem adjacent_gcd_price_eq_prime_midpoint {n : ℕ} (hn : 0 < n) :
    adjacentGcdPrice n = 2*Chebyshev.psi (3*n:ℕ)-Chebyshev.psi (2*n:ℕ)-Chebyshev.psi (4*n:ℕ) := by
  have h2 : 0 < 2*n := by omega
  let f (d : ℕ) := (((6*n/d:ℕ):ℝ)*vonMangoldt d)
  let g (d : ℕ) := (((4*n/d:ℕ):ℝ)*vonMangoldt d)
  have hi {d : ℕ} (hd : d ∈ Ioc (2*n) (4*n)) :
      4*n/d=1 ∧ 6*n/d=if d ≤ 3*n then 2 else 1 := by
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hd
    have hp : 0 < d := by omega
    have h1 : 1 ≤ 4*n/d := (Nat.le_div_iff_mul_le hp).mpr (by omega)
    have h1' : 4*n/d < 2 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
    have h2' : 6*n/d < 3 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
    have h1'' : 1 ≤ 6*n/d := (Nat.le_div_iff_mul_le hp).mpr (by omega)
    refine ⟨by omega,?_⟩
    split_ifs with hh
    · have := (Nat.le_div_iff_mul_le hp).mpr (by omega : 2*d ≤ 6*n)
      omega
    · have := (Nat.div_lt_iff_lt_mul hp).mpr (by omega : 6*n < 2*d)
      omega
  let S := Ioc (2*n) (4*n)
  have hf : (∑ d ∈ S,f d)=(∑ d ∈ Ioc (2*n) (3*n),vonMangoldt d)+(∑ d ∈ S,vonMangoldt d) := by
    have he : S.filter (fun d => d ≤ 3*n)=Ioc (2*n) (3*n) := by
      ext d; simp only [S,mem_filter,mem_Ioc]; omega
    rw [←he,sum_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro d hd
    dsimp only [f]
    rw [(hi hd).2]
    split_ifs <;> push_cast <;> ring
  have hg : (∑ d ∈ S,g d)=∑ d ∈ S,vonMangoldt d := by
    apply sum_congr rfl
    intro d hd
    simp only [g,(hi hd).1,Nat.cast_one,one_mul]
  rw [adjacentGcdPrice,log_octave_gcd_product h2,log_octave_gcd_product h2,
    show 2*(2*n)=4*n by omega]
  change 2*(∑ d ∈ S,f d)-3*(∑ d ∈ S,g d)=_
  rw [hf,hg,show S=Ioc (2*n) (4*n) by rfl,psi_interval (by omega),psi_interval (by omega)]
  ring

private def midpointContraction (b : ℝ) := ((2/3:ℝ)^b+(4/3:ℝ)^b)/2

private theorem midpoint_contraction_lt {b : ℝ} (hb : 0 < b) (h1 : b < 1) :
    midpointContraction b < 1 := by
  have h := (Real.strictConcaveOn_rpow hb h1).2
    (show (2/3:ℝ) ∈ Set.Ici 0 by norm_num) (show (4/3:ℝ) ∈ Set.Ici 0 by norm_num)
    (by norm_num : (2/3:ℝ) ≠ 4/3) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul,show (1/2:ℝ)*(2/3)+(1/2)*(4/3)=1 by norm_num,Real.one_rpow] at h
  dsimp only [midpointContraction]
  linarith only [h]

private theorem midpoint_power (x b : ℝ) (hx : 0 ≤ x) :
    ((2/3:ℝ)*x)^b+((4/3:ℝ)*x)^b = 2*midpointContraction b*x^b := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2/3) hx,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4/3) hx]
  dsimp only [midpointContraction]
  ring

/-- A one-sided midpoint inequality contracts each power strictly between
zero and one. The initial power envelope disappears under iteration. -/
private theorem midpoint_upper_transfer (V : ℝ → ℝ) {a b A C : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) (hA : 0 ≤ A)
    (hbase : ∀ x : ℝ,0 < x → V x ≤ C*x^a)
    (hprice : ∀ x : ℝ,0 < x → 2*V x-V ((2/3)*x)-V ((4/3)*x) ≤ A*x^b) :
    ∀ x : ℝ,0 < x → V x ≤ (A/(2*(1-midpointContraction b)))*x^b := by
  let L := A/(2*(1-midpointContraction b))
  have hq := midpoint_contraction_lt hb hb1
  have hLa : 2*L*(1-midpointContraction b)=A := by
    dsimp only [L]; field_simp [sub_ne_zero.mpr hq.ne']
  have hL : 0 ≤ L := div_nonneg hA (mul_nonneg (by norm_num) (sub_nonneg.mpr hq.le))
  have iter (k : ℕ) (x : ℝ) (hx : 0 < x) :
      V x ≤ L*x^b+(C*(midpointContraction a)^k)*x^a := by
    induction k generalizing x with
    | zero =>
      simpa only [pow_zero,mul_one] using (hbase x hx).trans
        (le_add_of_nonneg_left (mul_nonneg hL (Real.rpow_nonneg hx.le b)))
    | succ k ih =>
      have hr := add_le_add (ih ((2/3)*x) (by positivity)) (ih ((4/3)*x) (by positivity))
      have he (u : ℝ) :
          L*((2/3:ℝ)*x)^b+u*((2/3:ℝ)*x)^a+(L*((4/3:ℝ)*x)^b+u*((4/3:ℝ)*x)^a)=
          L*(2*midpointContraction b*x^b)+u*(2*midpointContraction a*x^a) := by
        rw [←midpoint_power x b hx.le,←midpoint_power x a hx.le]
        ring
      rw [he] at hr
      rw [pow_succ]
      have ha' := congrArg (fun z : ℝ => z*x^b) hLa
      linarith only [hr,hprice x hx,ha']
  intro x hx
  have hqa0 : 0 ≤ midpointContraction a := by dsimp only [midpointContraction]; positivity
  have hlim := ((tendsto_pow_atTop_nhds_zero_of_lt_one hqa0 (midpoint_contraction_lt ha ha1)).const_mul C).mul_const (x^a)
  have hout := le_of_tendsto_of_tendsto' (tendsto_const_nhds (x := V x)) (hlim.const_add (L*x^b)) (fun k => iter k x hx)
  simpa only [mul_zero,zero_mul,add_zero] using hout

#print axioms adjacent_gcd_price_eq_prime_midpoint
#print axioms midpoint_upper_transfer

/-- A sublinear upper power bound for a price can be sharpened to the
power of its signed dilation midpoint. Both exponents lie in (0,1). -/
theorem upper_power_from_dilation_midpoint {F : ℝ → ℝ} {a b : ℝ}
    (ha : a∈Set.Ioo (0:ℝ) 1) (hb : b∈Set.Ioo (0:ℝ) 1)
    (hF : ∃ C : ℝ, ∀ x : ℝ, 0<x → F x≤C*x^a)
    (hD : ∃ A : ℝ, ∀ x : ℝ, 0<x → 2*F (3*x)-F (2*x)-F (4*x)≤A*x^b) :
    ∃ K : ℝ, ∀ x : ℝ, 0<x → F x≤K*x^b := by
  obtain ⟨C,hC⟩ := hF
  obtain ⟨A,hA⟩ := hD
  refine ⟨_,midpoint_upper_transfer F ha.1 ha.2 hb.1 hb.2 (abs_nonneg A) hC ?_⟩
  intro x hx
  have h := hA (x/3) (by positivity)
  rw [show 3*(x/3)=x by ring,show 2*(x/3)=(2/3)*x by ring,
    show 4*(x/3)=(4/3)*x by ring] at h
  exact h.trans (mul_le_mul (le_abs_self A)
    (Real.rpow_le_rpow (by positivity) (by linarith only [hx]) hb.1.le)
    (Real.rpow_nonneg (by positivity) _) (abs_nonneg A))

private def midpointSignal (y : ℝ) :=
  2*Chebyshev.psi y-Chebyshev.psi ((2/3)*y)-Chebyshev.psi ((4/3)*y)

/-- Interpolation from multiples of three costs only the central prime
increments in an upper estimate, because the outer increments have minus signs. -/
private theorem extend_integer_midpoint {b A : ℝ} (hb : 0 < b)
    (h : ∀ n : ℕ,1 ≤ n → adjacentGcdPrice n ≤ A*(n:ℝ)^b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ,0 < y → midpointSignal y ≤ B*y^b := by
  let B := |A|+6/b+2*Chebyshev.psi 3
  have hp3 := Chebyshev.psi_nonneg 3
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B,hB,?_⟩
  intro y hy
  have hpower := Real.rpow_nonneg hy.le b
  by_cases hy3 : 3 ≤ y
  · let n := ⌊y/3⌋₊
    have hn : 1 ≤ n := (Nat.le_floor_iff (by positivity : 0 ≤ y/3)).mpr (by push_cast; linarith only [hy3])
    have hl : 3*(n:ℝ) ≤ y := by linarith only [Nat.floor_le (by positivity : 0 ≤ y/3)]
    have hu : y < 3*(n:ℝ)+3 := by linarith only [Nat.lt_floor_add_one (y/3)]
    have hlow := Chebyshev.psi_mono (show 2*(n:ℝ) ≤ (2/3)*y by linarith only [hl])
    have hhigh := Chebyshev.psi_mono (show 4*(n:ℝ) ≤ (4/3)*y by linarith only [hl])
    have hfl : 3*n ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy.le).mpr (by exact_mod_cast hl)
    have hfhi : ⌊y⌋₊ ≤ 3*n+3 := by
      have hh : (⌊y⌋₊:ℝ) ≤ 3*(n:ℝ)+3 := (Nat.floor_le hy.le).trans hu.le
      exact_mod_cast hh
    have hlog : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy3])
    have hmid : Chebyshev.psi y-Chebyshev.psi (3*(n:ℝ)) ≤ 3*Real.log y := by
      rw [Chebyshev.psi_eq_psi_coe_floor y,←Nat.cast_ofNat (R := ℝ) (n := 3),←Nat.cast_mul,←psi_interval hfl]
      calc _ ≤ ∑ _ ∈ Ioc (3*n) ⌊y⌋₊,Real.log y := by
             apply sum_le_sum
             intro d hd
             have hdn := (mem_Ioc.mp hd).1
             have hdr : 0 < (d:ℝ) := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt hdn)
             exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hdr ((Nat.cast_le.mpr (mem_Ioc.mp hd).2).trans (Nat.floor_le hy.le)))
           _ ≤ _ := by
             rw [sum_const,Nat.card_Ioc,nsmul_eq_mul]
             exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show ⌊y⌋₊-3*n ≤ 3 by omega)) hlog
    have hloc := h n hn
    rw [adjacent_gcd_price_eq_prime_midpoint hn] at hloc
    push_cast at hloc
    have hmain : midpointSignal y ≤ A*(n:ℝ)^b+6*Real.log y := by
      dsimp only [midpointSignal]
      linarith only [hloc,hmid,hlow,hhigh]
    have hlog' := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy b)
    rw [Real.log_rpow hy] at hlog'
    have hly : Real.log y ≤ y^b/b := (le_div_iff₀ hb).mpr (by linarith only [hlog'])
    have hprice := mul_le_mul (le_abs_self A)
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith only [hl,Nat.cast_nonneg (α:=ℝ) n] : (n:ℝ) ≤ y) hb.le)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (abs_nonneg A)
    apply hmain.trans
    have hz := mul_nonneg hp3 hpower
    dsimp only [B]
    calc _ ≤ |A| * y^b+6*(y^b/b) := add_le_add hprice (mul_le_mul_of_nonneg_left hly (by norm_num))
         _ ≤ _ := by rw [div_eq_mul_inv,div_eq_mul_inv]; linarith only [hz]
  · have hh : midpointSignal y ≤ 2*Chebyshev.psi y := by
      dsimp only [midpointSignal]
      linarith only [Chebyshev.psi_nonneg ((2/3)*y),Chebyshev.psi_nonneg ((4/3)*y)]
    apply hh.trans
    by_cases hy1 : 1 ≤ y
    · have hsmall := Chebyshev.psi_mono (le_of_not_ge hy3)
      have hp := Real.one_le_rpow hy1 hb.le
      have hcost : 2*Chebyshev.psi 3 ≤ B := by dsimp only [B]; linarith only [abs_nonneg A,div_nonneg (by norm_num : (0:ℝ) ≤ 6) hb.le]
      exact (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0:ℝ) ≤ 2)).trans ((le_mul_of_one_le_right (by positivity) hp).trans (mul_le_mul_of_nonneg_right hcost hpower))
    · rw [Chebyshev.psi_eq_zero_of_le_one (le_of_not_ge hy1),mul_zero]
      exact mul_nonneg hB hpower

/-- One upper estimate on the two adjacent integer products bounds the
entire Chebyshev surplus at the same exponent. -/
theorem prime_surplus_of_adjacent_gcd_price {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (h : ∃ C : ℝ, ∀ n : ℕ,1 ≤ n → adjacentGcdPrice n ≤ C*(n:ℝ)^b) :
    ∃ B : ℝ, ∀ x : ℝ,0 < x → Chebyshev.psi x-x ≤ B*x^b := by
  obtain ⟨C,hC⟩ := h
  obtain ⟨A,hA,hp⟩ := extend_integer_midpoint hb hC
  have hw : _root_.RHTower.zeroReSup < 8/9 := GaloisForLFunctions.ExceptionalLayerTheory.zeroReSup_le_sub_seven_eighths.trans_lt (by norm_num)
  obtain ⟨T,hT,ht⟩ := _root_.RHTower.exists_abs_chebyshevPsi_sub_le_rpow hw
  let V (x : ℝ) := Chebyshev.psi x-x
  have hv (x : ℝ) (hx : 0 < x) : V x ≤ T*x^(8/9:ℝ) := by
    rcases le_total 1 x with hh | hh
    · exact (le_abs_self _).trans (ht x hh)
    · dsimp only [V]
      rw [Chebyshev.psi_eq_zero_of_le_one hh,zero_sub]
      exact (neg_nonpos.mpr hx.le).trans (mul_nonneg hT (Real.rpow_nonneg hx.le _))
  have hrec (x : ℝ) (hx : 0 < x) : 2*V x-V ((2/3)*x)-V ((4/3)*x) ≤ A*x^b := by
    have he := hp x hx
    dsimp only [V,midpointSignal] at he ⊢
    linarith only [he]
  exact ⟨_,midpoint_upper_transfer V (by norm_num : (0:ℝ) < 8/9) (by norm_num) hb hb1 hA hv hrec⟩

/-- Upper estimates at every exponent strictly above b for the integer
price. Only exponents below one are needed. -/
def adjacentGcdUpperSpectrum (b : ℝ) : Prop :=
  ∀ t : ℝ,b < t → t < 1 → ∃ C : ℝ,∀ n : ℕ,1 ≤ n → adjacentGcdPrice n ≤ C*(n:ℝ)^t

private theorem width_of_prime_surplus {b : ℝ} (hb : 1/2 ≤ b)
    (h : ∃ B : ℝ,∀ x : ℝ,0 < x → Chebyshev.psi x-x ≤ B*x^b) :
    _root_.RHTower.zetaZeroAbscissa ≤ b := by
  obtain ⟨A,hA⟩ := h
  refine csSup_le _root_.RHTower.zetaZeroReSet_nonempty fun x hx => ?_
  obtain ⟨ρ,hz,rfl⟩ := hx
  by_contra! hlt
  have h1 : ρ.re < 1 := lt_of_not_ge (fun hh => riemannZeta_ne_zero_of_one_le_re hh hz)
  obtain ⟨c,hc,hpeak⟩ := GaloisForLFunctions.ExceptionalLayerTheory.both_prime_error_peaks_at_every_large_cutoff (hb.trans_lt hlt) h1 hz
  have hlim : Tendsto (fun n : ℕ => A*(n:ℝ)^(-(ρ.re-b))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (sub_pos.mpr hlt)).comp tendsto_natCast_atTop_atTop).const_mul A
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hlim.eventually_lt_const hc)
  obtain ⟨N,hl,hNk⟩ := (hpeak.and (eventually_ge_atTop (k^2))).exists
  obtain ⟨n,hn,hs,hlarge⟩ := hl 1 (by norm_num)
  have hkr : (k:ℝ) ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by exact_mod_cast hNk)
  have hr : 0 < (n:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hn).1
  have ht := mul_lt_mul_of_pos_right (hk n (Nat.cast_le.mp (hkr.trans hs.le))) (Real.rpow_pos_of_pos hr ρ.re)
  rw [mul_assoc,←Real.rpow_add hr,show -(ρ.re-b)+ρ.re=b by ring] at ht
  linarith only [ht,hA n hr,hlarge]

/-- An upper estimate for the ordinary-prime surplus excludes zeta zeros
to its right as soon as the exponent covers the square-root prime powers. -/
theorem zero_abscissa_of_ordinary_prime_surplus {b : ℝ} (hb : 1/2≤b)
    (h : ∃ B : ℝ, ∀ x : ℝ, 1≤x → Chebyshev.theta x-x≤B*x^b) :
    _root_.RHTower.zetaZeroAbscissa≤b := by
  obtain ⟨B,hB⟩ := h
  obtain ⟨D,hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine width_of_prime_surplus hb ⟨|B|+|D|,fun x hx => ?_⟩
  by_cases hx₁ : 1≤x
  · have htheta := (hB x hx₁).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.rpow_nonneg hx.le _))
    have hsqrt := Real.rpow_le_rpow_of_exponent_le hx₁ hb
    rw [←Real.sqrt_eq_rpow] at hsqrt
    have he := (hD x).trans (mul_le_mul (le_abs_self D) hsqrt (Real.sqrt_nonneg x) (abs_nonneg D))
    linarith only [htheta,he]
  · rw [Chebyshev.psi_eq_zero_of_le_one (le_of_not_ge hx₁),zero_sub]
    exact (neg_nonpos.mpr hx.le).trans (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.rpow_nonneg hx.le _))

/-- One signed rational product price has exactly the ordinary zeta zero
abscissa as its power threshold. -/
theorem adjacent_gcd_upper_spectrum_iff {b : ℝ} (hb : 1/2 ≤ b) :
    adjacentGcdUpperSpectrum b ↔ _root_.RHTower.zetaZeroAbscissa ≤ b := by
  constructor
  · intro h
    refine csSup_le _root_.RHTower.zetaZeroReSet_nonempty fun x hx => ?_
    obtain ⟨ρ,hz,rfl⟩ := hx
    by_contra! hlt
    obtain ⟨t,hbt,htr⟩ := exists_between hlt
    have hr1 : ρ.re < 1 := lt_of_not_ge (fun hh => riemannZeta_ne_zero_of_one_le_re hh hz)
    have ht0 : 0 < t := by linarith only [hb,hbt]
    have ht1 := htr.trans hr1
    exact htr.not_ge ((_root_.RHTower.re_le_zetaZeroAbscissa hz).trans
      (width_of_prime_surplus (hb.trans hbt.le) (prime_surplus_of_adjacent_gcd_price ht0 ht1 (h t hbt ht1))))
  · intro h t hbt _
    have ht0 : 0 ≤ t := by linarith only [hb,hbt]
    have hsup := _root_.RHTower.zeroReSup_le_of_forall_re_le fun q =>
      (_root_.RHTower.re_le_zetaZeroAbscissa (_root_.RHTower.riemannZeta_eq_zero_of_xiZeroCopy q)).trans h
    obtain ⟨C,hC,hψ⟩ := _root_.RHTower.exists_abs_chebyshevPsi_sub_le_rpow (hsup.trans_lt hbt)
    refine ⟨4*C*(4:ℝ)^t,fun n hn => ?_⟩
    have hr : (1:ℝ) ≤ n := Nat.one_le_cast.mpr hn
    let E (k : ℝ) := Chebyshev.psi (k*n)-k*n
    have hh (k : ℝ) (hk : 1 ≤ k) (hk4 : k ≤ 4) : |E k| ≤ C*((4:ℝ)^t*(n:ℝ)^t) := by
      have hu := (hψ (k*n) (one_le_mul_of_one_le_of_one_le hk hr)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity : 0 ≤ k*n)
          (mul_le_mul_of_nonneg_right hk4 (zero_le_one.trans hr)) ht0) hC)
      rwa [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (zero_le_one.trans hr)] at hu
    have hh2 := (abs_le.mp (hh 2 (by norm_num) (by norm_num))).1
    have hh3 := (abs_le.mp (hh 3 (by norm_num) (by norm_num))).2
    have hh4 := (abs_le.mp (hh 4 (by norm_num) (by norm_num))).1
    rw [adjacent_gcd_price_eq_prime_midpoint hn]
    push_cast
    dsimp only [E] at hh2 hh3 hh4
    linarith only [hh2,hh3,hh4]

#print axioms prime_surplus_of_adjacent_gcd_price
#print axioms adjacent_gcd_upper_spectrum_iff
#print axioms upper_power_from_dilation_midpoint
#print axioms zero_abscissa_of_ordinary_prime_surplus


/-- The ordinary-prime log product on (2n,3n] divided by that on (3n,4n]. -/
def primeMidpointPrice (n : ℕ) : ℝ :=
  (∑ p ∈ (Ioc (2*n) (3*n)).filter Nat.Prime,Real.log p)-
  (∑ p ∈ (Ioc (3*n) (4*n)).filter Nat.Prime,Real.log p)

private theorem theta_interval {a b : ℕ} (hab : a ≤ b) :
    (∑ p ∈ (Ioc a b).filter Nat.Prime,Real.log p)=Chebyshev.theta b-Chebyshev.theta a := by
  simp only [Chebyshev.theta,Nat.floor_natCast,sum_filter]
  linarith only [sum_Ioc_consecutive (fun p : ℕ => if p.Prime then Real.log p else 0) (Nat.zero_le a) hab]

theorem prime_midpoint_price_eq (n : ℕ) :
    primeMidpointPrice n=2*Chebyshev.theta (3*n:ℕ)-Chebyshev.theta (2*n:ℕ)-Chebyshev.theta (4*n:ℕ) := by
  rw [primeMidpointPrice,theta_interval (by omega),theta_interval (by omega)]
  ring

theorem midpoint_proper_power_error :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {n : ℕ}, 1 ≤ n →
      |adjacentGcdPrice n-primeMidpointPrice n| ≤ A*Real.sqrt n := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨8*|C|,by positivity,?_⟩
  intro n hn
  let E (k : ℝ) := Chebyshev.psi (k*n)-Chebyshev.theta (k*n)
  have hh {k : ℝ} (hk : 0 ≤ k) (hk4 : k ≤ 4) :
      |E k| ≤ |C| * (2*Real.sqrt n) := by
    dsimp only [E]
    rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi (k*n)))]
    have hnorm : Real.sqrt (k*n) ≤ 2*Real.sqrt n := by
      have hh := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hk4 (Nat.cast_nonneg (α:=ℝ) n))
      rwa [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),show Real.sqrt 4=2 by norm_num] at hh
    exact (hC _).trans (mul_le_mul (le_abs_self _) hnorm (Real.sqrt_nonneg _) (abs_nonneg _))
  have h2 := abs_le.mp (hh (k := 2) (by norm_num) (by norm_num))
  have h3 := abs_le.mp (hh (k := 3) (by norm_num) (by norm_num))
  have h4 := abs_le.mp (hh (k := 4) (by norm_num) (by norm_num))
  rw [adjacent_gcd_price_eq_prime_midpoint hn,prime_midpoint_price_eq,abs_le]
  push_cast
  dsimp only [E] at h2 h3 h4
  constructor <;> linarith only [h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]

/-- The one-sided prime product bound on these two equal-length
intervals has threshold exactly the rightmost zeta abscissa. -/
theorem prime_midpoint_upper_spectrum_iff {b : ℝ} (hb : 1/2 ≤ b) :
    (∀ t : ℝ,b < t → t < 1 → ∃ C : ℝ,∀ n : ℕ,1 ≤ n → primeMidpointPrice n ≤ C*(n:ℝ)^t) ↔
      _root_.RHTower.zetaZeroAbscissa ≤ b := by
  rw [←adjacent_gcd_upper_spectrum_iff hb]
  obtain ⟨A,hA,herr⟩ := midpoint_proper_power_error
  have step {t : ℝ} (ht : b < t) {n : ℕ} (hn : 1 ≤ n) :
      |adjacentGcdPrice n-primeMidpointPrice n| ≤ A*(n:ℝ)^t := by
    have hd := herr hn
    rw [Real.sqrt_eq_rpow] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn) (hb.trans ht.le)) hA)
  constructor <;> intro h t ht ht1 <;> obtain ⟨C,hC⟩ := h t ht ht1 <;>
    refine ⟨C+A,fun n hn => ?_⟩
  · linarith only [(abs_le.mp (step ht hn)).2,hC n hn]
  · linarith only [(abs_le.mp (step ht hn)).1,hC n hn]

/-- The ordinary prime midpoint criterion at 5/6 is exactly the absolute
eleven-thirds estimate on the entire signed conductor prefix. -/
theorem prime_midpoint_iff_eleven_thirds :
    (∀ t : ℝ,5/6 < t → t < 1 → ∃ C : ℝ,∀ n : ℕ,1 ≤ n → primeMidpointPrice n ≤ C*(n:ℝ)^t) ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |seventeenNinthsConductorPrefix N| ≤ C*(N:ℝ)^(11/3:ℝ) :=
  (prime_midpoint_upper_spectrum_iff (by norm_num)).trans five_sixths_iff_seventeenNinthsConductorPrefix

theorem riemannHypothesis_iff_prime_midpoint :
    RiemannHypothesis ↔ ∀ t : ℝ,1/2 < t → t < 1 → ∃ C : ℝ,∀ n : ℕ,1 ≤ n → primeMidpointPrice n ≤ C*(n:ℝ)^t := by
  rw [prime_midpoint_upper_spectrum_iff le_rfl]
  constructor
  · intro h
    apply csSup_le _root_.RHTower.zetaZeroReSet_nonempty
    rintro x ⟨ρ,hρ,rfl⟩
    by_contra! hhalf
    have hone : ρ.re < 1 := lt_of_not_ge (fun hh => riemannZeta_ne_zero_of_one_le_re hh hρ)
    exact (_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mp h ρ hhalf hone) hρ
  · intro h
    apply _root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro ρ hhalf _ hρ
    exact hhalf.not_ge ((_root_.RHTower.re_le_zetaZeroAbscissa hρ).trans h)

#print axioms midpoint_proper_power_error
#print axioms prime_midpoint_iff_eleven_thirds
#print axioms riemannHypothesis_iff_prime_midpoint

/-- Uniform lower bound in the ordinate for the Mellin numerator of
the two adjacent intervals. Strict concavity pays the entire critical strip. -/
theorem midpoint_mellin_numerator_lower {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    0 < 2*(3:ℝ)^z.re-(2:ℝ)^z.re-(4:ℝ)^z.re ∧
    2*(3:ℝ)^z.re-(2:ℝ)^z.re-(4:ℝ)^z.re ≤ ‖2*(3:ℂ)^z-(2:ℂ)^z-(4:ℂ)^z‖ := by
  have hc := (Real.strictConcaveOn_rpow h0 h1).2
    (show (2:ℝ) ∈ Set.Ici 0 by norm_num) (show (4:ℝ) ∈ Set.Ici 0 by norm_num)
    (by norm_num : (2:ℝ) ≠ 4) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul,show (1/2:ℝ)*2+(1/2)*4=3 by norm_num] at hc
  have hN2 : ‖(2:ℂ)^z‖=(2:ℝ)^z.re := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2) z
  have hN3 : ‖(3:ℂ)^z‖=(3:ℝ)^z.re := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 3) z
  have hN4 : ‖(4:ℂ)^z‖=(4:ℝ)^z.re := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 4) z
  have hn := norm_sub_norm_le (2*(3:ℂ)^z) ((2:ℂ)^z+(4:ℂ)^z)
  have hu := norm_add_le ((2:ℂ)^z) ((4:ℂ)^z)
  rw [norm_mul,hN3,show ‖(2:ℂ)‖=2 by norm_num,sub_add_eq_sub_sub] at hn
  rw [hN2,hN4] at hu
  exact ⟨by linarith only [hc],by linarith only [hu,hn]⟩

#print axioms midpoint_mellin_numerator_lower

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
