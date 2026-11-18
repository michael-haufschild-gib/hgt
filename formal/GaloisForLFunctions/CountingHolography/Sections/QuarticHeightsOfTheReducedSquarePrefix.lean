import GaloisForLFunctions.CountingHolography.Sections.InnerPrimesInTheReducedSquarePrefixNumerator
import GaloisForLFunctions.CountingHolography.Sections.TheSignedProductOverSquareConductors
import GaloisForLFunctions.CountingHolography.Sections.TheNumeratorAboveSquareRootMultiplicity

/-!
# Quartic logarithmic heights of the reduced square prefix

A fixed band of inner primes supplies quartic numerator mass even after
reduction. The subquartic signed price transfers that mass to the
denominator, whose gross product gives a matching upper bound.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology SquareRootThreshold _root_.RHTower

private abbrev P := squareGeneratorPrefix
private abbrev U (N : ℕ) := (P N).num.natAbs
private abbrev V (N : ℕ) := (P N).den
private abbrev q (j : ℕ) := ordinaryPrimeGenerator (j • successorSquareTriple j)

private theorem partial_log_factors (m : ℕ) (S : Finset ℕ) :
    ∑ p ∈ S, (m.factorization p:ℝ)*Real.log p ≤ Real.log m := by
  let T := S ∪ m.factorization.support
  have he : Real.log m=∑ p ∈ T, (m.factorization p:ℝ)*Real.log p := by
    rw [Real.log_nat_eq_sum_factorization]
    exact Finsupp.sum_of_support_subset _ subset_union_right _ (by simp)
  rw [he]
  exact sum_le_sum_of_subset_of_nonneg subset_union_left
    (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))

/-- Primes in one proportional band have both quadratic order and
quadratic logarithmic mass. -/
private theorem numerator_lower : ∃ b : ℝ, 0 < b ∧ ∀ᶠ N : ℕ in atTop,
    b*(N:ℝ)^4 ≤ Real.log (U N) := by
  obtain ⟨c,A,hc,hA,hinner⟩ := inner_primes_in_reduced_square_prefix
  obtain ⟨p₀,h₀⟩ := eventually_atTop.mp hinner
  let v := 1/(A+1)^2
  let u := v/2
  have hv : 0 < v := by dsimp only [v]; positivity
  have hu : 0 < u := half_pos hv
  have huv : u < v := half_lt_self hv
  have ht : Tendsto (fun N : ℕ => (N:ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop
  refine ⟨c*u*((v-u)/2),mul_pos (mul_pos hc hu) (half_pos (sub_pos.mpr huv)),?_⟩
  filter_upwards [ht.eventually (proportional_prime_mass hu huv),
    (ht.const_mul_atTop hu).eventually_ge_atTop (p₀:ℝ)] with N hmass hlate
  let X := (N:ℝ)^2
  let S := (Ioc ⌊u*X⌋₊ ⌊v*X⌋₊).filter Nat.Prime
  change (v-u)/2*X ≤ ∑ p ∈ S, Real.log p at hmass
  change (p₀:ℝ) ≤ u*X at hlate
  have hX : 0 ≤ X := sq_nonneg _
  have hrange (p : ℕ) (hp : p ∈ S) : c*(u*X) ≤ ((U N).factorization p:ℝ) := by
    obtain ⟨hmem,hprime⟩ := mem_filter.mp hp
    obtain ⟨hl,hh⟩ := mem_Ioc.mp hmem
    have hlo : u*X ≤ (p:ℝ) := (Nat.lt_floor_add_one _).le.trans
      (by exact_mod_cast Nat.succ_le_of_lt hl)
    have hhi : (p:ℝ) ≤ v*X := (Nat.cast_le.mpr hh).trans (Nat.floor_le (mul_nonneg hv.le hX))
    have hA' : 0 < A+1 := by positivity
    have he : v*X=((N:ℝ)/(A+1))^2 := by dsimp only [v,X]; rw [div_pow]; ring
    have hs := Real.sqrt_le_sqrt hhi
    rw [he,Real.sqrt_sq (div_nonneg (Nat.cast_nonneg _) hA'.le)] at hs
    have hfit : A*Real.sqrt p ≤ N := calc
      _ ≤ (A+1)*Real.sqrt p := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.sqrt_nonneg _)
      _ ≤ (A+1)*((N:ℝ)/(A+1)) := mul_le_mul_of_nonneg_left hs hA'.le
      _ = _ := by field_simp
    have h := h₀ p (Nat.cast_le.mp (hlate.trans hlo)) hprime N hfit
    rw [deningerRatExp_apply] at h
    push_cast at h
    exact (mul_le_mul_of_nonneg_left hlo hc.le).trans (h.trans (sub_le_self _ (Nat.cast_nonneg _)))
  have hsum := sum_le_sum (s := S) fun p hp =>
    mul_le_mul_of_nonneg_right (hrange p hp) (Real.log_natCast_nonneg p)
  rw [← mul_sum] at hsum
  have h := (mul_le_mul_of_nonneg_left hmass (mul_nonneg hc.le (mul_nonneg hu.le hX))).trans
    (hsum.trans (partial_log_factors (U N) S))
  calc _ = c*(u*X)*((v-u)/2*X) := by dsimp only [X]; ring
       _ ≤ _ := h

private theorem denominator_upper : ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ,
    Real.log (V N) ≤ D*(N:ℝ)^4 := by
  obtain ⟨K,hK,h⟩ := successorSquare_products_upper
  refine ⟨2*K,by positivity,fun N => ?_⟩
  induction N with
  | zero => simp [V,P,squareGeneratorPrefix]
  | succ n ih =>
    let j := n+1
    have hq := (h (m := j) (Nat.succ_pos n)).2
    have he : P j=P n*q j := prod_Ioc_succ_top (Nat.zero_le n) _
    have hv : V j ≤ V n*(q j).den := by
      change (P j).den ≤ _
      rw [he]
      exact Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero (P n).den_nz)
        (Nat.pos_of_ne_zero (q j).den_nz)) (Rat.mul_den_dvd _ _)
    have hlog := Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (P j).den_nz)) (Nat.cast_le.mpr hv)
    rw [Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr (P n).den_nz) (Nat.cast_ne_zero.mpr (q j).den_nz)] at hlog
    have hpoly : 2*(n:ℝ)^4+((j:ℝ)*(j:ℝ)^2+(j:ℝ)^2) ≤ 2*(j:ℝ)^4 := by
      dsimp only [j]; push_cast
      nlinarith only [Nat.cast_nonneg (α := ℝ) n,sq_nonneg (n:ℝ),pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 3]
    change Real.log (V j) ≤ 2*K*(j:ℝ)^4
    change Real.log (q j).den ≤ K*((j:ℝ)*(j:ℝ)^2+(j:ℝ)^2) at hq
    linarith only [ih,hq,hlog,mul_le_mul_of_nonneg_left hpoly hK]

private theorem price_eq (N : ℕ) :
    Real.log (P N:ℝ)=Real.log (U N)-Real.log (V N) := by
  have hr := squareGeneratorPrefix_pos N
  have hn : (((P N).num:ℤ):ℝ) ≠ 0 := Int.cast_ne_zero.mpr (Rat.num_pos.mpr hr).ne'
  have hd : ((P N).den:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (P N).den_nz
  have ha : ((U N):ℝ)=|((P N).num:ℝ)| := by
    rw [← Int.cast_abs,← Int.natCast_natAbs,Int.cast_natCast]
  rw [ha,Real.log_abs,Rat.cast_def,Real.log_div hn hd]

/-- At every sufficiently large endpoint both logarithmic heights of
the reduced ordinary square-generator prefix have quartic order. -/
theorem reduced_square_prefix_quartic_heights : ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ᶠ N : ℕ in atTop,
      c*(N:ℝ)^4 ≤ Real.log (squareGeneratorPrefix N).num.natAbs ∧
      Real.log (squareGeneratorPrefix N).num.natAbs ≤ C*(N:ℝ)^4 ∧
      c*(N:ℝ)^4 ≤ Real.log (squareGeneratorPrefix N).den ∧
      Real.log (squareGeneratorPrefix N).den ≤ C*(N:ℝ)^4 := by
  obtain ⟨b,hb,hnum⟩ := numerator_lower
  obtain ⟨D,hD,hden⟩ := denominator_upper
  have hw : zetaZeroWidth ≤ 3/8 := ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths.trans (by norm_num)
  obtain ⟨K,hK,hprice⟩ := (zetaZeroWidth_le_iff_square_generator_prefix
    (by norm_num : (0:ℝ) ≤ 3/8) (by norm_num)).mp hw
  have hlim := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/4)).comp tendsto_natCast_atTop_atTop).const_mul K
  rw [mul_zero] at hlim
  refine ⟨b/2,D+b,half_pos hb,add_nonneg hD hb.le,?_⟩
  filter_upwards [hnum,hlim.eventually_le_const (half_pos hb),eventually_ge_atTop 1] with N hn hsmall hN
  have hx : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hpow : (N:ℝ)^((3:ℝ)+2*(3/8:ℝ))=(N:ℝ)^(-(1/4):ℝ)*(N:ℝ)^4 := by
    rw [← Real.rpow_natCast (N:ℝ) 4,← Real.rpow_add hx]; congr 1; norm_num
  have hp := hprice N
  rw [hpow] at hp
  change K*(N:ℝ)^(-(1/4):ℝ) ≤ b/2 at hsmall
  have hsub : |Real.log (P N:ℝ)| ≤ b/2*(N:ℝ)^4 := hp.trans (by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hsmall (pow_nonneg hx.le _))
  rw [price_eq,abs_le] at hsub
  have hbpow := mul_nonneg hb.le (pow_nonneg hx.le 4)
  exact ⟨by linarith only [hn,hbpow],by linarith only [hsub.2,hden N,hbpow],
    by linarith only [hn,hsub.2],by linarith only [hden N,hbpow]⟩

#print axioms reduced_square_prefix_quartic_heights

end GaloisForLFunctions.CountingHolography.Sections
