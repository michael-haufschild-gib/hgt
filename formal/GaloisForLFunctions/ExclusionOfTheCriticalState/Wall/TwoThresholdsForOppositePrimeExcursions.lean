import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositePrimeExcursionsOnOneFixedBand
import Mathlib.Data.Nat.Log

/-!
# Two separate thresholds for opposite prime excursions

In the level-set argument of Guo, Wang and Yuan, Lemma 3.5
(arXiv:2611.22568), a pointwise restriction on superlevels precedes the
summation over heights. For two prime discrepancies we retain a separate
height on each axis. A single rectangle captures the signed excursions at
a common numerator with at most a squared logarithmic loss.
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

private def dyadicBin (t : ℝ) := Nat.log 2 ⌊t⌋₊

private theorem dyadic_bounds {t : ℝ} (ht : 1 ≤ t) :
    (2:ℝ)^dyadicBin t ≤ t ∧ t < 2*(2:ℝ)^dyadicBin t := by
  have hn : 0 < ⌊t⌋₊ := Nat.floor_pos.mpr ht
  have hlow := Nat.pow_log_le_self 2 hn.ne'
  have hhigh := Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) ⌊t⌋₊)
  refine ⟨(show (2:ℝ)^dyadicBin t ≤ (⌊t⌋₊:ℝ) by exact_mod_cast hlow).trans
    (Nat.floor_le (zero_le_one.trans ht)), (Nat.lt_floor_add_one t).trans_le ?_⟩
  rw [mul_comm]
  exact_mod_cast (show ⌊t⌋₊+1 ≤ 2^dyadicBin t*2 by simpa only [pow_succ,dyadicBin] using hhigh)

/-- Weighted upper rectangle at the two independent dyadic thresholds. -/
def excursionRectangle (S : Finset ℕ) (f g w : ℕ → ℝ) (r : ℕ × ℕ) : ℝ :=
  (2:ℝ)^r.1 * 2^r.2 *
    ∑ i ∈ S.filter (fun i => (2:ℝ)^r.1 ≤ f i ∧ (2:ℝ)^r.2 ≤ g i), w i

/-- For two heights between 1 and U, one rectangle captures the product
moment up to 4(1+floor(log₂ U))². The weights are arbitrary and nonnegative. -/
theorem product_moment_at_two_thresholds (S : Finset ℕ) (f g w : ℕ → ℝ) (U : ℕ)
    (hS : ∀ i ∈ S, f i ∈ Set.Icc 1 (U:ℝ) ∧ g i ∈ Set.Icc 1 (U:ℝ) ∧ 0≤w i) :
    ∃ r : ℕ × ℕ, r.1 ≤ Nat.log 2 U ∧ r.2 ≤ Nat.log 2 U ∧
      (∑ i ∈ S, f i*g i*w i) ≤ 4*((Nat.log 2 U:ℝ)+1)^2 * excursionRectangle S f g w r := by
  let B := Nat.log 2 U
  let R := range (B+1) ×ˢ range (B+1)
  let bin := fun i => (dyadicBin (f i),dyadicBin (g i))
  have hmap (i : ℕ) (hi : i∈S) : bin i ∈ R := by
    obtain ⟨hf,hg,_⟩ := hS i hi
    simp only [bin,R,B,mem_product,mem_range,dyadicBin]
    exact ⟨Nat.lt_succ_of_le (Nat.log_mono_right (Nat.floor_le_of_le hf.2)),
      Nat.lt_succ_of_le (Nat.log_mono_right (Nat.floor_le_of_le hg.2))⟩
  have hR : R.Nonempty := ⟨(0,0),mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩⟩
  obtain ⟨r,hr,hmax⟩ := R.exists_max_image (excursionRectangle S f g w) hR
  have hcell (z : ℕ × ℕ) :
      (∑ i ∈ S.filter (bin · = z), f i*g i*w i) ≤ 4*excursionRectangle S f g w z := by
    let D := S.filter (bin · = z)
    let E := S.filter fun i => (2:ℝ)^z.1 ≤ f i ∧ (2:ℝ)^z.2 ≤ g i
    have hd {i : ℕ} (hi : i∈D) : i∈S ∧ dyadicBin (f i)=z.1 ∧ dyadicBin (g i)=z.2 := by
      obtain ⟨hi,he⟩ := mem_filter.mp hi
      change (dyadicBin (f i),dyadicBin (g i))=z at he
      rw [←he]
      exact ⟨hi,rfl,rfl⟩
    have hsub : D ⊆ E := by
      intro i hi
      obtain ⟨his,hr₁,hr₂⟩ := hd hi
      obtain ⟨hf,hg,_⟩ := hS i his
      exact mem_filter.mpr ⟨his,hr₁ ▸ (dyadic_bounds hf.1).1,hr₂ ▸ (dyadic_bounds hg.1).1⟩
    calc _ ≤ ∑ i ∈ D, (4*(2:ℝ)^z.1*2^z.2)*w i := by
           apply sum_le_sum
           intro i hi
           obtain ⟨his,hr₁,hr₂⟩ := hd hi
           obtain ⟨hf,hg,hw⟩ := hS i his
           apply mul_le_mul_of_nonneg_right _ hw
           rw [← hr₁,← hr₂]
           exact (mul_le_mul (dyadic_bounds hf.1).2.le (dyadic_bounds hg.1).2.le
             (zero_le_one.trans hg.1) (by positivity)).trans_eq (by ring)
         _ = (4*(2:ℝ)^z.1*2^z.2)*∑ i ∈ D, w i := (mul_sum ..).symm
         _ ≤ (4*(2:ℝ)^z.1*2^z.2)*∑ i ∈ E, w i :=
           mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
             (fun i hi _ => (hS i (mem_filter.mp hi).1).2.2)) (by positivity)
         _ = _ := by unfold excursionRectangle; dsimp only [E]; ring
  obtain ⟨hr₁,hr₂⟩ := mem_product.mp hr
  refine ⟨r,Nat.le_of_lt_succ (mem_range.mp hr₁),Nat.le_of_lt_succ (mem_range.mp hr₂),?_⟩
  rw [← sum_fiberwise_of_maps_to hmap]
  calc _ ≤ ∑ _z ∈ R, 4*excursionRectangle S f g w r := sum_le_sum fun z hz =>
          (hcell z).trans (mul_le_mul_of_nonneg_left (hmax z hz) (by norm_num))
       _ = _ := by simp only [R,B,sum_const,card_product,card_range,nsmul_eq_mul,Nat.cast_add,
                      Nat.cast_mul,Nat.cast_one]; ring

/-- No observable denominator exceeds the numerator. This gives a uniform
height bound independent of the chosen flank and the band endpoints. -/
theorem odd_prime_excess_bound_by_numerator (S : Finset ℕ) (H : ℕ) :
    |oddQuotientPrimeExcess S H| ≤ 4*(H:ℝ) := by
  let D := S.filter fun n => 0<n ∧ n≤H
  have he : oddQuotientPrimeExcess D H=oddQuotientPrimeExcess S H := by
    unfold oddQuotientPrimeExcess
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases h : 0<n ∧ n≤H
    · rw [if_pos h]
    · rw [if_neg h]
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · simp
      · simp [Nat.div_eq_of_lt (lt_of_not_ge (fun hn => h ⟨hp,hn⟩))]
  rw [← he]
  refine (oddQuotientPrimeExcess_le D H H (fun i hi => mem_Ioc.mpr (mem_filter.mp hi).2)).trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)])
    (Nat.cast_nonneg H)

private def middleHeight (s : ℝ) (k L H : ℕ) : ℝ := max 0 (s*oddQuotientPrimeExcess (Ioc k L) H)
private def flankHeight (left : Bool) (s : ℝ) (k L H : ℕ) : ℝ :=
  max 0 ((-s)*oddQuotientPrimeExcess (middleTestFlank left k L H) H)

/-- One pair of separate amplitude cuts on the actual arithmetic bands.
Each common numerator retains its original reciprocal-square weight. -/
def primeExcursionRectangle (left : Bool) (s a g d T : ℝ) (k L : ℕ) (r : ℕ × ℕ) : ℝ :=
  excursionRectangle (largeOppositePrimeNumerators left s a g d T k L)
    (middleHeight s k L) (flankHeight left s k L) (fun H => 1/(H:ℝ)^2) r

theorem opposite_prime_moment_at_two_thresholds (left : Bool) {s a g d T : ℝ} (k L : ℕ)
    (hs : s=1 ∨ s= -1) (ha : 1 ≤ a*Real.exp (g*T)) :
    let S := largeOppositePrimeNumerators left s a g d T k L
    let B := Nat.log 2 (4*L^2)
    ∃ r : ℕ × ℕ, r.1≤B ∧ r.2≤B ∧ (∑ H ∈ S, oppositePrimeProduct left s k L H) ≤
      4*((B:ℝ)+1)^2*primeExcursionRectangle left s a g d T k L r := by
  dsimp only
  let S := largeOppositePrimeNumerators left s a g d T k L
  have hh (H : ℕ) (hH : H∈S) := mem_filter.mp hH
  apply (product_moment_at_two_thresholds S (middleHeight s k L) (flankHeight left s k L)
    (fun H => 1/(H:ℝ)^2) (4*L^2) ?_).imp
  · intro r h
    simpa only [S,primeExcursionRectangle,oppositePrimeProduct,middleHeight,flankHeight,mul_one_div] using h
  · intro H hj
    obtain ⟨hnum,hpos⟩ := hh H hj
    obtain ⟨hrange,hT,_⟩ := mem_filter.mp hnum
    have hp : 0<H := Nat.cast_pos.mp ((Real.exp_pos _).trans_le hT)
    have hroot := (Real.one_le_sqrt).mpr (Nat.one_le_cast.mpr hp)
    have h₁ : 1 ≤ a*Real.exp (g*T)*Real.sqrt H := one_le_mul_of_one_le_of_one_le ha hroot
    have hsg : |s|=1 := by rcases hs with rfl|rfl <;> norm_num
    have hcap (t : ℝ) (ht : |t|=1) (D : Finset ℕ) :
        max 0 (t*oddQuotientPrimeExcess D H) ≤ ((4*L^2:ℕ):ℝ) := by
      apply max_le (Nat.cast_nonneg _)
      calc _ ≤ |t*oddQuotientPrimeExcess D H| := le_abs_self _
           _ = |oddQuotientPrimeExcess D H| := by rw [abs_mul,ht,one_mul]
           _ ≤ 4*(H:ℝ) := odd_prime_excess_bound_by_numerator D H
           _ ≤ _ := by exact_mod_cast (Nat.mul_le_mul_left 4 (mem_range.mp hrange).le)
    refine ⟨⟨(h₁.trans hpos.1.le).trans (le_max_right ..),hcap _ hsg _⟩,
      ⟨(h₁.trans hpos.2.le).trans (le_max_right ..),hcap _ (abs_neg s |>.trans hsg) _⟩,by positivity⟩

/-- A violation of RH forces a rectangle with two fixed signed heights per
test. Both cut exponents are at most log₂(4L²). -/
theorem rh_or_large_two_threshold_prime_excursions : RiemannHypothesis ∨
    ∃ a c g d r : ℝ, 0<a ∧ 0<c ∧ 0<g ∧ 0<d ∧ d≤1/4 ∧ 0<r ∧
      ∀ η : ℝ, 0<η → η≤r → ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η)≤Real.log (k i) ∧ Real.log (k i)≤T i) ∧
        let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
        ∀ᶠ i in atTop, ∃ (s : ℝ) (left : Bool) (j : ℕ × ℕ), (s=1 ∨ s= -1) ∧
          j.1≤Nat.log 2 (4*(L i)^2) ∧ j.2≤Nat.log 2 (4*(L i)^2) ∧
          c*a^2*Real.exp ((1/2+3*g)*T i) <
            (L i:ℝ)*(4*((Nat.log 2 (4*(L i)^2):ℝ)+1)^2*
              primeExcursionRectangle left s a g d (T i) (k i) (L i) j) := by
  obtain hr | ⟨_,_,_,a,c,g,d,r,_,_,_,_,_,ha,hc,hg,hd,hd₁,hr,hseq⟩ :=
    riemannHypothesis_or_fixed_band_opposite_prime_moment
  · exact Or.inl hr
  refine Or.inr ⟨a,c,g,d,r,ha,hc,hg,hd,hd₁,hr,fun η hη hηr => ?_⟩
  obtain ⟨T,k,hT,hk,_,hs⟩ := hseq η hη hηr
  let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
  have hbase := ((Real.tendsto_exp_atTop.comp (hT.const_mul_atTop hg)).const_mul_atTop ha).eventually_ge_atTop 1
  refine ⟨T,k,hT,hk,?_⟩
  filter_upwards [hs,hbase] with i hi hb
  obtain ⟨_,_,s,left,_,_,hsign,_,_,_,_,_,hp⟩ := hi
  obtain ⟨j,h₁,h₂,hj⟩ := opposite_prime_moment_at_two_thresholds left (k i) (L i) hsign hb
  exact ⟨s,left,j,hsign,h₁,h₂,hp.trans_le (mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg _))⟩

#print axioms product_moment_at_two_thresholds
#print axioms rh_or_large_two_threshold_prime_excursions

end GaloisForLFunctions.ExclusionOfTheCriticalState
