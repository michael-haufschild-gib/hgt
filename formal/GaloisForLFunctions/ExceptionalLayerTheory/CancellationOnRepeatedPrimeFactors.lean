import GaloisForLFunctions.ExceptionalLayerTheory.CancellationOnTruncatedQuotientIntervals
import GaloisForLFunctions.ExceptionalLayerTheory.TheHalfWeightedMassOfProperPrimePowers
import GaloisForLFunctions.ExceptionalLayerTheory.TheInnerWeightOnLargePrimeMultiples
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Removing repeated primes from the two long factors

A proper prime-power first factor has logarithmic total mass at the
half weight. When an ordinary first prime divides the second factor,
dilation by that prime preserves its bounded prefixes and divides the
remaining horizon by the square of the prime.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Signed sum over the complementary factor at fixed first argument. -/
def factorSlice (D R X Y u : ℕ) : ℝ :=
  ∑ v ∈ Ioc (Y/u) (X/u), innerJump D v*centeredPrimeWeight R (X/u/v)

/-- Complementary factors coprime to the specified first argument. -/
def coprimeSlice (D R X Y p : ℕ) : ℝ :=
  ∑ v ∈ Ioc (Y/p) (X/p) with p.Coprime v, innerJump D v*centeredPrimeWeight R (X/p/v)

private theorem sqrt_div_bound (X u : ℕ) :
    ((Nat.sqrt (X/u) : ℕ) : ℝ) ≤ Real.sqrt X/Real.sqrt u := by
  have hs : ((Nat.sqrt (X/u) : ℕ) : ℝ) ≤ Real.sqrt (X/u : ℕ) :=
    (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by
      simpa only [sq,Nat.cast_mul] using (by exact_mod_cast Nat.sqrt_le (X/u) :
        ((Nat.sqrt (X/u) : ℕ) : ℝ)*Nat.sqrt (X/u) ≤ (X/u : ℕ)))
  exact hs.trans ((Real.sqrt_le_sqrt (Nat.cast_div_le (m := X) (n := u))).trans_eq
    (Real.sqrt_div (Nat.cast_nonneg X) u))

private theorem divisible_slice {p : ℕ} (hp : 0 < p) (L M : ℕ) (f : ℕ → ℝ) :
    (∑ v ∈ Ioc L M with p ∣ v, f v) = ∑ t ∈ Ioc (L/p) (M/p), f (p*t) := by
  have he : ((Ioc L M).filter fun v => p ∣ v) = (Ioc (L/p) (M/p)).image (fun t => p*t) := by
    ext v
    constructor
    · intro h
      obtain ⟨hh,hd⟩ := mem_filter.mp h
      obtain ⟨hl,hu⟩ := mem_Ioc.mp hh
      have hv : v/p*p=v := Nat.div_mul_cancel hd
      exact mem_image.mpr ⟨v/p,mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hp).mpr (by rwa [hv]),
        (Nat.le_div_iff_mul_le hp).mpr (by rwa [hv])⟩,by simpa only [Nat.mul_comm] using hv⟩
    · intro h
      obtain ⟨t,ht,rfl⟩ := mem_image.mp h
      obtain ⟨hl,hu⟩ := mem_Ioc.mp ht
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hp).mp hl,
        by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hu⟩,dvd_mul_right _ _⟩
  rw [he,sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hp hab

private theorem slice_difference {p : ℕ} (hp : p.Prime) (D R X Y : ℕ) :
    factorSlice D R X Y p-coprimeSlice D R X Y p =
      ∑ t ∈ Ioc (Y/(p*p)) (X/(p*p)), innerJump D (p*t)*centeredPrimeWeight R (X/(p*p)/t) := by
  let S := Ioc (Y/p) (X/p)
  let f := fun v => innerJump D v*centeredPrimeWeight R (X/p/v)
  have hc := sum_filter_add_sum_filter_not S (fun v => p ∣ v) f
  have hco : S.filter (fun v => ¬p ∣ v) = S.filter (fun v => p.Coprime v) :=
    filter_congr fun v _ => hp.coprime_iff_not_dvd.symm
  rw [hco] at hc
  change (∑ v ∈ S, f v)-(∑ v ∈ S with p.Coprime v, f v) = _
  rw [←hc,add_sub_cancel_right]
  dsimp [S]
  rw [divisible_slice hp.pos]
  simp only [f,Nat.div_div_eq_div_mul,Nat.mul_assoc]

/-- Uniform bounds for a full complementary slice and its shared-prime
part. The latter gains one whole prime in the denominator. -/
theorem factor_slice_bounds :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {D R : ℕ}, 1 ≤ D → 1 ≤ R → ∀ X Y : ℕ,
      let A := K*((D+1 : ℕ) : ℝ)*R*Real.sqrt X
      (∀ u, |factorSlice D R X Y u| ≤ A/Real.sqrt u) ∧
      (∀ p, p.Prime → 2*(D+1)<p → |factorSlice D R X Y p-coprimeSlice D R X Y p| ≤ A/p) := by
  obtain ⟨F,hF,hw⟩ := centeredPrimeWeight_uniform
  obtain ⟨C,hC,hm⟩ := mass_uniform
  refine ⟨4*(2+C)*F,by positivity,?_⟩
  intro D R hD hR X Y A
  let B := (2+C)*((D+1 : ℕ) : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb : 2+mass (D+1) ≤ B := by
    have hh := hm (D+1) (Nat.succ_pos D)
    dsimp [B]; push_cast at hh ⊢
    linarith only [hh,Nat.cast_nonneg (α := ℝ) D]
  have eqI (t : ℕ) : Ioc 0 t = Icc 1 t := by ext; simp only [mem_Ioc,mem_Icc]; omega
  have slice (a : ℕ → ℝ) (u L : ℕ) (ha : ∀ t, |∑ v ∈ Ioc 0 t, a v| ≤ B) :
      |∑ v ∈ Ioc L (X/u), a v*centeredPrimeWeight R (X/u/v)| ≤ A/Real.sqrt u := by
    have hh := abs_truncated_quotient_pair (N := X/u) L a (centeredPrimeWeight R) hB (mul_nonneg hF (Nat.cast_nonneg R))
      (fun t _ => ha t) (hw hR)
    exact hh.trans ((mul_le_mul_of_nonneg_left (sqrt_div_bound X u) (show 0 ≤ 4*B*(F*R) by positivity)).trans_eq
      (by dsimp [A,B]; ring))
  constructor
  · intro u
    exact slice _ u _ fun t => by rw [eqI]; exact (innerJump_prefix_bound D t).trans (by linarith only [hb])
  · intro p hp hlarge
    rw [slice_difference hp]
    have hh := slice (fun v => innerJump D (p*v)) (p*p) (Y/(p*p)) (fun t => by
      rw [eqI]; exact (innerJump_prime_multiple_prefix_bound hD hp hlarge t).trans hb)
    have hs : Real.sqrt ((p*p : ℕ) : ℝ) = p := by
      rw [Nat.cast_mul,←sq,Real.sqrt_sq (Nat.cast_nonneg p)]
    rwa [hs] at hh

/-- First factors above the divisor stencil with all complementary arguments. -/
def longFactorRow (D R X Y : ℕ) : ℝ :=
  ∑ u ∈ Ioc (2*(D+1)) X, vonMangoldt u*factorSlice D R X Y u

/-- Signed row over ordinary primes coprime to the complementary factor. -/
def coprimePrimeRow (D R X Y : ℕ) : ℝ :=
  ∑ p ∈ (Ioc (2*(D+1)) X).filter Nat.Prime, vonMangoldt p*coprimeSlice D R X Y p

/-- All proper prime-power first factors and all common primes can be
removed uniformly in the product interval and both weight cutoffs. -/
theorem repeated_prime_factors_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {D R X : ℕ}, 1 ≤ D → 1 ≤ R → 1 ≤ X → ∀ Y : ℕ,
      |longFactorRow D R X Y-coprimePrimeRow D R X Y| ≤
        K*((D+1 : ℕ) : ℝ)*R*Real.sqrt X*(1+Real.log X) := by
  obtain ⟨K,hK,h⟩ := factor_slice_bounds
  let C := Real.log 4+4
  have hC : 1 ≤ C := by dsimp [C]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  refine ⟨K*(7*C+1),by positivity,?_⟩
  intro D R X hD hR hX Y
  let A := K*((D+1 : ℕ) : ℝ)*R*Real.sqrt X
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨hu,hp⟩ := h hD hR X Y
  let S := Ioc (2*(D+1)) X
  have hsub : S ⊆ Icc 1 X := fun n hn => mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega,(mem_Ioc.mp hn).2⟩
  have hpp (n : ℕ) : 0 ≤ primePowerPart n := by unfold primePowerPart; split <;> first | exact le_rfl | exact vonMangoldt_nonneg
  unfold longFactorRow coprimePrimeRow
  rw [sum_filter,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ u ∈ S, A*(primePowerPart u/Real.sqrt u+vonMangoldt u/u) := by
      apply sum_le_sum
      intro u hs
      have hn := (mem_Ioc.mp hs).1
      by_cases prime : u.Prime
      · rw [if_pos prime,←mul_sub,abs_mul,abs_of_nonneg vonMangoldt_nonneg]
        apply (mul_le_mul_of_nonneg_left (hp u prime hn) vonMangoldt_nonneg).trans_eq
        change vonMangoldt u*(A/u) = _
        simp only [primePowerPart,if_pos prime,zero_div,zero_add]; ring
      · rw [if_neg prime,sub_zero,abs_mul,abs_of_nonneg vonMangoldt_nonneg]
        apply (mul_le_mul_of_nonneg_left (hu u) vonMangoldt_nonneg).trans
        change vonMangoldt u*(A/Real.sqrt u) ≤ _
        simp only [primePowerPart,if_neg prime,mul_add]
        have hpos := mul_nonneg hA (div_nonneg (@vonMangoldt_nonneg u) (Nat.cast_nonneg u))
        exact (show vonMangoldt u*(A/Real.sqrt u) = A*(vonMangoldt u/Real.sqrt u) by ring).le.trans
          (le_add_of_nonneg_right hpos)
    _ ≤ A*((∑ u ∈ Icc 1 X, primePowerPart u/Real.sqrt u)+(∑ u ∈ Icc 1 X, vonMangoldt u/u)) := by
      rw [←mul_sum,←sum_add_distrib]
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ =>
        add_nonneg (div_nonneg (hpp u) (Real.sqrt_nonneg _)) (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg u)))) hA
    _ ≤ A*(3*C*(2+Real.log X)+(Real.log X+C)) := by
      have hh := (abs_le.mp (Mertens.mertens_first X hX)).2
      exact mul_le_mul_of_nonneg_left (add_le_add (proper_power_half_weight X) (by dsimp [C]; linarith only [hh])) hA
    _ ≤ _ := by
      have hh : 3*C*(2+Real.log X)+(Real.log X+C) ≤ (7*C+1)*(1+Real.log X) := by
        linarith only [mul_nonneg (zero_le_one.trans hC) (Real.log_natCast_nonneg X)]
      exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by dsimp [A]; ring)

#print axioms repeated_prime_factors_bound
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
