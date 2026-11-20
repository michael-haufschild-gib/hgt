import GaloisForLFunctions.ExceptionalLayerTheory.PrimeRadicalWeightsOfTheDerivativeAreas
import GaloisForLFunctions.ExceptionalLayerTheory.OneLogarithmicDerivativeOrderReadsTheXiHistogram
import Mathlib.Data.Nat.Find

/-!
# Complete arithmetic classification of a prime-radical area

Writing m = a^p d with d free of nontrivial p-th powers, derivative
order 2p−1 sees the integer weight a in class d. For prime p equality
of two area moments is equivalent to equality of the total integer
weight in every class, with no upper bound on multiplicities. This
specifies the information retained even beyond the first collision 2^p.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Largest integer whose p-th power divides n, bounded by n. -/
def multiplicityRootPart (p n : ℕ) := Nat.findGreatest (fun a => a^p ∣ n) n

/-- The p-th-power-free part of a positive multiplicity. -/
def multiplicityPowerFreePart (p n : ℕ) := n/(multiplicityRootPart p n)^p

theorem multiplicity_power_free_decomposition {p n : ℕ} (hp : 0<p) (hn : 0<n) :
    0<multiplicityRootPart p n ∧ 0<multiplicityPowerFreePart p n ∧
      (multiplicityRootPart p n)^p*multiplicityPowerFreePart p n=n ∧
      ∀ d, d^p ∣ multiplicityPowerFreePart p n → d<2 := by
  let A := multiplicityRootPart p n
  let D := multiplicityPowerFreePart p n
  have h₁ : (1:ℕ)^p ∣ n := by simp
  have hA : 0<A := Nat.le_findGreatest hn h₁
  have hdiv : A^p ∣ n := Nat.findGreatest_spec hn h₁
  have he : A^p*D=n := (Nat.mul_comm ..).trans (Nat.div_mul_cancel hdiv)
  have hD : 0<D := Nat.pos_of_ne_zero fun hz => by rw [hz,mul_zero] at he; exact hn.ne' he.symm
  refine ⟨hA,hD,he,?_⟩
  intro d hd
  by_contra! htwo
  obtain ⟨k,hk⟩ := hd
  have hnew : (A*d)^p ∣ n := ⟨k,by rw [←he,hk,mul_pow,mul_assoc]⟩
  have had : 1≤A*d := Nat.mul_pos hA (by omega)
  have hbound : A*d≤n := (le_self_pow had hp.ne').trans (Nat.le_of_dvd hn hnew)
  have hmax : A*d≤A := Nat.le_findGreatest hbound hnew
  have hlt : A<A*d := by simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left (by omega : 1<d) hA
  exact hlt.not_ge hmax

theorem radical_weight_by_power_free_part {p n : ℕ} (hp : 0<p) (hn : 0<n) :
    (n:ℝ)^((p:ℝ)⁻¹) = (multiplicityRootPart p n:ℝ)*
      (multiplicityPowerFreePart p n:ℝ)^((p:ℝ)⁻¹) := by
  have he : (n:ℝ)=(multiplicityRootPart p n:ℝ)^p*(multiplicityPowerFreePart p n:ℝ) := by
    exact_mod_cast (multiplicity_power_free_decomposition hp hn).2.2.1.symm
  conv_lhs => rw [he]
  rw [Real.mul_rpow (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _),
    Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hp.ne']

/-- Integer weight retained by the area in a single p-th-power-free class. -/
def powerFreeClassCharge {ι : Type*} (p : ℕ) (S : Finset ι) (m : ι → ℕ) (a : ι → ℤ) (d : ℕ) : ℤ :=
  ∑ i ∈ S with multiplicityPowerFreePart p (m i)=d, a i*(multiplicityRootPart p (m i):ℤ)

/-- A signed sum of p-th roots vanishes precisely when the integer
charge vanishes separately in every occupied power-free class. -/
theorem radical_sum_zero_iff_class_charges {ι : Type*} {p : ℕ} (hp : p.Prime)
    (S : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ S, 0 < m i) (a : ι → ℤ) :
    (∑ i ∈ S, (a i:ℝ)*(m i:ℝ)^((p:ℝ)⁻¹))=0 ↔
      ∀ d ∈ S.image (fun i => multiplicityPowerFreePart p (m i)), powerFreeClassCharge p S m a d=0 := by
  classical
  let core (i : ι) := multiplicityPowerFreePart p (m i)
  let C := S.image core
  let v (d : C) := (d.val:ℝ)^((p:ℝ)⁻¹)
  let charge := powerFreeClassCharge p S m a
  have hfree (d : C) : 0<d.val ∧ ∀ b, b^p ∣ d.val → b<2 := by
    obtain ⟨i,hi,hd⟩ := Finset.mem_image.mp d.property
    rw [←hd]
    have h := multiplicity_power_free_decomposition hp.pos (hm i hi)
    exact ⟨h.2.1,h.2.2.2⟩
  have hind : LinearIndependent ℚ v := independent_prime_radical_classes hp Subtype.val
    (fun d => (hfree d).1) (fun d e hne q hq => hne (Subtype.ext
      (power_free_ratio_rigid hp.pos (hfree d).1 (hfree e).1 (hfree d).2 (hfree e).2 q hq)))
  have regroup : (∑ i ∈ S, (a i:ℝ)*(m i:ℝ)^((p:ℝ)⁻¹)) =
      ∑ d : C, (charge d.val:ℝ)*v d := by
    calc
      _ = ∑ d ∈ C, ∑ i ∈ S with core i=d, (a i:ℝ)*(m i:ℝ)^((p:ℝ)⁻¹) :=
        (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem core hi) _).symm
      _ = ∑ d ∈ C, (charge d:ℝ)*(d:ℝ)^((p:ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro d _
        simp only [charge,powerFreeClassCharge,Int.cast_sum,Int.cast_mul,Int.cast_natCast,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨his,he⟩ := Finset.mem_filter.mp hi
        rw [radical_weight_by_power_free_part hp.pos (hm i his),show multiplicityPowerFreePart p (m i)=d from he,mul_assoc]
      _ = _ := (Finset.sum_coe_sort ..).symm
  rw [regroup]
  constructor
  · intro h d hd
    have hh : ∑ c : C, ((charge c.val:ℚ) • v c)=0 := by
      simpa only [Rat.smul_def,Rat.cast_intCast] using h
    have hz := linearIndependent_iff'.mp hind Finset.univ (fun c => (charge c.val:ℚ)) hh
      ⟨d,hd⟩ (Finset.mem_univ _)
    exact_mod_cast hz
  · intro h
    exact Finset.sum_eq_zero fun c _ => by rw [show charge c.val=0 from h _ c.property,Int.cast_zero,zero_mul]

/-- Two integer histograms give identical derivative-(2p−1) areas
exactly when each occupied power-free class receives the same root weight. -/
theorem prime_area_equal_iff_class_charges {p W : ℕ} (hp : p.Prime) (a b : Fin W → ℕ) :
    divisorAreaMoment (2*p-1) (fun i => (a i:ℝ))=divisorAreaMoment (2*p-1) (fun i => (b i:ℝ)) ↔
      ∀ d ∈ Finset.univ.image (fun i : Fin W => multiplicityPowerFreePart p (i.val+1)),
        powerFreeClassCharge p Finset.univ (fun i : Fin W => i.val+1) (fun i => (a i:ℤ)-(b i:ℤ)) d=0 := by
  rw [←sub_eq_zero,divisorAreaMoment,divisorAreaMoment,←Finset.sum_sub_distrib]
  simpa only [prime_order_weight hp.pos,←mul_sub,Int.cast_sub,Int.cast_natCast,mul_comm] using
    radical_sum_zero_iff_class_charges hp Finset.univ (fun i : Fin W => i.val+1)
      (fun i _ => Nat.succ_pos _) (fun i => (a i:ℤ)-(b i:ℤ))

#print axioms multiplicity_power_free_decomposition
#print axioms radical_sum_zero_iff_class_charges
#print axioms prime_area_equal_iff_class_charges
end GaloisForLFunctions.ExceptionalLayerTheory
