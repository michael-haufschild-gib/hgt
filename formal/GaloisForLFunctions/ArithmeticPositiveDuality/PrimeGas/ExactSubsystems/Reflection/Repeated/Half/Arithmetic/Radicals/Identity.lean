import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Heat

/-! # A homogeneous polynomial identity for thermal reflection at a real probe -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Radicals

open Finset Real
open _root_.HTGeometry (finiteGibbsPartition)

variable {I : Type*} [Fintype I] {R : Type*} [CommSemiring R]

def except (b : I → R) (i : I) : R := by classical exact ∏ y ∈ univ.erase i, b y

def condition (b : I → R) := (∑ i, except b i)^(Fintype.card I) =
  (∏ i, b i)^(Fintype.card I-2)*(∑ i, b i)^(Fintype.card I)

theorem map_condition {S : Type*} [CommSemiring S] (f : R →+* S) {b : I → R}
    (h : condition b) : condition (fun i => f (b i)) := by
  classical
  simpa only [condition,except,map_mul,map_sum,map_pow,map_prod] using congrArg f h

/-- After clearing the geometric mean, coincidence is a polynomial equality in
the uncentered exponential weights. Its coefficients are integers at every real probe. -/
theorem thermal_condition_iff (E : I → ℝ) (t : ℝ) (hn : 2 ≤ Fintype.card I) :
    finiteGibbsPartition t (centered E)=finiteGibbsPartition (-t) (centered E) ↔
    condition (fun i => exp (t*E i)) := by
  classical
  let b := fun i => exp (t*E i)
  let g := exp (t*meanEnergy E)
  let n := Fintype.card I
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (show n≠0 by omega)
  have ng : g^n=∏ i, b i := by
    rw [← exp_sum,← mul_sum]
    change (exp (t*meanEnergy E))^n=exp _
    rw [← exp_nat_mul]
    congr 1
    unfold meanEnergy
    change (n : ℝ)*(t*((∑ i, E i)/n))=_
    field_simp
  have read (i : I) : exp (-t*centered E i)=g / b i := by
    rw [← exp_sub]
    congr 1
    unfold centered
    ring
  have other (i : I) : exp (-(-t)*centered E i)=b i / g := by
    rw [← exp_sub]
    congr 1
    unfold centered
    ring
  let B := ∑ i, except b i
  let D := ∑ i, b i
  have divided (i : I) : g^n * (g / b i)=g*except b i := by
    rw [ng,← prod_erase_mul univ b (mem_univ i)]
    change (except b i*b i)*(g / b i)=_
    field_simp [show b i≠0 from (exp_pos _).ne']
  have pos : g≠0 := (exp_pos _).ne'
  have left : g^n*finiteGibbsPartition t (centered E)=g*B := by
    simp only [finiteGibbsPartition,B,mul_sum,read,divided]
  have scale (i : I) : g*(b i/g)=b i := by field_simp [pos]
  have right : g*finiteGibbsPartition (-t) (centered E)=D := by
    simp only [finiteGibbsPartition,D,mul_sum,other,scale]
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hn
  have ex : n=2+r := hr
  have cross : finiteGibbsPartition t (centered E)=finiteGibbsPartition (-t) (centered E) ↔ g^2*B=g^n*D := by
    rw [← right,show g^2*B=g*(g*B) by ring,← left,mul_left_comm g (g^n)]
    exact ((mul_right_injective₀ (pow_ne_zero n pos)).eq_iff.trans (mul_right_injective₀ pos).eq_iff).symm
  have cancel : g^2*B=g^n*D ↔ B=g^r*D := by
    rw [ex,pow_add,mul_assoc]
    exact (mul_right_injective₀ (pow_ne_zero 2 pos)).eq_iff
  have bpos (i : I) : 0 ≤ b i := (exp_pos _).le
  have Bpos : 0 ≤ B := sum_nonneg fun i _ => prod_nonneg fun y _ => bpos y
  have Dpos : 0 ≤ D := sum_nonneg fun i _ => bpos i
  rw [cross,cancel,← pow_left_inj₀ (n := n) Bpos (mul_nonneg (pow_nonneg (show 0 ≤ g from (exp_pos _).le) r) Dpos)
    (show n≠0 by omega)]
  change (B^n=(g^r*D)^n) ↔ B^n=(∏ i, b i)^(n-2)*D^n
  rw [← ng,mul_pow,← pow_mul,← pow_mul,show n-2=r by omega,Nat.mul_comm r n]

/-- Reducing the polynomial at a place where precisely one label vanishes makes
the deleted product at that label the sole nonzero term. -/
theorem unique_zero {K : Type*} [Field K] {b : I → K} (x : I)
    (zero : b x=0) (others : ∀ y, y≠x → b y≠0) (hn : 2<Fintype.card I) : ¬condition b := by
  classical
  have good : except b x≠0 := prod_ne_zero_iff.mpr fun i hi => others i (mem_erase.mp hi).1
  have bad (y : I) (hy : y≠x) : except b y=0 :=
    prod_eq_zero (mem_erase.mpr ⟨hy.symm,mem_univ _⟩) zero
  have sum : (∑ i, except b i)=except b x := sum_eq_single_of_mem x (mem_univ x) fun y _ hy => bad y hy
  have all : (∏ i, b i)=0 := prod_eq_zero (mem_univ x) zero
  intro h
  unfold condition at h
  rw [sum,all,zero_pow (show Fintype.card I-2≠0 by omega),zero_mul] at h
  exact pow_ne_zero _ good h

#print axioms thermal_condition_iff
#print axioms unique_zero

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Radicals
