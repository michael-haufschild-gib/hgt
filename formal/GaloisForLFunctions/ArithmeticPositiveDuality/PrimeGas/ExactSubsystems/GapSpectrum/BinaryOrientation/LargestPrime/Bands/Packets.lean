import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Conditioning.Gibbs

/-! # Exact independence of observations on disjoint squarefree prime packets -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower _root_.RHTower.BAGTrace
open scoped ENNReal

private def joinPrimes {A B : Finset Nat.Primes} (h : A ⊆ B) : ↥A ⊕ ↥(B\A) ≃ ↥B where
  toFun := Sum.elim (fun p => ⟨p.val,h p.property⟩) (fun p => ⟨p.val,(Finset.mem_sdiff.mp p.property).1⟩)
  invFun p := if hp : p.val ∈ A then Sum.inl ⟨p.val,hp⟩
    else Sum.inr ⟨p.val,Finset.mem_sdiff.mpr ⟨p.property,hp⟩⟩
  left_inv := by
    rintro (p | p)
    · simp [p.property]
    · simp [(Finset.mem_sdiff.mp p.property).2]
  right_inv p := by dsimp; split <;> rfl

/-- Restricting the upper occupation vector to its two disjoint prime packets is a bijection. -/
def splitBits {A B : Finset Nat.Primes} (h : A ⊆ B) :
    SquarefreeBitConfig B ≃ SquarefreeBitConfig A × SquarefreeBitConfig (B\A) :=
  (Equiv.arrowCongr (joinPrimes h).symm (Equiv.refl (Fin 2))).trans (Equiv.sumArrowEquivProdArrow _ _ _)

theorem energy_split {A B : Finset Nat.Primes} (h : A ⊆ B) (x : SquarefreeBitConfig B) :
    finiteSquarefreeHamiltonian B x = finiteSquarefreeHamiltonian A ((splitBits h x).1)+
      finiteSquarefreeHamiltonian (B\A) ((splitBits h x).2) := by
  let f (p : ↥B) := ((x p).val:ℝ)*squarefreePrimeEnergy p.val
  change (∑ p, f p) = _
  rw [← (joinPrimes h).sum_comp f,Fintype.sum_sum_type]
  rfl

theorem partition_split {A B : Finset Nat.Primes} (h : A ⊆ B) (s : ℝ) :
    finiteSquarefreePartition B s = finiteSquarefreePartition A s*finiteSquarefreePartition (B\A) s := by
  let f (p : ↥B) := 1+squarefreePrimeNome s p.val
  change (∏ p, f p) = _
  rw [← (joinPrimes h).prod_comp f,Fintype.prod_sum_type]
  rfl

theorem weight_split {A B : Finset Nat.Primes} (h : A ⊆ B) (s : ℝ) (x : SquarefreeBitConfig B) :
    finiteSquarefreeBornWeight B s x = finiteSquarefreeBornWeight A s ((splitBits h x).1)*
      finiteSquarefreeBornWeight (B\A) s ((splitBits h x).2) := by
  simp only [finiteSquarefreeBornWeight_eq,energy_split h x,partition_split h s,mul_add,Real.exp_add,
    div_mul_div_comm]

theorem weight_pos (S : Finset Nat.Primes) (s : ℝ) (x : SquarefreeBitConfig S) :
    0 < finiteSquarefreeBornWeight S s x := by
  rw [finiteSquarefreeBornWeight_eq]
  exact div_pos (Real.exp_pos _) (finiteSquarefreePartition_pos _ _)

/-- The probability measure of an arbitrary observable on a finite prime packet. -/
def observed {X : Type*} [MeasurableSpace X] (S : Finset Nat.Primes) (s : ℝ)
    (f : SquarefreeBitConfig S → X) : ProbabilityMeasure X :=
  ⟨Measure.sum (fun x => ENNReal.ofReal (finiteSquarefreeBornWeight S s x) • Measure.dirac (f x)),by
    constructor
    rw [Measure.sum_apply _ MeasurableSet.univ,tsum_fintype]
    simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => (weight_pos S s x).le),
      show (∑ x, finiteSquarefreeBornWeight S s x) = 1 from sum_squarefreeBitWeight ..,ENNReal.ofReal_one]⟩

theorem observed_apply {X : Type*} [MeasurableSpace X] (S : Finset Nat.Primes) (s : ℝ)
    (f : SquarefreeBitConfig S → X) {U : Set X} (hU : MeasurableSet U) :
    (observed S s f : Measure X) U = ∑ x, U.indicator (fun _ => ENNReal.ofReal (finiteSquarefreeBornWeight S s x)) (f x) := by
  change Measure.sum _ U = _
  rw [Measure.sum_apply _ hU,tsum_fintype]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : f x ∈ U <;> simp [Measure.smul_apply,Measure.dirac_apply' _ hU,hx]

/-- The measured pair on a single upper-cutoff configuration has exactly the product law. -/
theorem observed_split {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {A B : Finset Nat.Primes} (h : A ⊆ B) (s : ℝ) (f : SquarefreeBitConfig A → X)
    (g : SquarefreeBitConfig (B\A) → Y) :
    observed B s (fun x => (f (splitBits h x).1,g (splitBits h x).2)) =
      (observed A s f).prod (observed (B\A) s g) := by
  classical
  apply ProbabilityMeasure.toMeasure_injective
  symm
  change (observed A s f : Measure X).prod (observed (B\A) s g : Measure Y) = _
  apply Measure.prod_eq
  intro U V hU hV
  change (observed B s (fun x => (f (splitBits h x).1,g (splitBits h x).2)) : Measure (X × Y)) (U ×ˢ V) =
    (observed A s f : Measure X) U*(observed (B\A) s g : Measure Y) V
  rw [observed_apply _ _ _ (hU.prod hV),observed_apply _ _ _ hU,observed_apply _ _ _ hV,Finset.sum_mul_sum]
  let F (y : SquarefreeBitConfig A × SquarefreeBitConfig (B\A)) :=
    U.indicator (fun _ => ENNReal.ofReal (finiteSquarefreeBornWeight A s y.1)) (f y.1)*
      V.indicator (fun _ => ENNReal.ofReal (finiteSquarefreeBornWeight (B\A) s y.2)) (g y.2)
  calc _ = ∑ x, F (splitBits h x) := by
         apply Finset.sum_congr rfl
         intro x _
         by_cases hu : f (splitBits h x).1 ∈ U <;> by_cases hv : g (splitBits h x).2 ∈ V <;>
           simp [F,hu,hv,weight_split h s x,ENNReal.ofReal_mul (weight_pos A s _).le]
       _ = ∑ y, F y := (splitBits h).sum_comp F
       _ = _ := Fintype.sum_prod_type F

#print axioms energy_split
#print axioms partition_split
#print axioms weight_split
#print axioms weight_pos
#print axioms observed_apply
#print axioms observed_split

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands
