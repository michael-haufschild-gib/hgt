import GaloisForLFunctions.HTGeometry.AiryTowerStokesRigidity

/-!
# Ordered-factorization classification of Airy towers

This module turns strict divisor chains into ordered multiplicative factorizations and constructs
the inverse chain from every nonempty list of factors at least two.  Combined with
`AiryTowerStokesRigidity`, this is the exact arithmetic classification of zero-loop
characteristics.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

namespace StrictDivisorChain

/-- Ordered quotients `eᵢ₋₁/eᵢ` of a strict divisor chain. -/
def factors {R : ℕ} : StrictDivisorChain R → List ℕ
  | .terminal .. => [R]
  | .step (R := R) (E := E) _ _ _ tail => (R / E) :: tail.factors

@[simp] theorem factors_nonempty {R : ℕ} (d : StrictDivisorChain R) : d.factors ≠ [] := by
  cases d <;> simp [factors]

/-- Every quotient in the ordered factorization is at least two. -/
theorem two_le_of_mem_factors {R a : ℕ} (d : StrictDivisorChain R) (ha : a ∈ d.factors) :
    2 ≤ a := by
  induction d with
  | @terminal R hR =>
      simp only [factors, List.mem_singleton] at ha
      subst a
      omega
  | @step R E hER hE hdvd tail ih =>
      simp only [factors, List.mem_cons] at ha
      rcases ha with rfl | ha
      · have hEpos : 0 < E := by omega
        have htwice : 2 * E ≤ R := by
          obtain ⟨q, rfl⟩ := hdvd
          have hq : 1 < q := by nlinarith
          nlinarith
        exact (Nat.le_div_iff_mul_le hEpos).2 htwice
      · exact ih ha

/-- Ordered factors telescope to the original ramification. -/
@[simp] theorem prod_factors {R : ℕ} (d : StrictDivisorChain R) : d.factors.prod = R := by
  induction d with
  | terminal => simp [factors]
  | @step R E hER hE hdvd tail ih =>
      simp only [factors, List.prod_cons, ih]
      exact Nat.div_mul_cancel hdvd

end StrictDivisorChain

/-- Nontrivial ordered multiplicative factorization of `R`. -/
structure OrderedFactorization (R : ℕ) where
  factors : List ℕ
  nonempty : factors ≠ []
  factor_ge_two : ∀ a ∈ factors, 2 ≤ a
  prod_eq : factors.prod = R

/-- A divisor chain yields its ordered quotient factorization. -/
def StrictDivisorChain.toOrderedFactorization {R : ℕ} (d : StrictDivisorChain R) :
    OrderedFactorization R where
  factors := d.factors
  nonempty := d.factors_nonempty
  factor_ge_two := fun a ha => d.two_le_of_mem_factors ha
  prod_eq := d.prod_factors

namespace OrderedFactorization

/-- Recursive inverse: a nonempty list of factors at least two yields a strict divisor chain of
its product. -/
def chainOfList (l : List ℕ) (hne : l ≠ []) (hge : ∀ a ∈ l, 2 ≤ a) :
    StrictDivisorChain l.prod := by
  match l with
  | [] => exact False.elim (hne rfl)
  | [a] =>
      have ha2 : 2 ≤ a := hge a (by simp)
      have ha1 : 1 < a := by omega
      exact StrictDivisorChain.terminal (by simpa using ha1)
  | a :: b :: rest =>
      let tailList := b :: rest
      have htailNonempty : tailList ≠ [] := by simp [tailList]
      have htailGe : ∀ x ∈ tailList, 2 ≤ x := by
        intro x hx
        exact hge x (by simp [tailList, hx])
      let tail := chainOfList tailList htailNonempty htailGe
      have htailR : 1 < tailList.prod := tail.ramification_gt_one
      have ha : 1 < a := lt_of_lt_of_le Nat.one_lt_two (hge a (by simp))
      have hdrop : tailList.prod < a * tailList.prod := by nlinarith
      have hdvd : tailList.prod ∣ a * tailList.prod := dvd_mul_left _ _
      exact StrictDivisorChain.step hdrop htailR hdvd tail
termination_by l.length

/-- Ordered factorization converted to a strict divisor chain. -/
def toStrictDivisorChain {R : ℕ} (f : OrderedFactorization R) : StrictDivisorChain R := by
  rw [← f.prod_eq]
  exact chainOfList f.factors f.nonempty f.factor_ge_two

/-- Every ordered factorization therefore generates an unconditional zero-loop Airy
characteristic. -/
def toAiryCharacteristic {R : ℕ} (f : OrderedFactorization R) :
    Characteristic R f.toStrictDivisorChain.firstExponent :=
  f.toStrictDivisorChain.toCharacteristic

@[simp] theorem toAiryCharacteristic_isAiryTower {R : ℕ} (f : OrderedFactorization R) :
    f.toAiryCharacteristic.IsAiryTower :=
  f.toStrictDivisorChain.toCharacteristic_isAiryTower

@[simp] theorem toAiryCharacteristic_diagonalLoop {R : ℕ} (f : OrderedFactorization R) :
    f.toAiryCharacteristic.diagonalLoop = 0 :=
  (f.toAiryCharacteristic.diagonalLoop_eq_zero_iff_isAiryTower).2
    f.toAiryCharacteristic_isAiryTower

end OrderedFactorization

end IrregularStokes
end GaloisForLFunctions
