import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Bands.Edges

/-! # Product formulas for the endpoint measurement -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Bands

open Finset Real

variable {n : ℕ} [NeZero n]

private theorem exp_edge_at (x : Fin n → ℝ) (i j : Fin n)
    (lo : ∀ a, x i ≤ x a) (hi : ∀ a, x a ≤ x j) :
    exp (edge x)=(exp (x i)*exp (x j))^n/(∏ a,exp (x a))^2 := by
  rw [edge_at x i j lo hi,exp_sub,exp_nat_mul,exp_add]
  rw [two_mul,exp_add,exp_sum,pow_two]

/-- The product of all observed probabilities and the two extreme
probabilities give the exponentiated statistic directly. -/
theorem observed_product (q : Fin n → ℝ) (pos : ∀ a, 0<q a) :
    ∃ i j, (∀ a, q i ≤ q a ∧ q a ≤ q j) ∧
      exp (reading q)=(∏ a,q a)^2/(q i*q j)^n := by
  obtain ⟨i,j,lo,hi⟩ := extrema q
  refine ⟨i,j,fun a => ⟨lo a,hi a⟩,?_⟩
  have hr (a) : exp (-log (q a))=(q a)⁻¹ := by rw [exp_neg,exp_log (pos a)]
  rw [reading,exp_edge_at (fun a => -log (q a)) j i (fun a => neg_le_neg (log_le_log (pos a) (hi a)))
    (fun a => neg_le_neg (log_le_log (pos i) (lo a)))]
  simp only [hr,prod_inv_distrib,←mul_inv_rev,inv_pow,inv_div_inv]

/-- An unlabelled measurement using products, a minimum and a maximum. -/
def odds (q : Fin n → ℝ) :=
  (∏ a,q a)^2/(univ.inf' univ_nonempty q * univ.sup' univ_nonempty q)^n

theorem odds_eq (q : Fin n → ℝ) (pos : ∀ a, 0<q a) : odds q=exp (reading q) := by
  obtain ⟨i,j,h,prod⟩ := observed_product q pos
  have lo := le_antisymm (inf'_le q (mem_univ i))
    (le_inf' univ_nonempty q fun a _ => (h a).1)
  have hi := le_antisymm (sup'_le univ_nonempty q fun a _ => (h a).2)
    (le_sup' q (mem_univ j))
  rw [odds,lo,hi,prod]

/-- For integer labels the exponential of the energy statistic is a
positive rational specified by the two endpoints and the product of all labels. -/
theorem integer_product_at (b : Fin n → ℕ+) (i j : Fin n)
    (lo : ∀ a, b i ≤ b a) (hi : ∀ a, b a ≤ b j) :
    exp (edge (fun a => log ((b a).val:ℝ)))=
      (((b i).val*(b j).val:ℕ):ℝ)^n / ((∏ a,(b a).val:ℕ):ℝ)^2 := by
  have pos (a) : 0<((b a).val:ℝ) := Nat.cast_pos.mpr (b a).property
  have lift {a c : Fin n} (h : b a ≤ b c) : ((b a).val:ℝ) ≤ ((b c).val:ℝ) :=
    Nat.cast_le.mpr h
  rw [exp_edge_at (fun a => log ((b a).val:ℝ)) i j (fun a => log_le_log (pos i) (lift (lo a)))
    (fun a => log_le_log (pos a) (lift (hi a)))]
  simp only [exp_log (pos _),Nat.cast_mul,Nat.cast_prod]

theorem two_edge (x : Fin 2 → ℝ) : edge x=0 := by
  have ordered (i j : Fin 2) (h : x i ≤ x j) (cover : ∀ a, a=i ∨ a=j) :
      edge x=(2:ℝ)*(x i+x j)-2*(x 0+x 1) := by
    have lo (a) : x i ≤ x a := by
      rcases cover a with e|e
      · simpa only [e] using (show x i ≤ x i from le_rfl)
      · simpa only [e] using h
    have hi (a) : x a ≤ x j := by
      rcases cover a with e|e
      · simpa only [e] using h
      · simpa only [e] using (show x j ≤ x j from le_rfl)
    rw [edge_at x i j lo hi,Fin.sum_univ_two,Nat.cast_ofNat]
  rcases le_total (x 0) (x 1) with h|h
  · rw [ordered 0 1 h (fun a => by fin_cases a <;> simp)]
    ring
  · rw [ordered 1 0 h (fun a => by fin_cases a <;> simp)]
    ring

#print axioms observed_product
#print axioms odds_eq
#print axioms integer_product_at
#print axioms two_edge

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Bands
