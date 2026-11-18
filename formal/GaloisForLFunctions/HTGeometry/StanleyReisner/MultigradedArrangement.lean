import GaloisForLFunctions.HTGeometry.SquarefreeVeroneseIdeal
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.CoordinateArrangementPolynomial

/-!
# The labelled multigraded point-count polynomial

Allowing the coordinate alphabets to have independent sizes retains the
labels forgotten by the ordinary face polynomial. Translation gives one
squarefree monomial for each admitted zero pattern. Its coefficient tests
membership of that individual face.
-/

namespace GaloisForLFunctions.HTGeometry
open Finset MvPolynomial ArithmeticHarmonicAnalysis.Codes
open scoped Classical
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Each free coordinate contributes its own torus-size factor. -/
def multigradedArrangement (K : Finset (Finset ι)) : MvPolynomial ι ℤ :=
  ∑ s ∈ K, ∏ i ∈ sᶜ, (X i - 1)

/-- Equating all coordinate sizes gives the ordinary point-count polynomial. -/
theorem multigradedArrangement_diagonal (K : Finset (Finset ι)) :
    aeval (fun _ : ι => (Polynomial.X : Polynomial ℤ)) (multigradedArrangement K) = arrangementPolynomial K := by
  simp [multigradedArrangement,arrangementPolynomial,card_compl]

/-- Translation into independent torus-size variables gives the complementary face monomials. -/
theorem multigradedArrangement_translate (K : Finset (Finset ι)) :
    aeval (fun i : ι => (X i+1 : MvPolynomial ι ℤ)) (multigradedArrangement K) =
      ∑ s ∈ K, ∏ i ∈ sᶜ, X i := by
  simp [multigradedArrangement]

/-- The translated squarefree coefficient is the indicator of one labelled face. -/
theorem multigradedArrangement_face (K : Finset (Finset ι)) (t : Finset ι) :
    coeff (∑ i ∈ tᶜ, Finsupp.single i (1:ℕ))
      (aeval (fun i : ι => (X i+1 : MvPolynomial ι ℤ)) (multigradedArrangement K)) =
      if t ∈ K then 1 else 0 := by
  rw [multigradedArrangement_translate,MvPolynomial.coeff_sum]
  have he (s : Finset ι) : (∑ i ∈ sᶜ, Finsupp.single i (1:ℕ)) =
      (∑ i ∈ tᶜ, Finsupp.single i (1:ℕ)) ↔ s = t := by
    refine ⟨fun h => ?_,fun h => h ▸ rfl⟩
    have hs := congrArg Finsupp.support h
    simpa only [VeroneseIdeal.support_sum_single,compl_inj_iff] using hs
  simp only [VeroneseIdeal.prod_X_eq_monomial,MvPolynomial.coeff_monomial,he]
  simp

/-- Labelled arrangement polynomials classify the entire face family, including isolated vertices. -/
theorem multigradedArrangement_injective : Function.Injective (multigradedArrangement (ι := ι)) := by
  intro K L h
  ext t
  have hc := congrArg (fun P : MvPolynomial ι ℤ =>
    coeff (∑ i ∈ tᶜ, Finsupp.single i (1:ℕ)) (aeval (fun i : ι => (X i+1 : MvPolynomial ι ℤ)) P)) h
  dsimp only at hc
  rw [multigradedArrangement_face,multigradedArrangement_face] at hc
  by_cases hk : t ∈ K <;> by_cases hl : t ∈ L <;> simp_all

/-- Actual point counts for labelled finite alphabets of independently varying sizes. -/
theorem multigradedArrangement_eval {A : ι → Type*} [∀ i, Fintype (A i)] (c : ∀ i, A i)
    (K : Finset (Finset ι)) :
    eval (fun i => (Fintype.card (A i) : ℤ)) (multigradedArrangement K) =
      ((arrangementWords (fun i => {c i}) K).card : ℤ) := by
  have hc (i : ι) : 1 ≤ Fintype.card (A i) := Fintype.card_pos_iff.mpr ⟨c i⟩
  rw [card_arrangementWords]
  simp only [multigradedArrangement,map_sum,map_prod,map_sub,eval_X,map_one,card_singleton,
    Nat.cast_sum,Nat.cast_prod]
  refine sum_congr rfl fun s _ => ?_
  have he : (univ.filter fun i => i ∉ s) = sᶜ := by ext; simp
  simp only [apply_ite Nat.cast, Nat.cast_one, Nat.cast_sub (hc _),prod_ite,
    prod_const_one,one_mul,he]

#print axioms multigradedArrangement_diagonal
#print axioms multigradedArrangement_injective
#print axioms multigradedArrangement_eval

end
end GaloisForLFunctions.HTGeometry
