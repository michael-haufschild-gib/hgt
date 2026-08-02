import GaloisForLFunctions.HTGeometry.NewtonFibreLift

/-!
# Two points of a deformed critical fibre

Two distinct factorisations over the horizon deform, with the same deformation of their critical
coefficients, into two factorisations that still share every coefficient from the critical orders on
— that is, share the critical observation — and still differ.

The observation is unchanged because both factors are monic of the two critical degrees, so their
coefficients from those degrees on are `1, 0, 0, …` for both; and the corrections supplied by the
lift live strictly below the critical degrees.  The two remain distinct because their constant terms
already differ modulo the deformation ideal, while the corrections lie inside it.

So a fibre with two points over a special observation has two points over the deformed observation.
That is the passage a count at the special fibre cannot make on its own.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {S : Type*} [CommRing S]

/-- The coefficients of a monic polynomial from its degree on are `1, 0, 0, …`. -/
theorem coeff_eq_of_monic_natDegree {A A' : S[X]} {m i : ℕ} (hA : A.Monic)
    (hAdeg : A.natDegree = m) (hA' : A'.Monic) (hA'deg : A'.natDegree = m) (hi : m ≤ i) :
    A.coeff i = A'.coeff i := by
  rcases eq_or_lt_of_le hi with rfl | hlt
  · rw [← hAdeg, hA.coeff_natDegree, hAdeg, ← hA'deg, hA'.coeff_natDegree]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- **Two points of the deformed fibre.**  Two factorisations over the horizon whose constant terms
differ modulo the deformation ideal deform, along the same deformation, into two factorisations with
the same critical observation and still-distinct constant terms. -/
theorem exists_two_deformed_factorisations [Nontrivial S] (I : Ideal S) [IsAdicComplete I S]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A₀ B₀ A₁ B₁ : S[X]}
    (hA₀ : A₀.Monic) (hA₀deg : A₀.natDegree = m) (hB₀ : B₀.Monic) (hB₀deg : B₀.natDegree = n)
    (hA₁ : A₁.Monic) (hA₁deg : A₁.natDegree = m) (hB₁ : B₁.Monic) (hB₁deg : B₁.natDegree = n)
    (hcop₀ : IsCoprime A₀ B₀) (hcop₁ : IsCoprime A₁ B₁)
    (hAB₀ : (X : S[X]) ^ (m + n) ∣ inversionError A₀ B₀)
    (hAB₁ : (X : S[X]) ^ (m + n) ∣ inversionError A₁ B₁)
    (hsep : A₀.coeff 0 - A₁.coeff 0 ∉ I)
    {Γ Γ' : S[X]} (hΓ : CoeffMem I Γ) (hΓ' : CoeffMem I Γ')
    (hΓdeg : Γ.natDegree < m + n) (hΓ'deg : Γ'.natDegree < m + n) :
    ∃ Z₀ W₀ Z₁ W₁ : S[X],
      (X : S[X]) ^ (m + n) ∣ inversionError Z₀ W₀ ∧
      (X : S[X]) ^ (m + n) ∣ inversionError Z₁ W₁ ∧
      (∀ i, m ≤ i → Z₀.coeff i = Z₁.coeff i) ∧
      (∀ j, n ≤ j → W₀.coeff j = W₁.coeff j) ∧
      Z₀.coeff 0 - Z₁.coeff 0 ∉ I ∧
      CoeffMem I (Z₀ - A₀) ∧ CoeffMem I (W₀ - B₀) ∧
      CoeffMem I (Z₁ - A₁) ∧ CoeffMem I (W₁ - B₁) ∧
      W₀.natDegree < m + n ∧ W₁.natDegree < m + n ∧
      Z₀.natDegree < m + n ∧ Z₁.natDegree < m + n ∧
      (∀ i, m ≤ i → Z₀.coeff i = A₀.coeff i + Γ.coeff i) ∧
      (∀ j, n ≤ j → W₀.coeff j = B₀.coeff j + Γ'.coeff j) := by
  obtain ⟨P₀, Q₀, hP₀deg, hQ₀deg, hP₀mem, hQ₀mem, hfac₀⟩ :=
    exists_deformed_factorisation I hm hn hA₀ hA₀deg (le_of_eq hB₀deg) hcop₀ hΓ hΓ' hAB₀
  obtain ⟨P₁, Q₁, hP₁deg, hQ₁deg, hP₁mem, hQ₁mem, hfac₁⟩ :=
    exists_deformed_factorisation I hm hn hA₁ hA₁deg (le_of_eq hB₁deg) hcop₁ hΓ hΓ' hAB₁
  have hred : ∀ (C D E : S[X]), CoeffMem I D → CoeffMem I E → CoeffMem I (C + D + E - C) := by
    intro C D E hD hE
    have hrw : C + D + E - C = D + E := by ring
    rw [hrw]
    exact hD.add hE
  have hWdeg : ∀ {B Q : S[X]}, B.natDegree = n → Q.natDegree < n →
      (B + Γ' + Q).natDegree < m + n := by
    intro B Q hB hQ
    refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ (by omega))
    exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (by omega) hΓ'deg)
  have hZdeg : ∀ {A P : S[X]}, A.natDegree = m → P.natDegree < m →
      (A + Γ + P).natDegree < m + n := by
    intro A P hA hP
    refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ (by omega))
    exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (by omega) hΓdeg)
  refine ⟨A₀ + Γ + P₀, B₀ + Γ' + Q₀, A₁ + Γ + P₁, B₁ + Γ' + Q₁, hfac₀, hfac₁, ?_, ?_, ?_,
    hred A₀ Γ P₀ hΓ hP₀mem, hred B₀ Γ' Q₀ hΓ' hQ₀mem,
    hred A₁ Γ P₁ hΓ hP₁mem, hred B₁ Γ' Q₁ hΓ' hQ₁mem,
    hWdeg hB₀deg hQ₀deg, hWdeg hB₁deg hQ₁deg,
    hZdeg hA₀deg hP₀deg, hZdeg hA₁deg hP₁deg, ?_, ?_⟩
  · intro i hi
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hP₀deg hi),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hP₁deg hi),
      coeff_eq_of_monic_natDegree hA₀ hA₀deg hA₁ hA₁deg hi]
  · intro j hj
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hQ₀deg hj),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hQ₁deg hj),
      coeff_eq_of_monic_natDegree hB₀ hB₀deg hB₁ hB₁deg hj]
  · intro hcon
    refine hsep ?_
    have hrw : A₀.coeff 0 - A₁.coeff 0
        = ((A₀ + Γ + P₀).coeff 0 - (A₁ + Γ + P₁).coeff 0)
          - (P₀.coeff 0 - P₁.coeff 0) := by
      simp only [Polynomial.coeff_add]
      ring
    rw [hrw]
    exact Submodule.sub_mem I hcon (Submodule.sub_mem I (hP₀mem 0) (hP₁mem 0))
  · intro i hi
    rw [Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hP₀deg hi), add_zero]
  · intro j hj
    rw [Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hQ₀deg hj), add_zero]

end GaloisForLFunctions.HTGeometry
