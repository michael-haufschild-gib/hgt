import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# Coefficient shift and variable translation act trivially on the top of the degree filtration

Substituting `Xᵢ + Rᵢ` for `Xᵢ` in a multivariable polynomial changes only the lower part of the
degree filtration: a monomial `X^f` becomes `X^f` plus terms of degree `< deg f`.  Composing with a
ring endomorphism `σ` of the coefficients therefore gives an operator

```text
Φ(P) = P^σ(X + R)
```

whose coefficients in the top degree of `P` are exactly `σ` applied to those of `P`, and which never
raises the total degree.  Both facts are proved here from the single monomial computation

```text
coeff e ∏ᵢ (Xᵢ + Rᵢ)^{fᵢ} = [e = f]    whenever deg f ≤ deg e,
```

itself an induction peeling one variable at a time.

`Φ` is the operator through which a difference automorphism acts on the polynomial relations of a
family of indefinite sums, and the two facts above are what make the induced descent terminate.
-/

open scoped BigOperators

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {K : Type*} [CommRing K] {ι : Type*}

/-! ## The degree of a monomial against the total degree -/

theorem totalDegree_eq_sup (P : MvPolynomial ι K) :
    P.totalDegree = P.support.sup fun s : ι →₀ ℕ => s.sum fun _ k => k := rfl

theorem degree_le_totalDegree {P : MvPolynomial ι K} {e : ι →₀ ℕ} (he : e ∈ P.support) :
    Finsupp.degree e ≤ P.totalDegree := by
  simpa [Finsupp.degree_apply, Finsupp.sum] using MvPolynomial.le_totalDegree he

theorem coeff_eq_zero_of_totalDegree_lt_degree {P : MvPolynomial ι K} {e : ι →₀ ℕ}
    (h : P.totalDegree < Finsupp.degree e) : coeff e P = 0 :=
  MvPolynomial.coeff_eq_zero_of_totalDegree_lt (by simpa [Finsupp.degree_apply] using h)

/-- A degree bound follows from the vanishing of all coefficients above it. -/
theorem totalDegree_le_of_coeff_eq_zero {Q : MvPolynomial ι K} {n : ℕ}
    (h : ∀ e : ι →₀ ℕ, n < Finsupp.degree e → coeff e Q = 0) : Q.totalDegree ≤ n := by
  refine Finset.sup_le fun e he => ?_
  by_contra hlt
  refine (MvPolynomial.mem_support_iff.mp he) (h e ?_)
  rw [Finsupp.degree_apply]
  simpa [Finsupp.sum] using Nat.lt_of_not_le hlt

/-- A nonzero polynomial has a monomial of maximal degree. -/
theorem exists_mem_support_degree_eq_totalDegree {P : MvPolynomial ι K} (hP : P ≠ 0) :
    ∃ e ∈ P.support, Finsupp.degree e = P.totalDegree := by
  obtain ⟨e, he, heq⟩ :=
    Finset.exists_mem_eq_sup P.support (MvPolynomial.support_nonempty.mpr hP)
      fun s : ι →₀ ℕ => s.sum fun _ k => k
  refine ⟨e, he, ?_⟩
  rw [Finsupp.degree_apply, totalDegree_eq_sup, heq]
  rfl

/-! ## The translated variables -/

/-- The variable `Xᵢ` translated by the coefficient `Rᵢ`. -/
def translatedVariable (R : ι → K) (i : ι) : MvPolynomial ι K := X i + C (R i)

/-- The image of the monomial `X^f` under the translation of every variable. -/
def translatedMonomial (R : ι → K) (f : ι →₀ ℕ) : MvPolynomial ι K :=
  f.prod fun i k => translatedVariable R i ^ k

@[simp] theorem translatedMonomial_zero (R : ι → K) : translatedMonomial R 0 = 1 :=
  Finsupp.prod_zero_index

theorem translatedMonomial_add (R : ι → K) (f g : ι →₀ ℕ) :
    translatedMonomial R (f + g) = translatedMonomial R f * translatedMonomial R g :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ k l => pow_add _ k l

theorem translatedMonomial_single_one (R : ι → K) (i : ι) :
    translatedMonomial R (Finsupp.single i 1) = translatedVariable R i := by
  have hsingle := Finsupp.prod_single_index (a := i) (b := 1)
    (h := fun i k => translatedVariable R i ^ k) (pow_zero (translatedVariable R i))
  rw [translatedMonomial, hsingle, pow_one]

theorem bind₁_monomial_translatedVariable (R : ι → K) (f : ι →₀ ℕ) (a : K) :
    bind₁ (translatedVariable R) (monomial f a) = C a * translatedMonomial R f :=
  MvPolynomial.bind₁_monomial _ _ _

/-! ## The translated monomial in the top degree -/

/-- **A translated monomial is the monomial itself in the top degree.**  All other monomials the
translation produces have strictly smaller degree, so at any exponent of degree at least `deg f`
the coefficient is the Kronecker symbol. -/
theorem coeff_translatedMonomial [DecidableEq ι] (R : ι → K) :
    ∀ (n : ℕ) (f : ι →₀ ℕ), Finsupp.degree f = n → ∀ e : ι →₀ ℕ, n ≤ Finsupp.degree e →
      coeff e (translatedMonomial R f) = if e = f then 1 else 0 := by
  classical
  intro n
  induction n with
  | zero =>
      intro f hf e _
      have hf0 : f = 0 := by rwa [Finsupp.degree_eq_zero_iff] at hf
      subst hf0
      rw [translatedMonomial_zero, coeff_one]
      exact if_congr eq_comm rfl rfl
  | succ n ih =>
      intro f hf e he
      have hfne : f ≠ 0 := by
        intro h
        rw [h] at hf
        simp at hf
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hfne
      have hi1 : 1 ≤ f i := Nat.one_le_iff_ne_zero.mpr (by simpa using hi)
      set f' : ι →₀ ℕ := f - Finsupp.single i 1 with hf'def
      have hsplit : f' + Finsupp.single i 1 = f :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi1)
      have hdeg' : Finsupp.degree f' = n := by
        have h1 : Finsupp.degree f' + Finsupp.degree (Finsupp.single i (1 : ℕ))
            = Finsupp.degree f := by rw [← map_add, hsplit]
        rw [Finsupp.degree_single, hf] at h1
        omega
      have hIH := ih f' hdeg'
      have hnotf' : coeff e (translatedMonomial R f') = 0 := by
        rw [hIH e (by omega), if_neg]
        intro hcon
        rw [hcon, hdeg'] at he
        omega
      have hCcomm : translatedMonomial R f' * C (R i) = C (R i) * translatedMonomial R f' :=
        mul_comm _ _
      rw [← hsplit, translatedMonomial_add, translatedMonomial_single_one, translatedVariable,
        mul_add, coeff_add, MvPolynomial.coeff_mul_X', hCcomm, MvPolynomial.coeff_C_mul,
        hnotf', mul_zero, add_zero]
      by_cases hie : i ∈ e.support
      · have hei : 1 ≤ e i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hie)
        have hesplit : (e - Finsupp.single i 1) + Finsupp.single i 1 = e :=
          tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hei)
        have hdege : Finsupp.degree (e - Finsupp.single i 1) = Finsupp.degree e - 1 := by
          have h2 : Finsupp.degree (e - Finsupp.single i 1)
              + Finsupp.degree (Finsupp.single i (1 : ℕ)) = Finsupp.degree e := by
            rw [← map_add, hesplit]
          rw [Finsupp.degree_single] at h2
          omega
        rw [if_pos hie, hIH _ (by omega)]
        by_cases hcase : e - Finsupp.single i 1 = f'
        · have hef : e = f' + Finsupp.single i 1 := by rw [← hesplit, hcase]
          rw [if_pos hcase, if_pos hef]
        · rw [if_neg hcase, if_neg]
          intro hcon
          exact hcase (by rw [hcon]; simp)
      · rw [if_neg hie, if_neg]
        intro hcon
        refine hie ?_
        rw [hcon]
        simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]
        omega

/-! ## Translation on the top of the filtration -/

/-- **Translating the variables does not change the top-degree coefficients.** -/
theorem coeff_bind₁_translatedVariable_of_le (R : ι → K) (P : MvPolynomial ι K) {e : ι →₀ ℕ}
    (he : P.totalDegree ≤ Finsupp.degree e) :
    coeff e (bind₁ (translatedVariable R) P) = coeff e P := by
  classical
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
  rw [map_sum, MvPolynomial.coeff_sum]
  have hterm : ∀ f ∈ P.support,
      coeff e (bind₁ (translatedVariable R) (monomial f (coeff f P)))
        = if f = e then coeff f P else 0 := by
    intro f hf
    rw [bind₁_monomial_translatedVariable, MvPolynomial.coeff_C_mul,
      coeff_translatedMonomial R (Finsupp.degree f) f rfl e
        (le_trans (degree_le_totalDegree hf) he)]
    by_cases hfe : f = e
    · subst hfe
      simp
    · rw [if_neg (fun hcon : e = f => hfe hcon.symm), if_neg hfe, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' P.support e fun f => coeff f P]
  by_cases hmem : e ∈ P.support
  · rw [if_pos hmem]
  · rw [if_neg hmem, MvPolynomial.notMem_support_iff.mp hmem]

theorem coeff_bind₁_translatedVariable_eq_zero (R : ι → K) (P : MvPolynomial ι K) {e : ι →₀ ℕ}
    (he : P.totalDegree < Finsupp.degree e) :
    coeff e (bind₁ (translatedVariable R) P) = 0 := by
  rw [coeff_bind₁_translatedVariable_of_le R P he.le]
  exact coeff_eq_zero_of_totalDegree_lt_degree he

/-- **Translating the variables never raises the total degree.** -/
theorem totalDegree_bind₁_translatedVariable_le (R : ι → K) (P : MvPolynomial ι K) :
    (bind₁ (translatedVariable R) P).totalDegree ≤ P.totalDegree :=
  totalDegree_le_of_coeff_eq_zero fun _ h => coeff_bind₁_translatedVariable_eq_zero R P h

/-! ## Shifting the coefficients and translating the variables -/

/-- `Φ(P) = P^σ(X + R)`: apply the coefficient endomorphism `σ` and translate every variable. -/
def shiftTranslate (σ : K →+* K) (R : ι → K) : MvPolynomial ι K →+* MvPolynomial ι K :=
  RingHom.comp
    ((bind₁ (translatedVariable R) : MvPolynomial ι K →ₐ[K] MvPolynomial ι K) :
      MvPolynomial ι K →+* MvPolynomial ι K)
    (MvPolynomial.map σ)

theorem shiftTranslate_apply (σ : K →+* K) (R : ι → K) (P : MvPolynomial ι K) :
    shiftTranslate σ R P = bind₁ (translatedVariable R) (MvPolynomial.map σ P) := rfl

@[simp] theorem shiftTranslate_C (σ : K →+* K) (R : ι → K) (a : K) :
    shiftTranslate σ R (C a) = C (σ a) := by
  rw [shiftTranslate_apply, MvPolynomial.map_C, MvPolynomial.bind₁_C_right]

@[simp] theorem shiftTranslate_X (σ : K →+* K) (R : ι → K) (i : ι) :
    shiftTranslate σ R (X i) = X i + C (R i) := by
  rw [shiftTranslate_apply, MvPolynomial.map_X, MvPolynomial.bind₁_X_right, translatedVariable]

theorem totalDegree_map_le (σ : K →+* K) (P : MvPolynomial ι K) :
    (MvPolynomial.map σ P).totalDegree ≤ P.totalDegree :=
  Finset.sup_mono (MvPolynomial.support_map_subset σ P)

/-- **The top-degree coefficients are shifted by `σ` and nothing else.** -/
theorem coeff_shiftTranslate_of_le (σ : K →+* K) (R : ι → K) (P : MvPolynomial ι K) {e : ι →₀ ℕ}
    (he : P.totalDegree ≤ Finsupp.degree e) :
    coeff e (shiftTranslate σ R P) = σ (coeff e P) := by
  rw [shiftTranslate_apply,
    coeff_bind₁_translatedVariable_of_le R _ (le_trans (totalDegree_map_le σ P) he),
    MvPolynomial.coeff_map]

/-- **The operator never raises the total degree.** -/
theorem totalDegree_shiftTranslate_le (σ : K →+* K) (R : ι → K) (P : MvPolynomial ι K) :
    (shiftTranslate σ R P).totalDegree ≤ P.totalDegree :=
  le_trans (totalDegree_bind₁_translatedVariable_le R _) (totalDegree_map_le σ P)

end

end GaloisForLFunctions
