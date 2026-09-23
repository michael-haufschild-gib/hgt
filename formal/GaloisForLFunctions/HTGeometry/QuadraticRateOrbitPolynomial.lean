import GaloisForLFunctions.HTGeometry.QuadraticRateSpectralRigidity

/-!
# The labeling orbit of a quadratic-rate spectral relation

A quadratic-rate relation `(∑ c_i E_i)^(2 : ℕ) = κ ∑ E_i^(2 : ℕ)` refers to a chosen labeling of the spectrum.
Multiplying the defect over every labeling gives a *symmetric* polynomial, hence a polynomial in
the elementary symmetric functions of the spectrum, hence a polynomial in the characteristic
coefficients of the underlying matrix.  The orbit obstruction therefore descends to the
Hamiltonian parameters, where flatness on an open set forces it to vanish identically.

This mirrors the linear construction of `SpectralRelationOrbitPolynomial`.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {I : Type*} [Fintype I]

/-- The quadratic-rate relation as a polynomial in the spectrum. -/
def quadraticRateRelationPolynomial (c : I → ℚ) (κ : ℚ) : MvPolynomial I ℚ :=
  (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) ^ (2 : ℕ)
    - MvPolynomial.C κ * ∑ i, (MvPolynomial.X i : MvPolynomial I ℚ) ^ (2 : ℕ)

/-- The product of the relation over every labeling of the spectrum. -/
def quadraticRateOrbitPolynomial (c : I → ℚ) (κ : ℚ) : MvPolynomial I ℚ := by
  classical
  exact ∏ σ : Equiv.Perm I, MvPolynomial.rename σ (quadraticRateRelationPolynomial c κ)

/-- Numerical value of the labeling-orbit obstruction on a real spectrum. -/
def quadraticRateOrbitValue (c : I → ℚ) (κ : ℚ) (energy : I → ℝ) : ℝ := by
  classical
  exact ∏ σ : Equiv.Perm I,
    ((∑ i, (c i : ℝ) * energy (σ i)) ^ (2 : ℕ) - (κ : ℝ) * ∑ i, energy i ^ (2 : ℕ))

/-! ## Evaluation -/

theorem eval₂_quadraticRateRelationPolynomial_real (c : I → ℚ) (κ : ℚ) (energy : I → ℝ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) energy (quadraticRateRelationPolynomial c κ)
      = (∑ i, (c i : ℝ) * energy i) ^ (2 : ℕ) - (κ : ℝ) * ∑ i, energy i ^ (2 : ℕ) := by
  simp [quadraticRateRelationPolynomial, MvPolynomial.eval₂_sum]

/-- The `σ`-labeled factor of the orbit obstruction is the quadratic-rate defect of the relabeled
coefficient packet. -/
theorem quadraticRateOrbitValue_factor (c : I → ℚ) (κ : ℚ) (energy : I → ℝ)
    (σ : Equiv.Perm I) :
    ((∑ i, (c i : ℝ) * energy (σ i)) ^ (2 : ℕ) - (κ : ℝ) * ∑ i, energy i ^ (2 : ℕ))
      = quadraticRateDefect (fun j => ((c (σ.symm j) : ℝ))) (κ : ℝ) energy := by
  have hsum : (∑ i, (c i : ℝ) * energy (σ i))
      = ∑ j, ((c (σ.symm j) : ℝ)) * energy j :=
    Fintype.sum_equiv σ _ _ fun i => by simp
  rw [quadraticRateDefect, hsum]

theorem eval₂_quadraticRateOrbitPolynomial_real (c : I → ℚ) (κ : ℚ) (energy : I → ℝ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) energy (quadraticRateOrbitPolynomial c κ)
      = quadraticRateOrbitValue c κ energy := by
  classical
  rw [quadraticRateOrbitPolynomial, quadraticRateOrbitValue, MvPolynomial.eval₂_prod]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [MvPolynomial.eval₂_rename, eval₂_quadraticRateRelationPolynomial_real]
  have h2 : (∑ i, (energy ∘ σ) i ^ (2 : ℕ)) = ∑ i, energy i ^ (2 : ℕ) :=
    Fintype.sum_equiv σ (fun i => (energy ∘ σ) i ^ (2 : ℕ)) (fun j => energy j ^ (2 : ℕ)) fun i => rfl
  rw [h2]
  rfl

theorem quadraticRateOrbitValue_eq_zero_iff (c : I → ℚ) (κ : ℚ) (energy : I → ℝ) :
    quadraticRateOrbitValue c κ energy = 0 ↔
      ∃ σ : Equiv.Perm I,
        quadraticRateDefect (fun j => ((c (σ.symm j) : ℝ))) (κ : ℝ) energy = 0 := by
  classical
  rw [quadraticRateOrbitValue, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨σ, -, hσ⟩
    exact ⟨σ, by rwa [← quadraticRateOrbitValue_factor c κ energy σ]⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, Finset.mem_univ σ, by rwa [quadraticRateOrbitValue_factor c κ energy σ]⟩

/-! ## Symmetry and descent to the characteristic coefficients -/

theorem quadraticRateOrbitPolynomial_isSymmetric (c : I → ℚ) (κ : ℚ) :
    MvPolynomial.IsSymmetric (quadraticRateOrbitPolynomial c κ) := by
  classical
  intro e
  simp only [quadraticRateOrbitPolynomial, map_prod, MvPolynomial.rename_rename]
  exact Fintype.prod_equiv (Equiv.mulLeft e)
    (fun σ : Equiv.Perm I =>
      MvPolynomial.rename (e * σ) (quadraticRateRelationPolynomial c κ))
    (fun σ : Equiv.Perm I =>
      MvPolynomial.rename σ (quadraticRateRelationPolynomial c κ))
    (fun σ => rfl)

/-! ## The characteristic-coefficient obstruction -/

/-- The orbit obstruction rewritten in the elementary symmetric functions of the spectrum, that is
in the characteristic coefficients of the Hamiltonian. -/
def quadraticRateCoefficientPolynomial (c : I → ℚ) (κ : ℚ) :
    MvPolynomial (Fin (Fintype.card I)) ℚ :=
  (MvPolynomial.esymmAlgEquiv I ℚ rfl).symm
    ⟨quadraticRateOrbitPolynomial c κ, quadraticRateOrbitPolynomial_isSymmetric c κ⟩

theorem esymmAlgHom_quadraticRateCoefficientPolynomial (c : I → ℚ) (κ : ℚ) :
    (MvPolynomial.esymmAlgHom I ℚ (Fintype.card I)
      (quadraticRateCoefficientPolynomial c κ)).1 = quadraticRateOrbitPolynomial c κ := by
  change ((MvPolynomial.esymmAlgEquiv I ℚ rfl)
      (quadraticRateCoefficientPolynomial c κ)).1 = quadraticRateOrbitPolynomial c κ
  simp [quadraticRateCoefficientPolynomial]

/-- Evaluating the characteristic-coefficient obstruction on elementary symmetric spectral data
reproduces the labeling-orbit obstruction. -/
theorem eval₂_quadraticRateCoefficientPolynomial_real_esymm (c : I → ℚ) (κ : ℚ)
    (energy : I → ℝ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ)
        (fun i : Fin (Fintype.card I) =>
          MvPolynomial.eval₂ (Rat.castHom ℝ) energy (MvPolynomial.esymm I ℚ (i + 1)))
        (quadraticRateCoefficientPolynomial c κ)
      = MvPolynomial.eval₂ (Rat.castHom ℝ) energy (quadraticRateOrbitPolynomial c κ) := by
  have h := congrArg (MvPolynomial.eval₂ (Rat.castHom ℝ) energy)
    (esymmAlgHom_quadraticRateCoefficientPolynomial c κ)
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq,
    ← MvPolynomial.eval₂_assoc] at h
  exact h

/-! ## Nonvanishing -/

theorem eval_quadraticRateRelationPolynomial (c : I → ℚ) (κ : ℚ) (energy : I → ℚ) :
    MvPolynomial.eval energy (quadraticRateRelationPolynomial c κ)
      = (∑ i, c i * energy i) ^ (2 : ℕ) - κ * ∑ i, energy i ^ (2 : ℕ) := by
  simp [quadraticRateRelationPolynomial]

variable [DecidableEq I]

/-- **The quadratic-rate relation is a nonzero polynomial** unless both the multiple and the
coefficient packet vanish. -/
theorem quadraticRateRelationPolynomial_eq_zero_iff (hcard : 2 ≤ Fintype.card I)
    (c : I → ℚ) (κ : ℚ) :
    quadraticRateRelationPolynomial c κ = 0 ↔ κ = 0 ∧ c = 0 := by
  constructor
  · intro hzero
    have hval : ∀ energy : I → ℚ, (∑ i, c i * energy i) ^ (2 : ℕ) = κ * ∑ i, energy i ^ (2 : ℕ) := by
      intro energy
      have := congrArg (MvPolynomial.eval energy) hzero
      rw [eval_quadraticRateRelationPolynomial] at this
      simpa [sub_eq_zero] using this
    have hsingle : ∀ i : I, c i ^ (2 : ℕ) = κ := by
      intro i
      have h := hval (fun x => if x = i then 1 else 0)
      have h1 : (∑ x, c x * (if x = i then (1:ℚ) else 0)) = c i := by simp
      have h2 : (∑ x, (if x = i then (1:ℚ) else 0) ^ (2 : ℕ)) = 1 := by simp
      rw [h1, h2, mul_one] at h
      exact h
    have hcross : ∀ i j : I, i ≠ j → c i * c j = 0 := by
      intro i j hij
      have h := hval (fun x => (if x = i then 1 else 0) + (if x = j then 1 else 0))
      have h1 : (∑ x, c x * ((if x = i then (1:ℚ) else 0) + (if x = j then 1 else 0)))
          = c i + c j := by
        simp only [mul_add, Finset.sum_add_distrib]
        simp
      have h2 : (∑ x, ((if x = i then (1:ℚ) else 0) + (if x = j then 1 else 0)) ^ (2 : ℕ)) = 2 := by
        have hji : ¬ (j = i) := fun hh => hij hh.symm
        have hval2 : ∀ x : I, ((if x = i then (1:ℚ) else 0) + (if x = j then 1 else 0)) ^ (2 : ℕ)
            = (if x = i then (1:ℚ) else 0) + (if x = j then 1 else 0) := by
          intro x
          by_cases hx : x = i
          · simp [hx, hij]
          · by_cases hy : x = j
            · simp [hy, hji]
            · simp [hx, hy]
        rw [Finset.sum_congr rfl fun x _ => hval2 x, Finset.sum_add_distrib]
        simp
        norm_num
      rw [h1, h2] at h
      have hi := hsingle i
      have hj := hsingle j
      nlinarith [h, hi, hj]
    obtain ⟨t, -, ht2⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset I)) (n := 2)
      (by simpa using hcard)
    obtain ⟨i, j, hij, -⟩ := Finset.card_eq_two.mp ht2
    have hκ : κ = 0 := by
      have hc := hcross i j hij
      have hi := hsingle i
      have hj := hsingle j
      nlinarith [hc, hi, hj]
    refine ⟨hκ, ?_⟩
    funext x
    have := hsingle x
    rw [hκ] at this
    have hx : c x = 0 := by nlinarith [this]
    rw [hx]
    rfl
  · rintro ⟨rfl, rfl⟩
    simp [quadraticRateRelationPolynomial]

theorem quadraticRateOrbitPolynomial_ne_zero (hcard : 2 ≤ Fintype.card I)
    {c : I → ℚ} {κ : ℚ} (h : ¬ (κ = 0 ∧ c = 0)) :
    quadraticRateOrbitPolynomial c κ ≠ 0 := by
  classical
  rw [quadraticRateOrbitPolynomial]
  refine Finset.prod_ne_zero_iff.mpr fun σ _ hrename => ?_
  refine h ?_
  rw [← quadraticRateRelationPolynomial_eq_zero_iff hcard c κ]
  exact MvPolynomial.rename_injective (f := (σ : I → I)) σ.injective (by simpa using hrename)


theorem quadraticRateCoefficientPolynomial_ne_zero (hcard : 2 ≤ Fintype.card I)
    {c : I → ℚ} {κ : ℚ} (h : ¬ (κ = 0 ∧ c = 0)) :
    quadraticRateCoefficientPolynomial c κ ≠ 0 := by
  intro hzero
  apply quadraticRateOrbitPolynomial_ne_zero hcard h
  rw [← esymmAlgHom_quadraticRateCoefficientPolynomial c κ, hzero]
  simp


end GaloisForLFunctions.HTGeometry

end
