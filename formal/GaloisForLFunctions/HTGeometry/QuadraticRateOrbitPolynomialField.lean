import GaloisForLFunctions.HTGeometry.QuadraticRateOrbitPolynomial

/-!
# The labeling orbit of a quadratic-rate relation over an arbitrary field

The rational construction of `QuadraticRateOrbitPolynomial` is not enough for the fixed-shell
nonflatness theorem.  There the multiple is `κ = b²`, the square of the constant value of a
projective spectral action on a sphere patch, which is an arbitrary real number; and the
characteristic-coefficient pullback used by the genericity machine lives over `ℂ`.  This module
repeats the construction over an arbitrary characteristic-zero integral domain, so both instances are
available: the relation, its labeling orbit, the symmetry of the orbit, its descent to the
elementary symmetric functions, and the non-vanishing of the resulting polynomial unless both the
multiple and the coefficient packet vanish.

The characteristic-zero hypothesis is used exactly once, to divide the cross term by two.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [CommRing K] [IsDomain K] {I : Type*} [Fintype I] [DecidableEq I]

/-- The quadratic-rate relation as a polynomial in the spectrum, over any field. -/
def fieldQuadraticRateRelationPolynomial (c : I → K) (κ : K) : MvPolynomial I K :=
  (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) ^ (2 : ℕ)
    - MvPolynomial.C κ * ∑ i, (MvPolynomial.X i : MvPolynomial I K) ^ (2 : ℕ)

/-- The product of the relation over every labeling of the spectrum. -/
def fieldQuadraticRateOrbitPolynomial (c : I → K) (κ : K) : MvPolynomial I K :=
  ∏ σ : Equiv.Perm I, MvPolynomial.rename σ (fieldQuadraticRateRelationPolynomial c κ)

/-- Numerical value of the labeling-orbit obstruction on a spectrum. -/
def fieldQuadraticRateOrbitValue (c : I → K) (κ : K) (energy : I → K) : K :=
  ∏ σ : Equiv.Perm I, ((∑ i, c i * energy (σ i)) ^ (2 : ℕ) - κ * ∑ i, energy i ^ (2 : ℕ))

/-! ## Evaluation -/

omit [IsDomain K] [DecidableEq I] in
theorem eval_fieldQuadraticRateRelationPolynomial (c : I → K) (κ : K) (energy : I → K) :
    MvPolynomial.eval energy (fieldQuadraticRateRelationPolynomial c κ)
      = (∑ i, c i * energy i) ^ (2 : ℕ) - κ * ∑ i, energy i ^ (2 : ℕ) := by
  simp [fieldQuadraticRateRelationPolynomial]

omit [IsDomain K] [DecidableEq I] in
/-- The `σ`-labeled factor is the relation for the relabeled coefficient packet. -/
theorem fieldQuadraticRateOrbitValue_factor (c : I → K) (κ : K) (energy : I → K)
    (σ : Equiv.Perm I) :
    ((∑ i, c i * energy (σ i)) ^ (2 : ℕ) - κ * ∑ i, energy i ^ (2 : ℕ))
      = (∑ j, c (σ.symm j) * energy j) ^ (2 : ℕ) - κ * ∑ j, energy j ^ (2 : ℕ) := by
  have hsum : (∑ i, c i * energy (σ i)) = ∑ j, c (σ.symm j) * energy j :=
    Fintype.sum_equiv σ _ _ fun i => by simp
  rw [hsum]

omit [IsDomain K] in
theorem eval_fieldQuadraticRateOrbitPolynomial (c : I → K) (κ : K) (energy : I → K) :
    MvPolynomial.eval energy (fieldQuadraticRateOrbitPolynomial c κ)
      = fieldQuadraticRateOrbitValue c κ energy := by
  classical
  rw [fieldQuadraticRateOrbitPolynomial, fieldQuadraticRateOrbitValue, map_prod]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [MvPolynomial.eval_rename, eval_fieldQuadraticRateRelationPolynomial]
  have h2 : (∑ i, (energy ∘ σ) i ^ (2 : ℕ)) = ∑ i, energy i ^ (2 : ℕ) :=
    Fintype.sum_equiv σ (fun i => (energy ∘ σ) i ^ (2 : ℕ)) (fun j => energy j ^ (2 : ℕ)) fun i => rfl
  rw [h2]
  rfl

theorem fieldQuadraticRateOrbitValue_eq_zero_iff (c : I → K) (κ : K) (energy : I → K) :
    fieldQuadraticRateOrbitValue c κ energy = 0 ↔
      ∃ σ : Equiv.Perm I,
        (∑ j, c (σ.symm j) * energy j) ^ (2 : ℕ) - κ * ∑ j, energy j ^ (2 : ℕ) = 0 := by
  classical
  rw [fieldQuadraticRateOrbitValue, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨σ, -, hσ⟩
    exact ⟨σ, by rwa [← fieldQuadraticRateOrbitValue_factor c κ energy σ]⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, Finset.mem_univ σ, by rwa [fieldQuadraticRateOrbitValue_factor c κ energy σ]⟩

/-! ## The real instance, in terms of the quadratic-rate defect -/

/-- Over the reals the labeling factors are exactly the quadratic-rate defects of the relabeled
coefficient packets. -/
theorem fieldQuadraticRateOrbitValue_real_eq_zero_iff (c : I → ℝ) (κ : ℝ) (energy : I → ℝ) :
    fieldQuadraticRateOrbitValue c κ energy = 0 ↔
      ∃ σ : Equiv.Perm I, quadraticRateDefect (fun j => c (σ.symm j)) κ energy = 0 := by
  rw [fieldQuadraticRateOrbitValue_eq_zero_iff]
  rfl

/-! ## Symmetry and descent to the characteristic coefficients -/

omit [IsDomain K] in
theorem fieldQuadraticRateOrbitPolynomial_isSymmetric (c : I → K) (κ : K) :
    MvPolynomial.IsSymmetric (fieldQuadraticRateOrbitPolynomial c κ) := by
  classical
  intro e
  simp only [fieldQuadraticRateOrbitPolynomial, map_prod, MvPolynomial.rename_rename]
  exact Fintype.prod_equiv (Equiv.mulLeft e)
    (fun σ : Equiv.Perm I =>
      MvPolynomial.rename (e * σ) (fieldQuadraticRateRelationPolynomial c κ))
    (fun σ : Equiv.Perm I =>
      MvPolynomial.rename σ (fieldQuadraticRateRelationPolynomial c κ))
    (fun σ => rfl)

/-- The orbit obstruction rewritten in the elementary symmetric functions of the spectrum, that
is in the characteristic coefficients of the Hamiltonian. -/
def fieldQuadraticRateCoefficientPolynomial (c : I → K) (κ : K) :
    MvPolynomial (Fin (Fintype.card I)) K :=
  (MvPolynomial.esymmAlgEquiv I K rfl).symm
    ⟨fieldQuadraticRateOrbitPolynomial c κ, fieldQuadraticRateOrbitPolynomial_isSymmetric c κ⟩

omit [IsDomain K] in
theorem esymmAlgHom_fieldQuadraticRateCoefficientPolynomial (c : I → K) (κ : K) :
    (MvPolynomial.esymmAlgHom I K (Fintype.card I)
      (fieldQuadraticRateCoefficientPolynomial c κ)).1
      = fieldQuadraticRateOrbitPolynomial c κ := by
  change ((MvPolynomial.esymmAlgEquiv I K rfl)
      (fieldQuadraticRateCoefficientPolynomial c κ)).1 = fieldQuadraticRateOrbitPolynomial c κ
  simp [fieldQuadraticRateCoefficientPolynomial]

omit [IsDomain K] in
/-- Evaluating the characteristic-coefficient obstruction on elementary symmetric spectral data
reproduces the labeling-orbit obstruction. -/
theorem eval_fieldQuadraticRateCoefficientPolynomial_esymm (c : I → K) (κ : K)
    (energy : I → K) :
    MvPolynomial.eval₂ (RingHom.id K)
        (fun i : Fin (Fintype.card I) =>
          MvPolynomial.eval₂ (RingHom.id K) energy (MvPolynomial.esymm I K (i + 1)))
        (fieldQuadraticRateCoefficientPolynomial c κ)
      = MvPolynomial.eval₂ (RingHom.id K) energy (fieldQuadraticRateOrbitPolynomial c κ) := by
  have h := congrArg (MvPolynomial.eval₂ (RingHom.id K) energy)
    (esymmAlgHom_fieldQuadraticRateCoefficientPolynomial c κ)
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq,
    ← MvPolynomial.eval₂_assoc] at h
  exact h

/-! ## Nonvanishing -/

variable [CharZero K]

/-- **The quadratic-rate relation is a nonzero polynomial** unless both the multiple and the
coefficient packet vanish.  Only two levels and characteristic zero are used. -/
theorem fieldQuadraticRateRelationPolynomial_eq_zero_iff (hcard : 2 ≤ Fintype.card I)
    (c : I → K) (κ : K) :
    fieldQuadraticRateRelationPolynomial c κ = 0 ↔ κ = 0 ∧ c = 0 := by
  constructor
  · intro hzero
    have hval : ∀ energy : I → K, (∑ i, c i * energy i) ^ (2 : ℕ) = κ * ∑ i, energy i ^ (2 : ℕ) := by
      intro energy
      have := congrArg (MvPolynomial.eval energy) hzero
      rw [eval_fieldQuadraticRateRelationPolynomial] at this
      simpa [sub_eq_zero] using this
    have hsingle : ∀ i : I, c i ^ (2 : ℕ) = κ := by
      intro i
      have h := hval (fun x => if x = i then 1 else 0)
      have h1 : (∑ x, c x * (if x = i then (1 : K) else 0)) = c i := by simp
      have h2 : (∑ x, (if x = i then (1 : K) else 0) ^ (2 : ℕ)) = 1 := by simp
      rw [h1, h2, mul_one] at h
      exact h
    have hcross : ∀ i j : I, i ≠ j → c i * c j = 0 := by
      intro i j hij
      have h := hval (fun x => (if x = i then 1 else 0) + (if x = j then 1 else 0))
      have h1 : (∑ x, c x * ((if x = i then (1 : K) else 0) + (if x = j then 1 else 0)))
          = c i + c j := by
        simp only [mul_add, Finset.sum_add_distrib]
        simp
      have h2 : (∑ x, ((if x = i then (1 : K) else 0) + (if x = j then 1 else 0)) ^ (2 : ℕ))
          = 2 := by
        have hji : ¬ (j = i) := fun hh => hij hh.symm
        have hval2 : ∀ x : I, ((if x = i then (1 : K) else 0) + (if x = j then 1 else 0)) ^ (2 : ℕ)
            = (if x = i then (1 : K) else 0) + (if x = j then 1 else 0) := by
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
      have htwo : (2 : K) * (c i * c j) = 0 := by
        have hexp : (c i + c j) ^ (2 : ℕ) = c i ^ (2 : ℕ) + 2 * (c i * c j) + c j ^ (2 : ℕ) := by ring
        rw [hexp, hi, hj] at h
        have : κ + 2 * (c i * c j) + κ = κ * 2 := by rw [h]
        linear_combination this
      have h2ne : (2 : K) ≠ 0 := two_ne_zero
      exact (mul_eq_zero.mp htwo).resolve_left h2ne
    obtain ⟨t, -, ht2⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset I)) (n := 2)
      (by simpa using hcard)
    obtain ⟨i, j, hij, -⟩ := Finset.card_eq_two.mp ht2
    have hκ : κ = 0 := by
      rcases mul_eq_zero.mp (hcross i j hij) with hzi | hzj
      · rw [← hsingle i, hzi]; ring
      · rw [← hsingle j, hzj]; ring
    refine ⟨hκ, ?_⟩
    funext x
    have hx := hsingle x
    rw [hκ] at hx
    have : c x = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx
      exact this
    rw [this]
    rfl
  · rintro ⟨rfl, rfl⟩
    simp [fieldQuadraticRateRelationPolynomial]

theorem fieldQuadraticRateOrbitPolynomial_ne_zero (hcard : 2 ≤ Fintype.card I)
    {c : I → K} {κ : K} (h : ¬ (κ = 0 ∧ c = 0)) :
    fieldQuadraticRateOrbitPolynomial c κ ≠ 0 := by
  classical
  rw [fieldQuadraticRateOrbitPolynomial]
  refine Finset.prod_ne_zero_iff.mpr fun σ _ hrename => ?_
  refine h ?_
  rw [← fieldQuadraticRateRelationPolynomial_eq_zero_iff hcard c κ]
  exact MvPolynomial.rename_injective (f := (σ : I → I)) σ.injective (by simpa using hrename)

theorem fieldQuadraticRateCoefficientPolynomial_ne_zero (hcard : 2 ≤ Fintype.card I)
    {c : I → K} {κ : K} (h : ¬ (κ = 0 ∧ c = 0)) :
    fieldQuadraticRateCoefficientPolynomial c κ ≠ 0 := by
  intro hzero
  apply fieldQuadraticRateOrbitPolynomial_ne_zero hcard h
  rw [← esymmAlgHom_fieldQuadraticRateCoefficientPolynomial c κ, hzero]
  simp

end GaloisForLFunctions.HTGeometry
