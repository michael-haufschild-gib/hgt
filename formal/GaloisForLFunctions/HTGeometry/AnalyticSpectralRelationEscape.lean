import GaloisForLFunctions.HTGeometry.FiniteAnalyticEscape
import GaloisForLFunctions.HTGeometry.SpectralRelationOrbitPolynomial

/-!
# Simultaneous analytic escape from every labeling of one spectral relation

For a fixed integer coefficient packet there are only finitely many
labelings.  If every labeled branch relation is nontrivial on one connected
analytic chart, a single point of that chart avoids all labelings.  At that
point the symmetric characteristic-coefficient obstruction is nonzero.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One labeled integer relation among analytic spectral branches. -/
def permutedAnalyticSpectralRelation
    {I P : Type*} [Fintype I]
    (k : I → ℤ) (branch : I → P → ℂ)
    (σ : Equiv.Perm I) (p : P) : ℂ :=
  ∑ i, (k i : ℂ) * branch (σ i) p

/-- Coefficient packet on the fixed branch labeling corresponding to one
permutation of the selected integer relation. -/
def permutedSpectralCoefficient
    {I : Type*} (k : I → ℤ) (σ : Equiv.Perm I) :
    I → ℂ :=
  fun j => (k (σ.symm j) : ℂ)

theorem sum_permutedSpectralCoefficient_eq_relation
    {I P : Type*} [Fintype I]
    (k : I → ℤ) (branch : I → P → ℂ)
    (σ : Equiv.Perm I) (p : P) :
    (∑ j, permutedSpectralCoefficient k σ j * branch j p) =
      permutedAnalyticSpectralRelation k branch σ p := by
  symm
  apply Fintype.sum_equiv σ
  intro i
  simp [permutedSpectralCoefficient]

/-- A nonzero balanced integer relation remains nonconstant after every
permutation of its coefficients. -/
theorem permutedSpectralCoefficient_not_constant
    {I : Type*} [Fintype I] [Nonempty I]
    {k : I → ℤ} (hbalanced : SpectralCharacterBalanced k)
    (hk : k ≠ 0) (σ : Equiv.Perm I) :
    ¬ ∀ x y, permutedSpectralCoefficient k σ x =
      permutedSpectralCoefficient k σ y := by
  intro hconstant
  have hkconstant : ∀ i j, k i = k j := by
    intro i j
    have h := hconstant (σ i) (σ j)
    simp only [permutedSpectralCoefficient,
      Equiv.symm_apply_apply] at h
    exact Int.cast_injective h
  let i₀ : I := Classical.choice inferInstance
  have hsum :
      (∑ i, k i) = (Fintype.card I : ℤ) * k i₀ := by
    calc
      (∑ i, k i) = ∑ i, k i₀ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hkconstant i i₀
      _ = (Fintype.card I : ℤ) * k i₀ := by
        simp
  have hmul : (Fintype.card I : ℤ) * k i₀ = 0 := by
    rw [← hsum]
    exact hbalanced
  have hcard : (Fintype.card I : ℤ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hi₀ : k i₀ = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hcard
  apply hk
  funext i
  rw [hkconstant i i₀, hi₀]
  rfl

theorem permutedAnalyticSpectralRelation_analyticOnNhd
    {I P : Type*} [Fintype I]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (k : I → ℤ) (branch : I → P → ℂ)
    (U : Set P)
    (hbranch : ∀ i, AnalyticOnNhd ℂ (branch i) U)
    (σ : Equiv.Perm I) :
    AnalyticOnNhd ℂ
      (permutedAnalyticSpectralRelation k branch σ) U := by
  intro p hp
  apply Finset.analyticAt_fun_sum
  intro i hi
  exact analyticAt_const.mul (hbranch (σ i) p hp)

/-- If every labeling of one spectral relation can be escaped somewhere in
the same analytic chart, then all labelings can be escaped simultaneously. -/
theorem exists_all_permutedAnalyticSpectralRelation_ne_zero
    {I P : Type*} [Fintype I]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (k : I → ℤ) (branch : I → P → ℂ)
    (U : Set P)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U)
    (hUnonempty : U.Nonempty)
    (hbranch : ∀ i, AnalyticOnNhd ℂ (branch i) U)
    (hlabel :
      ∀ σ : Equiv.Perm I,
        ∃ p ∈ U,
          permutedAnalyticSpectralRelation k branch σ p ≠ 0) :
    ∃ p ∈ U,
      ∀ σ : Equiv.Perm I,
        permutedAnalyticSpectralRelation k branch σ p ≠ 0 := by
  classical
  exact
    exists_forall_neZero_of_finite_analyticOnNhd_complex_local
      (fun σ => permutedAnalyticSpectralRelation k branch σ)
      U hUopen hUconnected hUnonempty
      (fun σ =>
        permutedAnalyticSpectralRelation_analyticOnNhd
          k branch U hbranch σ)
      hlabel

/-- Simultaneous branch escape makes the full symmetric labeling-orbit
obstruction nonzero. -/
theorem exists_spectralRelationOrbitValueComplex_ne_zero_of_analytic
    {I P : Type*} [Fintype I]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (k : I → ℤ) (branch : I → P → ℂ)
    (U : Set P)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U)
    (hUnonempty : U.Nonempty)
    (hbranch : ∀ i, AnalyticOnNhd ℂ (branch i) U)
    (hlabel :
      ∀ σ : Equiv.Perm I,
        ∃ p ∈ U,
          permutedAnalyticSpectralRelation k branch σ p ≠ 0) :
    ∃ p ∈ U,
      spectralRelationOrbitValueComplex k (fun i => branch i p) ≠ 0 := by
  classical
  obtain ⟨p, hpU, hp⟩ :=
    exists_all_permutedAnalyticSpectralRelation_ne_zero
      k branch U hUopen hUconnected hUnonempty hbranch hlabel
  refine ⟨p, hpU, ?_⟩
  unfold spectralRelationOrbitValueComplex
  rw [Finset.prod_ne_zero_iff]
  intro σ hσ
  simpa only [permutedAnalyticSpectralRelation] using hp σ

/-- The preceding analytic escape is detected without eigenvalue labels by
the universal polynomial in elementary symmetric spectral data. -/
theorem exists_coefficientObstruction_eval_ne_zero_of_analytic
    {I P : Type*} [Fintype I]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (k : I → ℤ) (branch : I → P → ℂ)
    (U : Set P)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U)
    (hUnonempty : U.Nonempty)
    (hbranch : ∀ i, AnalyticOnNhd ℂ (branch i) U)
    (hlabel :
      ∀ σ : Equiv.Perm I,
        ∃ p ∈ U,
          permutedAnalyticSpectralRelation k branch σ p ≠ 0) :
    ∃ p ∈ U,
      MvPolynomial.eval₂ (Rat.castHom ℂ)
          (fun i : Fin (Fintype.card I) =>
            MvPolynomial.eval₂ (Rat.castHom ℂ)
              (fun j => branch j p)
              (MvPolynomial.esymm I ℚ (i + 1)))
          (spectralRelationCoefficientPolynomial k) ≠ 0 := by
  obtain ⟨p, hpU, hp⟩ :=
    exists_spectralRelationOrbitValueComplex_ne_zero_of_analytic
      k branch U hUopen hUconnected hUnonempty hbranch hlabel
  refine ⟨p, hpU, ?_⟩
  rw [eval₂_spectralRelationCoefficientPolynomial_complex_esymm,
    eval₂_spectralRelationOrbitPolynomial]
  exact hp

end

end GaloisForLFunctions.HTGeometry
