import GaloisForLFunctions.HTGeometry.SpectralCharacterReplicaHeightLaw
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def spectralRelationLinearPolynomial
    {I : Type*} [Fintype I] (k : I → ℤ) :
    MvPolynomial I ℚ :=
  ∑ i, MvPolynomial.C (k i : ℚ) * MvPolynomial.X i

def spectralRelationOrbitPolynomial
    {I : Type*} [Fintype I] (k : I → ℤ) :
    MvPolynomial I ℚ := by
  classical
  exact
    ∏ σ : Equiv.Perm I,
      MvPolynomial.rename σ (spectralRelationLinearPolynomial k)

/-- Numerical value of the product over every labeling of a spectrum. -/
def spectralRelationOrbitValue
    {I : Type*} [Fintype I] (k : I → ℤ) (energy : I → ℝ) : ℝ := by
  classical
  exact
    ∏ σ : Equiv.Perm I,
      ∑ i, (k i : ℝ) * energy (σ i)

/-- Complex value of the same labeling-orbit obstruction. -/
def spectralRelationOrbitValueComplex
    {I : Type*} [Fintype I] (k : I → ℤ) (energy : I → ℂ) : ℂ := by
  classical
  exact
    ∏ σ : Equiv.Perm I,
      ∑ i, (k i : ℂ) * energy (σ i)

theorem spectralRelationOrbitValue_eq_zero_iff
    {I : Type*} [Fintype I] (k : I → ℤ) (energy : I → ℝ) :
    spectralRelationOrbitValue k energy = 0 ↔
      ∃ σ : Equiv.Perm I,
        ∑ i, (k i : ℝ) * energy (σ i) = 0 := by
  classical
  unfold spectralRelationOrbitValue
  rw [Finset.prod_eq_zero_iff]
  simp

theorem spectralRelationOrbitValue_ne_zero_iff
    {I : Type*} [Fintype I] (k : I → ℤ) (energy : I → ℝ) :
    spectralRelationOrbitValue k energy ≠ 0 ↔
      ∀ σ : Equiv.Perm I,
        ∑ i, (k i : ℝ) * energy (σ i) ≠ 0 := by
  classical
  unfold spectralRelationOrbitValue
  rw [Finset.prod_ne_zero_iff]
  simp

theorem spectralRelationOrbitPolynomial_isSymmetric
    {I : Type*} [Fintype I] (k : I → ℤ) :
    MvPolynomial.IsSymmetric
      (spectralRelationOrbitPolynomial k) := by
  classical
  intro e
  simp only [spectralRelationOrbitPolynomial, map_prod,
    MvPolynomial.rename_rename]
  exact Fintype.prod_equiv (Equiv.mulLeft e)
    (fun σ : Equiv.Perm I =>
      MvPolynomial.rename (e * σ)
        (spectralRelationLinearPolynomial k))
    (fun σ : Equiv.Perm I =>
      MvPolynomial.rename σ
        (spectralRelationLinearPolynomial k))
    (fun σ => rfl)

theorem eval_spectralRelationLinearPolynomial
    {I : Type*} [Fintype I] (k : I → ℤ) (energy : I → ℚ) :
    MvPolynomial.eval energy (spectralRelationLinearPolynomial k) =
      ∑ i, (k i : ℚ) * energy i := by
  simp [spectralRelationLinearPolynomial]

/-- Real evaluation of one integer spectral relation. -/
theorem eval₂_spectralRelationLinearPolynomial_real
    {I : Type*} [Fintype I] (k : I → ℤ) (energy : I → ℝ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) energy
        (spectralRelationLinearPolynomial k) =
      ∑ i, (k i : ℝ) * energy i := by
  rw [spectralRelationLinearPolynomial,
    MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_X]
  change (Rat.castHom ℝ) (k i : ℚ) * energy i =
    (k i : ℝ) * energy i
  rw [map_intCast]

theorem eval₂_spectralRelationLinearPolynomial_complex
    {I : Type*} [Fintype I] (k : I → ℤ) (energy : I → ℂ) :
    MvPolynomial.eval₂ (Rat.castHom ℂ) energy
        (spectralRelationLinearPolynomial k) =
      ∑ i, (k i : ℂ) * energy i := by
  rw [spectralRelationLinearPolynomial,
    MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_X]
  change (Rat.castHom ℂ) (k i : ℚ) * energy i =
    (k i : ℂ) * energy i
  rw [map_intCast]

theorem spectralRelationLinearPolynomial_ne_zero
    {I : Type*} [Fintype I] {k : I → ℤ} (hk : k ≠ 0) :
    spectralRelationLinearPolynomial k ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    simpa [Function.ne_iff] using hk
  intro hzero
  let point : I → ℚ := fun j => if j = i then 1 else 0
  have heval := congrArg (MvPolynomial.eval point) hzero
  rw [eval_spectralRelationLinearPolynomial] at heval
  have hsum : (∑ j, (k j : ℚ) * point j) = (k i : ℚ) := by
    classical
    simp [point]
  rw [hsum] at heval
  norm_num at heval
  exact hi (Int.cast_injective heval)

theorem spectralRelationOrbitPolynomial_ne_zero
    {I : Type*} [Fintype I] {k : I → ℤ} (hk : k ≠ 0) :
    spectralRelationOrbitPolynomial k ≠ 0 := by
  classical
  unfold spectralRelationOrbitPolynomial
  apply Finset.prod_ne_zero_iff.mpr
  intro σ _ hrename
  apply spectralRelationLinearPolynomial_ne_zero hk
  apply
    (MvPolynomial.rename_injective
      (f := (σ : I → I)) σ.injective)
  simpa using hrename

/-- The orbit obstruction vanishes exactly when at least one relabeling of
the real spectrum satisfies the selected integer relation. -/
theorem eval₂_spectralRelationOrbitPolynomial_real
    {I : Type*} [Fintype I] (k : I → ℤ) (energy : I → ℝ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) energy
        (spectralRelationOrbitPolynomial k) =
      spectralRelationOrbitValue k energy := by
  simp only [spectralRelationOrbitPolynomial,
    spectralRelationOrbitValue,
    MvPolynomial.eval₂_prod, MvPolynomial.eval₂_rename,
    eval₂_spectralRelationLinearPolynomial_real,
    Function.comp_apply]

theorem eval₂_spectralRelationOrbitPolynomial_complex
    {I : Type*} [Fintype I] (k : I → ℤ) (energy : I → ℂ) :
    MvPolynomial.eval₂ (Rat.castHom ℂ) energy
        (spectralRelationOrbitPolynomial k) =
      spectralRelationOrbitValueComplex k energy := by
  simp only [spectralRelationOrbitPolynomial,
    spectralRelationOrbitValueComplex,
    MvPolynomial.eval₂_prod, MvPolynomial.eval₂_rename,
    eval₂_spectralRelationLinearPolynomial_complex,
    Function.comp_apply]

def spectralRelationCoefficientPolynomial
    {I : Type*} [Fintype I] (k : I → ℤ) :
    MvPolynomial (Fin (Fintype.card I)) ℚ :=
  (MvPolynomial.esymmAlgEquiv I ℚ rfl).symm
    ⟨spectralRelationOrbitPolynomial k,
      spectralRelationOrbitPolynomial_isSymmetric k⟩

theorem esymmAlgHom_spectralRelationCoefficientPolynomial
    {I : Type*} [Fintype I] (k : I → ℤ) :
    (MvPolynomial.esymmAlgHom I ℚ (Fintype.card I)
      (spectralRelationCoefficientPolynomial k)).1 =
      spectralRelationOrbitPolynomial k := by
  change
    ((MvPolynomial.esymmAlgEquiv I ℚ rfl)
      (spectralRelationCoefficientPolynomial k)).1 =
      spectralRelationOrbitPolynomial k
  simp [spectralRelationCoefficientPolynomial]

/-- A nonzero relation has a nonzero obstruction already at the level of
the unordered characteristic coefficients. -/
theorem spectralRelationCoefficientPolynomial_ne_zero
    {I : Type*} [Fintype I] {k : I → ℤ} (hk : k ≠ 0) :
    spectralRelationCoefficientPolynomial k ≠ 0 := by
  intro hzero
  apply spectralRelationOrbitPolynomial_ne_zero hk
  rw [← esymmAlgHom_spectralRelationCoefficientPolynomial k, hzero]
  simp

/-- Evaluating the coefficient obstruction on elementary symmetric spectral
data reproduces the label-orbit obstruction. -/
theorem eval_spectralRelationCoefficientPolynomial_esymm
    {I : Type*} [Fintype I] (k : I → ℤ) (energy : I → ℚ) :
    MvPolynomial.eval
        (fun i : Fin (Fintype.card I) =>
          MvPolynomial.eval energy
            (MvPolynomial.esymm I ℚ (i + 1)))
        (spectralRelationCoefficientPolynomial k) =
      MvPolynomial.eval energy
        (spectralRelationOrbitPolynomial k) := by
  have h := congrArg (MvPolynomial.aeval energy)
    (esymmAlgHom_spectralRelationCoefficientPolynomial k)
  rw [MvPolynomial.esymmAlgHom_apply] at h
  simp only [MvPolynomial.comp_aeval_apply] at h
  have hid : algebraMap ℚ ℚ = RingHom.id ℚ := by
    ext x
    rfl
  simpa only [MvPolynomial.aeval_def, hid,
    MvPolynomial.eval₂_id] using h

/-- The same universal coefficient identity evaluated on a real spectrum. -/
theorem eval₂_spectralRelationCoefficientPolynomial_real_esymm
    {I : Type*} [Fintype I] (k : I → ℤ) (energy : I → ℝ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ)
        (fun i : Fin (Fintype.card I) =>
          MvPolynomial.eval₂ (Rat.castHom ℝ) energy
            (MvPolynomial.esymm I ℚ (i + 1)))
        (spectralRelationCoefficientPolynomial k) =
      MvPolynomial.eval₂ (Rat.castHom ℝ) energy
        (spectralRelationOrbitPolynomial k) := by
  have h := congrArg
    (MvPolynomial.eval₂ (Rat.castHom ℝ) energy)
    (esymmAlgHom_spectralRelationCoefficientPolynomial k)
  rw [MvPolynomial.esymmAlgHom_apply,
    MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq,
    ← MvPolynomial.eval₂_assoc] at h
  exact h

/-- Universal coefficient identity evaluated on a complex spectrum. -/
theorem eval₂_spectralRelationCoefficientPolynomial_complex_esymm
    {I : Type*} [Fintype I] (k : I → ℤ) (energy : I → ℂ) :
    MvPolynomial.eval₂ (Rat.castHom ℂ)
        (fun i : Fin (Fintype.card I) =>
          MvPolynomial.eval₂ (Rat.castHom ℂ) energy
            (MvPolynomial.esymm I ℚ (i + 1)))
        (spectralRelationCoefficientPolynomial k) =
      MvPolynomial.eval₂ (Rat.castHom ℂ) energy
        (spectralRelationOrbitPolynomial k) := by
  have h := congrArg
    (MvPolynomial.eval₂ (Rat.castHom ℂ) energy)
    (esymmAlgHom_spectralRelationCoefficientPolynomial k)
  rw [MvPolynomial.esymmAlgHom_apply,
    MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq,
    ← MvPolynomial.eval₂_assoc] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
