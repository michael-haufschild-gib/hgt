import GaloisForLFunctions.RHTower.MobiusDivisorCoareaHeadTransport

/-!
# Sharp conditional-energy decomposition for actual signed source fibres

Any finite collection of actual fibres has a forced component determined
by its total signed and absolute mass. The remaining conditional energy
is exactly the weighted variance of signed cell densities. Zero-mass
cells are included, since their signed mass is also zero.
-/
noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

private lemma zero_signed_mass (M : ℕ) (P R : Finset ℕ)
    (h : mobiusDivisorFibreAbsoluteMass M P R=0) :
    mobiusDivisorSelectionFibre M P R=0 := by
  apply abs_eq_zero.mp
  exact le_antisymm ((abs_mobiusDivisorSelectionFibre_le_absoluteMass M P R).trans_eq h)
    (abs_nonneg _)

/-- Every finite collection of actual cells obeys weighted Cauchy, including zero-mass cells. -/
theorem mobiusDivisorFibre_coarea_cauchy (M : ℕ) (P : Finset ℕ) (W : Finset (Finset ℕ)) :
    (∑ R ∈ W, mobiusDivisorSelectionFibre M P R)^(2 : ℕ) ≤
      (∑ R ∈ W, mobiusDivisorFibreAbsoluteMass M P R) *
      ∑ R ∈ W, (mobiusDivisorSelectionFibre M P R)^(2 : ℕ) / mobiusDivisorFibreAbsoluteMass M P R := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul W
    (fun R _ => mobiusDivisorFibreAbsoluteMass_nonneg M P R)
    (fun R _ => div_nonneg (sq_nonneg _) (mobiusDivisorFibreAbsoluteMass_nonneg M P R))
  intro R _
  by_cases hz : mobiusDivisorFibreAbsoluteMass M P R=0
  · simp [hz,zero_signed_mass M P R hz]
  · exact le_of_eq (by field_simp)

/-- Conditional energy is the forced signed-mass square plus exact cell-density variance. -/
theorem mobiusDivisorFibre_coarea_variance (M : ℕ) (P : Finset ℕ) (W : Finset (Finset ℕ)) :
    (∑ R ∈ W, (mobiusDivisorSelectionFibre M P R)^(2 : ℕ) / mobiusDivisorFibreAbsoluteMass M P R) =
    (∑ R ∈ W, mobiusDivisorSelectionFibre M P R)^(2 : ℕ) /
      (∑ R ∈ W, mobiusDivisorFibreAbsoluteMass M P R) +
    ∑ R ∈ W, (mobiusDivisorSelectionFibre M P R -
      ((∑ Q ∈ W, mobiusDivisorSelectionFibre M P Q) /
        (∑ Q ∈ W, mobiusDivisorFibreAbsoluteMass M P Q)) * mobiusDivisorFibreAbsoluteMass M P R)^(2 : ℕ) /
      mobiusDivisorFibreAbsoluteMass M P R := by
  let Y := ∑ R ∈ W, mobiusDivisorSelectionFibre M P R
  let V := ∑ R ∈ W, mobiusDivisorFibreAbsoluteMass M P R
  let J := ∑ R ∈ W, (mobiusDivisorSelectionFibre M P R)^(2 : ℕ) / mobiusDivisorFibreAbsoluteMass M P R
  change J = Y^(2 : ℕ)/V + ∑ R ∈ W,
    (mobiusDivisorSelectionFibre M P R-(Y/V)*mobiusDivisorFibreAbsoluteMass M P R)^(2 : ℕ) /
      mobiusDivisorFibreAbsoluteMass M P R
  by_cases hV : V=0
  · simp [hV,J]
  have hpoint (R : Finset ℕ) :
      (mobiusDivisorSelectionFibre M P R-(Y/V)*mobiusDivisorFibreAbsoluteMass M P R)^(2 : ℕ) /
        mobiusDivisorFibreAbsoluteMass M P R =
      (mobiusDivisorSelectionFibre M P R)^(2 : ℕ) / mobiusDivisorFibreAbsoluteMass M P R -
        2*(Y/V)*mobiusDivisorSelectionFibre M P R +
        (Y/V)^(2 : ℕ)*mobiusDivisorFibreAbsoluteMass M P R := by
    by_cases hz : mobiusDivisorFibreAbsoluteMass M P R=0
    · simp [hz,zero_signed_mass M P R hz]
    · field_simp
      ring
  have hs : (∑ R ∈ W,
      (mobiusDivisorSelectionFibre M P R-(Y/V)*mobiusDivisorFibreAbsoluteMass M P R)^(2 : ℕ) /
        mobiusDivisorFibreAbsoluteMass M P R) = J-2*(Y/V)*Y+(Y/V)^(2 : ℕ)*V := by
    simp only [hpoint,sum_add_distrib,sum_sub_distrib,← mul_sum]
    rfl
  have hm : 2*(Y/V)*Y-(Y/V)^(2 : ℕ)*V=Y^(2 : ℕ)/V := by field_simp; ring
  linarith only [hs,hm]

/-- Equality in actual-cell weighted Cauchy is exactly constant signed density on every cell. -/
theorem mobiusDivisorFibre_coarea_variance_zero_iff
    (M : ℕ) (P : Finset ℕ) (W : Finset (Finset ℕ)) :
    (∑ R ∈ W, (mobiusDivisorSelectionFibre M P R)^(2 : ℕ) / mobiusDivisorFibreAbsoluteMass M P R) =
      (∑ R ∈ W, mobiusDivisorSelectionFibre M P R)^(2 : ℕ) /
        (∑ R ∈ W, mobiusDivisorFibreAbsoluteMass M P R) ↔
    ∀ R ∈ W, mobiusDivisorSelectionFibre M P R =
      ((∑ Q ∈ W, mobiusDivisorSelectionFibre M P Q) /
        (∑ Q ∈ W, mobiusDivisorFibreAbsoluteMass M P Q)) * mobiusDivisorFibreAbsoluteMass M P R := by
  let μ := (∑ Q ∈ W, mobiusDivisorSelectionFibre M P Q) /
    (∑ Q ∈ W, mobiusDivisorFibreAbsoluteMass M P Q)
  have hd := mobiusDivisorFibre_coarea_variance M P W
  constructor
  · intro he R hR
    have hz : (∑ Q ∈ W, (mobiusDivisorSelectionFibre M P Q-μ*mobiusDivisorFibreAbsoluteMass M P Q)^(2 : ℕ) /
        mobiusDivisorFibreAbsoluteMass M P Q)=0 := by dsimp [μ]; linarith only [he,hd]
    have hterm := (sum_eq_zero_iff_of_nonneg (fun Q _ =>
      div_nonneg (sq_nonneg _) (mobiusDivisorFibreAbsoluteMass_nonneg M P Q))).mp hz R hR
    by_cases hA : mobiusDivisorFibreAbsoluteMass M P R=0
    · simp [hA,zero_signed_mass M P R hA]
    · have hs : (mobiusDivisorSelectionFibre M P R-μ*mobiusDivisorFibreAbsoluteMass M P R)^(2 : ℕ)=0 :=
        (div_eq_zero_iff.mp hterm).resolve_right hA
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · intro h
    have hz : (∑ R ∈ W,
        (mobiusDivisorSelectionFibre M P R-μ*mobiusDivisorFibreAbsoluteMass M P R)^(2 : ℕ) /
          mobiusDivisorFibreAbsoluteMass M P R)=0 := by
      apply sum_eq_zero
      intro R hR
      rw [show mobiusDivisorSelectionFibre M P R=μ*mobiusDivisorFibreAbsoluteMass M P R from h R hR]
      simp
    dsimp [μ] at hz
    linarith only [hd,hz]

end RHTower
