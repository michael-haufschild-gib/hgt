import GaloisForLFunctions.HTGeometry.FinitePacketSchwarzDoubledPositiveQuarticRealification
import GaloisForLFunctions.HTGeometry.SchurTriangulation

/-!
# Finite-matrix Schur positive quartic divisor charge

For any finite complex matrix and any unitary Schur triangularization, apply the finite-packet
positive quartic charge to the diagonal spectral packet. Charge zero is exactly the real-divisor
property of the ordinary Fredholm polynomial `det(1-zM)`. Consequently one nonreal divisor zero
forces strictly positive charge for every Schur triangularization, including non-normal matrices
and repeated spectra.
-/

open Complex Matrix
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One unitary Schur triangularization of a finite complex matrix. -/
structure FiniteMatrixSchurPacket {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) where
  U : Matrix (Fin n) (Fin n) ℂ
  T : Matrix (Fin n) (Fin n) ℂ
  unitary_left : Uᴴ * U = 1
  unitary_right : U * Uᴴ = 1
  triangular : T.BlockTriangular id
  conjugates_matrix : Uᴴ * M * U = T

/-- Every finite complex matrix has a Schur packet. -/
theorem nonempty_finiteMatrixSchurPacket {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Nonempty (FiniteMatrixSchurPacket M) := by
  obtain ⟨U, T, hU1, hU2, hT, hMT⟩ := exists_schur_triangulation n M
  exact ⟨⟨U, T, hU1, hU2, hT, hMT⟩⟩

/-- Positive quartic charge of one Schur diagonal packet. -/
def finiteMatrixSchurPositiveQuarticCharge
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) : ℝ :=
  finitePacketPositiveQuarticCharge (fun i => S.T i i)

/-- Every zero of the ordinary finite Fredholm polynomial is real. -/
def FiniteMatrixOrdinaryRealDivisor
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ z : ℂ, ((1 : Matrix (Fin n) (Fin n) ℂ) - z • M).det = 0 → z.im = 0

theorem finiteMatrixSchurPositiveQuarticCharge_nonneg
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) :
    0 ≤ finiteMatrixSchurPositiveQuarticCharge S :=
  finitePacketPositiveQuarticCharge_nonneg (fun i => S.T i i)

/-- Schur quartic charge vanishes exactly when the ordinary Fredholm divisor is real. -/
theorem finiteMatrixSchurPositiveQuarticCharge_eq_zero_iff_realDivisor
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) :
    finiteMatrixSchurPositiveQuarticCharge S = 0 ↔
      FiniteMatrixOrdinaryRealDivisor M := by
  constructor
  · intro hcharge
    have hdiag : ∀ i, (S.T i i).im = 0 :=
      (finitePacketPositiveQuarticCharge_eq_zero_iff
        (fun i => S.T i i)).mp hcharge
    intro z hz
    have hdet : ((1 : Matrix (Fin n) (Fin n) ℂ) + (-z) • M).det = 0 := by
      simpa only [neg_smul, sub_eq_add_neg] using hz
    have hprod := det_one_add_smul_eq_prod S.unitary_right S.triangular
      S.conjugates_matrix (-z)
    rw [hprod] at hdet
    obtain ⟨i, hi, hfactor⟩ := Finset.prod_eq_zero_iff.mp hdet
    have htii : S.T i i ≠ 0 := by
      intro hzero
      simp [hzero] at hfactor
    have htre : (S.T i i).re ≠ 0 := by
      intro hre
      apply htii
      apply Complex.ext hre (hdiag i)
    have him := congrArg Complex.im hfactor
    simp only [Complex.add_im, Complex.one_im, zero_add, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, hdiag i, mul_zero] at him
    exact neg_eq_zero.mp ((mul_eq_zero.mp him).resolve_right htre)
  · intro hreal
    apply (finitePacketPositiveQuarticCharge_eq_zero_iff
      (fun i => S.T i i)).mpr
    intro i
    by_cases hi : S.T i i = 0
    · simp [hi]
    · have hfactor : 1 + (-(S.T i i)⁻¹) * S.T i i = 0 := by
        field_simp [hi]
        ring
      have hdet : ((1 : Matrix (Fin n) (Fin n) ℂ) -
          (S.T i i)⁻¹ • M).det = 0 := by
        have hprod := det_one_add_smul_eq_prod S.unitary_right S.triangular
          S.conjugates_matrix (-(S.T i i)⁻¹)
        have hzprod : ∏ j, (1 + (-(S.T i i)⁻¹) * S.T j j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) hfactor
        rw [← hprod] at hzprod
        simpa only [neg_smul, sub_eq_add_neg] using hzprod
      have hinvIm : ((S.T i i)⁻¹).im = 0 := hreal _ hdet
      rw [Complex.inv_im] at hinvIm
      have hnorm : Complex.normSq (S.T i i) ≠ 0 := by
        simpa [Complex.normSq_eq_zero] using hi
      have hneg : -(S.T i i).im = 0 :=
        (div_eq_zero_iff).mp hinvIm |>.resolve_right hnorm
      linarith

/-- One nonreal ordinary-divisor zero makes every Schur-packet charge strictly positive. -/
theorem finiteMatrixSchurPositiveQuarticCharge_pos_of_nonrealDivisor
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) {z : ℂ}
    (hz : ((1 : Matrix (Fin n) (Fin n) ℂ) - z • M).det = 0)
    (him : z.im ≠ 0) :
    0 < finiteMatrixSchurPositiveQuarticCharge S := by
  have hnonneg := finiteMatrixSchurPositiveQuarticCharge_nonneg S
  have hne : finiteMatrixSchurPositiveQuarticCharge S ≠ 0 := by
    intro hzero
    have hreal :=
      (finiteMatrixSchurPositiveQuarticCharge_eq_zero_iff_realDivisor S).mp hzero
    exact him (hreal z hz)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- A nonzero ordinary-divisor zero contributes its reciprocal local quartic charge to every
Schur packet.  This is quantitative: unlike mere positivity, it gives a lower bound stable under
small perturbations of the divisor zero. -/
theorem sourcePairPositiveQuarticCharge_inv_le_finiteMatrixSchurPositiveQuarticCharge
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (S : FiniteMatrixSchurPacket M) {z : ℂ}
    (hz : ((1 : Matrix (Fin n) (Fin n) ℂ) - z • M).det = 0)
    (hz0 : z ≠ 0) :
    sourcePairPositiveQuarticCharge (z⁻¹).re (z⁻¹).im ≤
      finiteMatrixSchurPositiveQuarticCharge S := by
  have hdet : ((1 : Matrix (Fin n) (Fin n) ℂ) + (-z) • M).det = 0 := by
    simpa only [neg_smul, sub_eq_add_neg] using hz
  have hprod := det_one_add_smul_eq_prod S.unitary_right S.triangular
    S.conjugates_matrix (-z)
  rw [hprod] at hdet
  obtain ⟨i, hi, hfactor⟩ := Finset.prod_eq_zero_iff.mp hdet
  have hmul : z * S.T i i = 1 := by
    calc
      z * S.T i i = -(1 + (-z) * S.T i i) + 1 := by ring
      _ = 1 := by rw [hfactor]; simp
  have htii : S.T i i = z⁻¹ := by
    apply mul_left_cancel₀ hz0
    rw [hmul, mul_inv_cancel₀ hz0]
  have hlocal :
      sourcePairPositiveQuarticCharge (S.T i i).re (S.T i i).im ≤
        ∑ j, sourcePairPositiveQuarticCharge (S.T j j).re (S.T j j).im :=
    Finset.single_le_sum
      (fun j _ => sourcePairPositiveQuarticCharge_nonneg (S.T j j).re (S.T j j).im)
      (Finset.mem_univ i)
  simpa only [finiteMatrixSchurPositiveQuarticCharge,
    finitePacketPositiveQuarticCharge, htii] using hlocal

end

end GaloisForLFunctions.HTGeometry
