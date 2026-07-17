import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Finite tomography of a matrix Wigner--Smith clock

For an `n × n` complex delay matrix `Q`, diagonal channel delays together with the real and
imaginary polarizations of every unordered channel pair reconstruct every entry of `Q`.  The
reporters can be indexed without redundancy by ordered pairs:

* `(j,j)` reports `Qjj`;
* `(j,k)` with `j < k` reports the expanded quadratic form at `e_j + e_k`;
* `(k,j)` reports the expanded quadratic form at `e_j + i e_k`.

There are exactly `n²` such scalar reporters.  The reconstruction is purely algebraic and does not
assume Hermiticity, unitarity, a spectral decomposition, or any scattering-model hypothesis.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Diagonal channel-delay reporter. -/
def matrixDelayDiagonal {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (j : Fin n) : ℂ :=
  Q j j

/-- Expanded quadratic reporter at the channel vector `e_j + e_k`. -/
def matrixDelayPlus {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (j k : Fin n) : ℂ :=
  Q j j + Q j k + Q k j + Q k k

/-- Expanded quadratic reporter at the channel vector `e_j + i e_k`. -/
def matrixDelayImaginary {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (j k : Fin n) : ℂ :=
  Q j j + I * Q j k - I * Q k j + Q k k

/-- The nonredundant delay panel: one scalar reporter for each ordered channel pair. -/
def matrixDelayPanel {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) :
    Fin n × Fin n → ℂ := fun p =>
  if p.1 = p.2 then
    matrixDelayDiagonal Q p.1
  else if p.1 < p.2 then
    matrixDelayPlus Q p.1 p.2
  else
    matrixDelayImaginary Q p.2 p.1

/-- The delay panel contains exactly `n²` scalar reporters. -/
theorem matrixDelayPanel_reporter_count (n : ℕ) :
    Fintype.card (Fin n × Fin n) = n ^ 2 := by
  simp [pow_two]

/-- Diagonal ordered pairs carry the diagonal matrix entries. -/
theorem matrixDelayPanel_diagonal {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    matrixDelayPanel Q (j, j) = Q j j := by
  simp [matrixDelayPanel, matrixDelayDiagonal]

/-- The increasing orientation of an off-diagonal pair carries its real polarization. -/
theorem matrixDelayPanel_plus {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℂ) (j k : Fin n) (hjk : j < k) :
    matrixDelayPanel Q (j, k) = matrixDelayPlus Q j k := by
  simp [matrixDelayPanel, ne_of_lt hjk, hjk]

/-- The decreasing orientation of an off-diagonal pair carries its imaginary polarization. -/
theorem matrixDelayPanel_imaginary {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℂ) (j k : Fin n) (hjk : j < k) :
    matrixDelayPanel Q (k, j) = matrixDelayImaginary Q j k := by
  simp [matrixDelayPanel, ne_of_gt hjk, not_lt_of_ge hjk.le]

/-- Exact polarization reconstruction of the forward off-diagonal entry. -/
theorem matrixDelay_offDiagonal_reconstruct {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℂ) (j k : Fin n) :
    Q j k =
      ((matrixDelayPlus Q j k - matrixDelayDiagonal Q j - matrixDelayDiagonal Q k) -
        I * (matrixDelayImaginary Q j k - matrixDelayDiagonal Q j -
          matrixDelayDiagonal Q k)) / 2 := by
  simp only [matrixDelayPlus, matrixDelayDiagonal, matrixDelayImaginary]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact polarization reconstruction of the reverse off-diagonal entry. -/
theorem matrixDelay_reverseOffDiagonal_reconstruct {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℂ) (j k : Fin n) :
    Q k j =
      ((matrixDelayPlus Q j k - matrixDelayDiagonal Q j - matrixDelayDiagonal Q k) +
        I * (matrixDelayImaginary Q j k - matrixDelayDiagonal Q j -
          matrixDelayDiagonal Q k)) / 2 := by
  simp only [matrixDelayPlus, matrixDelayDiagonal, matrixDelayImaginary]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Finite matrix-delay tomography.**  Equality of all `n²` scalar reporters forces equality of
the complete complex delay matrices. -/
theorem matrixDelayPanel_injective {n : ℕ} :
    Function.Injective
      (matrixDelayPanel : Matrix (Fin n) (Fin n) ℂ → Fin n × Fin n → ℂ) := by
  intro Q R hpanel
  ext j k
  by_cases hjk : j = k
  · subst k
    simpa [matrixDelayPanel_diagonal] using congrFun hpanel (j, j)
  · rcases lt_or_gt_of_ne hjk with hjk | hkj
    · have hjj : matrixDelayDiagonal Q j = matrixDelayDiagonal R j := by
        simpa [matrixDelayDiagonal, matrixDelayPanel_diagonal] using
          congrFun hpanel (j, j)
      have hkk : matrixDelayDiagonal Q k = matrixDelayDiagonal R k := by
        simpa [matrixDelayDiagonal, matrixDelayPanel_diagonal] using
          congrFun hpanel (k, k)
      have hplus : matrixDelayPlus Q j k = matrixDelayPlus R j k := by
        simpa [matrixDelayPanel_plus Q j k hjk,
          matrixDelayPanel_plus R j k hjk] using congrFun hpanel (j, k)
      have himaginary :
          matrixDelayImaginary Q j k = matrixDelayImaginary R j k := by
        simpa [matrixDelayPanel_imaginary Q j k hjk,
          matrixDelayPanel_imaginary R j k hjk] using congrFun hpanel (k, j)
      rw [matrixDelay_offDiagonal_reconstruct Q j k,
        matrixDelay_offDiagonal_reconstruct R j k]
      rw [hjj, hkk, hplus, himaginary]
    · have hkk : matrixDelayDiagonal Q k = matrixDelayDiagonal R k := by
        simpa [matrixDelayDiagonal, matrixDelayPanel_diagonal] using
          congrFun hpanel (k, k)
      have hjj : matrixDelayDiagonal Q j = matrixDelayDiagonal R j := by
        simpa [matrixDelayDiagonal, matrixDelayPanel_diagonal] using
          congrFun hpanel (j, j)
      have hplus : matrixDelayPlus Q k j = matrixDelayPlus R k j := by
        simpa [matrixDelayPanel_plus Q k j hkj,
          matrixDelayPanel_plus R k j hkj] using congrFun hpanel (k, j)
      have himaginary :
          matrixDelayImaginary Q k j = matrixDelayImaginary R k j := by
        simpa [matrixDelayPanel_imaginary Q k j hkj,
          matrixDelayPanel_imaginary R k j hkj] using congrFun hpanel (j, k)
      rw [matrixDelay_reverseOffDiagonal_reconstruct Q k j,
        matrixDelay_reverseOffDiagonal_reconstruct R k j]
      rw [hkk, hjj, hplus, himaginary]

end


end GaloisForLFunctions.HTGeometry
