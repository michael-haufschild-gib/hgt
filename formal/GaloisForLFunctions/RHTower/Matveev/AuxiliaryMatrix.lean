import GaloisForLFunctions.RHTower.Matveev.PerturbedComponents
import Mathlib.NumberTheory.SiegelsLemma

/-!
# The integer auxiliary matrix of the effective construction

For rational primes the auxiliary matrix has **integer** entries: the direction coefficients of the
perturbed normalization are integers, and the sample weights are `S`-units.  No coefficient number
field, no ring of integers, and no house appear.  Siegel's lemma over `ℤ` therefore supplies the
auxiliary coefficients directly, with the usual height bound.

A kernel vector of this matrix is exactly a family of vanishing component boxes, which by the
multinomial shift law makes the exact direction powers vanish — and hence, by the perturbation
estimate, makes the normalized frequency powers small.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

attribute [local instance] Matrix.seminormedAddCommGroup

open Finset Matrix

variable {d : ℕ}

/-- The exponent box of width `L`. -/
abbrev BoxIndex (d L : ℕ) := Fin d → Fin (L + 1)

/-- The row index: a sample together with a multi-index of directions. -/
abbrev RowIndex (d S T : ℕ) := Fin S × (Fin d → Fin T)

/-- The integer exponent vector of a box index. -/
def boxExponent {L : ℕ} (t : BoxIndex d L) : Fin d → ℤ := fun j => ((t j : ℕ) : ℤ)

/-- The natural exponent vector of a box index. -/
def boxNat {L : ℕ} (t : BoxIndex d L) : Fin d → ℕ := fun j => (t j : ℕ)

/-- The integer entry of the auxiliary matrix. -/
def auxEntry (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d) {L S T : ℕ}
    (row : RowIndex d S T) (t : BoxIndex d L) : ℤ :=
  (∏ i ∈ Finset.univ.erase pivot,
      perturbedDirection b pivot (boxExponent t) i ^ (row.2 i : ℕ))
    * ((freqUnit p (boxNat t) (row.1 : ℕ) : ℕ) : ℤ)

/-- The integer auxiliary matrix. -/
def auxMatrix (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d) (L S T : ℕ) :
    Matrix (RowIndex d S T) (BoxIndex d L) ℤ := fun row t => auxEntry p b pivot row t

/-- **Siegel's lemma for the auxiliary matrix.**  A wide integer system has a nonzero integer
solution of controlled height. -/
theorem exists_auxKernel (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d) (L S T : ℕ)
    (hlt : Fintype.card (RowIndex d S T) < Fintype.card (BoxIndex d L))
    (hpos : 0 < Fintype.card (RowIndex d S T)) :
    ∃ η : BoxIndex d L → ℤ, η ≠ 0 ∧ auxMatrix p b pivot L S T *ᵥ η = 0 ∧
      ‖η‖ ≤ ((Fintype.card (BoxIndex d L) : ℝ) * max 1 ‖auxMatrix p b pivot L S T‖)
        ^ ((Fintype.card (RowIndex d S T) : ℝ)
          / (Fintype.card (BoxIndex d L) - Fintype.card (RowIndex d S T))) :=
  Int.Matrix.exists_ne_zero_int_vec_norm_le _ hlt hpos

/-! ## From the kernel to vanishing component boxes -/

/-- The real weights attached to a sample: the `S`-unit values of the box frequencies. -/
def sampleWeight (p : Fin d → ℕ) {L : ℕ} (s : ℕ) (t : BoxIndex d L) : ℝ :=
  ((freqUnit p (boxNat t) s : ℕ) : ℝ)

theorem sampleWeight_nonneg (p : Fin d → ℕ) {L : ℕ} (s : ℕ) (t : BoxIndex d L) :
    0 ≤ sampleWeight p s t := by
  rw [sampleWeight]
  positivity

set_option maxHeartbeats 1000000 in
/-- **A kernel vector kills every component box inside the row range.** -/
theorem componentSum_eq_zero_of_auxKernel (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d)
    {L S T : ℕ} (η : BoxIndex d L → ℤ)
    (hker : auxMatrix p b pivot L S T *ᵥ η = 0) (s : Fin S) (ν : Fin d → ℕ)
    (hν : ∀ i, ν i < T) :
    componentSum b pivot (fun t : BoxIndex d L => boxExponent t) (fun t => ((η t : ℤ) : ℝ))
      (sampleWeight p (s : ℕ)) ν = 0 := by
  have hrow := congrFun hker (⟨s, fun i => ⟨ν i, hν i⟩⟩ : RowIndex d S T)
  have hcast : ((∑ t, auxEntry p b pivot (⟨s, fun i => ⟨ν i, hν i⟩⟩ : RowIndex d S T) t * η t
      : ℤ) : ℝ) = 0 := by
    have h : (∑ t, auxEntry p b pivot (⟨s, fun i => ⟨ν i, hν i⟩⟩ : RowIndex d S T) t * η t : ℤ)
        = 0 := by
      simpa [Matrix.mulVec, dotProduct, auxMatrix] using hrow
    rw [h]
    norm_num
  rw [componentSum]
  rw [← hcast, Int.cast_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [auxEntry, sampleWeight]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- **Layer C capstone.**  A Siegel kernel vector makes the `k`-th normalized frequency combination
of the auxiliary data small at every sample, with the residue proportional to the linear form.  For
a vanishing form this is the classical exact annihilation. -/
theorem abs_auxFrequencySum_le_of_kernel (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d)
    {L S T : ℕ} (η : BoxIndex d L → ℤ)
    (hker : auxMatrix p b pivot L S T *ᵥ η = 0) (s : Fin S) {k : ℕ} (hk : k < T) {M : ℝ}
    (h₁ : ∀ t : BoxIndex d L, |(b pivot : ℝ) * primeLogForm p (boxExponent t)| ≤ M)
    (h₂ : ∀ t : BoxIndex d L, |directionForm p b pivot (boxExponent t)| ≤ M) :
    |∑ t : BoxIndex d L, ((η t : ℤ) : ℝ)
        * ((b pivot : ℝ) * primeLogForm p (boxExponent t)) ^ k * sampleWeight p (s : ℕ) t|
      ≤ (k : ℝ) * M ^ (k - 1) * |primeLogForm p b|
        * ∑ t : BoxIndex d L, |((η t : ℤ) : ℝ)| * |((boxExponent t) pivot : ℝ)|
            * sampleWeight p (s : ℕ) t := by
  refine abs_pivotFrequencySum_le_of_components p b pivot
    (fun t : BoxIndex d L => boxExponent t) (fun t => ((η t : ℤ) : ℝ))
    (sampleWeight p (s : ℕ)) h₁ h₂ (sampleWeight_nonneg p (s : ℕ)) k ?_
  intro ν hν
  refine componentSum_eq_zero_of_auxKernel p b pivot η hker s ν ?_
  rw [Finset.mem_piAntidiag] at hν
  intro i
  by_cases hi : i = pivot
  · subst hi
    have hz : ν i = 0 := by
      by_contra hne
      have hmem := hν.2 i hne
      simp at hmem
    omega
  · have hmem : i ∈ Finset.univ.erase pivot := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
    have hle : ν i ≤ k := by
      rw [← hν.1]
      exact Finset.single_le_sum (f := ν) (fun j _ => Nat.zero_le _) hmem
    omega

end GaloisForLFunctions.RHTower.Matveev
