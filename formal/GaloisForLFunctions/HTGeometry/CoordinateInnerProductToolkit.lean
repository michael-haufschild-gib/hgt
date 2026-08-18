import GaloisForLFunctions.HTGeometry.SpectralGapQuadraticForm
import GaloisForLFunctions.HTGeometry.IncidenceLeakageDimensionLoss

/-!
# The coordinate inner product against Hilbert--Schmidt energy

Column-wise, the Hilbert--Schmidt energy of a matrix is the total coordinate square norm of its
columns, so a uniform bound on how much a matrix can shrink or stretch a vector is exactly a bound
on how it rescales Hilbert--Schmidt energy.  A Hermitian idempotent splits every square norm into
its captured and its complementary part, and a Hermitian family's quadratic Casimir has the total
family energy as its coordinate form.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The self inner product is the square norm. -/
theorem cinner_self_re (v : X → ℂ) : (cinner v v).re = cnormSq v := by
  rw [cinner_self, Complex.ofReal_re]

/-- The coordinate inner product is additive in its first slot. -/
theorem cinner_sub_left (u v w : X → ℂ) : cinner (u - v) w = cinner u w - cinner v w := by
  simp only [cinner, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.sub_apply, map_sub, sub_mul]

/-- The coordinate inner product is additive in its second slot. -/
theorem cinner_sub_right (u v w : X → ℂ) : cinner u (v - w) = cinner u v - cinner u w := by
  simp only [cinner, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.sub_apply, mul_sub]

/-- The coordinate inner product commutes with finite sums in its second slot. -/
theorem cinner_sum_right {J : Type*} [Fintype J] (u : X → ℂ) (f : J → X → ℂ) :
    cinner u (∑ j, f j) = ∑ j, cinner u (f j) := by
  have h : ∀ i : X, (starRingEnd ℂ) (u i) * ((∑ j, f j) i)
      = ∑ j, (starRingEnd ℂ) (u i) * f j i := by
    intro i
    rw [Finset.sum_apply, Finset.mul_sum]
  simp only [cinner]
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_comm]

/-- **Pythagoras for a Hermitian idempotent.**  The square norm splits into the captured part and
the part the projector discards. -/
theorem cnormSq_split_of_hermitian_idem {P : Matrix X X ℂ} (hP : Pᴴ = P) (hPP : P * P = P)
    (v : X → ℂ) : cnormSq v = cnormSq (P *ᵥ v) + cnormSq (v - P *ᵥ v) := by
  have hmove : cinner (P *ᵥ v) v = cinner v (P *ᵥ v) := by
    conv_lhs => rw [← hP]
    rw [← cinner_mulVec P v v]
  have hPv : P *ᵥ (P *ᵥ v) = P *ᵥ v := by rw [Matrix.mulVec_mulVec, hPP]
  have hidem : cinner (P *ᵥ v) (P *ᵥ v) = cinner v (P *ᵥ v) := by
    have h := cinner_mulVec P v (P *ᵥ v)
    rw [hPv, hP] at h
    exact h.symm
  have hexp : cinner (v - P *ᵥ v) (v - P *ᵥ v) = cinner v v - cinner v (P *ᵥ v) := by
    rw [cinner_sub_left, cinner_sub_right, cinner_sub_right, hmove, hidem]
    ring
  have h2 : ((cnormSq (v - P *ᵥ v) : ℝ) : ℂ)
      = ((cnormSq v : ℝ) : ℂ) - ((cnormSq (P *ᵥ v) : ℝ) : ℂ) := by
    rw [← cinner_self, hexp, cinner_self, ← hidem, cinner_self]
  have h3 : cnormSq (v - P *ᵥ v) = cnormSq v - cnormSq (P *ᵥ v) := by exact_mod_cast h2
  linarith

/-- A Hermitian idempotent is a contraction. -/
theorem cnormSq_mulVec_le_of_hermitian_idem {P : Matrix X X ℂ} (hP : Pᴴ = P) (hPP : P * P = P)
    (v : X → ℂ) : cnormSq (P *ᵥ v) ≤ cnormSq v := by
  have h := cnormSq_split_of_hermitian_idem hP hPP v
  have hnn := cnormSq_nonneg (v - P *ᵥ v)
  linarith

/-- Hilbert--Schmidt energy is the total square norm of the columns. -/
theorem hsSqRe_eq_sum_col (Y : Matrix X X ℂ) : hsSqRe Y = ∑ i, cnormSq (fun j => Y j i) := by
  rw [hsSqRe_eq_sum]
  rfl

/-- A column of a product is the matrix applied to the corresponding column. -/
theorem col_of_mul (M Y : Matrix X X ℂ) (i : X) :
    (fun j => (M * Y) j i) = M *ᵥ (fun j => Y j i) := by
  funext j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- **A vectorwise bound rescales Hilbert--Schmidt energy.**  Left multiplication by a matrix that
shrinks every vector by a factor shrinks the energy of every matrix by the same factor. -/
theorem hsSqRe_mul_le {c : ℝ} (M Y : Matrix X X ℂ)
    (h : ∀ v : X → ℂ, cnormSq (M *ᵥ v) ≤ c * cnormSq v) :
    hsSqRe (M * Y) ≤ c * hsSqRe Y := by
  rw [hsSqRe_eq_sum_col, hsSqRe_eq_sum_col, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [col_of_mul]
  exact h _

/-- **The quadratic Casimir carries the family energy.**  The coordinate form of the Casimir of a
Hermitian family at a vector is the total energy the family emits there. -/
theorem cinner_casimir_re {J : Type*} [Fintype J] (A : J → Matrix X X ℂ)
    (hsymm : ∀ j, (A j)ᴴ = A j) (v : X → ℂ) :
    (cinner v ((∑ j, A j * A j) *ᵥ v)).re = ∑ j, cnormSq (A j *ᵥ v) := by
  have hsplit : (∑ j, A j * A j) *ᵥ v = ∑ j, (A j * A j) *ᵥ v := by
    simp only [Matrix.sum_mulVec]
  have hterm : ∀ j : J, cinner v ((A j * A j) *ᵥ v) = ((cnormSq (A j *ᵥ v) : ℝ) : ℂ) := by
    intro j
    rw [← Matrix.mulVec_mulVec, cinner_mulVec, hsymm j, cinner_self]
  rw [hsplit, cinner_sum_right, Finset.sum_congr rfl fun j _ => hterm j, ← Complex.ofReal_sum,
    Complex.ofReal_re]

end

end GaloisForLFunctions.HTGeometry
