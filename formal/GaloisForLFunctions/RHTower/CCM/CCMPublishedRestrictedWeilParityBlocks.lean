import GaloisForLFunctions.RHTower.CCM.CCMPublishedRestrictedWeilMatrix
import GaloisForLFunctions.RHTower.CCM.CCMParityFreeOddGroundFourier

/-!
# Literal published restricted-Weil parity blocks

Rebuilds the exact finite published restricted-Weil packet in centered even/odd coordinates.
The parity frames are complete isometries; the scalar-shifted matrix splits into positive
semidefinite parity blocks; projected clock displacement gives the exact rank-one cross
commutator consumed by `CCMParityFreeOddGroundData`.

Every aperture has an unconditional positive-semidefinite singular spectral-floor shift. If its
full radical is a simple odd line, clock injectivity forces source visibility and the commutator
forces a nonzero normalization pairing. Thus the full finite odd-ground data are derived from the
literal published packet, with neither visibility nor normalization assumed.
-/

open Matrix Complex
open scoped Matrix ComplexOrder

namespace RHTower

noncomputable section

abbrev CCMCenteredParityIndex (N : ℕ) := Option (Fin N × Bool)
abbrev CCMEvenParityIndex (N : ℕ) := Option (Fin N)

def ccmParityFrameScale : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem ccmParityFrameScale_sq :
    ccmParityFrameScale * ccmParityFrameScale = (1 / 2 : ℂ) := by
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hsqrtC : ((Real.sqrt 2 : ℝ) : ℂ) * (Real.sqrt 2 : ℝ) = 2 := by
    exact_mod_cast hsqrt
  have hsqrt_ne : (Real.sqrt 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [ccmParityFrameScale]
  field_simp
  simpa only [pow_two] using hsqrtC.symm

@[simp] theorem star_ccmParityFrameScale : star ccmParityFrameScale = ccmParityFrameScale := by
  simp [ccmParityFrameScale]

def ccmEvenParityFrame (N : ℕ) :
    Matrix (CCMCenteredParityIndex N) (CCMEvenParityIndex N) ℂ
  | none, none => 1
  | some (k, _), some l => if k = l then ccmParityFrameScale else 0
  | _, _ => 0

def ccmOddParityFrame (N : ℕ) :
    Matrix (CCMCenteredParityIndex N) (Fin N) ℂ
  | none, _ => 0
  | some (k, false), l => if k = l then ccmParityFrameScale else 0
  | some (k, true), l => if k = l then -ccmParityFrameScale else 0

theorem ccmEvenParityFrame_orthonormal (N : ℕ) :
    (ccmEvenParityFrame N)ᴴ * ccmEvenParityFrame N = 1 := by
  ext i j
  rcases i with _ | i
  · rcases j with _ | j
    · simp [Matrix.mul_apply, ccmEvenParityFrame]
    · simp [Matrix.mul_apply, ccmEvenParityFrame]
  · rcases j with _ | j
    · simp [Matrix.mul_apply, ccmEvenParityFrame]
    · by_cases hij : i = j
      · subst j
        simp only [Matrix.mul_apply, ccmEvenParityFrame, Matrix.conjTranspose_apply,
          Fintype.sum_option]
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single i]
        · simp [ccmParityFrameScale_sq]
        · intro k _ hki
          simp [hki]
        · simp
      · simp only [Matrix.mul_apply, ccmEvenParityFrame, Matrix.conjTranspose_apply,
          Fintype.sum_option]
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single j]
        · simp [hij, Ne.symm hij]
        · intro k _ hkj
          simp [hkj]
        · simp

theorem ccmOddParityFrame_orthonormal (N : ℕ) :
    (ccmOddParityFrame N)ᴴ * ccmOddParityFrame N = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.mul_apply, ccmOddParityFrame, Matrix.conjTranspose_apply,
      Fintype.sum_option]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i]
    · rw [Fintype.sum_bool]
      simp [star_ccmParityFrameScale, ccmParityFrameScale_sq]
      norm_num
    · intro k _ hki
      simp [hki]
    · simp
  · simp only [Matrix.mul_apply, ccmOddParityFrame, Matrix.conjTranspose_apply,
      Fintype.sum_option]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single j]
    · rw [Fintype.sum_bool]
      simp [hij, Ne.symm hij]
    · intro k _ hkj
      simp [hkj]
    · simp

theorem ccmParityFrames_orthogonal (N : ℕ) :
    (ccmEvenParityFrame N)ᴴ * ccmOddParityFrame N = 0 := by
  ext i j
  rcases i with _ | i
  · simp [Matrix.mul_apply, ccmEvenParityFrame, ccmOddParityFrame]
  · by_cases hij : i = j
    · subst j
      simp only [Matrix.mul_apply, ccmEvenParityFrame, ccmOddParityFrame,
        Matrix.conjTranspose_apply, Fintype.sum_option]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single i]
      · simp [ccmParityFrameScale_sq]
      · intro k _ hki
        simp [hki]
      · simp
    · simp only [Matrix.mul_apply, ccmEvenParityFrame, ccmOddParityFrame,
        Matrix.conjTranspose_apply, Fintype.sum_option]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj
        simp [hkj]
      · simp

def ccmCenteredParityReflection (N : ℕ) :
    CCMCenteredParityIndex N ≃ CCMCenteredParityIndex N where
  toFun
    | none => none
    | some (k, b) => some (k, !b)
  invFun
    | none => none
    | some (k, b) => some (k, !b)
  left_inv i := by rcases i with _ | ⟨k, b⟩ <;> simp
  right_inv i := by rcases i with _ | ⟨k, b⟩ <;> simp

@[simp] theorem ccmCenteredParityReflection_involutive (N : ℕ)
    (i : CCMCenteredParityIndex N) :
    ccmCenteredParityReflection N (ccmCenteredParityReflection N i) = i := by
  rcases i with _ | ⟨k, b⟩ <;> simp [ccmCenteredParityReflection]

def ccmParityCenteredMode (N : ℕ) : CCMCenteredParityIndex N → ℤ
  | none => 0
  | some (k, false) => (k.1 + 1 : ℕ)
  | some (k, true) => -((k.1 + 1 : ℕ) : ℤ)

def ccmParityCenteredClock (N : ℕ) (i : CCMCenteredParityIndex N) : ℝ :=
  ccmParityCenteredMode N i

def ccmParityCenteredFrequency (a : ℝ) (N : ℕ)
    (i : CCMCenteredParityIndex N) : ℝ :=
  Real.pi * ccmParityCenteredClock N i / a

def ccmPublishedParitySource (a : ℝ) (N : ℕ)
    (i : CCMCenteredParityIndex N) : ℝ :=
  -(1 / Real.pi) * ccmPublishedRestrictedWeilPairing a
    (fun h => Real.sin (ccmParityCenteredFrequency a N i * h))

def ccmPublishedParityDiagonal (a : ℝ) (N : ℕ)
    (i : CCMCenteredParityIndex N) : ℝ :=
  ccmPublishedRestrictedWeilPairing a
    (fun h => 2 * (1 - h / (2 * a)) *
      Real.cos (ccmParityCenteredFrequency a N i * h))

def ccmPublishedParityWeilMatrix (a : ℝ) (N : ℕ) :
    Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℝ :=
  ccmDividedDifferenceMatrix (ccmParityCenteredClock N)
    (ccmPublishedParitySource a N) (ccmPublishedParityDiagonal a N)

theorem ccmParityCenteredMode_reflection (N : ℕ)
    (i : CCMCenteredParityIndex N) :
    ccmParityCenteredMode N (ccmCenteredParityReflection N i) =
      -ccmParityCenteredMode N i := by
  rcases i with _ | ⟨k, b⟩
  · simp [ccmParityCenteredMode, ccmCenteredParityReflection]
  · cases b <;> simp [ccmParityCenteredMode, ccmCenteredParityReflection]

theorem ccmParityCenteredClock_reflection (N : ℕ)
    (i : CCMCenteredParityIndex N) :
    ccmParityCenteredClock N (ccmCenteredParityReflection N i) =
      -ccmParityCenteredClock N i := by
  rw [ccmParityCenteredClock, ccmParityCenteredClock,
    ccmParityCenteredMode_reflection]
  exact_mod_cast rfl

theorem ccmParityCenteredClock_injective (N : ℕ) :
    Function.Injective (ccmParityCenteredClock N) := by
  intro i j hij
  unfold ccmParityCenteredClock at hij
  have hmode : ccmParityCenteredMode N i = ccmParityCenteredMode N j := by
    exact_mod_cast hij
  rcases i with _ | ⟨i, bi⟩
  · rcases j with _ | ⟨j, bj⟩
    · rfl
    · cases bj <;> simp [ccmParityCenteredMode] at hmode <;> omega
  · rcases j with _ | ⟨j, bj⟩
    · cases bi <;> simp [ccmParityCenteredMode] at hmode <;> omega
    · cases bi <;> cases bj
      · have hijFin : i = j := by
          apply Fin.ext
          simp [ccmParityCenteredMode] at hmode
          omega
        subst j
        rfl
      · simp [ccmParityCenteredMode] at hmode
        omega
      · simp [ccmParityCenteredMode] at hmode
        omega
      · have hijFin : i = j := by
          apply Fin.ext
          simp [ccmParityCenteredMode] at hmode
          omega
        subst j
        rfl

theorem ccmParityCenteredFrequency_reflection (a : ℝ) (N : ℕ)
    (i : CCMCenteredParityIndex N) :
    ccmParityCenteredFrequency a N (ccmCenteredParityReflection N i) =
      -ccmParityCenteredFrequency a N i := by
  rw [ccmParityCenteredFrequency, ccmParityCenteredFrequency,
    ccmParityCenteredClock_reflection]
  ring

theorem ccmPublishedParitySource_reflection (a : ℝ) (N : ℕ)
    (i : CCMCenteredParityIndex N) :
    ccmPublishedParitySource a N (ccmCenteredParityReflection N i) =
      -ccmPublishedParitySource a N i := by
  unfold ccmPublishedParitySource
  rw [ccmParityCenteredFrequency_reflection]
  have hsin :
      (fun h : ℝ => Real.sin (-ccmParityCenteredFrequency a N i * h)) =
        fun h : ℝ => -Real.sin (ccmParityCenteredFrequency a N i * h) := by
    funext h
    rw [neg_mul, Real.sin_neg]
  rw [hsin, ccmPublishedRestrictedWeilPairing_neg]
  ring

theorem ccmPublishedParityDiagonal_reflection (a : ℝ) (N : ℕ)
    (i : CCMCenteredParityIndex N) :
    ccmPublishedParityDiagonal a N (ccmCenteredParityReflection N i) =
      ccmPublishedParityDiagonal a N i := by
  rw [ccmPublishedParityDiagonal, ccmParityCenteredFrequency_reflection]
  congr 1
  funext h
  rw [neg_mul, Real.cos_neg]

theorem ccmPublishedParityWeilMatrix_displacement (a : ℝ) (N : ℕ) :
    ccmDiagonalClock (ccmParityCenteredClock N) *
          ccmPublishedParityWeilMatrix a N -
        ccmPublishedParityWeilMatrix a N *
          ccmDiagonalClock (ccmParityCenteredClock N) =
      Matrix.vecMulVec (ccmPublishedParitySource a N) ccmConstantBoundary -
        Matrix.vecMulVec ccmConstantBoundary (ccmPublishedParitySource a N) := by
  exact ccmDividedDifference_displacement _ _ _
    (ccmParityCenteredClock_injective N)

def ccmParityReflectionMatrix (N : ℕ) :
    Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ :=
  (ccmReflectionMatrix (ccmCenteredParityReflection N)).map (algebraMap ℝ ℂ)

theorem ccmParityReflectionMatrix_mul_apply (N : ℕ)
    {m : Type*} [Fintype m]
    (M : Matrix (CCMCenteredParityIndex N) m ℂ)
    (i : CCMCenteredParityIndex N) (j : m) :
    (ccmParityReflectionMatrix N * M) i j =
      M (ccmCenteredParityReflection N i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (ccmCenteredParityReflection N i)]
  · simp [ccmParityReflectionMatrix, ccmReflectionMatrix]
  · intro b _ hne
    simp [ccmParityReflectionMatrix, ccmReflectionMatrix, hne]
  · simp

theorem ccm_mul_parityReflectionMatrix_apply (N : ℕ)
    {m : Type*} [Fintype m]
    (M : Matrix m (CCMCenteredParityIndex N) ℂ)
    (i : m) (j : CCMCenteredParityIndex N) :
    (M * ccmParityReflectionMatrix N) i j =
      M i (ccmCenteredParityReflection N j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (ccmCenteredParityReflection N j)]
  · simp [ccmParityReflectionMatrix, ccmReflectionMatrix]
  · intro b _ hne
    have hne' : j ≠ ccmCenteredParityReflection N b := by
      intro h
      have hr := congrArg (ccmCenteredParityReflection N) h
      exact hne (by simpa using hr.symm)
    simp [ccmParityReflectionMatrix, ccmReflectionMatrix, hne']
  · simp

theorem ccmParityReflectionMatrix_isHermitian (N : ℕ) :
    (ccmParityReflectionMatrix N).IsHermitian := by
  show (ccmParityReflectionMatrix N)ᴴ = ccmParityReflectionMatrix N
  ext i j
  simp only [Matrix.conjTranspose_apply, ccmParityReflectionMatrix,
    Matrix.map_apply, ccmReflectionMatrix]
  by_cases h : i = ccmCenteredParityReflection N j
  · have h' : j = ccmCenteredParityReflection N i :=
      (ccm_eq_reflection_iff (ccmCenteredParityReflection N)
        (ccmCenteredParityReflection_involutive N) i j).1 h
    rw [if_pos h, if_pos h']
    norm_num
  · have h' : j ≠ ccmCenteredParityReflection N i := fun h' =>
      h ((ccm_eq_reflection_iff (ccmCenteredParityReflection N)
        (ccmCenteredParityReflection_involutive N) i j).2 h')
    rw [if_neg h, if_neg h']
    norm_num

theorem ccmParityReflectionMatrix_sq (N : ℕ) :
    ccmParityReflectionMatrix N * ccmParityReflectionMatrix N = 1 := by
  ext i j
  rw [ccmParityReflectionMatrix_mul_apply]
  by_cases hij : i = j
  · subst j
    simp [ccmParityReflectionMatrix, ccmReflectionMatrix]
  · simp [ccmParityReflectionMatrix, ccmReflectionMatrix, hij, Ne.symm hij]

theorem ccmParityReflectionMatrix_mul_evenFrame (N : ℕ) :
    ccmParityReflectionMatrix N * ccmEvenParityFrame N = ccmEvenParityFrame N := by
  ext i j
  rw [ccmParityReflectionMatrix_mul_apply]
  rcases i with _ | ⟨i, b⟩ <;> rcases j with _ | j
  · rfl
  · rfl
  · cases b <;> rfl
  · cases b <;> simp [ccmCenteredParityReflection, ccmEvenParityFrame]

theorem ccmParityReflectionMatrix_mul_oddFrame (N : ℕ) :
    ccmParityReflectionMatrix N * ccmOddParityFrame N = -ccmOddParityFrame N := by
  ext i j
  rw [ccmParityReflectionMatrix_mul_apply]
  rcases i with _ | ⟨i, b⟩
  · simp [ccmCenteredParityReflection, ccmOddParityFrame]
  · cases b <;> by_cases hij : i = j <;>
      simp [ccmCenteredParityReflection, ccmOddParityFrame, hij]

theorem ccmParityFrames_complete (N : ℕ) :
    ccmEvenParityFrame N * (ccmEvenParityFrame N)ᴴ +
        ccmOddParityFrame N * (ccmOddParityFrame N)ᴴ = 1 := by
  ext i j
  rcases i with _ | ⟨i, bi⟩
  · rcases j with _ | ⟨j, bj⟩
    · simp [Matrix.mul_apply, ccmEvenParityFrame, ccmOddParityFrame]
    · simp [Matrix.mul_apply, ccmEvenParityFrame, ccmOddParityFrame]
  · rcases j with _ | ⟨j, bj⟩
    · simp [Matrix.mul_apply, ccmEvenParityFrame, ccmOddParityFrame]
    · by_cases hij : i = j
      · subst j
        cases bi <;> cases bj <;>
          simp [Matrix.mul_apply, ccmEvenParityFrame, ccmOddParityFrame]
        all_goals
          rw [show (starRingEnd ℂ) ccmParityFrameScale = ccmParityFrameScale from
            star_ccmParityFrameScale, ccmParityFrameScale_sq]
          norm_num
      · cases bi <;> cases bj <;>
          simp [Matrix.mul_apply, ccmEvenParityFrame, ccmOddParityFrame,
            hij, Ne.symm hij]

theorem ccmParityFrames_reconstruct (N : ℕ) {m : Type*} [Fintype m]
    (A : Matrix (CCMCenteredParityIndex N) m ℂ) :
    A = ccmEvenParityFrame N * ((ccmEvenParityFrame N)ᴴ * A) +
      ccmOddParityFrame N * ((ccmOddParityFrame N)ᴴ * A) := by
  calc
    A = (1 : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ) * A := by
      rw [Matrix.one_mul]
    _ = (ccmEvenParityFrame N * (ccmEvenParityFrame N)ᴴ +
          ccmOddParityFrame N * (ccmOddParityFrame N)ᴴ) * A := by
      rw [ccmParityFrames_complete]
    _ = ccmEvenParityFrame N * ((ccmEvenParityFrame N)ᴴ * A) +
        ccmOddParityFrame N * ((ccmOddParityFrame N)ᴴ * A) := by
      rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]

theorem ccmEvenFrame_conjTranspose_mul_eq_zero_of_odd
    (N : ℕ) {m : Type*} [Fintype m]
    (A : Matrix (CCMCenteredParityIndex N) m ℂ)
    (hA : ccmParityReflectionMatrix N * A = -A) :
    (ccmEvenParityFrame N)ᴴ * A = 0 := by
  have hER : (ccmEvenParityFrame N)ᴴ * ccmParityReflectionMatrix N =
      (ccmEvenParityFrame N)ᴴ := by
    have h := congrArg Matrix.conjTranspose
      (ccmParityReflectionMatrix_mul_evenFrame N)
    simpa [Matrix.conjTranspose_mul,
      (ccmParityReflectionMatrix_isHermitian N).eq] using h
  have hx : (ccmEvenParityFrame N)ᴴ * A =
      -((ccmEvenParityFrame N)ᴴ * A) := by
    calc
      (ccmEvenParityFrame N)ᴴ * A =
          ((ccmEvenParityFrame N)ᴴ * ccmParityReflectionMatrix N) * A := by
            rw [hER]
      _ = (ccmEvenParityFrame N)ᴴ *
          (ccmParityReflectionMatrix N * A) := by
            rw [Matrix.mul_assoc]
      _ = -((ccmEvenParityFrame N)ᴴ * A) := by rw [hA]; simp
  ext i j
  have hij := congr_fun (congr_fun hx i) j
  simp only [Matrix.neg_apply] at hij
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hij)

theorem ccmOddFrame_conjTranspose_mul_eq_zero_of_even
    (N : ℕ) {m : Type*} [Fintype m]
    (A : Matrix (CCMCenteredParityIndex N) m ℂ)
    (hA : ccmParityReflectionMatrix N * A = A) :
    (ccmOddParityFrame N)ᴴ * A = 0 := by
  have hOR : (ccmOddParityFrame N)ᴴ * ccmParityReflectionMatrix N =
      -(ccmOddParityFrame N)ᴴ := by
    have h := congrArg Matrix.conjTranspose
      (ccmParityReflectionMatrix_mul_oddFrame N)
    simpa [Matrix.conjTranspose_mul,
      (ccmParityReflectionMatrix_isHermitian N).eq] using h
  have hx : (ccmOddParityFrame N)ᴴ * A =
      -((ccmOddParityFrame N)ᴴ * A) := by
    calc
      (ccmOddParityFrame N)ᴴ * A =
          -((ccmOddParityFrame N)ᴴ * ccmParityReflectionMatrix N) * A := by
            rw [hOR]
            simp
      _ = -((ccmOddParityFrame N)ᴴ *
          (ccmParityReflectionMatrix N * A)) := by
            simp [Matrix.mul_assoc]
      _ = -((ccmOddParityFrame N)ᴴ * A) := by rw [hA]
  ext i j
  have hij := congr_fun (congr_fun hx i) j
  simp only [Matrix.neg_apply] at hij
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hij)

def ccmPublishedParityShift (a mu : ℝ) (N : ℕ) :
    Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ :=
  (ccmScalarShift (ccmPublishedParityWeilMatrix a N) mu).map (algebraMap ℝ ℂ)

def ccmParityClockMatrix (N : ℕ) :
    Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ :=
  (ccmDiagonalClock (ccmParityCenteredClock N)).map (algebraMap ℝ ℂ)

def ccmPublishedParityEvenBlock (a mu : ℝ) (N : ℕ) :
    Matrix (CCMEvenParityIndex N) (CCMEvenParityIndex N) ℂ :=
  (ccmEvenParityFrame N)ᴴ * ccmPublishedParityShift a mu N * ccmEvenParityFrame N

def ccmPublishedParityOddBlock (a mu : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (ccmOddParityFrame N)ᴴ * ccmPublishedParityShift a mu N * ccmOddParityFrame N

def ccmPublishedParityCrossFrequency (N : ℕ) :
    Matrix (CCMEvenParityIndex N) (Fin N) ℂ :=
  (ccmEvenParityFrame N)ᴴ * ccmParityClockMatrix N * ccmOddParityFrame N

def ccmPublishedParityEta (N : ℕ) : CCMEvenParityIndex N → ℂ :=
  (ccmEvenParityFrame N)ᴴ *ᵥ (fun _ => 1)

def ccmPublishedParityBeta (a : ℝ) (N : ℕ) : Fin N → ℂ :=
  (ccmOddParityFrame N)ᴴ *ᵥ
    (fun i => (ccmPublishedParitySource a N i : ℂ))

theorem ccmPublishedParityShift_commutes_reflection (a mu : ℝ) (N : ℕ) :
    ccmPublishedParityShift a mu N * ccmParityReflectionMatrix N =
      ccmParityReflectionMatrix N * ccmPublishedParityShift a mu N := by
  have hQ : ccmPublishedParityWeilMatrix a N *
        ccmReflectionMatrix (ccmCenteredParityReflection N) =
      ccmReflectionMatrix (ccmCenteredParityReflection N) *
        ccmPublishedParityWeilMatrix a N := by
    apply ccmReflectionMatrix_commutes_dividedDifference
    · exact ccmCenteredParityReflection_involutive N
    · exact ccmParityCenteredClock_reflection N
    · exact ccmPublishedParitySource_reflection a N
    · exact ccmPublishedParityDiagonal_reflection a N
  have hshift := ccmScalarShift_commutes
    (ccmPublishedParityWeilMatrix a N)
    (ccmReflectionMatrix (ccmCenteredParityReflection N)) mu hQ
  have hmap := congrArg (fun M => M.map (algebraMap ℝ ℂ)) hshift
  simpa only [ccmPublishedParityShift, ccmParityReflectionMatrix,
    ← Matrix.map_mul] using hmap

theorem ccmParityClockMatrix_anticommutes_reflection (N : ℕ) :
    ccmParityClockMatrix N * ccmParityReflectionMatrix N =
      -(ccmParityReflectionMatrix N * ccmParityClockMatrix N) := by
  ext i j
  rw [ccm_mul_parityReflectionMatrix_apply, Matrix.neg_apply,
    ccmParityReflectionMatrix_mul_apply]
  by_cases hji : j = ccmCenteredParityReflection N i
  · subst j
    simp [ccmParityClockMatrix, ccmDiagonalClock, Matrix.diagonal,
      ccmParityCenteredClock_reflection]
  · have hij : i ≠ ccmCenteredParityReflection N j := by
      intro h
      apply hji
      have hr := congrArg (ccmCenteredParityReflection N) h
      simpa using hr.symm
    have hrij : ccmCenteredParityReflection N i ≠ j := Ne.symm hji
    simp [ccmParityClockMatrix, ccmDiagonalClock, Matrix.diagonal, hij, hrij]

theorem ccmPublishedParityShift_mul_evenFrame (a mu : ℝ) (N : ℕ) :
    ccmPublishedParityShift a mu N * ccmEvenParityFrame N =
      ccmEvenParityFrame N * ccmPublishedParityEvenBlock a mu N := by
  let Q := ccmPublishedParityShift a mu N
  let E := ccmEvenParityFrame N
  let O := ccmOddParityFrame N
  have hQE : ccmParityReflectionMatrix N * (Q * E) = Q * E := by
    calc
      ccmParityReflectionMatrix N * (Q * E) =
          (ccmParityReflectionMatrix N * Q) * E := by rw [Matrix.mul_assoc]
      _ = (Q * ccmParityReflectionMatrix N) * E := by
        rw [ccmPublishedParityShift_commutes_reflection a mu N]
      _ = Q * (ccmParityReflectionMatrix N * E) := by rw [Matrix.mul_assoc]
      _ = Q * E := by rw [ccmParityReflectionMatrix_mul_evenFrame]
  have hcross : Oᴴ * (Q * E) = 0 :=
    ccmOddFrame_conjTranspose_mul_eq_zero_of_even N (Q * E) hQE
  calc
    Q * E = E * (Eᴴ * (Q * E)) + O * (Oᴴ * (Q * E)) :=
      ccmParityFrames_reconstruct N (Q * E)
    _ = E * (Eᴴ * Q * E) + O * (Oᴴ * (Q * E)) := by
      simp only [Matrix.mul_assoc]
    _ = E * ccmPublishedParityEvenBlock a mu N := by
      rw [hcross]
      simp [ccmPublishedParityEvenBlock, Q, E, O, Matrix.mul_assoc]

theorem ccmPublishedParityShift_mul_oddFrame (a mu : ℝ) (N : ℕ) :
    ccmPublishedParityShift a mu N * ccmOddParityFrame N =
      ccmOddParityFrame N * ccmPublishedParityOddBlock a mu N := by
  let Q := ccmPublishedParityShift a mu N
  let E := ccmEvenParityFrame N
  let O := ccmOddParityFrame N
  have hQO : ccmParityReflectionMatrix N * (Q * O) = -(Q * O) := by
    calc
      ccmParityReflectionMatrix N * (Q * O) =
          (ccmParityReflectionMatrix N * Q) * O := by rw [Matrix.mul_assoc]
      _ = (Q * ccmParityReflectionMatrix N) * O := by
        rw [ccmPublishedParityShift_commutes_reflection a mu N]
      _ = Q * (ccmParityReflectionMatrix N * O) := by rw [Matrix.mul_assoc]
      _ = -(Q * O) := by
        rw [ccmParityReflectionMatrix_mul_oddFrame]
        simp only [Matrix.mul_neg]
        simp only [O]
  have hcross : Eᴴ * (Q * O) = 0 :=
    ccmEvenFrame_conjTranspose_mul_eq_zero_of_odd N (Q * O) hQO
  calc
    Q * O = E * (Eᴴ * (Q * O)) + O * (Oᴴ * (Q * O)) :=
      ccmParityFrames_reconstruct N (Q * O)
    _ = E * (Eᴴ * (Q * O)) + O * (Oᴴ * Q * O) := by
      simp only [Matrix.mul_assoc]
    _ = O * ccmPublishedParityOddBlock a mu N := by
      rw [hcross]
      simp [ccmPublishedParityOddBlock, Q, E, O, Matrix.mul_assoc]

theorem ccmParityClockMatrix_mul_oddFrame (N : ℕ) :
    ccmParityClockMatrix N * ccmOddParityFrame N =
      ccmEvenParityFrame N * ccmPublishedParityCrossFrequency N := by
  let D := ccmParityClockMatrix N
  let E := ccmEvenParityFrame N
  let O := ccmOddParityFrame N
  have hanti : ccmParityReflectionMatrix N * D =
      -(D * ccmParityReflectionMatrix N) := by
    have h := ccmParityClockMatrix_anticommutes_reflection N
    have hn := congrArg Neg.neg h
    simpa [D] using hn.symm
  have hDO : ccmParityReflectionMatrix N * (D * O) = D * O := by
    calc
      ccmParityReflectionMatrix N * (D * O) =
          (ccmParityReflectionMatrix N * D) * O := by rw [Matrix.mul_assoc]
      _ = -(D * ccmParityReflectionMatrix N) * O := by rw [hanti]
      _ = -(D * (ccmParityReflectionMatrix N * O)) := by
        simp [Matrix.mul_assoc]
      _ = D * O := by
        rw [ccmParityReflectionMatrix_mul_oddFrame]
        simp only [Matrix.mul_neg, neg_neg]
        simp only [O]
  have hcross : Oᴴ * (D * O) = 0 :=
    ccmOddFrame_conjTranspose_mul_eq_zero_of_even N (D * O) hDO
  calc
    D * O = E * (Eᴴ * (D * O)) + O * (Oᴴ * (D * O)) :=
      ccmParityFrames_reconstruct N (D * O)
    _ = E * (Eᴴ * D * O) + O * (Oᴴ * (D * O)) := by
      simp only [Matrix.mul_assoc]
    _ = E * ccmPublishedParityCrossFrequency N := by
      rw [hcross]
      simp [ccmPublishedParityCrossFrequency, D, E, O, Matrix.mul_assoc]

def ccmPublishedParityEtaFull (N : ℕ) : CCMCenteredParityIndex N → ℂ :=
  fun _ => 1

def ccmPublishedParityBetaFull (a : ℝ) (N : ℕ) :
    CCMCenteredParityIndex N → ℂ :=
  fun i => (ccmPublishedParitySource a N i : ℂ)

theorem ccmParityReflectionMatrix_mulVec_apply (N : ℕ)
    (v : CCMCenteredParityIndex N → ℂ) (i : CCMCenteredParityIndex N) :
    (ccmParityReflectionMatrix N *ᵥ v) i =
      v (ccmCenteredParityReflection N i) := by
  rw [Matrix.mulVec, dotProduct,
    Finset.sum_eq_single (ccmCenteredParityReflection N i)]
  · simp [ccmParityReflectionMatrix, ccmReflectionMatrix]
  · intro b _ hne
    simp [ccmParityReflectionMatrix, ccmReflectionMatrix, hne]
  · simp

theorem ccmPublishedParityEtaFull_even (N : ℕ) :
    ccmParityReflectionMatrix N *ᵥ ccmPublishedParityEtaFull N =
      ccmPublishedParityEtaFull N := by
  funext i
  rw [ccmParityReflectionMatrix_mulVec_apply]
  rfl

theorem ccmPublishedParityBetaFull_odd (a : ℝ) (N : ℕ) :
    ccmParityReflectionMatrix N *ᵥ ccmPublishedParityBetaFull a N =
      -ccmPublishedParityBetaFull a N := by
  funext i
  rw [ccmParityReflectionMatrix_mulVec_apply]
  simp only [ccmPublishedParityBetaFull, Pi.neg_apply]
  exact_mod_cast ccmPublishedParitySource_reflection a N i

theorem ccmEvenFrame_conjTranspose_mulVec_eq_zero_of_odd
    (N : ℕ) (v : CCMCenteredParityIndex N → ℂ)
    (hv : ccmParityReflectionMatrix N *ᵥ v = -v) :
    (ccmEvenParityFrame N)ᴴ *ᵥ v = 0 := by
  have hER : (ccmEvenParityFrame N)ᴴ * ccmParityReflectionMatrix N =
      (ccmEvenParityFrame N)ᴴ := by
    have h := congrArg Matrix.conjTranspose
      (ccmParityReflectionMatrix_mul_evenFrame N)
    simpa [Matrix.conjTranspose_mul,
      (ccmParityReflectionMatrix_isHermitian N).eq] using h
  have hx : (ccmEvenParityFrame N)ᴴ *ᵥ v =
      -((ccmEvenParityFrame N)ᴴ *ᵥ v) := by
    calc
      (ccmEvenParityFrame N)ᴴ *ᵥ v =
          ((ccmEvenParityFrame N)ᴴ * ccmParityReflectionMatrix N) *ᵥ v := by
            rw [hER]
      _ = (ccmEvenParityFrame N)ᴴ *ᵥ
          (ccmParityReflectionMatrix N *ᵥ v) := by
            rw [Matrix.mulVec_mulVec]
      _ = -((ccmEvenParityFrame N)ᴴ *ᵥ v) := by
        rw [hv, Matrix.mulVec_neg]
  funext i
  have hi := congr_fun hx i
  simp only [Pi.neg_apply] at hi
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hi)

theorem ccmOddFrame_conjTranspose_mulVec_eq_zero_of_even
    (N : ℕ) (v : CCMCenteredParityIndex N → ℂ)
    (hv : ccmParityReflectionMatrix N *ᵥ v = v) :
    (ccmOddParityFrame N)ᴴ *ᵥ v = 0 := by
  have hOR : (ccmOddParityFrame N)ᴴ * ccmParityReflectionMatrix N =
      -(ccmOddParityFrame N)ᴴ := by
    have h := congrArg Matrix.conjTranspose
      (ccmParityReflectionMatrix_mul_oddFrame N)
    simpa [Matrix.conjTranspose_mul,
      (ccmParityReflectionMatrix_isHermitian N).eq] using h
  have hx : (ccmOddParityFrame N)ᴴ *ᵥ v =
      -((ccmOddParityFrame N)ᴴ *ᵥ v) := by
    calc
      (ccmOddParityFrame N)ᴴ *ᵥ v =
          -(-((ccmOddParityFrame N)ᴴ *ᵥ v)) := by simp
      _ = -((-(ccmOddParityFrame N)ᴴ) *ᵥ v) := by
        rw [Matrix.neg_mulVec]
      _ = -(((ccmOddParityFrame N)ᴴ * ccmParityReflectionMatrix N) *ᵥ v) := by
        rw [hOR]
      _ = -((ccmOddParityFrame N)ᴴ *ᵥ
          (ccmParityReflectionMatrix N *ᵥ v)) := by
        exact congrArg Neg.neg
          (Matrix.mulVec_mulVec v (ccmOddParityFrame N)ᴴ
            (ccmParityReflectionMatrix N)).symm
      _ = -((ccmOddParityFrame N)ᴴ *ᵥ v) := by rw [hv]
  funext i
  have hi := congr_fun hx i
  simp only [Pi.neg_apply] at hi
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hi)

theorem ccmParityFrames_mulVec_reconstruct (N : ℕ)
    (v : CCMCenteredParityIndex N → ℂ) :
    v = ccmEvenParityFrame N *ᵥ ((ccmEvenParityFrame N)ᴴ *ᵥ v) +
      ccmOddParityFrame N *ᵥ ((ccmOddParityFrame N)ᴴ *ᵥ v) := by
  calc
    v = (1 : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ) *ᵥ v := by
      simp
    _ = (ccmEvenParityFrame N * (ccmEvenParityFrame N)ᴴ +
          ccmOddParityFrame N * (ccmOddParityFrame N)ᴴ) *ᵥ v := by
      rw [ccmParityFrames_complete]
    _ = ccmEvenParityFrame N *ᵥ ((ccmEvenParityFrame N)ᴴ *ᵥ v) +
        ccmOddParityFrame N *ᵥ ((ccmOddParityFrame N)ᴴ *ᵥ v) := by
      rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem ccmPublishedParityEta_reconstruct (N : ℕ) :
    ccmEvenParityFrame N *ᵥ ccmPublishedParityEta N =
      ccmPublishedParityEtaFull N := by
  have hzero : (ccmOddParityFrame N)ᴴ *ᵥ ccmPublishedParityEtaFull N = 0 :=
    ccmOddFrame_conjTranspose_mulVec_eq_zero_of_even N _
      (ccmPublishedParityEtaFull_even N)
  have h := ccmParityFrames_mulVec_reconstruct N (ccmPublishedParityEtaFull N)
  rw [hzero] at h
  simp only [Matrix.mulVec_zero, add_zero] at h
  change ccmEvenParityFrame N *ᵥ
      ((ccmEvenParityFrame N)ᴴ *ᵥ ccmPublishedParityEtaFull N) =
    ccmPublishedParityEtaFull N
  exact h.symm

theorem ccmPublishedParityBeta_reconstruct (a : ℝ) (N : ℕ) :
    ccmOddParityFrame N *ᵥ ccmPublishedParityBeta a N =
      ccmPublishedParityBetaFull a N := by
  have hzero : (ccmEvenParityFrame N)ᴴ *ᵥ ccmPublishedParityBetaFull a N = 0 :=
    ccmEvenFrame_conjTranspose_mulVec_eq_zero_of_odd N _
      (ccmPublishedParityBetaFull_odd a N)
  have h := ccmParityFrames_mulVec_reconstruct N
    (ccmPublishedParityBetaFull a N)
  rw [hzero] at h
  simp only [Matrix.mulVec_zero, zero_add] at h
  change ccmOddParityFrame N *ᵥ
      ((ccmOddParityFrame N)ᴴ *ᵥ ccmPublishedParityBetaFull a N) =
    ccmPublishedParityBetaFull a N
  exact h.symm

theorem ccmPublishedParityShift_displacement (a mu : ℝ) (N : ℕ) :
    ccmParityClockMatrix N * ccmPublishedParityShift a mu N -
        ccmPublishedParityShift a mu N * ccmParityClockMatrix N =
      Matrix.vecMulVec (ccmPublishedParityBetaFull a N)
          (star (ccmPublishedParityEtaFull N)) -
        Matrix.vecMulVec (ccmPublishedParityEtaFull N)
          (star (ccmPublishedParityBetaFull a N)) := by
  let Q := ccmPublishedParityWeilMatrix a N
  let D := ccmDiagonalClock (ccmParityCenteredClock N)
  let R := Matrix.vecMulVec (ccmPublishedParitySource a N) ccmConstantBoundary -
    Matrix.vecMulVec ccmConstantBoundary (ccmPublishedParitySource a N)
  have hreal := ccmScalarShift_displacement Q D R mu
    (ccmPublishedParityWeilMatrix_displacement a N)
  have hmap := congrArg (fun M : Matrix (CCMCenteredParityIndex N)
      (CCMCenteredParityIndex N) ℝ => M.map (algebraMap ℝ ℂ)) hreal
  have hRmap : R.map (algebraMap ℝ ℂ) =
      Matrix.vecMulVec (ccmPublishedParityBetaFull a N)
          (star (ccmPublishedParityEtaFull N)) -
        Matrix.vecMulVec (ccmPublishedParityEtaFull N)
          (star (ccmPublishedParityBetaFull a N)) := by
    ext i j
    simp [R, Matrix.vecMulVec_apply, ccmConstantBoundary,
      ccmPublishedParityEtaFull, ccmPublishedParityBetaFull]
  change (D * ccmScalarShift Q mu - ccmScalarShift Q mu * D).map
      (algebraMap ℝ ℂ) = R.map (algebraMap ℝ ℂ) at hmap
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, hRmap] at hmap
  simpa only [ccmParityClockMatrix, ccmPublishedParityShift, D, Q] using hmap

theorem ccmPublishedParityEvenBlock_posSemidef
    (a mu : ℝ) (N : ℕ)
    (hT : (ccmPublishedParityShift a mu N).PosSemidef) :
    (ccmPublishedParityEvenBlock a mu N).PosSemidef := by
  simpa only [ccmPublishedParityEvenBlock] using
    hT.conjTranspose_mul_mul_same (ccmEvenParityFrame N)

theorem ccmPublishedParityOddBlock_posSemidef
    (a mu : ℝ) (N : ℕ)
    (hT : (ccmPublishedParityShift a mu N).PosSemidef) :
    (ccmPublishedParityOddBlock a mu N).PosSemidef := by
  simpa only [ccmPublishedParityOddBlock] using
    hT.conjTranspose_mul_mul_same (ccmOddParityFrame N)

theorem star_ccmPublishedParityBetaFull_vecMul_oddFrame
    (a : ℝ) (N : ℕ) :
    star (ccmPublishedParityBetaFull a N) ᵥ* ccmOddParityFrame N =
      star (ccmPublishedParityBeta a N) := by
  have h := Matrix.star_mulVec (ccmOddParityFrame N)ᴴ
    (ccmPublishedParityBetaFull a N)
  change star (ccmPublishedParityBetaFull a N) ᵥ* ccmOddParityFrame N =
    star ((ccmOddParityFrame N)ᴴ *ᵥ ccmPublishedParityBetaFull a N)
  simpa only [Matrix.conjTranspose_conjTranspose] using h.symm

theorem star_ccmPublishedParityEtaFull_vecMul_oddFrame (N : ℕ) :
    star (ccmPublishedParityEtaFull N) ᵥ* ccmOddParityFrame N = 0 := by
  have hzero : (ccmOddParityFrame N)ᴴ *ᵥ ccmPublishedParityEtaFull N = 0 :=
    ccmOddFrame_conjTranspose_mulVec_eq_zero_of_even N _
      (ccmPublishedParityEtaFull_even N)
  have h := Matrix.star_mulVec (ccmOddParityFrame N)ᴴ
    (ccmPublishedParityEtaFull N)
  rw [hzero] at h
  simpa [Matrix.conjTranspose_conjTranspose] using h.symm

theorem ccmPublishedParityEvenFrame_conjTranspose_mulVec_etaFull (N : ℕ) :
    (ccmEvenParityFrame N)ᴴ *ᵥ ccmPublishedParityEtaFull N =
      ccmPublishedParityEta N := by
  rfl

theorem ccmPublishedParityEvenFrame_conjTranspose_mulVec_betaFull
    (a : ℝ) (N : ℕ) :
    (ccmEvenParityFrame N)ᴴ *ᵥ ccmPublishedParityBetaFull a N = 0 :=
  ccmEvenFrame_conjTranspose_mulVec_eq_zero_of_odd N _
    (ccmPublishedParityBetaFull_odd a N)

theorem ccmPublishedParityCross_commutator (a mu : ℝ) (N : ℕ) :
    ccmPublishedParityEvenBlock a mu N *
          ccmPublishedParityCrossFrequency N -
        ccmPublishedParityCrossFrequency N *
          ccmPublishedParityOddBlock a mu N =
      Matrix.vecMulVec (ccmPublishedParityEta N)
        (star (ccmPublishedParityBeta a N)) := by
  let T := ccmPublishedParityShift a mu N
  let D := ccmParityClockMatrix N
  let E := ccmEvenParityFrame N
  let O := ccmOddParityFrame N
  let P := ccmPublishedParityEvenBlock a mu N
  let M := ccmPublishedParityOddBlock a mu N
  let B := ccmPublishedParityCrossFrequency N
  have hTE : T * E = E * P := by
    exact ccmPublishedParityShift_mul_evenFrame a mu N
  have hTO : T * O = O * M := by
    exact ccmPublishedParityShift_mul_oddFrame a mu N
  have hDO : D * O = E * B := by
    exact ccmParityClockMatrix_mul_oddFrame N
  have hEE : Eᴴ * E = 1 := ccmEvenParityFrame_orthonormal N
  have hfirst : Eᴴ * (T * D) * O = P * B := by
    calc
      Eᴴ * (T * D) * O = Eᴴ * (T * (D * O)) := by
        simp only [Matrix.mul_assoc]
      _ = Eᴴ * (T * (E * B)) := by rw [hDO]
      _ = Eᴴ * ((T * E) * B) := by rw [Matrix.mul_assoc]
      _ = Eᴴ * ((E * P) * B) := by rw [hTE]
      _ = (Eᴴ * E) * (P * B) := by simp only [Matrix.mul_assoc]
      _ = P * B := by rw [hEE, Matrix.one_mul]
  have hsecond : Eᴴ * (D * T) * O = B * M := by
    calc
      Eᴴ * (D * T) * O = Eᴴ * (D * (T * O)) := by
        simp only [Matrix.mul_assoc]
      _ = Eᴴ * (D * (O * M)) := by rw [hTO]
      _ = Eᴴ * ((D * O) * M) := by rw [Matrix.mul_assoc]
      _ = Eᴴ * ((E * B) * M) := by rw [hDO]
      _ = (Eᴴ * E) * (B * M) := by simp only [Matrix.mul_assoc]
      _ = B * M := by rw [hEE, Matrix.one_mul]
  have hcomm : T * D - D * T =
      Matrix.vecMulVec (ccmPublishedParityEtaFull N)
          (star (ccmPublishedParityBetaFull a N)) -
        Matrix.vecMulVec (ccmPublishedParityBetaFull a N)
          (star (ccmPublishedParityEtaFull N)) := by
    have h := ccmPublishedParityShift_displacement a mu N
    calc
      T * D - D * T = -(D * T - T * D) := by abel
      _ = -(Matrix.vecMulVec (ccmPublishedParityBetaFull a N)
            (star (ccmPublishedParityEtaFull N)) -
          Matrix.vecMulVec (ccmPublishedParityEtaFull N)
            (star (ccmPublishedParityBetaFull a N))) := by rw [h]
      _ = Matrix.vecMulVec (ccmPublishedParityEtaFull N)
            (star (ccmPublishedParityBetaFull a N)) -
          Matrix.vecMulVec (ccmPublishedParityBetaFull a N)
            (star (ccmPublishedParityEtaFull N)) := by abel
  have hproject := congrArg (fun X => Eᴴ * X * O) hcomm
  rw [Matrix.mul_sub, Matrix.sub_mul, hfirst, hsecond,
    Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul] at hproject
  rw [ccmPublishedParityEvenFrame_conjTranspose_mulVec_etaFull,
    star_ccmPublishedParityBetaFull_vecMul_oddFrame,
    ccmPublishedParityEvenFrame_conjTranspose_mulVec_betaFull,
    star_ccmPublishedParityEtaFull_vecMul_oddFrame,
    Matrix.zero_vecMulVec, sub_zero] at hproject
  simpa only [B, M, P] using hproject

theorem ccmParityFrameScale_ne_zero : ccmParityFrameScale ≠ 0 := by
  intro hzero
  have hsq := ccmParityFrameScale_sq
  rw [hzero] at hsq
  norm_num at hsq

theorem ccmOddParityFrame_mulVec_apply_false (N : ℕ) (c : Fin N → ℂ)
    (k : Fin N) :
    (ccmOddParityFrame N *ᵥ c) (some (k, false)) =
      ccmParityFrameScale * c k := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single k]
  · simp [ccmOddParityFrame]
  · intro j _ hj
    simp [ccmOddParityFrame, Ne.symm hj]
  · simp

theorem ccmOddParityFrame_mulVec_injective (N : ℕ) :
    Function.Injective (fun c : Fin N → ℂ => ccmOddParityFrame N *ᵥ c) := by
  intro c d hcd
  funext k
  have hk := congr_fun hcd (some (k, false))
  change (ccmOddParityFrame N *ᵥ c) (some (k, false)) =
    (ccmOddParityFrame N *ᵥ d) (some (k, false)) at hk
  rw [ccmOddParityFrame_mulVec_apply_false,
    ccmOddParityFrame_mulVec_apply_false] at hk
  exact (mul_left_cancel₀ ccmParityFrameScale_ne_zero hk)

theorem ccmEvenParityFrame_mulVec_injective (N : ℕ) :
    Function.Injective
      (fun c : CCMEvenParityIndex N → ℂ => ccmEvenParityFrame N *ᵥ c) := by
  intro c d hcd
  have h := congrArg (fun v => (ccmEvenParityFrame N)ᴴ *ᵥ v) hcd
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ccmEvenParityFrame_orthonormal, Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

theorem ccmParityClockMatrix_eq_diagonal (N : ℕ) :
    ccmParityClockMatrix N =
      Matrix.diagonal (fun i => (ccmParityCenteredClock N i : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [ccmParityClockMatrix, ccmDiagonalClock, Matrix.diagonal]
  · simp [ccmParityClockMatrix, ccmDiagonalClock, Matrix.diagonal, hij]

theorem ccmParityClockMatrix_mulVec_oddFrame_injective (N : ℕ) :
    Function.Injective (fun c : Fin N → ℂ =>
      ccmParityClockMatrix N *ᵥ (ccmOddParityFrame N *ᵥ c)) := by
  intro c d hcd
  funext k
  have hk := congr_fun hcd (some (k, false))
  change (ccmParityClockMatrix N *ᵥ (ccmOddParityFrame N *ᵥ c))
      (some (k, false)) =
    (ccmParityClockMatrix N *ᵥ (ccmOddParityFrame N *ᵥ d))
      (some (k, false)) at hk
  rw [ccmParityClockMatrix_eq_diagonal] at hk
  simp only [Matrix.mulVec_diagonal] at hk
  rw [
    ccmOddParityFrame_mulVec_apply_false,
    ccmOddParityFrame_mulVec_apply_false] at hk
  have hclock :
      ((ccmParityCenteredClock N (some (k, false)) : ℝ) : ℂ) ≠ 0 := by
    change (((((k.1 + 1 : ℕ) : ℤ) : ℝ) : ℂ)) ≠ 0
    exact_mod_cast (Nat.succ_ne_zero k.1)
  have hscaled := mul_left_cancel₀ hclock hk
  exact mul_left_cancel₀ ccmParityFrameScale_ne_zero hscaled

theorem ccmPublishedParityCrossFrequency_mulVec_injective (N : ℕ) :
    Function.Injective (fun c : Fin N → ℂ =>
      ccmPublishedParityCrossFrequency N *ᵥ c) := by
  intro c d hcd
  change ccmPublishedParityCrossFrequency N *ᵥ c =
    ccmPublishedParityCrossFrequency N *ᵥ d at hcd
  apply ccmParityClockMatrix_mulVec_oddFrame_injective N
  have hDO := ccmParityClockMatrix_mul_oddFrame N
  calc
    ccmParityClockMatrix N *ᵥ (ccmOddParityFrame N *ᵥ c) =
        (ccmParityClockMatrix N * ccmOddParityFrame N) *ᵥ c := by
      rw [← Matrix.mulVec_mulVec]
    _ = (ccmEvenParityFrame N *
          ccmPublishedParityCrossFrequency N) *ᵥ c := by rw [hDO]
    _ = ccmEvenParityFrame N *ᵥ
        (ccmPublishedParityCrossFrequency N *ᵥ c) := by
      rw [Matrix.mulVec_mulVec]
    _ = ccmEvenParityFrame N *ᵥ
        (ccmPublishedParityCrossFrequency N *ᵥ d) := by rw [hcd]
    _ = (ccmEvenParityFrame N *
          ccmPublishedParityCrossFrequency N) *ᵥ d := by
      rw [← Matrix.mulVec_mulVec]
    _ = (ccmParityClockMatrix N * ccmOddParityFrame N) *ᵥ d := by rw [hDO]
    _ = ccmParityClockMatrix N *ᵥ (ccmOddParityFrame N *ᵥ d) := by
      rw [Matrix.mulVec_mulVec]

theorem exists_ccmPublishedParityFreeOddGroundData_of_visible_block_ground
    (a mu : ℝ) (N : ℕ)
    (hT : (ccmPublishedParityShift a mu N).PosSemidef)
    (c : Fin N → ℂ)
    (hMc : ccmPublishedParityOddBlock a mu N *ᵥ c = 0)
    (hline : ∀ v : Fin N → ℂ,
      ccmPublishedParityOddBlock a mu N *ᵥ v = 0 →
        ∃ z : ℂ, v = z • c)
    (hvisible : ccmPublishedParityEvenBlock a mu N *ᵥ
      (ccmPublishedParityCrossFrequency N *ᵥ c) ≠ 0) :
    ∃ S : CCMParityFreeOddGroundData (CCMEvenParityIndex N) (Fin N),
      S.Qplus = ccmPublishedParityEvenBlock a mu N ∧
      S.Qminus = ccmPublishedParityOddBlock a mu N ∧
      S.frequency = ccmPublishedParityCrossFrequency N ∧
      S.eta = ccmPublishedParityEta N ∧
      S.beta = ccmPublishedParityBeta a N := by
  let P := ccmPublishedParityEvenBlock a mu N
  let M := ccmPublishedParityOddBlock a mu N
  let B := ccmPublishedParityCrossFrequency N
  let eta := ccmPublishedParityEta N
  let beta := ccmPublishedParityBeta a N
  let delta := Bᴴ *ᵥ eta
  let q : ℂ := star c ⬝ᵥ delta
  have hP : P.PosSemidef := ccmPublishedParityEvenBlock_posSemidef a mu N hT
  have hM : M.PosSemidef := ccmPublishedParityOddBlock_posSemidef a mu N hT
  have hMc' : M *ᵥ c = 0 := by simpa only [M] using hMc
  have hcross : P * B - B * M = Matrix.vecMulVec eta (star beta) := by
    exact ccmPublishedParityCross_commutator a mu N
  have hPB : P *ᵥ (B *ᵥ c) ≠ 0 := by
    simpa only [P, B] using hvisible
  have haction : P *ᵥ (B *ᵥ c) = (star beta ⬝ᵥ c) • eta := by
    have h := congrArg (fun X : Matrix (CCMEvenParityIndex N) (Fin N) ℂ => X *ᵥ c)
      hcross
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hMc', Matrix.mulVec_zero, sub_zero, Matrix.vecMulVec_mulVec] at h
    simpa [P, M, B, eta, beta, smul_eq_mul, mul_comm] using h
  have hpair : star (B *ᵥ c) ⬝ᵥ eta = q := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have henergy_ne : star (B *ᵥ c) ⬝ᵥ (P *ᵥ (B *ᵥ c)) ≠ 0 := by
    intro hzero
    exact hPB ((hP.dotProduct_mulVec_zero_iff (B *ᵥ c)).mp hzero)
  have hq : q ≠ 0 := by
    intro hqzero
    apply henergy_ne
    rw [haction, dotProduct_smul, hpair, hqzero]
    simp
  let s : ℂ := (star q)⁻¹
  let g : Fin N → ℂ := s • c
  have hs : s ≠ 0 := inv_ne_zero (star_ne_zero.mpr hq)
  have hgkernel : M *ᵥ g = 0 := by
    change M *ᵥ (s • c) = 0
    rw [Matrix.mulVec_smul, hMc']
    simp
  have hgline : ∀ v : Fin N → ℂ, M *ᵥ v = 0 → ∃ z : ℂ, v = z • g := by
    intro v hv
    obtain ⟨z, hz⟩ := hline v (by simpa only [M] using hv)
    refine ⟨z * s⁻¹, ?_⟩
    rw [hz]
    simp [g, smul_smul, hs]
  have hgnorm : star g ⬝ᵥ delta = 1 := by
    simp only [g, star_smul, smul_dotProduct]
    change star s * q = 1
    simp [s, hq]
  have hgvisible : P *ᵥ (B *ᵥ g) ≠ 0 := by
    intro hzero
    change P *ᵥ (B *ᵥ (s • c)) = 0 at hzero
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul] at hzero
    exact hPB ((smul_eq_zero.mp hzero).resolve_left hs)
  let S : CCMParityFreeOddGroundData (CCMEvenParityIndex N) (Fin N) :=
    { Qplus := P
      Qminus := M
      frequency := B
      eta := eta
      beta := beta
      ground := g
      plus_posSemidef := hP
      minus_posSemidef := hM
      cross_commutator := hcross
      ground_kernel := hgkernel
      ground_radical := hgline
      frequency_ground_not_kernel := hgvisible
      normalized := hgnorm }
  exact ⟨S, rfl, rfl, rfl, rfl, rfl⟩

theorem exists_ccmPublishedParityFreeOddGroundData_of_simple_full_odd_ground
    (a mu : ℝ) (N : ℕ)
    (hT : (ccmPublishedParityShift a mu N).PosSemidef)
    (c : Fin N → ℂ) (hc : c ≠ 0)
    (hground : ccmPublishedParityShift a mu N *ᵥ
      (ccmOddParityFrame N *ᵥ c) = 0)
    (hline : ∀ v : CCMCenteredParityIndex N → ℂ,
      ccmPublishedParityShift a mu N *ᵥ v = 0 →
        ∃ z : ℂ, v = z • (ccmOddParityFrame N *ᵥ c)) :
    ∃ S : CCMParityFreeOddGroundData (CCMEvenParityIndex N) (Fin N),
      S.Qplus = ccmPublishedParityEvenBlock a mu N ∧
      S.Qminus = ccmPublishedParityOddBlock a mu N ∧
      S.frequency = ccmPublishedParityCrossFrequency N ∧
      S.eta = ccmPublishedParityEta N ∧
      S.beta = ccmPublishedParityBeta a N := by
  let T := ccmPublishedParityShift a mu N
  let P := ccmPublishedParityEvenBlock a mu N
  let M := ccmPublishedParityOddBlock a mu N
  let B := ccmPublishedParityCrossFrequency N
  let E := ccmEvenParityFrame N
  let O := ccmOddParityFrame N
  have hTO : T * O = O * M := ccmPublishedParityShift_mul_oddFrame a mu N
  have hTE : T * E = E * P := ccmPublishedParityShift_mul_evenFrame a mu N
  have hOO : Oᴴ * O = 1 := ccmOddParityFrame_orthonormal N
  have hEE : Eᴴ * E = 1 := ccmEvenParityFrame_orthonormal N
  have hEO : Eᴴ * O = 0 := ccmParityFrames_orthogonal N
  have hMc : M *ᵥ c = 0 := by
    apply ccmOddParityFrame_mulVec_injective N
    calc
      O *ᵥ (M *ᵥ c) = (O * M) *ᵥ c := by rw [← Matrix.mulVec_mulVec]
      _ = (T * O) *ᵥ c := by rw [hTO]
      _ = T *ᵥ (O *ᵥ c) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by simpa only [T, O] using hground
      _ = O *ᵥ 0 := by rw [Matrix.mulVec_zero]
  have hMline : ∀ v : Fin N → ℂ, M *ᵥ v = 0 → ∃ z : ℂ, v = z • c := by
    intro v hv
    have hfull : T *ᵥ (O *ᵥ v) = 0 := by
      calc
        T *ᵥ (O *ᵥ v) = (T * O) *ᵥ v := by rw [← Matrix.mulVec_mulVec]
        _ = (O * M) *ᵥ v := by rw [hTO]
        _ = O *ᵥ (M *ᵥ v) := by rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [hv, Matrix.mulVec_zero]
    obtain ⟨z, hz⟩ := hline (O *ᵥ v) (by simpa only [T, O] using hfull)
    refine ⟨z, ccmOddParityFrame_mulVec_injective N ?_⟩
    change O *ᵥ v = O *ᵥ (z • c)
    rw [Matrix.mulVec_smul]
    simpa only [O] using hz
  have hvisible : P *ᵥ (B *ᵥ c) ≠ 0 := by
    intro hPB
    have hfullEven : T *ᵥ (E *ᵥ (B *ᵥ c)) = 0 := by
      calc
        T *ᵥ (E *ᵥ (B *ᵥ c)) = (T * E) *ᵥ (B *ᵥ c) := by
          rw [← Matrix.mulVec_mulVec]
        _ = (E * P) *ᵥ (B *ᵥ c) := by rw [hTE]
        _ = E *ᵥ (P *ᵥ (B *ᵥ c)) :=
          (Matrix.mulVec_mulVec (B *ᵥ c) E P).symm
        _ = 0 := by rw [hPB, Matrix.mulVec_zero]
    obtain ⟨z, hz⟩ := hline (E *ᵥ (B *ᵥ c))
      (by simpa only [T, E, B] using hfullEven)
    have hBc : B *ᵥ c = 0 := by
      have hleft : Eᴴ *ᵥ (E *ᵥ (B *ᵥ c)) = B *ᵥ c := by
        rw [Matrix.mulVec_mulVec, hEE, Matrix.one_mulVec]
      have hright : Eᴴ *ᵥ (z • (O *ᵥ c)) = 0 := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hEO,
          Matrix.zero_mulVec, smul_zero]
      have hz' : E *ᵥ (B *ᵥ c) = z • (O *ᵥ c) := by
        simpa only [E, O, B] using hz
      have hzproj' := congrArg (fun v => Eᴴ *ᵥ v) hz'
      rw [hleft, hright] at hzproj'
      exact hzproj'
    apply hc
    apply ccmPublishedParityCrossFrequency_mulVec_injective N
    simpa only [B, Matrix.mulVec_zero] using hBc
  apply exists_ccmPublishedParityFreeOddGroundData_of_visible_block_ground
    a mu N hT c
  · simpa only [M] using hMc
  · intro v hv
    exact hMline v (by simpa only [M] using hv)
  · simpa only [P, B] using hvisible

theorem ccmPublishedParityWeilMatrix_transpose (a : ℝ) (N : ℕ) :
    (ccmPublishedParityWeilMatrix a N).transpose =
      ccmPublishedParityWeilMatrix a N := by
  exact ccmDividedDifferenceMatrix_transpose _ _ _

theorem exists_ccmPublishedParityGroundShift (a : ℝ) (N : ℕ) :
    ∃ mu : ℝ,
      (ccmPublishedParityShift a mu N).PosSemidef ∧
      ∃ c : CCMCenteredParityIndex N → ℂ,
        ccmPublishedParityShift a mu N *ᵥ c = 0 ∧ c ≠ 0 := by
  let Q := ccmPublishedParityWeilMatrix a N
  let QC := Q.map (algebraMap ℝ ℂ)
  have hQC : QC.IsHermitian := by
    exact realSymmetric_complexification_isHermitian Q
      (ccmPublishedParityWeilMatrix_transpose a N)
  have huniv :
      (Finset.univ : Finset (CCMCenteredParityIndex N)).Nonempty :=
    ⟨none, Finset.mem_univ _⟩
  obtain ⟨i0, _hi0, hmin⟩ :=
    Finset.exists_min_image
      (Finset.univ : Finset (CCMCenteredParityIndex N))
      hQC.eigenvalues huniv
  let mu : ℝ := hQC.eigenvalues i0
  let U : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ :=
    hQC.eigenvectorUnitary
  let d : CCMCenteredParityIndex N → ℂ :=
    fun i => ((hQC.eigenvalues i - mu : ℝ) : ℂ)
  have hdnonneg : ∀ i, 0 ≤ d i := by
    intro i
    exact RCLike.ofReal_nonneg.mpr
      (sub_nonneg.mpr (hmin i (Finset.mem_univ i)))
  have hdiag : (Matrix.diagonal d).PosSemidef :=
    Matrix.PosSemidef.diagonal hdnonneg
  have hspec :
      QC = U * Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) * Uᴴ := by
    simpa [U, Function.comp_def, Matrix.star_eq_conjTranspose] using
      hQC.spectral_theorem
  have hUunit : U * Uᴴ = 1 := by
    change
      (hQC.eigenvectorUnitary : Matrix (CCMCenteredParityIndex N)
          (CCMCenteredParityIndex N) ℂ) *
        (hQC.eigenvectorUnitary : Matrix (CCMCenteredParityIndex N)
          (CCMCenteredParityIndex N) ℂ)ᴴ = 1
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self hQC.eigenvectorUnitary
  have hmuConj :
      U * ((mu : ℂ) •
          (1 : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ)) * Uᴴ =
        (mu : ℂ) •
          (1 : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ) := by
    calc
      U * ((mu : ℂ) • 1) * Uᴴ = (mu : ℂ) • (U * Uᴴ) := by simp
      _ = (mu : ℂ) • 1 := by rw [hUunit]
  have hdiagShift :
      Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) -
          (mu : ℂ) •
            (1 : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ) =
        Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d]
    · simp [Matrix.diagonal, hij]
  have hshiftSpectral :
      QC - (mu : ℂ) •
          (1 : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ) =
        U * Matrix.diagonal d * Uᴴ := by
    have hspecSub := congrArg
      (fun M : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ =>
        M - (mu : ℂ) • 1) hspec
    calc
      QC - (mu : ℂ) • 1 =
          U * Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) * Uᴴ -
            (mu : ℂ) • 1 := hspecSub
      _ = U * Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) * Uᴴ -
            U * ((mu : ℂ) • 1) * Uᴴ := by rw [hmuConj]
      _ = U *
          (Matrix.diagonal (fun i => (hQC.eigenvalues i : ℂ)) -
            (mu : ℂ) • 1) * Uᴴ := by noncomm_ring
      _ = U * Matrix.diagonal d * Uᴴ := by rw [hdiagShift]
  have hmapShift :
      ccmPublishedParityShift a mu N =
        QC - (mu : ℂ) •
          (1 : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [ccmPublishedParityShift, ccmScalarShift, Q, QC]
    · simp [ccmPublishedParityShift, ccmScalarShift, Q, QC, hij]
  have hT : (ccmPublishedParityShift a mu N).PosSemidef := by
    rw [hmapShift, hshiftSpectral]
    exact hdiag.mul_mul_conjTranspose_same U
  let c : CCMCenteredParityIndex N → ℂ := ⇑(hQC.eigenvectorBasis i0)
  have hcne : c ≠ 0 := by
    exact (WithLp.ofLp_eq_zero 2).ne.mpr
      (hQC.eigenvectorBasis.orthonormal.ne_zero i0)
  have hTc :
      (QC - (mu : ℂ) •
        (1 : Matrix (CCMCenteredParityIndex N) (CCMCenteredParityIndex N) ℂ)) *ᵥ c = 0 := by
    rw [Matrix.sub_mulVec, hQC.mulVec_eigenvectorBasis,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    simp [c, mu]
  refine ⟨mu, hT, c, ?_, hcne⟩
  rw [hmapShift]
  exact hTc

def CCMPublishedSimpleOddGroundBranch (a mu : ℝ) (N : ℕ) : Prop :=
  ∃ c : Fin N → ℂ,
    c ≠ 0 ∧
    ccmPublishedParityShift a mu N *ᵥ (ccmOddParityFrame N *ᵥ c) = 0 ∧
    ∀ v : CCMCenteredParityIndex N → ℂ,
      ccmPublishedParityShift a mu N *ᵥ v = 0 →
        ∃ z : ℂ, v = z • (ccmOddParityFrame N *ᵥ c)

theorem exists_ccmPublishedParityGroundShift_simpleOddAdapter
    (a : ℝ) (N : ℕ) :
    ∃ mu : ℝ,
      (ccmPublishedParityShift a mu N).PosSemidef ∧
      (∃ c : CCMCenteredParityIndex N → ℂ,
        ccmPublishedParityShift a mu N *ᵥ c = 0 ∧ c ≠ 0) ∧
      (CCMPublishedSimpleOddGroundBranch a mu N →
        ∃ S : CCMParityFreeOddGroundData (CCMEvenParityIndex N) (Fin N),
          S.Qplus = ccmPublishedParityEvenBlock a mu N ∧
          S.Qminus = ccmPublishedParityOddBlock a mu N ∧
          S.frequency = ccmPublishedParityCrossFrequency N ∧
          S.eta = ccmPublishedParityEta N ∧
          S.beta = ccmPublishedParityBeta a N) := by
  obtain ⟨mu, hT, hkernel⟩ := exists_ccmPublishedParityGroundShift a N
  refine ⟨mu, hT, hkernel, ?_⟩
  rintro ⟨c, hc, hground, hline⟩
  exact exists_ccmPublishedParityFreeOddGroundData_of_simple_full_odd_ground
    a mu N hT c hc hground hline

end

end RHTower
