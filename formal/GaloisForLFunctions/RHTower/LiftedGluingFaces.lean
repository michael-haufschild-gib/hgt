/-
# Lifted gluing faces: deck scale and unipotent seam are independent constraints

`CutoffCochain` proves non-identification: square-zero cross-boundary cochains cannot be nontrivial
deck roots of unity.  It names `g = w·(1+Δ)` but does not prove the faces are free parameters.

This module proves, in the concrete cutoff-witness matrix model over `ℚ`:

1. `liftedGlue s t = (s • 1)(1 + t · Δ₀)` with `Δ₀² = 0`;
2. deck face (diagonal) = `s`, seam entry (off-diagonal) = `s·t`;
3. deck face free at fixed seam ratio; seam free at fixed deck;
4. Fitting boundary of the unipotent defect is linear in `t` only and live for `t ≠ 0`;
5. `1 + Δ₀` is never a nontrivial `2^k`-th root of unity.

**Dual-gate status: FAIL (packaging).** Free `(s,t)` of a two-parameter definition is not new
knowledge (skeptic 2026-07-08). Retained as dictionary for `standardPres` / `seamDef` only.
The dual-gate claim lives in `FittingDeckChargeBarrier.lean`.
-/
import GaloisForLFunctions.RHTower.CutoffCochain
import GaloisForLFunctions.RHTower.DeckChargeCalculus

noncomputable section

namespace RHTower

open Matrix Polynomial

/-! ### §1 Model over `ℚ` -/

/-- Cross-boundary nilpotent over `ℚ`. -/
def crossNilpℚ : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]

theorem crossNilpℚ_sq : crossNilpℚ * crossNilpℚ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [crossNilpℚ, Matrix.mul_apply, Fin.sum_univ_two]

theorem crossNilpℚ_eq_crossWitness : crossNilpℚ = crossWitness := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

def deckScalarℚ (s : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := s • (1 : Matrix (Fin 2) (Fin 2) ℚ)

/-- Lifted gluing over `ℚ`. -/
def liftedGlueℚ (s t : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  deckScalarℚ s * (1 + t • crossNilpℚ)

theorem liftedGlueℚ_eq_add (s t : ℚ) :
    liftedGlueℚ s t = deckScalarℚ s + (s * t) • crossNilpℚ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftedGlueℚ, deckScalarℚ, crossNilpℚ, Matrix.mul_apply, Matrix.smul_apply,
      one_apply]

theorem liftedGlueℚ_00 (s t : ℚ) : liftedGlueℚ s t 0 0 = s := by
  simp [liftedGlueℚ_eq_add, deckScalarℚ, crossNilpℚ, Matrix.smul_apply, one_apply]

theorem liftedGlueℚ_10 (s t : ℚ) : liftedGlueℚ s t 1 0 = s * t := by
  simp [liftedGlueℚ_eq_add, deckScalarℚ, crossNilpℚ, Matrix.smul_apply, one_apply]

theorem liftedGlueℚ_11 (s t : ℚ) : liftedGlueℚ s t 1 1 = s := by
  simp [liftedGlueℚ_eq_add, deckScalarℚ, crossNilpℚ, Matrix.smul_apply, one_apply]

def deckFaceℚ (g : Matrix (Fin 2) (Fin 2) ℚ) : ℚ := g 0 0

theorem deckFaceℚ_liftedGlue (s t : ℚ) : deckFaceℚ (liftedGlueℚ s t) = s := by
  simp [deckFaceℚ, liftedGlueℚ_00]

/-! ### §2 Face independence -/

/-- Same deck face, different seam entries. -/
theorem same_deck_different_seam {t₁ t₂ : ℚ} (ht : t₁ ≠ t₂) :
    deckFaceℚ (liftedGlueℚ 1 t₁) = deckFaceℚ (liftedGlueℚ 1 t₂) ∧
      liftedGlueℚ 1 t₁ 1 0 ≠ liftedGlueℚ 1 t₂ 1 0 := by
  refine ⟨by simp [deckFaceℚ_liftedGlue], ?_⟩
  simpa [liftedGlueℚ_10] using ht

/-- Same seam parameter, different deck faces. -/
theorem same_seam_different_deck {s₁ s₂ t : ℚ} (hs : s₁ ≠ s₂) :
    deckFaceℚ (liftedGlueℚ s₁ t) ≠ deckFaceℚ (liftedGlueℚ s₂ t) := by
  simpa [deckFaceℚ_liftedGlue] using hs

/-- Joint realization: faces recover the parameters at `s ≠ 0`. -/
theorem faces_recover {s t : ℚ} (hs : s ≠ 0) :
    deckFaceℚ (liftedGlueℚ s t) = s ∧ liftedGlueℚ s t 1 0 / s = t := by
  refine ⟨deckFaceℚ_liftedGlue s t, ?_⟩
  rw [liftedGlueℚ_10]
  field_simp [hs]

/-! ### §3 Fitting is pure seam -/

def standardPres (m : ℕ) : Matrix (Fin 2) (Fin 2) ℚ[X] :=
  !![(X : ℚ[X]) ^ m, 1; 0, 1]

def seamDef (t : ℚ) : Matrix (Fin 2) (Fin 2) ℚ[X] :=
  (C t) • (!![(0 : ℚ[X]), 0; 1, 0])

theorem fittingTrace_seamDef (m : ℕ) (t : ℚ) :
    fittingBoundaryTrace (standardPres m) (seamDef t) = -C t := by
  -- copy the explicit computation of `exists_nonfake_crossBoundary`
  have hadj : (standardPres m).adjugate = !![1, -1; 0, (X : ℚ[X]) ^ m] := by
    simp [standardPres, Matrix.adjugate_fin_two]
  have hΔ : seamDef t = !![0, 0; C t, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [seamDef, Matrix.smul_apply]
  unfold fittingBoundaryTrace
  rw [hadj, hΔ, Matrix.mul_fin_two, Matrix.trace_fin_two]
  simp

theorem fittingClass_seamDef (m : ℕ) (t : ℚ) :
    fittingBoundaryClass m (standardPres m) (seamDef t) = jetClass ℚ m (-C t) := by
  rw [fittingBoundaryClass, fittingTrace_seamDef]

theorem fittingClass_seamDef_ne_zero {m : ℕ} (hm : 0 < m) {t : ℚ} (ht : t ≠ 0) :
    fittingBoundaryClass m (standardPres m) (seamDef t) ≠ 0 := by
  rw [fittingClass_seamDef]
  intro hzero
  have hmem : (-C t : ℚ[X]) ∈ jetIdeal ℚ m :=
    (Ideal.Quotient.eq_zero_iff_mem).mp hzero
  have hdvd : (X : ℚ[X]) ^ m ∣ -C t :=
    Ideal.mem_span_singleton.mp (by simpa [jetIdeal] using hmem)
  obtain ⟨c, hc⟩ := hdvd
  have hL : (-C t : ℚ[X]).coeff 0 = -t := by simp
  have hR : (((X : ℚ[X]) ^ m) * c).coeff 0 = 0 := by
    rw [Polynomial.coeff_X_pow_mul']
    split_ifs with hle
    · omega
    · simp
  have hco : (-C t : ℚ[X]).coeff 0 = (((X : ℚ[X]) ^ m) * c).coeff 0 := by
    rw [hc]
  rw [hL, hR] at hco
  exact ht (neg_eq_zero.mp hco)

/-- Fitting class is a pure function of the seam parameter `t` (no deck scale appears). -/
theorem fitting_depends_only_on_seam (m : ℕ) (t : ℚ) :
    fittingBoundaryClass m (standardPres m) (seamDef t) =
      jetClass ℚ m (-C t) :=
  fittingClass_seamDef m t

/-! ### §4 Unipotent ≠ torsion (direct, no typeclass pain) -/

theorem pow_one_add_crossNilpℚ (n : ℕ) :
    (1 + crossNilpℚ) ^ n = 1 + n • crossNilpℚ :=
  pow_one_add_of_sq_zero crossNilpℚ_sq n

theorem crossNilpℚ_of_pow_eq_one {k : ℕ}
    (hroot : (1 + crossNilpℚ) ^ (2 ^ k) = 1) : crossNilpℚ = 0 := by
  have hp := pow_one_add_crossNilpℚ (2 ^ k)
  rw [hroot] at hp
  have hsmul : (2 ^ k : ℕ) • crossNilpℚ = 0 := left_eq_add.mp hp
  ext i j
  have hentry : ((2 ^ k : ℕ) • crossNilpℚ) i j = (0 : Matrix (Fin 2) (Fin 2) ℚ) i j := by
    rw [hsmul]
  have : ((2 ^ k : ℚ) * crossNilpℚ i j) = 0 := by
    simpa [Matrix.smul_apply, nsmul_eq_mul, Matrix.zero_apply] using hentry
  have hne : (2 ^ k : ℚ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0))
  exact (mul_eq_zero.mp this).resolve_left hne

/-! ### §5 Capstone -/

/-- **Gluing-face independence.**  Over the cutoff-witness model:
* deck face recovers `s` for every lifted gluing;
* seam entries can vary at fixed deck, and deck can vary at fixed seam parameter;
* Fitting boundary of the unipotent defect is nontrivial for `t ≠ 0` and depends only on `t`;
* unipotent `1+Δ₀` is never a nontrivial `2^k`-th root of unity. -/
theorem gluing_faces_independent (m : ℕ) (hm : 0 < m) :
    (∀ s t : ℚ, deckFaceℚ (liftedGlueℚ s t) = s) ∧
    (∀ t₁ t₂ : ℚ, t₁ ≠ t₂ →
      deckFaceℚ (liftedGlueℚ 1 t₁) = deckFaceℚ (liftedGlueℚ 1 t₂) ∧
        liftedGlueℚ 1 t₁ 1 0 ≠ liftedGlueℚ 1 t₂ 1 0) ∧
    (∀ s₁ s₂ t : ℚ, s₁ ≠ s₂ →
      deckFaceℚ (liftedGlueℚ s₁ t) ≠ deckFaceℚ (liftedGlueℚ s₂ t)) ∧
    (∀ t : ℚ, t ≠ 0 →
      fittingBoundaryClass m (standardPres m) (seamDef t) ≠ 0) ∧
    (∀ k : ℕ, (1 + crossNilpℚ) ^ (2 ^ k) = 1 → crossNilpℚ = 0) := by
  exact ⟨fun s t => deckFaceℚ_liftedGlue s t,
    fun t₁ t₂ ht => same_deck_different_seam ht,
    fun s₁ s₂ t hs => same_seam_different_deck hs,
    fun t ht => fittingClass_seamDef_ne_zero hm ht,
    fun k h => crossNilpℚ_of_pow_eq_one h⟩

end RHTower
