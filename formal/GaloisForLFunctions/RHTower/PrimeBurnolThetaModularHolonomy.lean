import GaloisForLFunctions.RHTower.PrimeBurnolSourceFrameCubicHolonomy
import GaloisForLFunctions.RHTower.PrimeBurnolFiniteOffDiagonalFaithfulness
import GaloisForLFunctions.HTGeometry.TanhSubstitution
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Prime Burnol--theta modular holonomy

The literal complete Burnol Gram is doubled without changing its source coefficients. The
archimedean theta polarization is realized on the same finite packet by its canonical
prime-dependent `sech/tanh` rotation. Their multiplicative commutator is therefore a fully formed
pre-divisor source--completion holonomy, with exact neutral vanishing, functional-equation
reversal, determinant blindness, and cubic modular transgression.
-/

open Complex Matrix
open scoped Kronecker

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

abbrev PrimeBurnolThetaIndex (N : ℕ) := Fin N × Fin 2

def primeBurnolThetaRapidity (a : ℝ) (p : Nat.Primes) : ℝ :=
  a * Real.log (p : ℝ) / 2

def primeBurnolThetaVisibility (a : ℝ) (p : Nat.Primes) : ℝ :=
  1 / Real.cosh (primeBurnolThetaRapidity a p)

def primeBurnolThetaContrast (a : ℝ) (p : Nat.Primes) : ℝ :=
  Real.tanh (primeBurnolThetaRapidity a p)

theorem primeBurnolThetaVisibility_sq_add_contrast_sq (a : ℝ) (p : Nat.Primes) :
    primeBurnolThetaVisibility a p ^ 2 + primeBurnolThetaContrast a p ^ 2 = 1 := by
  have h := HTGeometry.one_sub_tanh_sq (primeBurnolThetaRapidity a p)
  rw [primeBurnolThetaVisibility, primeBurnolThetaContrast]
  calc
    (1 / Real.cosh (primeBurnolThetaRapidity a p)) ^ 2 +
          Real.tanh (primeBurnolThetaRapidity a p) ^ 2 =
        1 / Real.cosh (primeBurnolThetaRapidity a p) ^ 2 +
          Real.tanh (primeBurnolThetaRapidity a p) ^ 2 := by ring
    _ = (1 - Real.tanh (primeBurnolThetaRapidity a p) ^ 2) +
          Real.tanh (primeBurnolThetaRapidity a p) ^ 2 := by rw [h]
    _ = 1 := by ring

theorem primeBurnolThetaVisibility_neg (a : ℝ) (p : Nat.Primes) :
    primeBurnolThetaVisibility (-a) p = primeBurnolThetaVisibility a p := by
  rw [primeBurnolThetaVisibility, primeBurnolThetaVisibility,
    primeBurnolThetaRapidity, primeBurnolThetaRapidity]
  rw [show -a * Real.log (p : ℝ) / 2 = -(a * Real.log (p : ℝ) / 2) by ring,
    Real.cosh_neg]

theorem primeBurnolThetaContrast_neg (a : ℝ) (p : Nat.Primes) :
    primeBurnolThetaContrast (-a) p = -primeBurnolThetaContrast a p := by
  rw [primeBurnolThetaContrast, primeBurnolThetaContrast,
    primeBurnolThetaRapidity, primeBurnolThetaRapidity]
  rw [show -a * Real.log (p : ℝ) / 2 = -(a * Real.log (p : ℝ) / 2) by ring,
    Real.tanh_neg]

def primeBurnolThetaBlock (a : ℝ) (p : Nat.Primes) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((primeBurnolThetaVisibility a p : ℝ) : ℂ),
      -((primeBurnolThetaContrast a p : ℝ) : ℂ);
     ((primeBurnolThetaContrast a p : ℝ) : ℂ),
      ((primeBurnolThetaVisibility a p : ℝ) : ℂ)]

theorem primeBurnolThetaBlock_neg_mul (a : ℝ) (p : Nat.Primes) :
    primeBurnolThetaBlock (-a) p * primeBurnolThetaBlock a p = 1 := by
  have hpyth :
      (((primeBurnolThetaVisibility a p) ^ 2 +
        (primeBurnolThetaContrast a p) ^ 2 : ℝ) : ℂ) = 1 := by
    rw [primeBurnolThetaVisibility_sq_add_contrast_sq]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primeBurnolThetaBlock, Matrix.mul_apply, Fin.sum_univ_two,
      primeBurnolThetaVisibility_neg, primeBurnolThetaContrast_neg]
  · simpa [pow_two] using hpyth
  · ring
  · ring
  · simpa [add_comm, pow_two] using hpyth

theorem primeBurnolThetaBlock_mul_neg (a : ℝ) (p : Nat.Primes) :
    primeBurnolThetaBlock a p * primeBurnolThetaBlock (-a) p = 1 := by
  simpa only [neg_neg] using primeBurnolThetaBlock_neg_mul (-a) p

def primeBurnolThetaFrameMatrix
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) :
    Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ :=
  fun i j => if _h : i.1 = j.1 then
    primeBurnolThetaBlock a (pe i.1).1 i.2 j.2 else 0

theorem primeBurnolThetaFrameMatrix_mul
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (a b : ℝ) :
    primeBurnolThetaFrameMatrix pe a * primeBurnolThetaFrameMatrix pe b =
      fun i j => if _h : i.1 = j.1 then
        (primeBurnolThetaBlock a (pe i.1).1 *
          primeBurnolThetaBlock b (pe i.1).1) i.2 j.2 else 0 := by
  ext i j
  rcases i with ⟨i, r⟩
  rcases j with ⟨j, s⟩
  by_cases hij : i = j
  · subst j
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, primeBurnolThetaFrameMatrix,
      dite_true]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [hki]
    · simp
  · simp only [Matrix.mul_apply, Fintype.sum_prod_type, primeBurnolThetaFrameMatrix,
      hij, dite_false]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i = k
    · subst k
      simp [hij]
    · simp [hik]

theorem primeBurnolThetaFrameMatrix_neg_mul
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) :
    primeBurnolThetaFrameMatrix pe (-a) * primeBurnolThetaFrameMatrix pe a = 1 := by
  rw [primeBurnolThetaFrameMatrix_mul]
  funext i j
  by_cases h : i.1 = j.1
  · simp only [h, dite_true]
    rw [primeBurnolThetaBlock_neg_mul]
    change (if i.2 = j.2 then (1 : ℂ) else 0) =
      (if i = j then (1 : ℂ) else 0)
    simp [Prod.ext_iff, h]
  · have hij : i ≠ j := fun hij => h (congrArg Prod.fst hij)
    simp [h, hij]

theorem primeBurnolThetaFrameMatrix_mul_neg
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) :
    primeBurnolThetaFrameMatrix pe a * primeBurnolThetaFrameMatrix pe (-a) = 1 := by
  simpa only [neg_neg] using primeBurnolThetaFrameMatrix_neg_mul pe (-a)

def primeBurnolThetaFrameUnit
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) :
    (Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ)ˣ where
  val := primeBurnolThetaFrameMatrix pe a
  inv := primeBurnolThetaFrameMatrix pe (-a)
  val_inv := primeBurnolThetaFrameMatrix_mul_neg pe a
  inv_val := primeBurnolThetaFrameMatrix_neg_mul pe a

@[simp] theorem primeBurnolThetaFrameUnit_neg
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (a : ℝ) :
    primeBurnolThetaFrameUnit pe (-a) = (primeBurnolThetaFrameUnit pe a)⁻¹ := by
  apply Units.ext
  rfl

@[simp] theorem primeBurnolThetaVisibility_zero (p : Nat.Primes) :
    primeBurnolThetaVisibility 0 p = 1 := by
  simp [primeBurnolThetaVisibility, primeBurnolThetaRapidity]

@[simp] theorem primeBurnolThetaContrast_zero (p : Nat.Primes) :
    primeBurnolThetaContrast 0 p = 0 := by
  simp [primeBurnolThetaContrast, primeBurnolThetaRapidity]

@[simp] theorem primeBurnolThetaBlock_zero (p : Nat.Primes) :
    primeBurnolThetaBlock 0 p = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [primeBurnolThetaBlock]

@[simp] theorem primeBurnolThetaFrameMatrix_zero
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    primeBurnolThetaFrameMatrix pe 0 = 1 := by
  ext i j
  by_cases h : i.1 = j.1
  · rcases i with ⟨i, r⟩
    rcases j with ⟨j, s⟩
    simp only at h
    subst j
    rw [primeBurnolThetaFrameMatrix]
    simp only [dite_true]
    rw [primeBurnolThetaBlock_zero]
    change (if r = s then (1 : ℂ) else 0) =
      (if (i, r) = (i, s) then (1 : ℂ) else 0)
    simp [Prod.ext_iff]
  · have hij : i ≠ j := fun hij => h (congrArg Prod.fst hij)
    rw [primeBurnolThetaFrameMatrix]
    simp [h, hij]

@[simp] theorem primeBurnolThetaFrameUnit_zero
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) :
    primeBurnolThetaFrameUnit pe 0 = 1 := by
  apply Units.ext
  exact primeBurnolThetaFrameMatrix_zero pe

/-- Complete Burnol density acting identically on the two theta channels. -/
def primeBurnolDoubledGramUnit
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    (Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ)ˣ :=
  GeneralLinearGroup.kronecker (primeBurnolWindowGramUnit pe hpe kappa) 1

@[simp] theorem coe_primeBurnolDoubledGramUnit
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    (↑(primeBurnolDoubledGramUnit pe hpe kappa) :
      Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) =
      primeBurnolWindowGramMatrix pe kappa ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rfl

/-- Fully literal finite Burnol--theta modular holonomy. -/
def primeBurnolThetaModularHolonomy
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (a : ℝ) :
    (Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ)ˣ :=
  sourceFrameModularHolonomy (primeBurnolDoubledGramUnit pe hpe kappa)
    (primeBurnolThetaFrameUnit pe a)

@[simp] theorem primeBurnolThetaModularHolonomy_zero
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    primeBurnolThetaModularHolonomy pe hpe kappa 0 = 1 := by
  simp [primeBurnolThetaModularHolonomy, sourceFrameModularHolonomy]

theorem primeBurnolThetaModularHolonomy_neg
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (a : ℝ) :
    primeBurnolThetaModularHolonomy pe hpe kappa (-a) =
      (primeBurnolThetaFrameUnit pe a)⁻¹ *
        (primeBurnolThetaModularHolonomy pe hpe kappa a)⁻¹ *
          primeBurnolThetaFrameUnit pe a := by
  rw [primeBurnolThetaModularHolonomy, primeBurnolThetaFrameUnit_neg]
  exact sourceFrameModularHolonomy_inv _ _

theorem det_primeBurnolThetaModularHolonomy
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (a : ℝ) :
    Matrix.det
      (↑(primeBurnolThetaModularHolonomy pe hpe kappa a) :
        Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) = 1 := by
  exact det_sourceFrameModularHolonomy _ _

/-- Neutral theta polarization on the doubled finite source packet. -/
def primeBurnolThetaNeutralProjection (N : ℕ) :
    Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ :=
  (1 : Matrix (Fin N) (Fin N) ℂ) ⊗ₖ
    (modularTwoBlockCornerProjection : Matrix (Fin 2) (Fin 2) ℂ)

theorem primeBurnolThetaNeutralProjection_idempotent (N : ℕ) :
    primeBurnolThetaNeutralProjection N * primeBurnolThetaNeutralProjection N =
      primeBurnolThetaNeutralProjection N := by
  have hp :
      (modularTwoBlockCornerProjection : Matrix (Fin 2) (Fin 2) ℂ) *
          modularTwoBlockCornerProjection = modularTwoBlockCornerProjection := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [modularTwoBlockCornerProjection, Matrix.mul_apply, Fin.sum_univ_two]
  rw [primeBurnolThetaNeutralProjection, ← Matrix.mul_kronecker_mul, hp]
  simp

theorem primeBurnolDoubledGramUnit_commutes_neutral
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    (↑(primeBurnolDoubledGramUnit pe hpe kappa) :
        Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) *
        primeBurnolThetaNeutralProjection N =
      primeBurnolThetaNeutralProjection N *
        (↑(primeBurnolDoubledGramUnit pe hpe kappa) :
          Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) := by
  rw [coe_primeBurnolDoubledGramUnit, primeBurnolThetaNeutralProjection,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

theorem primeBurnolDoubledModularAction_neutral
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    sourceModularAutomorphism (primeBurnolDoubledGramUnit pe hpe kappa)
        (primeBurnolThetaNeutralProjection N) =
      primeBurnolThetaNeutralProjection N := by
  let D := primeBurnolDoubledGramUnit pe hpe kappa
  have hcomm :
      (↑D : Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) *
          primeBurnolThetaNeutralProjection N =
        primeBurnolThetaNeutralProjection N * (↑D :
          Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) :=
    primeBurnolDoubledGramUnit_commutes_neutral pe hpe kappa
  change (↑(D⁻¹) : Matrix (PrimeBurnolThetaIndex N)
      (PrimeBurnolThetaIndex N) ℂ) * primeBurnolThetaNeutralProjection N *
      (↑D : Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) = _
  rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc]
  have hinv :
      (↑(D⁻¹) : Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) *
          (↑D : Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) = 1 := by
    exact Units.inv_mul D
  rw [hinv, Matrix.one_mul]

/-- Cubic extension defect of the literal Burnol density against the literal theta frame. -/
def primeBurnolThetaCubicDefect
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (a : ℝ) :
    Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ :=
  sourceFrameCubicDefect (primeBurnolDoubledGramUnit pe hpe kappa)
    (primeBurnolThetaFrameUnit pe a) (primeBurnolThetaNeutralProjection N)

/-- Exact modular anomaly of the literal Burnol--theta cubic defect. -/
def primeBurnolThetaCubicAnomaly
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (a : ℝ) :
    Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ :=
  sourceFrameCubicAnomaly (primeBurnolDoubledGramUnit pe hpe kappa)
    (primeBurnolThetaFrameUnit pe a) (primeBurnolThetaNeutralProjection N)

theorem IsSigmaTrace.map_primeBurnolThetaCubicDefect
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (a : ℝ)
    (tau : Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ →+ ℂ)
    (htau : IsSigmaTrace
      (sourceModularAutomorphism (primeBurnolDoubledGramUnit pe hpe kappa)) tau) :
    tau (primeBurnolThetaCubicDefect pe hpe kappa a) =
      tau (primeBurnolThetaCubicAnomaly pe hpe kappa a) := by
  exact htau.map_sourceFrameCubicDefect _ _ _
    (primeBurnolThetaNeutralProjection_idempotent N) tau

@[simp] theorem primeBurnolThetaCubicDefect_zero
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    primeBurnolThetaCubicDefect pe hpe kappa 0 = 0 := by
  rw [primeBurnolThetaCubicDefect, primeBurnolThetaFrameUnit_zero]
  apply sourceFrameCubicDefect_eq_zero_of_central
  · simp
  · exact primeBurnolDoubledModularAction_neutral pe hpe kappa

/-- **Exact source--archimedean fusion law.** Each matrix entry of the source/frame commutator is
the literal Burnol covariance edge times the difference of the two local theta blocks. Thus only
cross-source edges joining different archimedean rapidities can generate finite holonomy. -/
theorem primeBurnolDoubledGram_thetaFrame_commutator_apply
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) (a : ℝ) (i j : Fin N) (r s : Fin 2) :
    (((↑(primeBurnolDoubledGramUnit pe hpe kappa) :
          Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) *
        (↑(primeBurnolThetaFrameUnit pe a) :
          Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ)) -
      ((↑(primeBurnolThetaFrameUnit pe a) :
          Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) *
        (↑(primeBurnolDoubledGramUnit pe hpe kappa) :
          Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ)))
        (i, r) (j, s) =
      primeBurnolWindowGramMatrix pe kappa i j *
        (primeBurnolThetaBlock a (pe j).1 r s -
          primeBurnolThetaBlock a (pe i).1 r s) := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    coe_primeBurnolDoubledGramUnit, Matrix.kronecker_apply,
    primeBurnolThetaFrameUnit, primeBurnolThetaFrameMatrix]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp [Matrix.one_apply]
      ring
    · intro k _ hki
      simp [hki.symm]
    · simp
  · intro k _ hkj
    simp [hkj]
  · simp

/-- Distinct primes acquire distinct theta contrasts at every nonneutral grade. -/
theorem primeBurnolThetaContrast_ne_of_prime_ne
    {a : ℝ} (ha : a ≠ 0) {p q : Nat.Primes} (hpq : p ≠ q) :
    primeBurnolThetaContrast a p ≠ primeBurnolThetaContrast a q := by
  intro hcontrast
  have hrapid : primeBurnolThetaRapidity a p = primeBurnolThetaRapidity a q :=
    HTGeometry.tanh_strictMono.injective hcontrast
  have hmul : a * Real.log (p : ℝ) = a * Real.log (q : ℝ) := by
    dsimp [primeBurnolThetaRapidity] at hrapid
    linarith
  have hlog : Real.log (p : ℝ) = Real.log (q : ℝ) := by
    exact (mul_left_cancel₀ ha) hmul
  apply hpq
  apply Subtype.ext
  exact_mod_cast Real.log_injOn_pos
    (Set.mem_Ioi.mpr (by exact_mod_cast p.property.pos))
    (Set.mem_Ioi.mpr (by exact_mod_cast q.property.pos)) hlog

/-- One nonzero literal cross-prime Burnol edge forces source density and theta frame not to
commute at every nonneutral grade. -/
theorem primeBurnolDoubledGram_thetaFrame_ne_commute_of_offDiagonal
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) {a : ℝ} (ha : a ≠ 0) (i j : Fin N)
    (hp : (pe i).1 ≠ (pe j).1)
    (hgram : primeBurnolWindowGramMatrix pe kappa i j ≠ 0) :
    (↑(primeBurnolDoubledGramUnit pe hpe kappa) :
        Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) *
        (↑(primeBurnolThetaFrameUnit pe a) :
          Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) ≠
      (↑(primeBurnolThetaFrameUnit pe a) :
        Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) *
        (↑(primeBurnolDoubledGramUnit pe hpe kappa) :
          Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) := by
  intro hcomm
  have hzero :
      ((((↑(primeBurnolDoubledGramUnit pe hpe kappa) :
            Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) *
          (↑(primeBurnolThetaFrameUnit pe a) :
            Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ)) -
        ((↑(primeBurnolThetaFrameUnit pe a) :
            Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ) *
          (↑(primeBurnolDoubledGramUnit pe hpe kappa) :
            Matrix (PrimeBurnolThetaIndex N) (PrimeBurnolThetaIndex N) ℂ)))
          (i, (1 : Fin 2)) (j, (0 : Fin 2))) = 0 := by
    rw [hcomm, sub_self]
    rfl
  rw [primeBurnolDoubledGram_thetaFrame_commutator_apply] at hzero
  have hcontrast :
      (primeBurnolThetaContrast a (pe j).1 : ℂ) ≠
        (primeBurnolThetaContrast a (pe i).1 : ℂ) := by
    exact_mod_cast primeBurnolThetaContrast_ne_of_prime_ne ha hp.symm
  apply (mul_ne_zero hgram (sub_ne_zero.mpr hcontrast)) hzero

/-- One nonzero cross-prime Burnol edge makes the finite source--theta holonomy nontrivial at every
nonneutral grade. -/
theorem primeBurnolThetaModularHolonomy_ne_one_of_offDiagonal
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) {a : ℝ} (ha : a ≠ 0) (i j : Fin N)
    (hp : (pe i).1 ≠ (pe j).1)
    (hgram : primeBurnolWindowGramMatrix pe kappa i j ≠ 0) :
    primeBurnolThetaModularHolonomy pe hpe kappa a ≠ 1 := by
  intro hhol
  have hunit := (GaloisForLFunctions.HTGeometry.sourceFrameModularHolonomy_eq_one_iff
    (primeBurnolDoubledGramUnit pe hpe kappa) (primeBurnolThetaFrameUnit pe a)).1 hhol
  have hmatrix := congrArg Units.val hunit
  exact primeBurnolDoubledGram_thetaFrame_ne_commute_of_offDiagonal
    pe hpe kappa ha i j hp hgram hmatrix

/-- **Off-neutral finite faithfulness.** Any finite literal packet containing two distinct primes
has nontrivial Burnol--theta holonomy at every nonneutral grade. -/
theorem primeBurnolThetaModularHolonomy_ne_one
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) {a : ℝ} (ha : a ≠ 0) (i j : Fin N)
    (hp : (pe i).1 ≠ (pe j).1) :
    primeBurnolThetaModularHolonomy pe hpe kappa a ≠ 1 := by
  exact primeBurnolThetaModularHolonomy_ne_one_of_offDiagonal
    pe hpe kappa ha i j hp (primeBurnolWindowGramMatrix_apply_ne_zero pe kappa i j)

end

end RHTower
