import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneOperations

/-! The special parameter has a diagonal unramified Weil action
and monodromy given by the shift along its ordered basis. -/

noncomputable section

open NumberField IsDedekindDomain Module
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/-- The shift towards increasing indices, with zero in the first coordinate. -/
def specialShift (n : ℕ) : End ℂ (Fin n → ℂ) where
  toFun v i := if hi : 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0
  map_add' v u := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]
  map_smul' c v := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]

theorem specialShift_apply {n : ℕ} (v : Fin n → ℂ) (i : Fin n) :
    specialShift n v i = if hi : 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0 := rfl

theorem specialShift_pow_apply {n : ℕ} (k : ℕ) (v : Fin n → ℂ) (i : Fin n) :
    (specialShift n ^ k) v i = if hi : k ≤ (i : ℕ) then v ⟨i - k, by omega⟩ else 0 := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', End.mul_apply, specialShift_apply]
    by_cases h1 : 1 ≤ (i : ℕ)
    · rw [dif_pos h1, ih]
      by_cases h2 : k + 1 ≤ (i : ℕ)
      · rw [dif_pos h2, dif_pos (by simp only; omega)]
        congr 2
        simp only; omega
      · rw [dif_neg h2, dif_neg (by simp only; omega)]
    · rw [dif_neg h1, dif_neg (by omega)]

theorem isNilpotent_specialShift (n : ℕ) : IsNilpotent (specialShift n) :=
  ⟨n, LinearMap.ext fun v => funext fun i => by
    rw [specialShift_pow_apply, dif_neg (by omega)]; rfl⟩

/-- The ordered Frobenius eigenvalues of the centered special parameter. -/
def specialEigenvalue (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (i : Fin n) : ℂˣ :=
  qPow w ((i.val : ℝ) - ((n : ℝ) - 1) / 2)

/-- The length `n` special parameter, with one monodromy string. -/
def WDRep.sp (h : IsPlaceOver A w) (n : ℕ) : WDRep h (Fin n → ℂ) where
  ρ := (diag (h := h) (specialEigenvalue w n)).ρ
  N := specialShift n
  smooth := (diag (h := h) _).smooth
  semisimple σ := (diag (h := h) _).semisimple σ
  nilpotent := isNilpotent_specialShift n
  comm σ := LinearMap.ext fun v => funext fun i => by
    simp only [End.mul_apply, diag_ρ_apply, LinearMap.smul_apply, Pi.smul_apply,
      specialShift_apply, smul_eq_mul]
    split_ifs with hi
    · have he : (specialEigenvalue w n i : ℂ) = ((normV w : ℕ) : ℂ) *
          specialEigenvalue w n ⟨i.val - 1, by omega⟩ := by
        rw [← coe_qPow_one, specialEigenvalue, specialEigenvalue, ← Units.val_mul, ← qPow_add]
        congr 2
        simp only [Nat.cast_sub hi, Nat.cast_one]
        ring
      rw [he, mul_zpow, mul_assoc]
    · simp

@[simp] theorem WDRep.sp_ρ_apply (n : ℕ) (σ : Weil h) (v : Fin n → ℂ) (i : Fin n) :
    (sp h n).ρ σ v i = (specialEigenvalue w n i : ℂ) ^ deg σ * v i := diag_ρ_apply _ _ _ _

@[simp] theorem WDRep.sp_N (n : ℕ) : (sp h n).N = specialShift n := rfl

def WD.lpSp (n : ℕ) : WD h := WD.mk (WDRep.sp h n)

theorem WD.lpDim_sp (n : ℕ) : (lpSp (h := h) n).lpDim = n := by
  rw [lpSp, lpDim_mk, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]


end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WDRep.sp
