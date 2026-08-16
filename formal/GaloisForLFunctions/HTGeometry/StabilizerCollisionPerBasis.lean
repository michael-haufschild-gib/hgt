import GaloisForLFunctions.HTGeometry.StabilizerProjectorExpansion
import GaloisForLFunctions.HTGeometry.StabilizerSignOrthogonality
import GaloisForLFunctions.HTGeometry.SpectralCollisionFunctional

/-!
# The sign-averaged collision of one commuting family

Averaging the squared diagonal of a stabilizer projector over the sign patterns of a fixed
commuting family kills all cross terms, leaving the average over the span of the family of the
squared Pauli diagonals.  Parseval for the Pauli basis totals those squares at a unit state.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Diagonal

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The diagonal entry of a matrix in a state. -/
def matDiag (A : Matrix α α ℂ) (ψ : α → ℂ) : ℂ := finiteComplexInner ψ (A *ᵥ ψ)

theorem matDiag_add (A B : Matrix α α ℂ) (ψ : α → ℂ) :
    matDiag (A + B) ψ = matDiag A ψ + matDiag B ψ := by
  simp only [matDiag, Matrix.add_mulVec, finiteComplexInner, Pi.add_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem matDiag_zero (ψ : α → ℂ) : matDiag (0 : Matrix α α ℂ) ψ = 0 := by
  simp [matDiag, finiteComplexInner]

theorem matDiag_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix α α ℂ) (ψ : α → ℂ) :
    matDiag (∑ p ∈ s, A p) ψ = ∑ p ∈ s, matDiag (A p) ψ := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, matDiag_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, matDiag_add, ih]

theorem mulVec_apply' (A : Matrix α α ℂ) (ψ : α → ℂ) (x : α) :
    (A *ᵥ ψ) x = ∑ y, A x y * ψ y := rfl

theorem matDiag_smul (c : ℂ) (A : Matrix α α ℂ) (ψ : α → ℂ) :
    matDiag (c • A) ψ = c * matDiag A ψ := by
  simp only [matDiag, finiteComplexInner, mulVec_apply', Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem matDiag_one (ψ : α → ℂ) : matDiag (1 : Matrix α α ℂ) ψ = finiteComplexInner ψ ψ := by
  rw [matDiag, Matrix.one_mulVec]

/-- The rank-one matrix of a state. -/
def rankOneMat (ψ : α → ℂ) : Matrix α α ℂ := fun a b => (starRingEnd ℂ) (ψ b) * ψ a

theorem trace_star_mul_rankOneMat {A : Matrix α α ℂ} (hA : A.IsHermitian) (ψ : α → ℂ) :
    Matrix.trace (star A * rankOneMat ψ) = matDiag A ψ := by
  simp only [Matrix.trace, Matrix.diag_apply, matDiag, finiteComplexInner, Matrix.mul_apply,
    mulVec_apply']
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hherm : (starRingEnd ℂ) (A y x) = A x y := by
    have h := congrFun (congrFun hA x) y
    rwa [Matrix.conjTranspose_apply] at h
  have hstar : (star A) x y = (starRingEnd ℂ) (A y x) := rfl
  rw [hstar, hherm]
  show A x y * ((starRingEnd ℂ) (ψ x) * ψ y) = (starRingEnd ℂ) (ψ x) * (A x y * ψ y)
  ring

theorem frobSq_rankOneMat (ψ : α → ℂ) (hψ : (∑ x, ‖ψ x‖ ^ 2) = 1) :
    frobSq (rankOneMat ψ) = 1 := by
  have hterm : ∀ a b : α, ‖rankOneMat ψ a b‖ ^ 2 = ‖ψ b‖ ^ 2 * ‖ψ a‖ ^ 2 := by
    intro a b
    rw [rankOneMat, norm_mul, Complex.norm_conj, mul_pow]
  calc frobSq (rankOneMat ψ) = ∑ a, ∑ b, ‖ψ b‖ ^ 2 * ‖ψ a‖ ^ 2 := by
        rw [frobSq]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b
    _ = ∑ a, (∑ b, ‖ψ b‖ ^ 2) * ‖ψ a‖ ^ 2 := by
        exact Finset.sum_congr rfl fun a _ => (Finset.sum_mul _ _ _).symm
    _ = 1 := by
        simp only [hψ, one_mul]

theorem conj_matDiag {A : Matrix α α ℂ} (hA : A.IsHermitian) (ψ : α → ℂ) :
    (starRingEnd ℂ) (matDiag A ψ) = matDiag A ψ := by
  have hherm : ∀ x y : α, (starRingEnd ℂ) (A y x) = A x y := by
    intro x y
    have h := congrFun (congrFun hA x) y
    rwa [Matrix.conjTranspose_apply] at h
  simp only [matDiag, finiteComplexInner, mulVec_apply', map_sum, map_mul, Complex.conj_conj,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hherm x y]
  ring

theorem matDiag_sq {A : Matrix α α ℂ} (hA : A.IsHermitian) (ψ : α → ℂ) :
    (matDiag A ψ) ^ 2 = ((‖matDiag A ψ‖ ^ 2 : ℝ) : ℂ) := by
  have hmc := Complex.mul_conj (matDiag A ψ)
  rw [conj_matDiag hA] at hmc
  rw [← sq] at hmc
  rw [hmc, ← Complex.sq_norm]

end Diagonal

section Parseval

variable {n : ℕ}

theorem bijective_pauliOf : Function.Bijective (pauliOf (n := n)) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨pauliOf_injective, ?_⟩
  rw [card_pauliSymp']
  simp

/-- **Parseval over Pauli labels at a unit state.** -/
theorem sum_matDiag_pauliMat_sq (ψ : FiniteQubitConfiguration (Fin n) → ℂ)
    (hψ : (∑ x, ‖ψ x‖ ^ 2) = 1) :
    (∑ v : PauliSymp n, (matDiag (pauliMat v) ψ) ^ 2) = (2 : ℂ) ^ n := by
  classical
  have hherm : ∀ v : PauliSymp n, (pauliMat v).IsHermitian := fun v =>
    finitePauliMatrix_isHermitian _
  have hsq : ∀ v : PauliSymp n,
      (matDiag (pauliMat v) ψ) ^ 2 = ((‖matDiag (pauliMat v) ψ‖ ^ 2 : ℝ) : ℂ) :=
    fun v => matDiag_sq (hherm v) ψ
  have hreal : (∑ v : PauliSymp n, ‖matDiag (pauliMat v) ψ‖ ^ 2) = (2 : ℝ) ^ n := by
    have hbij := bijective_pauliOf (n := n)
    have hterm : ∀ v : PauliSymp n,
        ‖matDiag (pauliMat v) ψ‖ ^ 2 =
          ‖Matrix.trace (star (pauliMat v) * rankOneMat ψ)‖ ^ 2 := by
      intro v
      rw [trace_star_mul_rankOneMat (hherm v) ψ]
    have hbijsum : (∑ v : PauliSymp n, ‖Matrix.trace (star (pauliMat v) * rankOneMat ψ)‖ ^ 2) =
        ∑ P : Fin n → Option (Fin 3),
          ‖Matrix.trace (star (finitePauliMatrix P) * rankOneMat ψ)‖ ^ 2 :=
      Fintype.sum_bijective (pauliOf (n := n)) hbij _ _ fun v => rfl
    rw [Finset.sum_congr rfl fun v _ => hterm v, hbijsum,
      sum_normSq_trace_star_pauli_mul, frobSq_rankOneMat ψ hψ, mul_one, Fintype.card_fin]
  calc (∑ v : PauliSymp n, (matDiag (pauliMat v) ψ) ^ 2)
      = ∑ v : PauliSymp n, ((‖matDiag (pauliMat v) ψ‖ ^ 2 : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun v _ => hsq v
    _ = (((∑ v : PauliSymp n, ‖matDiag (pauliMat v) ψ‖ ^ 2 : ℝ)) : ℂ) := by
        rw [Complex.ofReal_sum]
    _ = (2 : ℂ) ^ n := by
        rw [hreal]
        norm_num

end Parseval

section PerBasis

variable {n : ℕ} {b : Fin n → PauliSymp n}

/-- **The diagonal of a stabilizer projector.** -/
theorem matDiag_stabProjector (hb : ∀ i j, symForm (b i) (b j) = 0) (ε : Fin n → ZMod 2)
    (ψ : FiniteQubitConfiguration (Fin n) → ℂ) :
    matDiag (stabProjector b hb ε) ψ =
      ((2 : ℂ) ^ n)⁻¹ * ∑ S : Finset (Fin n),
        signOf (∑ i ∈ S, ε i) * stabSign b hb S * matDiag (pauliMat (labSum b S)) ψ := by
  classical
  rw [stabProjector_eq_smul_expansion, matDiag_smul, matDiag_sum]
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [stabProd_eq_smul, smul_smul, matDiag_smul]

/-- **The sign average of the squared diagonal.** -/
theorem sum_sign_matDiag_sq (hb : ∀ i j, symForm (b i) (b j) = 0)
    (ψ : FiniteQubitConfiguration (Fin n) → ℂ) :
    (∑ ε : Fin n → ZMod 2, (matDiag (stabProjector b hb ε) ψ) ^ 2) =
      ((2 : ℂ) ^ n)⁻¹ * ∑ S : Finset (Fin n), (matDiag (pauliMat (labSum b S)) ψ) ^ 2 := by
  classical
  have hpow : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n two_ne_zero
  have hexp : ∀ ε : Fin n → ZMod 2, (matDiag (stabProjector b hb ε) ψ) ^ 2 =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        (((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹) *
          ((signOf (∑ i ∈ S, ε i) * signOf (∑ i ∈ T, ε i)) *
            (stabSign b hb S * stabSign b hb T *
              (matDiag (pauliMat (labSum b S)) ψ * matDiag (pauliMat (labSum b T)) ψ))) := by
    intro ε
    rw [matDiag_stabProjector, mul_pow, sq (∑ S : Finset (Fin n), _), Finset.sum_mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => by ring
  rw [Finset.sum_congr rfl fun ε _ => hexp ε]
  have hswap : (∑ ε : Fin n → ZMod 2, ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
      (((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹) *
        ((signOf (∑ i ∈ S, ε i) * signOf (∑ i ∈ T, ε i)) *
          (stabSign b hb S * stabSign b hb T *
            (matDiag (pauliMat (labSum b S)) ψ * matDiag (pauliMat (labSum b T)) ψ)))) =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n), ∑ ε : Fin n → ZMod 2,
        (((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹) *
          ((signOf (∑ i ∈ S, ε i) * signOf (∑ i ∈ T, ε i)) *
            (stabSign b hb S * stabSign b hb T *
              (matDiag (pauliMat (labSum b S)) ψ * matDiag (pauliMat (labSum b T)) ψ))) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun S _ => Finset.sum_comm
  rw [hswap]
  have hinner : ∀ S T : Finset (Fin n),
      (∑ ε : Fin n → ZMod 2,
        (((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹) *
          ((signOf (∑ i ∈ S, ε i) * signOf (∑ i ∈ T, ε i)) *
            (stabSign b hb S * stabSign b hb T *
              (matDiag (pauliMat (labSum b S)) ψ * matDiag (pauliMat (labSum b T)) ψ)))) =
      (if S = T then ((2 : ℂ) ^ n)⁻¹ * (matDiag (pauliMat (labSum b S)) ψ) ^ 2 else 0) := by
    intro S T
    have hfac : (∑ ε : Fin n → ZMod 2,
        (((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹) *
          ((signOf (∑ i ∈ S, ε i) * signOf (∑ i ∈ T, ε i)) *
            (stabSign b hb S * stabSign b hb T *
              (matDiag (pauliMat (labSum b S)) ψ * matDiag (pauliMat (labSum b T)) ψ)))) =
        (∑ ε : Fin n → ZMod 2, signOf (∑ i ∈ S, ε i) * signOf (∑ i ∈ T, ε i)) *
          ((((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹) *
            (stabSign b hb S * stabSign b hb T *
              (matDiag (pauliMat (labSum b S)) ψ * matDiag (pauliMat (labSum b T)) ψ))) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun ε _ => by ring
    rw [hfac, sum_signOf_subsetSum_mul]
    by_cases hST : S = T
    · subst hST
      rw [if_pos rfl, if_pos rfl]
      have hs := stabSign_sq hb S
      have hcancel : ((2 : ℂ) ^ n) * (((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹) =
          ((2 : ℂ) ^ n)⁻¹ := by
        field_simp
      calc ((2 : ℂ) ^ n) * (((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹ *
            (stabSign b hb S * stabSign b hb S *
              (matDiag (pauliMat (labSum b S)) ψ * matDiag (pauliMat (labSum b S)) ψ)))
          = (((2 : ℂ) ^ n) * (((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹)) *
              ((stabSign b hb S * stabSign b hb S) *
                (matDiag (pauliMat (labSum b S)) ψ * matDiag (pauliMat (labSum b S)) ψ)) := by
            ring
        _ = ((2 : ℂ) ^ n)⁻¹ * (1 * (matDiag (pauliMat (labSum b S)) ψ *
              matDiag (pauliMat (labSum b S)) ψ)) := by rw [hcancel, hs]
        _ = ((2 : ℂ) ^ n)⁻¹ * (matDiag (pauliMat (labSum b S)) ψ) ^ 2 := by ring
    · rw [if_neg hST, if_neg hST, zero_mul]
  rw [Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => hinner S T]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ S)]

/-- **The subset sum is the span sum.** -/
theorem sum_labSum_eq_sum_span (hbasis : IsLagrBasis b)
    (f : PauliSymp n → ℂ) :
    (∑ S : Finset (Fin n), f (labSum b S)) = ∑ v ∈ spanOf b, f v := by
  classical
  rw [spanOf, Finset.sum_image fun S hS T hT hST =>
    injOn_subsetSum hbasis (Finset.mem_coe.mpr hS) (Finset.mem_coe.mpr hT) hST]
  rfl

end PerBasis

end GaloisForLFunctions.HTGeometry
