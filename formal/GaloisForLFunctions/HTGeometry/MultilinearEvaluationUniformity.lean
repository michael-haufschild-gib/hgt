import GaloisForLFunctions.HTGeometry.ReedMullerEvaluationRank

/-!
# Uniformity of low-degree multilinear evaluation modulo eight

Surjectivity of the degree-at-most-`m` multilinear evaluation map over `ZMod 2` lifts to `ZMod 8`:
a coefficient vector correct modulo two leaves a remainder divisible by two, and three corrections
exhaust the ring because `8 = 0`.  A surjective homomorphism of finite additive groups has fibres of
constant size, so the evaluation vector of a uniformly random coefficient vector is uniform on
`(ZMod 8)^k` whenever the `k < 2^(m+1)` Boolean evaluation points are distinct.
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Lift

/-- Reduction of coefficients modulo two. -/
def redEight_multilinearEvaluationUniformity : ZMod 8 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

theorem redEight_eq_zero_imp : ∀ z : ZMod 8, redEight_multilinearEvaluationUniformity z = 0 → ∃ t : ZMod 8, z = 2 * t := by
  decide

/-- Lift a modulo-two coefficient vector to a modulo-eight coefficient vector. -/
def liftEight {m : ℕ} (c : MonLe ι m → ZMod 2) : MonLe ι m → ZMod 8 :=
  fun S => ((c S).val : ZMod 8)

theorem redEight_liftEight {m : ℕ} (c : MonLe ι m → ZMod 2) (S : MonLe ι m) :
    redEight_multilinearEvaluationUniformity (liftEight c S) = c S := by
  rw [liftEight, redEight_multilinearEvaluationUniformity, map_natCast]
  exact ZMod.natCast_rightInverse (c S)

theorem redEight_evalMatrix {k m : ℕ} (x : Fin k → (ι → Bool)) (j : Fin k) (S : MonLe ι m) :
    redEight_multilinearEvaluationUniformity (reedMullerEvalMatrix (ZMod 8) m x j S) = reedMullerEvalMatrix (ZMod 2) m x j S := by
  rw [reedMullerEvalMatrix, reedMullerEvalMatrix, apply_ite redEight_multilinearEvaluationUniformity, map_one, map_zero]

theorem redEight_mulVec_liftEight {k m : ℕ} (x : Fin k → (ι → Bool))
    (c : MonLe ι m → ZMod 2) (j : Fin k) :
    redEight_multilinearEvaluationUniformity ((reedMullerEvalMatrix (ZMod 8) m x *ᵥ liftEight c) j) =
      (reedMullerEvalMatrix (ZMod 2) m x *ᵥ c) j := by
  show redEight_multilinearEvaluationUniformity (∑ S, reedMullerEvalMatrix (ZMod 8) m x j S * liftEight c S) =
    ∑ S, reedMullerEvalMatrix (ZMod 2) m x j S * c S
  rw [map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_mul, redEight_evalMatrix, redEight_liftEight]

/-- One correction step: every value vector agrees with an evaluation vector modulo two. -/
theorem exists_mulVec_add_two_smul_multilinearEvaluationUniformity {k m : ℕ} (hk : k < 2 ^ (m + 1))
    (x : Fin k → (ι → Bool)) (hx : Function.Injective x) (w : Fin k → ZMod 8) :
    ∃ (c : MonLe ι m → ZMod 8) (v : Fin k → ZMod 8),
      w = reedMullerEvalMatrix (ZMod 8) m x *ᵥ c + (2 : ZMod 8) • v := by
  classical
  obtain ⟨cbar, hcbar⟩ := surjective_mulVec_evalMatrix hk x hx (fun j => redEight_multilinearEvaluationUniformity (w j))
  have hcbar' : ∀ j, (reedMullerEvalMatrix (ZMod 2) m x *ᵥ cbar) j = redEight_multilinearEvaluationUniformity (w j) := congrFun hcbar
  have hred : ∀ j, redEight_multilinearEvaluationUniformity (w j - (reedMullerEvalMatrix (ZMod 8) m x *ᵥ liftEight cbar) j) = 0 := by
    intro j
    rw [map_sub, redEight_mulVec_liftEight, hcbar' j, sub_self]
  choose v hv using fun j => redEight_eq_zero_imp _ (hred j)
  refine ⟨liftEight cbar, v, funext fun j => ?_⟩
  have := hv j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination this

/-- **Surjectivity of low-degree multilinear evaluation over `ZMod 8`.** -/
theorem surjective_mulVec_evalMatrix_eight {k m : ℕ} (hk : k < 2 ^ (m + 1))
    (x : Fin k → (ι → Bool)) (hx : Function.Injective x) :
    Function.Surjective fun c : MonLe ι m → ZMod 8 => (reedMullerEvalMatrix (ZMod 8) m x) *ᵥ c := by
  classical
  intro w
  obtain ⟨c₁, v₁, h₁⟩ := exists_mulVec_add_two_smul_multilinearEvaluationUniformity hk x hx w
  obtain ⟨c₂, v₂, h₂⟩ := exists_mulVec_add_two_smul_multilinearEvaluationUniformity hk x hx v₁
  obtain ⟨c₃, v₃, h₃⟩ := exists_mulVec_add_two_smul_multilinearEvaluationUniformity hk x hx v₂
  refine ⟨c₁ + (2 : ZMod 8) • c₂ + (4 : ZMod 8) • c₃, funext fun j => ?_⟩
  have e₁ := congrFun h₁ j
  have e₂ := congrFun h₂ j
  have e₃ := congrFun h₃ j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e₁ e₂ e₃
  have hlin : (reedMullerEvalMatrix (ZMod 8) m x *ᵥ (c₁ + (2 : ZMod 8) • c₂ + (4 : ZMod 8) • c₃)) j =
      (reedMullerEvalMatrix (ZMod 8) m x *ᵥ c₁) j + 2 * (reedMullerEvalMatrix (ZMod 8) m x *ᵥ c₂) j +
        4 * (reedMullerEvalMatrix (ZMod 8) m x *ᵥ c₃) j := by
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp [smul_eq_mul]
  show (reedMullerEvalMatrix (ZMod 8) m x *ᵥ (c₁ + (2 : ZMod 8) • c₂ + (4 : ZMod 8) • c₃)) j = w j
  rw [hlin]
  have h8 : (8 : ZMod 8) = 0 := by decide
  linear_combination -e₁ - 2 * e₂ - 4 * e₃ - v₃ j * h8

end Lift

section Uniformity

variable {k m : ℕ}

/-- **Constant fibres.**  Every value vector has as many coefficient preimages as the zero vector. -/
theorem card_fiber_mulVec_evalMatrix_eq (hk : k < 2 ^ (m + 1)) (x : Fin k → (ι → Bool))
    (hx : Function.Injective x) (w : Fin k → ZMod 8) :
    (Finset.univ.filter fun c : MonLe ι m → ZMod 8 =>
        reedMullerEvalMatrix (ZMod 8) m x *ᵥ c = w).card =
      (Finset.univ.filter fun c : MonLe ι m → ZMod 8 =>
        reedMullerEvalMatrix (ZMod 8) m x *ᵥ c = 0).card := by
  classical
  obtain ⟨c₀, hc₀⟩ := surjective_mulVec_evalMatrix_eight hk x hx w
  have hc₀' : reedMullerEvalMatrix (ZMod 8) m x *ᵥ c₀ = w := hc₀
  have himg : (Finset.univ.filter fun c : MonLe ι m → ZMod 8 =>
      reedMullerEvalMatrix (ZMod 8) m x *ᵥ c = 0).image (fun c => c + c₀) =
      Finset.univ.filter fun c : MonLe ι m → ZMod 8 => reedMullerEvalMatrix (ZMod 8) m x *ᵥ c = w := by
    ext d
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [Matrix.mulVec_add, hc, hc₀', zero_add]
    · intro hd
      refine ⟨d - c₀, ?_, by abel⟩
      rw [Matrix.mulVec_sub, hd, hc₀', sub_self]
  rw [← himg, Finset.card_image_of_injective _ (add_left_injective c₀)]

/-- **Uniformity of the evaluation vector.**  For every test function on value vectors, the sum over
coefficient families is a fixed multiple of the sum over `(ZMod 8)^k`. -/
theorem sum_comp_mulVec_evalMatrix (hk : k < 2 ^ (m + 1)) (x : Fin k → (ι → Bool))
    (hx : Function.Injective x) {M : Type*} [AddCommMonoid M] (F : (Fin k → ZMod 8) → M) :
    (∑ c : MonLe ι m → ZMod 8, F (reedMullerEvalMatrix (ZMod 8) m x *ᵥ c)) =
      (Finset.univ.filter fun c : MonLe ι m → ZMod 8 =>
        reedMullerEvalMatrix (ZMod 8) m x *ᵥ c = 0).card • ∑ w : Fin k → ZMod 8, F w := by
  classical
  have himg : (Finset.univ.image fun c : MonLe ι m → ZMod 8 =>
      reedMullerEvalMatrix (ZMod 8) m x *ᵥ c) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun w => ?_
    obtain ⟨c, hc⟩ := surjective_mulVec_evalMatrix_eight hk x hx w
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩
  rw [Finset.sum_comp, himg, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [card_fiber_mulVec_evalMatrix_eq hk x hx w]

end Uniformity

end GaloisForLFunctions.HTGeometry
