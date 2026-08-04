import GaloisForLFunctions.HTGeometry.ExponentialTowerUnitCost
import GaloisForLFunctions.HTGeometry.PolynomialCascadeModel

/-!
# Exponential cascades with arbitrary linear parts

The cascade built from `f_k(w) = exp(a_k w + b_k)` has the derivative law
`δ Y_{k+1} = a_k·Y_{k+1}·δ Y_k`, so its model derivation sends the `k`-th variable to the tower
monomial scaled by `∏_{j<k} a_j`.  The shifts `b_k` never appear.

That model is the tower's, conjugated by the scaling automorphism `X_k ↦ a_k X_k` and rescaled by
`a_0`.  Since conjugation and scaling only multiply determinants by nonzero constants, the tower's
observability determinant transports, and no induction has to be redone.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The accumulated scale of a scaled exponential cascade. -/
noncomputable def scaleWeight (a : ℕ → ℂ) (k : ℕ) : ℂ := ∏ j ∈ Finset.range k, a j

@[simp] theorem scaleWeight_zero (a : ℕ → ℂ) : scaleWeight a 0 = 1 := by
  simp [scaleWeight]

theorem scaleWeight_succ (a : ℕ → ℂ) (k : ℕ) :
    scaleWeight a (k + 1) = scaleWeight a k * a k := by
  rw [scaleWeight, scaleWeight, Finset.prod_range_succ]

/-- The model derivation of a scaled exponential cascade. -/
noncomputable def scaledDerivation (a : ℕ → ℂ) :
    Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) :=
  MvPolynomial.mkDerivation ℂ fun k => MvPolynomial.C (scaleWeight a k) * towerMonomial k

@[simp] theorem scaledDerivation_X (a : ℕ → ℂ) (k : ℕ) :
    scaledDerivation a (MvPolynomial.X k)
      = MvPolynomial.C (scaleWeight a k) * towerMonomial k :=
  MvPolynomial.mkDerivation_X ℂ _ k

/-- The scaling automorphism of the model. -/
noncomputable def scaleHom (a : ℕ → ℂ) : MvPolynomial ℕ ℂ →ₐ[ℂ] MvPolynomial ℕ ℂ :=
  MvPolynomial.aeval fun k => MvPolynomial.C (a k) * MvPolynomial.X k

@[simp] theorem scaleHom_C (a : ℕ → ℂ) (c : ℂ) :
    scaleHom a (MvPolynomial.C c) = MvPolynomial.C c := MvPolynomial.aeval_C _ _

@[simp] theorem scaleHom_X (a : ℕ → ℂ) (k : ℕ) :
    scaleHom a (MvPolynomial.X k) = MvPolynomial.C (a k) * MvPolynomial.X k := by
  simp [scaleHom]

theorem scaleHom_injective {a : ℕ → ℂ} (ha : ∀ k, a k ≠ 0) :
    Function.Injective (scaleHom a) := by
  have hcomp : (scaleHom (fun k => (a k)⁻¹)).comp (scaleHom a) = AlgHom.id ℂ (MvPolynomial ℕ ℂ) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, scaleHom_X, map_mul, scaleHom_C, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (ha k), map_one, one_mul]
  intro x y hxy
  have := congrArg (scaleHom (fun k => (a k)⁻¹)) hxy
  rw [show (scaleHom (fun k => (a k)⁻¹)) (scaleHom a x)
      = ((scaleHom (fun k => (a k)⁻¹)).comp (scaleHom a)) x from rfl,
    show (scaleHom (fun k => (a k)⁻¹)) (scaleHom a y)
      = ((scaleHom (fun k => (a k)⁻¹)).comp (scaleHom a)) y from rfl, hcomp] at this
  simpa using this

/-- The scaling automorphism on a tower monomial. -/
theorem scaleHom_towerMonomial (a : ℕ → ℂ) (k : ℕ) :
    scaleHom a (towerMonomial k)
      = MvPolynomial.C (∏ j ∈ Finset.Icc 1 k, a j) * towerMonomial k := by
  induction k with
  | zero => simp [towerMonomial]
  | succ k ih =>
      rw [towerMonomial_succ, map_mul, ih, scaleHom_X,
        Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
      simp only [map_mul]
      ring

/-- The weight identity behind the conjugation. -/
theorem scale_weight_identity (a : ℕ → ℂ) (k : ℕ) :
    a k * scaleWeight a k = a 0 * ∏ j ∈ Finset.Icc 1 k, a j := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [scaleWeight_succ, Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
      calc a (k + 1) * (scaleWeight a k * a k)
          = (a k * scaleWeight a k) * a (k + 1) := by ring
        _ = (a 0 * ∏ j ∈ Finset.Icc 1 k, a j) * a (k + 1) := by rw [ih]
        _ = a 0 * ((∏ j ∈ Finset.Icc 1 k, a j) * a (k + 1)) := by ring

theorem scaledDerivation_C_mul (a : ℕ → ℂ) (c : ℂ) (P : MvPolynomial ℕ ℂ) :
    scaledDerivation a (MvPolynomial.C c * P) = MvPolynomial.C c * scaledDerivation a P := by
  rw [← MvPolynomial.smul_eq_C_mul, ← MvPolynomial.smul_eq_C_mul]
  simp

/-- **The conjugation identity.**  The scaled model derivation is the tower's, conjugated by the
scaling automorphism and rescaled by `a 0`. -/
theorem scaledDerivation_scaleHom (a : ℕ → ℂ) (P : MvPolynomial ℕ ℂ) :
    scaledDerivation a (scaleHom a P)
      = MvPolynomial.C (a 0) * scaleHom a (towerDerivation P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have h1 : scaleHom a (MvPolynomial.C c) = MvPolynomial.C c := MvPolynomial.aeval_C _ _
      have h2 : towerDerivation (MvPolynomial.C c : MvPolynomial ℕ ℂ) = 0 := by
        rw [show (MvPolynomial.C c : MvPolynomial ℕ ℂ)
          = algebraMap ℂ (MvPolynomial ℕ ℂ) c from rfl]
        exact towerDerivation.map_algebraMap c
      rw [h1, h2, map_zero, mul_zero,
        show (MvPolynomial.C c : MvPolynomial ℕ ℂ) = algebraMap ℂ (MvPolynomial ℕ ℂ) c from rfl,
        (scaledDerivation a).map_algebraMap]
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq, map_add, map_add, mul_add]
  | mul_X p k hp =>
      have hL : scaledDerivation a (scaleHom a (p * MvPolynomial.X k))
          = scaleHom a p * (MvPolynomial.C (a k) *
              (MvPolynomial.C (scaleWeight a k) * towerMonomial k))
            + (MvPolynomial.C (a k) * MvPolynomial.X k) *
              (MvPolynomial.C (a 0) * scaleHom a (towerDerivation p)) := by
        rw [map_mul, scaleHom_X, Derivation.leibniz, hp, scaledDerivation_C_mul,
          scaledDerivation_X]
        simp only [smul_eq_mul]
      have hR : scaleHom a (towerDerivation (p * MvPolynomial.X k))
          = scaleHom a p * (MvPolynomial.C (∏ j ∈ Finset.Icc 1 k, a j) * towerMonomial k)
            + (MvPolynomial.C (a k) * MvPolynomial.X k) * scaleHom a (towerDerivation p) := by
        rw [Derivation.leibniz, towerDerivation_X]
        simp only [smul_eq_mul, map_add, map_mul, scaleHom_X, scaleHom_towerMonomial]
      have hw : (MvPolynomial.C (a k) : MvPolynomial ℕ ℂ) * MvPolynomial.C (scaleWeight a k)
          = MvPolynomial.C (a 0) * MvPolynomial.C (∏ j ∈ Finset.Icc 1 k, a j) := by
        rw [← map_mul, ← map_mul, scale_weight_identity]
      rw [hL, hR]
      linear_combination (scaleHom a p * towerMonomial k) * hw


/-- **The conjugation identity on jets.** -/
theorem iterate_scaledDerivation_scaleHom (a : ℕ → ℂ) (P : MvPolynomial ℕ ℂ) (i : ℕ) :
    ((scaledDerivation a : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (scaleHom a P)
      = MvPolynomial.C (a 0) ^ i *
        scaleHom a (((towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) P) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, ← map_pow, scaledDerivation_C_mul,
        scaledDerivation_scaleHom, Function.iterate_succ_apply', map_pow]
      ring

theorem pderiv_C_mul (k : ℕ) (c : ℂ) (P : MvPolynomial ℕ ℂ) :
    (MvPolynomial.pderiv k) (MvPolynomial.C c * P)
      = MvPolynomial.C c * (MvPolynomial.pderiv k) P := by
  rw [← MvPolynomial.smul_eq_C_mul, ← MvPolynomial.smul_eq_C_mul]
  simp

/-- **The scaling automorphism transports partial derivatives.** -/
theorem pderiv_scaleHom (a : ℕ → ℂ) (k : ℕ) (P : MvPolynomial ℕ ℂ) :
    (MvPolynomial.pderiv k) (scaleHom a P)
      = MvPolynomial.C (a k) * scaleHom a ((MvPolynomial.pderiv k) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [scaleHom_C, MvPolynomial.pderiv_C]
      simp
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq, map_add, map_add, mul_add]
  | mul_X p j hp =>
      have hL : (MvPolynomial.pderiv k) (scaleHom a (p * MvPolynomial.X j))
          = scaleHom a p * (MvPolynomial.C (a j) * (MvPolynomial.pderiv k) (MvPolynomial.X j))
            + MvPolynomial.C (a j) * MvPolynomial.X j *
              (MvPolynomial.C (a k) * scaleHom a ((MvPolynomial.pderiv k) p)) := by
        rw [map_mul, scaleHom_X, Derivation.leibniz, pderiv_C_mul, hp]
        simp only [smul_eq_mul]
      have hR : scaleHom a ((MvPolynomial.pderiv k) (p * MvPolynomial.X j))
          = scaleHom a p * scaleHom a ((MvPolynomial.pderiv k) (MvPolynomial.X j))
            + MvPolynomial.C (a j) * MvPolynomial.X j * scaleHom a ((MvPolynomial.pderiv k) p) := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul, map_add, map_mul, scaleHom_X]
      rw [hL, hR]
      by_cases hkj : k = j
      · subst hkj
        rw [MvPolynomial.pderiv_X_self, map_one]
        ring
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hkj), map_zero]
        ring


/-! ## The transported determinant -/

theorem iterate_scaledDerivation_C_mul (a : ℕ → ℂ) (c : ℂ) (P : MvPolynomial ℕ ℂ) (i : ℕ) :
    ((scaledDerivation a : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (MvPolynomial.C c * P)
      = MvPolynomial.C c * ((scaledDerivation a : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) P := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, scaledDerivation_C_mul]

/-- The scaled model's jets are the tower's, up to constants and the scaling automorphism. -/
theorem scaled_jet_eq (a : ℕ → ℂ) (N i : ℕ) :
    MvPolynomial.C (a N) *
        ((scaledDerivation a : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (MvPolynomial.X N)
      = MvPolynomial.C (a 0) ^ i * scaleHom a (towerJet N i) := by
  have h1 := iterate_scaledDerivation_scaleHom a (MvPolynomial.X N) i
  rw [scaleHom_X, iterate_scaledDerivation_C_mul] at h1
  exact h1

/-- **The scaled model's output-jet determinant is nonzero.** -/
theorem scaled_jet_det_ne_zero {a : ℕ → ℂ} (ha : ∀ k, a k ≠ 0) (m : ℕ) :
    (Matrix.of fun i j : Fin (m + 1) =>
        (MvPolynomial.pderiv ((i : ℕ) + 1))
          (((scaledDerivation a : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[(j : ℕ)])
            (MvPolynomial.X (m + 1)))).det ≠ 0 := by
  classical
  set A : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial ℕ ℂ) :=
    Matrix.of fun i j => (MvPolynomial.pderiv ((i : ℕ) + 1))
      (((scaledDerivation a : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[(j : ℕ)])
        (MvPolynomial.X (m + 1))) with hA
  set B : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial ℕ ℂ) :=
    Matrix.of fun i j => (MvPolynomial.pderiv ((i : ℕ) + 1)) (towerJet (m + 1) (j : ℕ)) with hB
  have hentry : ∀ i j : Fin (m + 1),
      MvPolynomial.C (a (m + 1)) * A i j
        = MvPolynomial.C (a 0) ^ (j : ℕ) * MvPolynomial.C (a ((i : ℕ) + 1)) *
            scaleHom a (B i j) := by
    intro i j
    have h1 : (MvPolynomial.pderiv ((i : ℕ) + 1))
        (MvPolynomial.C (a (m + 1)) *
          ((scaledDerivation a : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[(j : ℕ)])
            (MvPolynomial.X (m + 1)))
        = (MvPolynomial.pderiv ((i : ℕ) + 1))
          (MvPolynomial.C (a 0) ^ (j : ℕ) * scaleHom a (towerJet (m + 1) (j : ℕ))) := by
      rw [scaled_jet_eq a (m + 1) (j : ℕ)]
    rw [pderiv_C_mul] at h1
    rw [hA, hB, Matrix.of_apply, Matrix.of_apply]
    rw [h1, ← map_pow, pderiv_C_mul, pderiv_scaleHom, map_pow]
    ring
  set M3 : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial ℕ ℂ) :=
    (scaleHom a).mapMatrix B with hM3
  set M2 : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial ℕ ℂ) :=
    Matrix.of fun i j => MvPolynomial.C (a ((i : ℕ) + 1)) * M3 i j with hM2
  set M1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial ℕ ℂ) :=
    Matrix.of fun i j => MvPolynomial.C (a 0) ^ (j : ℕ) * M2 i j with hM1
  have h2 : M2.det = (∏ i : Fin (m + 1), MvPolynomial.C (a ((i : ℕ) + 1))) * M3.det :=
    Matrix.det_mul_column _ _
  have h1 : M1.det = (∏ j : Fin (m + 1), MvPolynomial.C (a 0) ^ (j : ℕ)) * M2.det :=
    Matrix.det_mul_row _ _
  have h3 : M3.det = scaleHom a B.det := (AlgHom.map_det (scaleHom a) B).symm
  have hAM : (Matrix.of fun i j : Fin (m + 1) => MvPolynomial.C (a (m + 1)) * A i j) = M1 := by
    funext i j
    rw [Matrix.of_apply, hentry i j, hM1, hM2, hM3]
    simp only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
    ring
  have hleft : MvPolynomial.C (a (m + 1)) ^ (m + 1) * A.det
      = (Matrix.of fun i j : Fin (m + 1) => MvPolynomial.C (a (m + 1)) * A i j).det := by
    rw [Matrix.det_mul_column (fun _ : Fin (m + 1) => MvPolynomial.C (a (m + 1))) A]
    simp
  have hdetA : MvPolynomial.C (a (m + 1)) ^ (m + 1) * A.det
      = ((∏ j : Fin (m + 1), MvPolynomial.C (a 0) ^ (j : ℕ)) *
          ∏ i : Fin (m + 1), MvPolynomial.C (a ((i : ℕ) + 1))) * scaleHom a B.det := by
    rw [hleft, hAM, h1, h2, h3]
    ring
  intro hzero
  rw [hzero, mul_zero] at hdetA
  have hBdet : B.det ≠ 0 := towerJet_det_ne_zero m
  have hφ : scaleHom a B.det ≠ 0 := by
    intro h0
    exact hBdet (scaleHom_injective ha (by rw [h0, map_zero]))
  have hCne : ∀ k : ℕ, (MvPolynomial.C (a k) : MvPolynomial ℕ ℂ) ≠ 0 := by
    intro k h
    exact ha k (MvPolynomial.C_eq_zero.mp h)
  have hprod : (((∏ j : Fin (m + 1), MvPolynomial.C (a 0) ^ (j : ℕ)) *
      ∏ i : Fin (m + 1), MvPolynomial.C (a ((i : ℕ) + 1))) : MvPolynomial ℕ ℂ) ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr ?_) (Finset.prod_ne_zero_iff.mpr ?_)
    · intro j _
      exact pow_ne_zero _ (hCne 0)
    · intro i _
      exact hCne ((i : ℕ) + 1)
  exact (mul_ne_zero hprod hφ) hdetA.symm

end GaloisForLFunctions.HTGeometry
