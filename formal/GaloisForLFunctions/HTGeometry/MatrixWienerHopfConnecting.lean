import GaloisForLFunctions.HTGeometry.MatrixWienerHopfIndex
import GaloisForLFunctions.HTGeometry.WienerHopfConeExtension

/-!
# The stable connecting map of the Wiener–Hopf extension

For every `n` and every unitary `U ∈ Mₙ(C(S¹)) ≅ Mₙ(C*(ℝ)⁺)`, `U` lifts to `Mₙ` of the unitized
`C₀((-∞, +∞]) ⋊ ℝ` (`exists_wienerHopf_lift_matrix`), and every lift `c + Y` has Schrödinger image
on `L²(ℝ)ⁿ` Fredholm of index `wind(det U)` (`wienerHopf_connecting_index_matrix`): the connecting
map `K₁(C*(ℝ)) → K₀(𝒦) = ℤ` is the analytic Wiener–Hopf index on stable classes
(`wienerHopf_connecting_map_matrix`).

Modulo compact operators, `c + ρ(Y) = (P̂ + ĉ(1 - P̂)) T_U` (`twist_mul_toeplitz`, with `ĉ` the
scalar block of `c = U(1)` commuting with `P̂`); the twist is invertible because `c` is unitary
(`twist_mul_twist`), and `ind T_U = wind(det U)` is the matrix Wiener–Hopf index theorem.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-! ## Twisted Toeplitz algebra in a ring -/

section TwistAlgebra

variable {R : Type*} [Ring R] {P : R} (hP : P * P = P)
include hP

theorem twist_mul_toeplitz {c a : R} (hc : c * P = P * c) :
    (P + c * (1 - P)) * (P * (c + a) * P + (1 - P)) = c + P * a * P := by
  have e1 : P * (P * (c + a) * P) = P * (c + a) * P := by
    rw [← mul_assoc, ← mul_assoc, hP]
  have e2 : c * (1 - P) * (P * (c + a) * P) = 0 := by
    rw [mul_assoc c, ← mul_assoc (1 - P), ← mul_assoc (1 - P), one_sub_mul_idem hP, zero_mul,
      zero_mul, mul_zero]
  have e3 : c * (1 - P) * (1 - P) = c * (1 - P) := by rw [mul_assoc, one_sub_idem_mul_self hP]
  have e4 : P * c * P = c * P := by rw [← hc, mul_assoc, hP]
  calc (P + c * (1 - P)) * (P * (c + a) * P + (1 - P))
      = P * (P * (c + a) * P) + P * (1 - P) + c * (1 - P) * (P * (c + a) * P) +
          c * (1 - P) * (1 - P) := by noncomm_ring
    _ = P * c * P + P * a * P + c * (1 - P) := by
        rw [e1, idem_mul_one_sub hP, e2, e3]
        noncomm_ring
    _ = c + P * a * P := by
        rw [e4]
        noncomm_ring

theorem twist_mul_twist {c d : R} (hd : d * P = P * d) :
    (P + c * (1 - P)) * (P + d * (1 - P)) = P + c * d * (1 - P) := by
  have e1 : P * (d * (1 - P)) = 0 := by
    rw [← mul_assoc, ← hd, mul_assoc, idem_mul_one_sub hP, mul_zero]
  have e2 : c * (1 - P) * P = 0 := by rw [mul_assoc, one_sub_mul_idem hP, mul_zero]
  have e3 : c * (1 - P) * (d * (1 - P)) = c * d * (1 - P) := by
    have hd' : (1 - P) * d = d * (1 - P) := by rw [sub_mul, mul_sub, one_mul, mul_one, hd]
    rw [mul_assoc, ← mul_assoc (1 - P), hd', mul_assoc, one_sub_idem_mul_self hP, ← mul_assoc]
  rw [add_mul, mul_add, mul_add, hP, e1, e2, e3, add_zero, zero_add]

end TwistAlgebra

/-! ## Scalar matrices of operators -/

/-- The block operator of a scalar matrix. -/
def scalarBlock (c : Matrix (Fin n) (Fin n) ℂ) : L2Vec n →L[ℂ] L2Vec n :=
  l2BlockOp (c.map fun a => a • (1 : L2Real →L[ℂ] L2Real))

theorem scalarBlock_mul (c d : Matrix (Fin n) (Fin n) ℂ) :
    scalarBlock (c * d) = scalarBlock c * scalarBlock d := by
  rw [scalarBlock, scalarBlock, scalarBlock, ← l2BlockOp_mul]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.mul_apply, Finset.sum_smul, smul_mul_smul_comm, mul_one]

theorem scalarBlock_one : scalarBlock (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  rw [scalarBlock, Matrix.map_one (fun a : ℂ => a • (1 : L2Real →L[ℂ] L2Real)) (zero_smul ℂ _)
    (one_smul ℂ _), l2BlockOp_one]

theorem scalarBlock_comm_halfProjVec (c : Matrix (Fin n) (Fin n) ℂ) :
    scalarBlock c * halfProjVec = halfProjVec * scalarBlock c := by
  rw [scalarBlock, halfProjVec, ← l2BlockOp_mul, ← l2BlockOp_mul]
  congr 1
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, smul_mul_assoc, one_mul,
    mul_smul_comm, mul_one]

theorem matCircle_constMat (c : Matrix (Fin n) (Fin n) ℂ) : matCircle (constMat c) = scalarBlock c := by
  rw [matCircle, scalarBlock]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, constMat]
  rw [Algebra.algebraMap_eq_smul_one, circleMultiplier_smul, circleMultiplier_one]

theorem matCircle_add (U V : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) :
    matCircle (U + V) = matCircle U + matCircle V := by
  rw [matCircle, matCircle, matCircle, ← l2BlockOp_add]
  congr 1
  exact Matrix.map_add _ circleMultiplier_add U V

/-- The twist `P̂ + ĉ (1 - P̂)` by a unitary scalar matrix is invertible. -/
def halfTwistVecEquiv {c : Matrix (Fin n) (Fin n) ℂ} (hc : c ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    L2Vec n ≃L[ℂ] L2Vec n :=
  ContinuousLinearEquiv.equivOfInverse (halfProjVec + scalarBlock c * (1 - halfProjVec))
    (halfProjVec + scalarBlock (star c) * (1 - halfProjVec))
    (fun f => by
      change (((halfProjVec + scalarBlock (star c) * (1 - halfProjVec)) *
        (halfProjVec + scalarBlock c * (1 - halfProjVec)) : L2Vec n →L[ℂ] L2Vec n)) f = f
      rw [twist_mul_twist halfProjVec_mul_self (scalarBlock_comm_halfProjVec c), ← scalarBlock_mul,
        Matrix.mem_unitaryGroup_iff'.mp hc, scalarBlock_one, one_mul, add_sub_cancel]
      rfl)
    (fun f => by
      change (((halfProjVec + scalarBlock c * (1 - halfProjVec)) *
        (halfProjVec + scalarBlock (star c) * (1 - halfProjVec)) : L2Vec n →L[ℂ] L2Vec n)) f = f
      rw [twist_mul_twist halfProjVec_mul_self (scalarBlock_comm_halfProjVec (star c)),
        ← scalarBlock_mul, Matrix.mem_unitaryGroup_iff.mp hc, scalarBlock_one, one_mul,
        add_sub_cancel]
      rfl)

theorem halfTwistVecEquiv_coe {c : Matrix (Fin n) (Fin n) ℂ}
    (hc : c ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ((halfTwistVecEquiv hc : L2Vec n ≃L[ℂ] L2Vec n) : L2Vec n →L[ℂ] L2Vec n) =
      halfProjVec + scalarBlock c * (1 - halfProjVec) := rfl

/-- Multiplication by the cut-off on every summand. -/
def coneCutVec : L2Vec n →L[ℂ] L2Vec n := l2BlockOp (Matrix.diagonal fun _ => coneCutMul)

theorem coneCutVec_mul_matCircle (V : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) :
    coneCutVec * matCircle V = l2BlockOp fun i j => coneCutMul * circleMultiplier (V i j) := by
  rw [coneCutVec, matCircle, ← l2BlockOp_mul]
  congr 1
  refine Matrix.ext fun i j => ?_
  rw [Matrix.diagonal_mul, Matrix.map_apply]

theorem coneCutVec_sub_halfProjVec_mul_matCircle (V : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) :
    (coneCutVec - halfProjVec) * matCircle V =
      l2BlockOp fun i j => (coneCutMul - halfProj) * circleMultiplier (V i j) := by
  rw [coneCutVec, halfProjVec, ← l2BlockOp_sub, Matrix.diagonal_sub, matCircle, ← l2BlockOp_mul]
  congr 1
  refine Matrix.ext fun i j => ?_
  rw [Matrix.diagonal_mul, Matrix.map_apply]

/-- **The stable connecting map of the Wiener–Hopf extension is the analytic index.**  For a
unitary matrix symbol `U ∈ Mₙ(C(S¹))` and a lift `(c, Y)` of it to `Mₙ` of the unitized
`C₀((-∞, +∞]) ⋊ ℝ` (`c_{ij} + σ(Y_{ij}) = C_{U_{ij}}`), the Schrödinger image `c + ρ(Y)` on `L²(ℝ)ⁿ`
is Fredholm of index `wind(det U)`. -/
theorem wienerHopf_connecting_index_matrix {U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)}
    (hU : star U * U = 1) {c : Matrix (Fin n) (Fin n) ℂ}
    {Y : Matrix (Fin n) (Fin n) ConeCrossedProduct}
    (hlift : ∀ i j, c i j • (1 : L2Real →L[ℂ] L2Real) + convRegular (coneSymbolMap (Y i j)) =
      circleMultiplier (U i j)) :
    IsFredholmOp (l2BlockOp fun i j => c i j • (1 : L2Real →L[ℂ] L2Real) + coneSchrodinger (Y i j)) ∧
      fredholmIndex (l2BlockOp fun i j =>
        c i j • (1 : L2Real →L[ℂ] L2Real) + coneSchrodinger (Y i j)) = circleWinding U.det := by
  choose V hV hVz using fun i j => exists_circle_of_convRegular (coneSymbolMap (Y i j))
  have hUV : ∀ i j, U i j = algebraMap ℂ C(UnitCircle, ℂ) (c i j) + V i j := fun i j => by
    apply circleMultiplier_injective
    rw [circleMultiplier_add, hVz, ← hlift, Algebra.algebraMap_eq_smul_one, circleMultiplier_smul,
      circleMultiplier_one]
  have hc : c = evalMat U circleOne := Matrix.ext fun i j => by
    rw [evalMat_apply, hUV, ContinuousMap.add_apply, show V i j circleOne = 0 from hV i j,
      add_zero]
    rfl
  have hcu : c ∈ Matrix.unitaryGroup (Fin n) ℂ := hc ▸ evalMat_mem_unitaryGroup hU circleOne
  have hUm : U = constMat c + Matrix.of V := Matrix.ext fun i j => hUV i j
  have hCU : matCircle U = scalarBlock c + matCircle (Matrix.of V) := by
    rw [hUm, matCircle_add, matCircle_constMat]
  -- the operator and its decomposition
  have hX : (l2BlockOp fun i j => c i j • (1 : L2Real →L[ℂ] L2Real) + coneSchrodinger (Y i j)) =
      scalarBlock c + l2BlockOp fun i j => coneSchrodinger (Y i j) := by
    rw [scalarBlock, ← l2BlockOp_add]
    rfl
  have hK1 : IsCompactOperator ⇑((l2BlockOp fun i j => coneSchrodinger (Y i j)) -
      coneCutVec * matCircle (Matrix.of V) : L2Vec n →L[ℂ] L2Vec n) := by
    rw [coneCutVec_mul_matCircle, ← l2BlockOp_sub]
    refine isCompactOperator_l2BlockOp fun i j => ?_
    have h := isCompactOperator_coneSchrodinger_sub (Y i j)
    rw [← hVz] at h
    exact h
  have hK2 : IsCompactOperator ⇑((coneCutVec - halfProjVec) * matCircle (Matrix.of V) :
      L2Vec n →L[ℂ] L2Vec n) := by
    rw [coneCutVec_sub_halfProjVec_mul_matCircle]
    exact isCompactOperator_l2BlockOp fun i j => isCompactOperator_cutDiff_circleMultiplier (hV i j)
  have hK3 := isCompactOperator_matHankelPlus (Matrix.of V)
  have hKc := hK1.add (hK2.add hK3)
  have hE : (halfProjVec + scalarBlock c * (1 - halfProjVec)) * matWH U =
      scalarBlock c + halfProjVec * matCircle (Matrix.of V) * halfProjVec := by
    rw [matWH, hCU]
    exact twist_mul_toeplitz halfProjVec_mul_self (scalarBlock_comm_halfProjVec c)
  have hdecomp : (l2BlockOp fun i j => c i j • (1 : L2Real →L[ℂ] L2Real) + coneSchrodinger (Y i j)) =
      (halfProjVec + scalarBlock c * (1 - halfProjVec)) * matWH U +
        (((l2BlockOp fun i j => coneSchrodinger (Y i j)) - coneCutVec * matCircle (Matrix.of V)) +
          ((coneCutVec - halfProjVec) * matCircle (Matrix.of V) +
            halfProjVec * matCircle (Matrix.of V) * (1 - halfProjVec))) := by
    rw [hX, hE, sub_mul, mul_sub, mul_one]
    abel
  obtain ⟨hF, hI⟩ := fredholmIndex_matWH hU
  have hEF : IsFredholmOp ((halfProjVec + scalarBlock c * (1 - halfProjVec)) * matWH U) ∧
      fredholmIndex ((halfProjVec + scalarBlock c * (1 - halfProjVec)) * matWH U) =
        fredholmIndex (matWH U) :=
    hF.equiv_comp (halfTwistVecEquiv hcu)
  rw [hdecomp]
  exact ⟨hEF.1.add_compact hKc, by rw [fredholmIndex_add_compact hEF.1 hKc, hEF.2, hI]⟩

/-- **Every unitary matrix symbol lifts** to `Mₙ` of the unitized cone crossed product, with scalar
part its value at `1`. -/
theorem exists_wienerHopf_lift_matrix (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) :
    ∃ Y : Matrix (Fin n) (Fin n) ConeCrossedProduct, ∀ i j,
      evalMat U circleOne i j • (1 : L2Real →L[ℂ] L2Real) + convRegular (coneSymbolMap (Y i j)) =
        circleMultiplier (U i j) := by
  choose Y hY using fun i j => exists_wienerHopf_lift (U i j)
  exact ⟨Matrix.of Y, fun i j => hY i j⟩

/-- **Capstone: the connecting map `K₁(C*(ℝ)) → K₀(𝒦) = ℤ` of the Wiener–Hopf extension is the
analytic Wiener–Hopf index on stable classes.**  Every unitary `U ∈ Mₙ(C(S¹)) ≅ Mₙ(C*(ℝ)⁺)` lifts,
and every lift has Schrödinger image Fredholm of index `wind(det U)`. -/
theorem wienerHopf_connecting_map_matrix {U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)}
    (hU : star U * U = 1) :
    (∃ Y : Matrix (Fin n) (Fin n) ConeCrossedProduct, ∀ i j,
      evalMat U circleOne i j • (1 : L2Real →L[ℂ] L2Real) + convRegular (coneSymbolMap (Y i j)) =
        circleMultiplier (U i j)) ∧
    ∀ (c : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ConeCrossedProduct),
      (∀ i j, c i j • (1 : L2Real →L[ℂ] L2Real) + convRegular (coneSymbolMap (Y i j)) =
        circleMultiplier (U i j)) →
      IsFredholmOp (l2BlockOp fun i j => c i j • (1 : L2Real →L[ℂ] L2Real) + coneSchrodinger (Y i j)) ∧
        fredholmIndex (l2BlockOp fun i j =>
          c i j • (1 : L2Real →L[ℂ] L2Real) + coneSchrodinger (Y i j)) = circleWinding U.det :=
  ⟨exists_wienerHopf_lift_matrix U, fun _ _ h => wienerHopf_connecting_index_matrix hU h⟩

end GaloisForLFunctions.HTGeometry
