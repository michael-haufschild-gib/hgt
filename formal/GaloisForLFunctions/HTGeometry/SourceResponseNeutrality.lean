import GaloisForLFunctions.HTGeometry.SourceGramResponse

/-!
# Functional-equation neutrality of source responses

Let `J` be a unitary symmetry of a cyclic source: `J L = L J` and `J v = ζ v` with `|ζ| = 1`
`(SR.18)`; a unitary involution is the functional-equation case.  Then `J` commutes with the
semigroup and `J x(t) = ζ x(t)`, `J* x(t) = ζ̄ x(t)`.  For the conjugated intervention
`K^J = J K J*`:

* `Y_{K^J}(t) = ζ̄ J Y_K(t)` — both solve `Z' + L Z = -K^J x`, `Z(0) = 0`;
* `W_T(K^J) = W_T(K)`, `‖K^J‖ = ‖K‖` and `‖K^J‖_HS = ‖K‖_HS`;
* `J G J* = G` — both solve the Lyapunov equation — so `G` and `C = G⁻¹` commute with `J`;
* `Ġ_{K^J} = J Ġ_K J*` — both solve `Λ X = -(K^J G + G K^J)` — hence
  `Ċ_{K^J} = J Ċ_K J*` and `tr (C Ġ_{K^J}) = tr (C Ġ_K)` `(SR.19)`.

So the symmetry transports every response isometrically and cannot single out an intervention.
-/

open Filter Topology Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- A unitary symmetry of a cyclic source `(SR.18)`. -/
structure SourceSymmetry (σ : CyclicSource H) where
  /-- The symmetry. -/
  J : H →L[ℂ] H
  mem_unitary : J ∈ unitary (H →L[ℂ] H)
  comm : J * σ.L = σ.L * J
  /-- The phase of the source vector. -/
  ζ : ℂ
  norm_ζ : ‖ζ‖ = 1
  apply_v : J σ.v = ζ • σ.v

namespace SourceSymmetry

variable {σ : CyclicSource H} (j : SourceSymmetry σ)

omit [FiniteDimensional ℂ H] in
theorem star_mul_self : star j.J * j.J = 1 := Unitary.star_mul_self_of_mem j.mem_unitary

omit [FiniteDimensional ℂ H] in
theorem mul_star_self : j.J * star j.J = 1 := Unitary.mul_star_self_of_mem j.mem_unitary

omit [FiniteDimensional ℂ H] in
theorem star_apply_apply (y : H) : star j.J (j.J y) = y := by
  have h := congrArg (· y) j.star_mul_self
  simpa [mul_apply_eq_comp] using h

omit [FiniteDimensional ℂ H] in
theorem apply_star_apply (y : H) : j.J (star j.J y) = y := by
  have h := congrArg (· y) j.mul_star_self
  simpa [mul_apply_eq_comp] using h

omit [FiniteDimensional ℂ H] in
theorem norm_apply (y : H) : ‖j.J y‖ = ‖y‖ :=
  (Unitary.linearIsometryEquiv (⟨j.J, j.mem_unitary⟩ : unitary (H →L[ℂ] H))).norm_map y

omit [FiniteDimensional ℂ H] in
theorem norm_star_apply (y : H) : ‖star j.J y‖ = ‖y‖ := by
  rw [← j.norm_apply, j.apply_star_apply]

omit [FiniteDimensional ℂ H] in
theorem conj_mul_ζ : (starRingEnd ℂ) j.ζ * j.ζ = 1 := by
  rw [Complex.conj_mul', j.norm_ζ]
  simp

omit [FiniteDimensional ℂ H] in
/-- An eigenvector of `J` with phase `ζ` is an eigenvector of `J*` with phase `ζ̄`. -/
theorem star_apply_of_apply {y : H} (hy : j.J y = j.ζ • y) :
    star j.J y = (starRingEnd ℂ) j.ζ • y := by
  calc star j.J y = ((starRingEnd ℂ) j.ζ * j.ζ) • star j.J y := by rw [j.conj_mul_ζ, one_smul]
    _ = (starRingEnd ℂ) j.ζ • star j.J (j.ζ • y) := by rw [map_smul, smul_smul]
    _ = (starRingEnd ℂ) j.ζ • y := by rw [← hy, j.star_apply_apply]

omit [FiniteDimensional ℂ H] in
theorem star_comm : star j.J * σ.L = σ.L * star j.J := by
  have h := congrArg star j.comm
  simp only [star_mul, σ.isSelfAdjoint.star_eq] at h
  exact h.symm

omit [FiniteDimensional ℂ H] in
theorem apply_L (y : H) : j.J (σ.L y) = σ.L (j.J y) := by
  have h := congrArg (· y) j.comm
  simpa [mul_apply_eq_comp] using h

omit [FiniteDimensional ℂ H] in
theorem comm_S (t : ℝ) : j.J * σ.S t = σ.S t * j.J :=
  (((Commute.neg_right (j.comm : Commute j.J σ.L)).smul_right t).exp_right).eq

omit [FiniteDimensional ℂ H] in
theorem apply_x (t : ℝ) : j.J (σ.x t) = j.ζ • σ.x t := by
  have h := congrArg (· σ.v) (j.comm_S t)
  simp only [mul_apply_eq_comp] at h
  rw [CyclicSource.x, h, j.apply_v, map_smul]

omit [FiniteDimensional ℂ H] in
theorem star_apply_x (t : ℝ) : star j.J (σ.x t) = (starRingEnd ℂ) j.ζ • σ.x t :=
  j.star_apply_of_apply (j.apply_x t)

/-! ### Conjugated interventions -/

/-- The conjugated intervention `K^J = J K J*`. -/
def conjugate (K : H →L[ℂ] H) : H →L[ℂ] H := j.J * K * star j.J

omit [FiniteDimensional ℂ H] in
theorem isSelfAdjoint_conjugate {K : H →L[ℂ] H} (hK : IsSelfAdjoint K) :
    IsSelfAdjoint (j.conjugate K) :=
  hK.conjugate j.J

omit [FiniteDimensional ℂ H] in
theorem conjugate_apply_x (K : H →L[ℂ] H) (t : ℝ) :
    j.conjugate K (σ.x t) = (starRingEnd ℂ) j.ζ • j.J (K (σ.x t)) := by
  simp only [conjugate, mul_apply_eq_comp, j.star_apply_x, map_smul]

/-- **`(SR.19)`: response transport** `Y_{K^J}(t) = ζ̄ J Y_K(t)`. -/
theorem response_conjugate (K : H →L[ℂ] H) :
    σ.response (j.conjugate K) = fun t => (starRingEnd ℂ) j.ζ • j.J (σ.response K t) := by
  set Φ : H →L[ℂ] H := (starRingEnd ℂ) j.ζ • j.J
  refine (σ.response_unique (j.conjugate K) (fun t => ?_) ?_).symm
  · have h := (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (σ.hasDerivAt_response K t)
    refine h.congr_deriv ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', Φ, smul_apply, map_sub, map_neg,
      j.apply_L, j.conjugate_apply_x, map_smul]
  · simp [σ.response_zero]

theorem norm_response_conjugate (K : H →L[ℂ] H) (t : ℝ) :
    ‖σ.response (j.conjugate K) t‖ = ‖σ.response K t‖ := by
  rw [j.response_conjugate, norm_smul, RCLike.norm_conj, j.norm_ζ, one_mul, j.norm_apply]

/-- **`(SR.19)`: work neutrality** `W_T(K^J) = W_T(K)`. -/
theorem responseWork_conjugate (T : ℝ) (K : H →L[ℂ] H) :
    σ.responseWork T (j.conjugate K) = σ.responseWork T K := by
  simp only [CyclicSource.responseWork, j.norm_response_conjugate]

/-- The response kernel is transported: `Y_{K^J} = 0` exactly when `Y_K = 0`. -/
theorem response_conjugate_eq_zero_iff (K : H →L[ℂ] H) (t : ℝ) :
    σ.response (j.conjugate K) t = 0 ↔ σ.response K t = 0 := by
  rw [← norm_eq_zero, j.norm_response_conjugate, norm_eq_zero]

omit [FiniteDimensional ℂ H] in
theorem norm_le_one : ‖j.J‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by rw [j.norm_apply, one_mul]

omit [FiniteDimensional ℂ H] in
theorem norm_star_le_one : ‖star j.J‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by rw [j.norm_star_apply, one_mul]

omit [FiniteDimensional ℂ H] in
/-- Conjugation is an isometry of the operator norm. -/
theorem norm_conjugate (K : H →L[ℂ] H) : ‖j.conjugate K‖ = ‖K‖ := by
  have h1 : ‖j.conjugate K‖ ≤ ‖K‖ :=
    calc ‖j.J * K * star j.J‖ ≤ ‖j.J‖ * ‖K‖ * ‖star j.J‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖K‖ * 1 := by
          gcongr
          · exact j.norm_le_one
          · exact j.norm_star_le_one
      _ = ‖K‖ := by ring
  have hK : K = star j.J * j.conjugate K * j.J := by
    simp only [conjugate, ← mul_assoc, j.star_mul_self, one_mul]
    rw [mul_assoc, j.star_mul_self, mul_one]
  have h2 : ‖K‖ ≤ ‖j.conjugate K‖ :=
    calc ‖K‖ = ‖star j.J * j.conjugate K * j.J‖ := by rw [← hK]
      _ ≤ ‖star j.J‖ * ‖j.conjugate K‖ * ‖j.J‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖j.conjugate K‖ * 1 := by
          gcongr
          · exact j.norm_star_le_one
          · exact j.norm_le_one
      _ = ‖j.conjugate K‖ := by ring
  exact le_antisymm h1 h2

/-- Conjugation is an isometry of the Hilbert–Schmidt norm. -/
theorem hsNormSq_conjugate (K : H →L[ℂ] H) : (j.conjugate K).hsNormSq = K.hsNormSq := by
  set u : unitary (H →L[ℂ] H) := ⟨star j.J, Unitary.star_mem j.mem_unitary⟩
  set b := stdOrthonormalBasis ℂ H
  set b' := b.map (Unitary.linearIsometryEquiv u)
  rw [ContinuousLinearMap.hsNormSq_eq (CyclicSource.isHilbertSchmidt_of_finiteDimensional _)
      b.toHilbertBasis,
    ContinuousLinearMap.hsNormSq_eq (CyclicSource.isHilbertSchmidt_of_finiteDimensional _)
      b'.toHilbertBasis]
  refine tsum_congr fun i => ?_
  simp only [OrthonormalBasis.coe_toHilbertBasis, b', OrthonormalBasis.map_apply, u, conjugate,
    mul_apply_eq_comp, j.norm_apply]
  rfl

/-- Reconstruction constants are transported: a coercivity constant `W_T(K) ≥ c ‖K‖²_HS` for all
interventions holds verbatim along the conjugated interventions. -/
theorem responseWork_coercive_conjugate {T c : ℝ}
    (h : ∀ K : H →L[ℂ] H, c * K.hsNormSq ≤ σ.responseWork T K) (K : H →L[ℂ] H) :
    c * (j.conjugate K).hsNormSq ≤ σ.responseWork T (j.conjugate K) := by
  rw [j.hsNormSq_conjugate, j.responseWork_conjugate]
  exact h K

/-! ### Gram, inverse-cost and determinant transport -/

omit [FiniteDimensional ℂ H] in
theorem L_mul_conj (X : H →L[ℂ] H) :
    σ.L * (j.J * X * star j.J) = j.J * (σ.L * X) * star j.J := by
  rw [← mul_assoc, ← mul_assoc, ← j.comm, mul_assoc j.J σ.L X]

omit [FiniteDimensional ℂ H] in
theorem conj_mul_L (X : H →L[ℂ] H) :
    j.J * X * star j.J * σ.L = j.J * (X * σ.L) * star j.J := by
  rw [mul_assoc, j.star_comm, ← mul_assoc, mul_assoc j.J X σ.L]

omit [FiniteDimensional ℂ H] in
theorem conj_rankOne_v :
    j.J * InnerProductSpace.rankOne ℂ σ.v σ.v * star j.J =
      InnerProductSpace.rankOne ℂ σ.v σ.v := by
  ext y
  have hadj : ⟪σ.v, star j.J y⟫_ℂ = (starRingEnd ℂ) j.ζ * ⟪σ.v, y⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, j.apply_v,
      inner_smul_left]
  simp only [mul_apply_eq_comp, InnerProductSpace.rankOne_apply, map_smul, j.apply_v, hadj,
    smul_smul]
  rw [mul_assoc, mul_comm ⟪σ.v, y⟫_ℂ, ← mul_assoc, j.conj_mul_ζ, one_mul]

/-- The Gramian is `J`-invariant: `J G J* = G`. -/
theorem conj_gram : j.J * σ.gram * star j.J = σ.gram := by
  refine σ.eq_gram_of_lyapunov ?_
  rw [j.L_mul_conj, j.conj_mul_L, ← add_mul, ← mul_add, σ.lyapunov_gram, j.conj_rankOne_v]

theorem comm_gram : j.J * σ.gram = σ.gram * j.J := by
  calc j.J * σ.gram = j.J * σ.gram * star j.J * j.J := by
        rw [mul_assoc (j.J * σ.gram), j.star_mul_self, mul_one]
    _ = σ.gram * j.J := by rw [j.conj_gram]

theorem star_comm_gram : star j.J * σ.gram = σ.gram * star j.J := by
  calc star j.J * σ.gram = star j.J * (σ.gram * j.J) * star j.J := by
        rw [mul_assoc (star j.J), mul_assoc σ.gram, j.mul_star_self, mul_one]
    _ = star j.J * (j.J * σ.gram) * star j.J := by rw [j.comm_gram]
    _ = σ.gram * star j.J := by rw [← mul_assoc, j.star_mul_self, one_mul]

/-- **`(SR.19)`: Gram response transport** `Ġ_{K^J} = J Ġ_K J*`. -/
theorem gramDot_conjugate {K : H →L[ℂ] H} (hK : IsSelfAdjoint K) :
    σ.gramDot (j.conjugate K) = j.J * σ.gramDot K * star j.J := by
  obtain ⟨c, hc, hcoer⟩ := σ.exists_coercive
  refine lyapunovOp_injective hc hcoer ?_
  rw [lyapunovOp_apply, lyapunovOp_apply, σ.lyapunov_gramDot (j.isSelfAdjoint_conjugate hK)]
  have e1 : j.conjugate K * σ.gram = j.J * (K * σ.gram) * star j.J := by
    rw [conjugate, mul_assoc (j.J * K), j.star_comm_gram, ← mul_assoc, mul_assoc j.J K]
  have e2 : σ.gram * j.conjugate K = j.J * (σ.gram * K) * star j.J := by
    rw [conjugate, ← mul_assoc, ← mul_assoc, ← j.comm_gram, mul_assoc j.J σ.gram K]
  rw [e1, e2, j.L_mul_conj, j.conj_mul_L]
  calc -(j.J * (K * σ.gram) * star j.J + j.J * (σ.gram * K) * star j.J)
      = j.J * (-(K * σ.gram + σ.gram * K)) * star j.J := by noncomm_ring
    _ = j.J * (σ.L * σ.gramDot K + σ.gramDot K * σ.L) * star j.J := by
        rw [σ.lyapunov_gramDot hK]
    _ = _ := by noncomm_ring

theorem comm_inverseCost : j.J * Ring.inverse σ.gram = Ring.inverse σ.gram * j.J := by
  have hG := σ.isUnit_gram
  set C := Ring.inverse σ.gram
  calc j.J * C = C * σ.gram * j.J * C := by rw [Ring.inverse_mul_cancel _ hG, one_mul]
    _ = C * (σ.gram * j.J) * C := by rw [mul_assoc C]
    _ = C * (j.J * σ.gram) * C := by rw [j.comm_gram]
    _ = C * j.J * (σ.gram * C) := by simp only [mul_assoc]
    _ = C * j.J := by rw [Ring.mul_inverse_cancel _ hG, mul_one]

theorem star_comm_inverseCost :
    star j.J * Ring.inverse σ.gram = Ring.inverse σ.gram * star j.J := by
  have hc := j.comm_inverseCost
  set C := Ring.inverse σ.gram
  calc star j.J * C = star j.J * (C * j.J) * star j.J := by
        rw [mul_assoc (star j.J), mul_assoc C, j.mul_star_self, mul_one]
    _ = star j.J * (j.J * C) * star j.J := by rw [hc]
    _ = C * star j.J := by rw [← mul_assoc, j.star_mul_self, one_mul]

/-- **`(SR.19)`: inverse-cost transport** `Ċ_{K^J} = J Ċ_K J*`. -/
theorem inverseCostResponse_conjugate {K : H →L[ℂ] H} (hK : IsSelfAdjoint K) :
    -(Ring.inverse σ.gram * σ.gramDot (j.conjugate K) * Ring.inverse σ.gram) =
      j.J * -(Ring.inverse σ.gram * σ.gramDot K * Ring.inverse σ.gram) * star j.J := by
  rw [j.gramDot_conjugate hK]
  have hc1 := j.comm_inverseCost
  have hc2 := j.star_comm_inverseCost
  set C := Ring.inverse σ.gram
  have h : C * (j.J * σ.gramDot K * star j.J) * C = j.J * (C * σ.gramDot K * C) * star j.J := by
    calc C * (j.J * σ.gramDot K * star j.J) * C
        = (C * j.J) * σ.gramDot K * (star j.J * C) := by simp only [mul_assoc]
      _ = (j.J * C) * σ.gramDot K * (C * star j.J) := by rw [← hc1, hc2]
      _ = j.J * (C * σ.gramDot K * C) * star j.J := by simp only [mul_assoc]
  rw [h]
  noncomm_ring

/-- **`(SR.19)`: determinant-response neutrality** `tr (C Ġ_{K^J}) = tr (C Ġ_K)`. -/
theorem logDetResponse_conjugate {K : H →L[ℂ] H} (hK : IsSelfAdjoint K) :
    LinearMap.trace ℂ H (Ring.inverse σ.gram * σ.gramDot (j.conjugate K) : H →L[ℂ] H) =
      LinearMap.trace ℂ H (Ring.inverse σ.gram * σ.gramDot K : H →L[ℂ] H) := by
  rw [j.gramDot_conjugate hK]
  have hc1 := j.comm_inverseCost
  set C := Ring.inverse σ.gram
  have h1 : C * (j.J * σ.gramDot K * star j.J) = j.J * (C * σ.gramDot K * star j.J) := by
    rw [← mul_assoc, ← mul_assoc, ← hc1]
    simp only [mul_assoc]
  have h2 : C * σ.gramDot K * star j.J * j.J = C * σ.gramDot K := by
    rw [mul_assoc, j.star_mul_self, mul_one]
  rw [h1, ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm,
    ← ContinuousLinearMap.toLinearMap_mul, h2]

end SourceSymmetry

end GaloisForLFunctions.HTGeometry
