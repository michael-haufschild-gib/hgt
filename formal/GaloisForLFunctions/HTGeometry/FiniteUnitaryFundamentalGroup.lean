import GaloisForLFunctions.HTGeometry.CircleFundamentalGroup
import GaloisForLFunctions.HTGeometry.FundamentalGroupContinuousHom
import GaloisForLFunctions.HTGeometry.FiniteUnitaryFundamentalGroupStabilization

/-!
# Determinant classifies finite-unitary loops

The determinant induces an isomorphism from the fundamental group of every
positive-dimensional complex unitary group to that of the circle, hence to
the integers. Surjective stabilization and the one-dimensional determinant
section prove injectivity by induction. In particular, stabilization is an
isomorphism, and determinant winding is the complete loop invariant.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix FiniteUnitaryStabilization

noncomputable section

/-- The determinant as a continuous homomorphism to the unit circle. -/
def finiteUnitaryDeterminant (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix.unitaryGroup ι ℂ →ₜ* Circle where
  toFun U := ⟨(U : Matrix ι ι ℂ).det, by
    apply mem_sphere_zero_iff_norm.mpr
    exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary U.2)⟩
  map_one' := by apply Subtype.ext; exact Matrix.det_one
  map_mul' U V := by apply Subtype.ext; exact Matrix.det_mul _ _
  continuous_toFun := by
    apply continuous_induced_rng.2
    change Continuous (fun U : Matrix.unitaryGroup ι ℂ => (U : Matrix ι ι ℂ).det)
    fun_prop

/-- A diagonal continuous homomorphism splitting the determinant. -/
def finiteUnitaryCircleSection {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) :
    Circle →ₜ* Matrix.unitaryGroup ι ℂ where
  toFun z := unitaryDeterminantSection i0 z
    (Unitary.mem_iff.mp (circleUnitary z).2).1
  map_one' := unitaryDeterminantSection_one i0
  map_mul' z w := by
    apply Subtype.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : i = i0 <;> simp [Function.update, h]
  continuous_toFun := by
    apply continuous_induced_rng.2
    change Continuous (fun z : Circle =>
      Matrix.diagonal (Function.update (fun _ : ι => (1 : ℂ)) i0 (z : ℂ)))
    fun_prop

/-- The diagonal section is a right inverse of determinant in every nonzero
matrix dimension. -/
theorem finiteUnitaryDeterminant_comp_section
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) :
    (finiteUnitaryDeterminant ι).comp (finiteUnitaryCircleSection i0) =
      ContinuousMonoidHom.id Circle := by
  ext z
  exact unitaryDeterminantSection_det i0 z
    (Unitary.mem_iff.mp (circleUnitary z).2).1

/-- In dimension one the determinant section is also a left inverse. -/
theorem finiteUnitaryCircleSection_comp_det_one :
    (finiteUnitaryCircleSection (0 : Fin 1)).comp (finiteUnitaryDeterminant (Fin 1)) =
      ContinuousMonoidHom.id (Matrix.unitaryGroup (Fin 1) ℂ) := by
  apply ContinuousMonoidHom.ext
  intro U
  apply Subtype.ext
  ext i j
  fin_cases i
  fin_cases j
  change (Matrix.diagonal (Function.update (fun _ : Fin 1 => (1 : ℂ)) 0
    (U : Matrix (Fin 1) (Fin 1) ℂ).det)) 0 0 = (U : Matrix (Fin 1) (Fin 1) ℂ) 0 0
  simp

/-- Block stabilization as a continuous homomorphism. -/
def finiteUnitaryStabilizationHom (n : ℕ) :
    Matrix.unitaryGroup (Fin n) ℂ →ₜ* Matrix.unitaryGroup (Fin (n + 1)) ℂ :=
  { unitaryEmbedSucc n with continuous_toFun := continuous_unitaryEmbedSucc n }

/-- Block stabilization preserves determinant. -/
theorem finiteUnitaryDeterminant_comp_stabilization (n : ℕ) :
    (finiteUnitaryDeterminant (Fin (n + 1))).comp (finiteUnitaryStabilizationHom n) =
      finiteUnitaryDeterminant (Fin n) := by
  ext U
  exact det_embedSucc n U

/-- The bundled induced stabilization agrees with the existing loop-class map. -/
theorem fundamentalGroupContinuousHom_stabilization (n : ℕ)
    (p : FundamentalGroup (Matrix.unitaryGroup (Fin n) ℂ) 1) :
    fundamentalGroupContinuousHom (finiteUnitaryStabilizationHom n) p =
      unitaryEmbedSuccFundamentalGroupMap n p := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    rw [fundamentalGroupContinuousHom_mk]
    rfl

/-- Determinant induces a bijection on fundamental groups in every positive
matrix dimension. -/
theorem finiteUnitaryDeterminant_fundamentalGroup_bijective (n : ℕ) :
    Function.Bijective
      (fundamentalGroupContinuousHom (finiteUnitaryDeterminant (Fin (n + 1)))) := by
  have hright (k : ℕ) : Function.RightInverse
      (fundamentalGroupContinuousHom (finiteUnitaryCircleSection (0 : Fin (k + 1))))
      (fundamentalGroupContinuousHom (finiteUnitaryDeterminant (Fin (k + 1)))) := by
    intro p
    have h := congrArg (fun f => fundamentalGroupContinuousHom f p)
      (finiteUnitaryDeterminant_comp_section (0 : Fin (k + 1)))
    simpa only [fundamentalGroupContinuousHom_comp, MonoidHom.comp_apply,
      fundamentalGroupContinuousHom_id, MonoidHom.id_apply] using h
  refine ⟨?_, (hright n).surjective⟩
  induction n with
  | zero =>
    have hleft : Function.LeftInverse
        (fundamentalGroupContinuousHom (finiteUnitaryCircleSection (0 : Fin 1)))
        (fundamentalGroupContinuousHom (finiteUnitaryDeterminant (Fin 1))) := by
      intro p
      have h := congrArg (fun f => fundamentalGroupContinuousHom f p)
        finiteUnitaryCircleSection_comp_det_one
      simpa only [fundamentalGroupContinuousHom_comp, MonoidHom.comp_apply,
        fundamentalGroupContinuousHom_id, MonoidHom.id_apply] using h
    exact hleft.injective
  | succ n ih =>
    intro p q hpq
    obtain ⟨p', rfl⟩ := unitaryEmbedSuccFundamentalGroupMap_surjective n p
    obtain ⟨q', rfl⟩ := unitaryEmbedSuccFundamentalGroupMap_surjective n q
    congr 1
    apply ih
    have hcomm := congrArg fundamentalGroupContinuousHom
      (finiteUnitaryDeterminant_comp_stabilization (n + 1))
    rw [fundamentalGroupContinuousHom_comp] at hcomm
    have hpoint (r : FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1) :=
      DFunLike.congr_fun hcomm r
    simp only [MonoidHom.comp_apply, fundamentalGroupContinuousHom_stabilization] at hpoint
    exact (hpoint p').symm.trans (hpq.trans (hpoint q'))

/-- The determinant gives the full fundamental-group classification. -/
def finiteUnitaryDeterminantFundamentalGroupEquiv (n : ℕ) :
    FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 ≃*
      FundamentalGroup Circle 1 :=
  MulEquiv.ofBijective
    (fundamentalGroupContinuousHom (finiteUnitaryDeterminant (Fin (n + 1))))
    (finiteUnitaryDeterminant_fundamentalGroup_bijective n)

/-- The fundamental group of `U(n+1)` is the integer winding group. -/
def finiteUnitaryFundamentalGroupEquivInt (n : ℕ) :
    FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 ≃* Multiplicative ℤ :=
  (finiteUnitaryDeterminantFundamentalGroupEquiv n).trans circleFundamentalGroupEquivInt

/-- Stabilization is injective on fundamental groups in every positive dimension. -/
theorem unitaryEmbedSuccFundamentalGroupMap_injective (n : ℕ) :
    Function.Injective (unitaryEmbedSuccFundamentalGroupMap (n + 1)) := by
  intro p q hpq
  apply (finiteUnitaryDeterminant_fundamentalGroup_bijective n).1
  have hcomm := congrArg fundamentalGroupContinuousHom
    (finiteUnitaryDeterminant_comp_stabilization (n + 1))
  rw [fundamentalGroupContinuousHom_comp] at hcomm
  have hpoint (r : FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1) :=
    DFunLike.congr_fun hcomm r
  have h := congrArg
    (fundamentalGroupContinuousHom (finiteUnitaryDeterminant (Fin (n + 2)))) hpq
  simp only [MonoidHom.comp_apply, fundamentalGroupContinuousHom_stabilization] at hpoint
  exact (hpoint p).symm.trans (h.trans (hpoint q))

/-- Stabilization is an isomorphism on fundamental groups. -/
def finiteUnitaryStabilizationFundamentalGroupEquiv (n : ℕ) :
    FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 ≃*
      FundamentalGroup (Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1 :=
  MulEquiv.ofBijective (fundamentalGroupContinuousHom (finiteUnitaryStabilizationHom (n + 1)))
    (by
      have heq : (fundamentalGroupContinuousHom (finiteUnitaryStabilizationHom (n + 1)) :
          FundamentalGroup (Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1 →
          FundamentalGroup (Matrix.unitaryGroup (Fin (n + 2)) ℂ) 1) =
          unitaryEmbedSuccFundamentalGroupMap (n + 1) :=
        funext (fundamentalGroupContinuousHom_stabilization (n + 1))
      rw [heq]
      exact ⟨unitaryEmbedSuccFundamentalGroupMap_injective n,
        unitaryEmbedSuccFundamentalGroupMap_surjective n⟩)

/-- Two unitary loops are homotopic exactly when their determinant loops are. -/
theorem finiteUnitary_loops_homotopic_iff_det (n : ℕ)
    (p q : Path (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) 1) :
    p.Homotopic q ↔
      ((p.map (finiteUnitaryDeterminant (Fin (n + 1))).continuous).cast
        (finiteUnitaryDeterminant (Fin (n + 1))).map_one.symm
        (finiteUnitaryDeterminant (Fin (n + 1))).map_one.symm).Homotopic
      ((q.map (finiteUnitaryDeterminant (Fin (n + 1))).continuous).cast
        (finiteUnitaryDeterminant (Fin (n + 1))).map_one.symm
        (finiteUnitaryDeterminant (Fin (n + 1))).map_one.symm) := by
  rw [← Path.Homotopic.Quotient.eq, ← Path.Homotopic.Quotient.eq,
    ← fundamentalGroupContinuousHom_mk, ← fundamentalGroupContinuousHom_mk]
  exact (finiteUnitaryDeterminant_fundamentalGroup_bijective n).1.eq_iff.symm

end

end GaloisForLFunctions.HTGeometry
