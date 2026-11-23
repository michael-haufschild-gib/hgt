import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.LineClosure

/-! # Counting the missing dimensions of positive conserving propagation

The kernel of the unique admissible orthogonal projection measures the
omitted dimension. A one-dimensional kernel determines a single line.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap Submodule
open scoped InnerProductSpace

/-- The kernel has actual finite dimension r, including the zero-dimensional case. -/
def MissingDimension (P : Projection) (r : ℕ) : Prop :=
  FiniteDimensional ℂ P.val.toLinearMap.ker ∧ Module.finrank ℂ P.val.toLinearMap.ker = r

/-- Fourth-trace loss with the dimension of the omitted space fixed. -/
def lossesAtRank (r : ℕ) : Set ℝ := {y | ∃ P : Projection, MissingDimension P r ∧
  Conserving (projected P) ∧ traceLoss (projected P) = y}

private theorem projection_absorbs {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {P Q : H →L[ℂ] H} (hQ : Q*Q = Q)
    (hk : Q.toLinearMap.ker ≤ P.toLinearMap.ker) : P*Q = P := by
  apply ContinuousLinearMap.ext
  intro x
  have h : x-Q x ∈ Q.toLinearMap.ker := by
    change Q (x-Q x) = 0
    rw [map_sub,show Q (Q x) = Q x from congrArg (fun T : H →L[ℂ] H => T x) hQ,sub_self]
  have he : P (x-Q x) = 0 := hk h
  rw [map_sub,sub_eq_zero] at he
  exact he.symm

/-- A self-adjoint projection is determined by its kernel. -/
theorem projection_eq_of_ker {P Q : Projection} (hk : P.val.toLinearMap.ker = Q.val.toLinearMap.ker) :
    P = Q := by
  have h := projection_absorbs Q.property.isIdempotentElem.eq hk.ge
  have h' := congrArg star h
  rw [star_mul,P.property.isSelfAdjoint.star_eq,Q.property.isSelfAdjoint.star_eq] at h'
  exact Subtype.ext (h'.symm.trans (projection_absorbs P.property.isIdempotentElem.eq hk.le))

theorem omitLine_ker (v : Gas) : (omitLine v).val.toLinearMap.ker = ℂ ∙ v := by
  change (ℂ ∙ v)ᗮ.starProjection.toLinearMap.ker = _
  rw [Submodule.ker_starProjection,Submodule.orthogonal_orthogonal]

theorem missingDimension_one_iff (P : Projection) :
    MissingDimension P 1 ↔ ∃ v : Gas, v ≠ 0 ∧ P = omitLine v := by
  constructor
  · rintro ⟨_,hd⟩
    have h := (Submodule.isAtom_iff_finrank_eq_one.mpr hd).ne_bot
    obtain ⟨v,hv,hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    refine ⟨v,hv₀,projection_eq_of_ker ?_⟩
    rw [omitLine_ker,eq_span_singleton_of_mem_of_finrank_eq_one hd hv hv₀]
  · rintro ⟨v,hv,rfl⟩
    rw [MissingDimension,omitLine_ker]
    exact ⟨inferInstance,finrank_span_singleton hv⟩

/-- A finite projection misses no directions exactly when it is the identity. -/
theorem missingDimension_zero_iff (P : Projection) : MissingDimension P 0 ↔ P.val = 1 := by
  let I : Projection := ⟨1,IsStarProjection.one GasOp⟩
  have hk : I.val.toLinearMap.ker = ⊥ := LinearMap.ker_id
  constructor
  · rintro ⟨_,hd⟩
    have he := projection_eq_of_ker (P := P) (Q := I) ((Submodule.finrank_eq_zero.mp hd).trans hk.symm)
    exact congrArg Subtype.val he
  · intro he
    have hp : P = I := Subtype.ext he
    rw [hp,MissingDimension,hk]
    exact ⟨inferInstance,finrank_bot ℂ Gas⟩

theorem lossesAtRank_zero : lossesAtRank 0 = {0} := by
  let I : Projection := ⟨1,IsStarProjection.one GasOp⟩
  have hl : traceLoss criticalOperator = 0 := by
    rw [traceLoss,show (4:ℕ) = 2*2 from rfl,pow_mul,critical_fourth_trace,sub_self]
  ext y
  constructor
  · rintro ⟨P,hd,_,rfl⟩
    exact ((congrArg traceLoss ((projected_eq_critical_iff P).mpr ((missingDimension_zero_iff P).mp hd))).trans hl)
  · rintro rfl
    refine ⟨I,(missingDimension_zero_iff _).mpr rfl,(projected_conserves_iff _).mpr ?_,?_⟩
    · change Function.Injective ((1:GasOp)*criticalOperator)
      rw [one_mul]
      exact critical_injective
    · rw [(projected_eq_critical_iff I).mpr rfl,hl]

#print axioms lossesAtRank_zero
#print axioms projection_eq_of_ker
#print axioms missingDimension_one_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
