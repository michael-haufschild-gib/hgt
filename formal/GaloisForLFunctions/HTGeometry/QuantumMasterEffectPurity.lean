import GaloisForLFunctions.HTGeometry.QuantumMasterConstraintSpectrum

/-!
# Purity of a Hilbert--Schmidt quantum master effect

For a rectangular Hilbert--Schmidt channel `C`, the positive input-side effect `C† C` has
unnormalized order-two purity at most the square of its total mass:

`‖C† C‖²_HS ≤ ‖C‖⁴_HS`.

Since `Tr(C† C) = ‖C‖²_HS` and `Tr((C† C)²) = ‖C† C‖²_HS`, division by the squared mass gives
the usual density-operator purity bound `0 ≤ Tr(ρ²) ≤ 1`.  This formulation is rectangular and
therefore applies to constraint channels before their master effects are formed.

Physics provenance: direct measurement of the nonlinear functional `Tr(ρ²)` as quantum-state
purity is developed in A. K. Ekert, C. M. Alves, D. K. L. Oi, M. Horodecki, P. Horodecki, and
L. C. Kwek, *Physical Review Letters* 88 (2002), 217901,
DOI 10.1103/PhysRevLett.88.217901.
-/

open scoped BigOperators InnerProductSpace

namespace HTGeometry

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The normalized order-two purity of the input-side quantum master effect `C† C`.
The zero channel is assigned purity zero by the ambient field's zero-division convention. -/
def quantumMasterEffectPurity (C : E →L[ℂ] F) : ℝ :=
  ContinuousLinearMap.hsNormSq (ContinuousLinearMap.adjoint C ∘L C) /
    ContinuousLinearMap.hsNormSq C ^ (2 : ℕ)

/-- The Hilbert--Schmidt square of `C† C` is at most the fourth power of the Hilbert--Schmidt norm
of `C`.  Equivalently, `Tr((C† C)²) ≤ Tr(C† C)²`. -/
theorem hsNormSq_adjoint_comp_self_le_sq
    (C : E →L[ℂ] F) (hC : ContinuousLinearMap.IsHilbertSchmidt C) :
    ContinuousLinearMap.hsNormSq (ContinuousLinearMap.adjoint C ∘L C) ≤
      ContinuousLinearMap.hsNormSq C ^ (2 : ℕ) := by
  let b := ContinuousLinearMap.hsBasis ℂ E
  have hmaster : ContinuousLinearMap.IsHilbertSchmidt
      (ContinuousLinearMap.adjoint C ∘L C) :=
    hC.comp_left (ContinuousLinearMap.adjoint C)
  have hopSq : ‖C‖ ^ (2 : ℕ) ≤ ContinuousLinearMap.hsNormSq C := by
    have hop := ContinuousLinearMap.opNorm_le_hsNorm hC
    have hsquare : ‖C‖ ^ (2 : ℕ) ≤ ContinuousLinearMap.hsNorm C ^ (2 : ℕ) := by
      nlinarith [norm_nonneg C, ContinuousLinearMap.hsNorm_nonneg C]
    calc
      ‖C‖ ^ (2 : ℕ) ≤ ContinuousLinearMap.hsNorm C ^ (2 : ℕ) := hsquare
      _ = ContinuousLinearMap.hsNormSq C := by
        rw [ContinuousLinearMap.hsNorm,
          Real.sq_sqrt (ContinuousLinearMap.hsNormSq_nonneg C)]
  have hadjointNorm : ‖ContinuousLinearMap.adjoint C‖ = ‖C‖ := by
    exact (ContinuousLinearMap.adjoint :
      (E →L[ℂ] F) ≃ₗᵢ⋆[ℂ] (F →L[ℂ] E)).norm_map C
  calc
    ContinuousLinearMap.hsNormSq (ContinuousLinearMap.adjoint C ∘L C) =
        ∑' i, ‖(ContinuousLinearMap.adjoint C ∘L C) (b i)‖ ^ (2 : ℕ) :=
      ContinuousLinearMap.hsNormSq_eq hmaster b
    _ ≤ ∑' i, ‖ContinuousLinearMap.adjoint C‖ ^ (2 : ℕ) * ‖C (b i)‖ ^ (2 : ℕ) :=
      (hmaster.summable b).tsum_le_tsum (fun i => by
        calc
          ‖(ContinuousLinearMap.adjoint C ∘L C) (b i)‖ ^ (2 : ℕ) =
              ‖ContinuousLinearMap.adjoint C (C (b i))‖ ^ (2 : ℕ) := by
            rw [ContinuousLinearMap.comp_apply]
          _ ≤ (‖ContinuousLinearMap.adjoint C‖ * ‖C (b i)‖) ^ (2 : ℕ) := by
            gcongr
            exact (ContinuousLinearMap.adjoint C).le_opNorm _
          _ = ‖ContinuousLinearMap.adjoint C‖ ^ (2 : ℕ) * ‖C (b i)‖ ^ (2 : ℕ) := by
            ring)
        ((hC.summable b).mul_left (‖ContinuousLinearMap.adjoint C‖ ^ (2 : ℕ)))
    _ = ‖ContinuousLinearMap.adjoint C‖ ^ (2 : ℕ) *
        ContinuousLinearMap.hsNormSq C := by
      rw [tsum_mul_left, ← ContinuousLinearMap.hsNormSq_eq hC b]
    _ = ‖C‖ ^ (2 : ℕ) * ContinuousLinearMap.hsNormSq C := by
      rw [hadjointNorm]
    _ ≤ ContinuousLinearMap.hsNormSq C *
        ContinuousLinearMap.hsNormSq C :=
      mul_le_mul_of_nonneg_right hopSq
        (ContinuousLinearMap.hsNormSq_nonneg C)
    _ = ContinuousLinearMap.hsNormSq C ^ (2 : ℕ) := by
      ring

/-- Quantum master-effect purity is nonnegative, with no summability premise. -/
theorem quantumMasterEffectPurity_nonneg (C : E →L[ℂ] F) :
    0 ≤ quantumMasterEffectPurity C := by
  exact div_nonneg
    (ContinuousLinearMap.hsNormSq_nonneg (ContinuousLinearMap.adjoint C ∘L C))
    (sq_nonneg (ContinuousLinearMap.hsNormSq C))

/-- Every Hilbert--Schmidt channel has master-effect purity at most one.  For the zero channel the
purity is zero; otherwise this is the unnormalized purity inequality divided by positive mass. -/
theorem quantumMasterEffectPurity_le_one
    (C : E →L[ℂ] F) (hC : ContinuousLinearMap.IsHilbertSchmidt C) :
    quantumMasterEffectPurity C ≤ 1 := by
  by_cases hzero : C = 0
  · subst C
    simp [quantumMasterEffectPurity, ContinuousLinearMap.hsNormSq]
  · have hmassNe : ContinuousLinearMap.hsNormSq C ≠ 0 := by
      intro hmass
      exact hzero ((ContinuousLinearMap.hsNormSq_eq_zero_iff hC).mp hmass)
    have hmassPos : 0 < ContinuousLinearMap.hsNormSq C :=
      lt_of_le_of_ne (ContinuousLinearMap.hsNormSq_nonneg C) (Ne.symm hmassNe)
    rw [quantumMasterEffectPurity, div_le_iff₀ (sq_pos_of_pos hmassPos)]
    simpa only [one_mul] using hsNormSq_adjoint_comp_self_le_sq C hC

/-- The normalized master-effect purity belongs to the physical interval `[0,1]`. -/
theorem quantumMasterEffectPurity_mem_Icc
    (C : E →L[ℂ] F) (hC : ContinuousLinearMap.IsHilbertSchmidt C) :
    quantumMasterEffectPurity C ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨quantumMasterEffectPurity_nonneg C, quantumMasterEffectPurity_le_one C hC⟩

section SquareConstraint

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a square constraint, rectangular master-effect purity is literally the normalized trace
ratio `Re Tr(T²) / Re Tr(T)²`, where `T = C† C`. -/
theorem quantumMasterEffectPurity_eq_traceRatio
    (C : H →L[ℂ] H) (hC : ContinuousLinearMap.IsHilbertSchmidt C) :
    quantumMasterEffectPurity C =
      RCLike.re (ContinuousLinearMap.opTrace
          (quantumMasterConstraint C ∘L quantumMasterConstraint C)) /
        RCLike.re (ContinuousLinearMap.opTrace
          (quantumMasterConstraint C)) ^ (2 : ℕ) := by
  let T := quantumMasterConstraint C
  have hT : ContinuousLinearMap.IsHilbertSchmidt T := by
    exact hC.comp_left (ContinuousLinearMap.adjoint C)
  have hself : ContinuousLinearMap.adjoint T = T := by
    simp only [T, quantumMasterConstraint,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  have hnum : RCLike.re (ContinuousLinearMap.opTrace (T ∘L T)) =
      ContinuousLinearMap.hsNormSq T := by
    calc
      RCLike.re (ContinuousLinearMap.opTrace (T ∘L T)) =
          RCLike.re (ContinuousLinearMap.opTrace
            (ContinuousLinearMap.adjoint T ∘L T)) := by
        rw [hself]
      _ = ContinuousLinearMap.hsNormSq T :=
        ContinuousLinearMap.re_opTrace_adjoint_comp_self hT
  have hden : RCLike.re (ContinuousLinearMap.opTrace T) =
      ContinuousLinearMap.hsNormSq C := by
    exact re_opTrace_quantumMasterConstraint_eq_hsNormSq hC
  calc
    quantumMasterEffectPurity C =
        ContinuousLinearMap.hsNormSq T /
          ContinuousLinearMap.hsNormSq C ^ (2 : ℕ) := by
      rfl
    _ = RCLike.re (ContinuousLinearMap.opTrace (T ∘L T)) /
          RCLike.re (ContinuousLinearMap.opTrace T) ^ (2 : ℕ) := by
      rw [hnum, hden]

/-- Trace form of the quantum-state purity inequality for every Hilbert--Schmidt master
constraint. -/
theorem re_opTrace_sq_quantumMasterConstraint_le_sq_trace
    (C : H →L[ℂ] H) (hC : ContinuousLinearMap.IsHilbertSchmidt C) :
    RCLike.re (ContinuousLinearMap.opTrace
        (quantumMasterConstraint C ∘L quantumMasterConstraint C)) ≤
      RCLike.re (ContinuousLinearMap.opTrace
        (quantumMasterConstraint C)) ^ (2 : ℕ) := by
  let T := quantumMasterConstraint C
  have hT : ContinuousLinearMap.IsHilbertSchmidt T := by
    exact hC.comp_left (ContinuousLinearMap.adjoint C)
  have hself : ContinuousLinearMap.adjoint T = T := by
    simp only [T, quantumMasterConstraint,
      ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  calc
    RCLike.re (ContinuousLinearMap.opTrace (T ∘L T)) =
        ContinuousLinearMap.hsNormSq T := by
      calc
        RCLike.re (ContinuousLinearMap.opTrace (T ∘L T)) =
            RCLike.re (ContinuousLinearMap.opTrace
              (ContinuousLinearMap.adjoint T ∘L T)) := by
          rw [hself]
        _ = ContinuousLinearMap.hsNormSq T :=
          ContinuousLinearMap.re_opTrace_adjoint_comp_self hT
    _ ≤ ContinuousLinearMap.hsNormSq C ^ (2 : ℕ) := by
      simpa only [T, quantumMasterConstraint] using
        hsNormSq_adjoint_comp_self_le_sq C hC
    _ = RCLike.re (ContinuousLinearMap.opTrace T) ^ (2 : ℕ) := by
      rw [re_opTrace_quantumMasterConstraint_eq_hsNormSq hC]

/-- The master-constraint trace ratio is a physical purity in `[0,1]`. -/
theorem quantumMasterConstraint_tracePurity_mem_Icc
    (C : H →L[ℂ] H) (hC : ContinuousLinearMap.IsHilbertSchmidt C) :
    RCLike.re (ContinuousLinearMap.opTrace
          (quantumMasterConstraint C ∘L quantumMasterConstraint C)) /
        RCLike.re (ContinuousLinearMap.opTrace
          (quantumMasterConstraint C)) ^ (2 : ℕ) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [← quantumMasterEffectPurity_eq_traceRatio C hC]
  exact quantumMasterEffectPurity_mem_Icc C hC

end SquareConstraint

end

end HTGeometry
