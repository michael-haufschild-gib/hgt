import GaloisForLFunctions.RHTower.DeningerMeyerHalfDensityXiGraphClosure
import GaloisForLFunctions.RHTower.DeningerMeyerFiniteXiJetPacket

open Complex Filter Set Topology
open scoped Classical

namespace RHTower

noncomputable section

/-- Simultaneous zeroth Xi evaluation on a finite divisor packet. -/
def deningerMeyerFiniteXiZerothPacketLM
    (S : Finset XiDivisorSupport) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] (↥S → ℂ) :=
  LinearMap.pi fun rho =>
    deningerMeyerXiSupportJetEvaluationLM rho.1
      (⟨0, xiSupportMultiplicity_pos rho.1⟩ :
        DeningerArithmeticJetIndex rho.1)

@[simp]
theorem deningerMeyerFiniteXiZerothPacketLM_apply
    (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) (rho : ↥S) :
    deningerMeyerFiniteXiZerothPacketLM S u rho =
      deningerMeyerHalfDensityXiEvaluationLM rho.1 u :=
  rfl

theorem deningerMeyerFiniteXiZerothPacketLM_linearIndependent
    (S : Finset XiDivisorSupport) :
    LinearIndependent ℂ
      (fun rho : ↥S =>
        deningerMeyerXiSupportJetEvaluationLM rho.1
          (⟨0, xiSupportMultiplicity_pos rho.1⟩ :
            DeningerArithmeticJetIndex rho.1)) := by
  let slot : ↥S → DeningerMeyerFiniteXiJetSlot S := fun rho =>
    ⟨rho, ⟨0, xiSupportMultiplicity_pos rho.1⟩⟩
  have hslot : Function.Injective slot := by
    intro rho sigma h
    exact congrArg Sigma.fst h
  have h :=
    (deningerMeyerFiniteXiSupportJetEvaluationLM_linearIndependent S).comp
      slot hslot
  change LinearIndependent ℂ
    (fun rho : ↥S => deningerMeyerXiSupportJetEvaluationLM rho.1 (slot rho).2)
  exact h

theorem deningerMeyerFiniteXiZerothPacketLM_surjective
    (S : Finset XiDivisorSupport) :
    Function.Surjective (deningerMeyerFiniteXiZerothPacketLM S) :=
  piMap_surjective_of_linearIndependent _
    (deningerMeyerFiniteXiZerothPacketLM_linearIndependent S)

/-- Literal Meyer class isolating one zeroth evaluation in a finite packet. -/
def deningerMeyerFiniteXiZerothBasisClass
    (S : Finset XiDivisorSupport) (rho : ↥S) :
    DeningerMeyerStrongLogCohomology :=
  Classical.choose
    (deningerMeyerFiniteXiZerothPacketLM_surjective S
      (Pi.single rho (1 : ℂ)))

@[simp]
theorem deningerMeyerFiniteXiZerothBasisClass_evaluation
    (S : Finset XiDivisorSupport) (rho sigma : ↥S) :
    deningerMeyerHalfDensityXiEvaluationLM sigma.1
        (deningerMeyerFiniteXiZerothBasisClass S rho) =
      (Pi.single rho (1 : ℂ) : ↥S → ℂ) sigma := by
  have h := Classical.choose_spec
    (deningerMeyerFiniteXiZerothPacketLM_surjective S
      (Pi.single rho (1 : ℂ)))
  exact congrFun h sigma

/-- Rescaled centered orbit isolating one off-line Xi coordinate. -/
def deningerMeyerFiniteXiZerothGraphNullAtom
    (S : Finset XiDivisorSupport) (rho : ↥S) (n : ℕ) :
    DeningerMeyerStrongLogCohomology :=
  Complex.exp
      (-((deningerMeyerHalfDensityXiGraphTime rho.1 n : ℝ) : ℂ) *
        ((rho.1 : ℂ) - 1 / 2)) •
    deningerMeyerStrongLogCenteredCohomologyFlow
      (deningerMeyerHalfDensityXiGraphTime rho.1 n)
      (deningerMeyerFiniteXiZerothBasisClass S rho)

theorem deningerMeyerFiniteXiZerothGraphNullAtom_evaluation
    (S : Finset XiDivisorSupport) (rho sigma : ↥S) (n : ℕ) :
    deningerMeyerHalfDensityXiEvaluationLM sigma.1
        (deningerMeyerFiniteXiZerothGraphNullAtom S rho n) =
      (Pi.single rho (1 : ℂ) : ↥S → ℂ) sigma := by
  rw [deningerMeyerFiniteXiZerothGraphNullAtom, map_smul,
    deningerMeyerXiSupportEvaluationLM_centeredFlow,
    deningerMeyerFiniteXiZerothBasisClass_evaluation]
  by_cases h : sigma = rho
  · subst sigma
    rw [Pi.single_eq_same, mul_one, smul_eq_mul, ← Complex.exp_add]
    rw [show
      -((deningerMeyerHalfDensityXiGraphTime rho.1 n : ℝ) : ℂ) *
            ((rho.1 : ℂ) - 1 / 2) +
          ((deningerMeyerHalfDensityXiGraphTime rho.1 n : ℝ) : ℂ) *
            ((rho.1 : ℂ) - 1 / 2) = 0 by ring,
      Complex.exp_zero]
  · rw [Pi.single_eq_of_ne h]
    simp

theorem deningerMeyerFiniteXiZerothGraphNullAtom_tendsto_zero
    (S : Finset XiDivisorSupport) (rho : ↥S)
    (hrho : (rho.1 : ℂ).re ≠ 1 / 2) :
    Tendsto
      (fun n => deningerMeyerHalfDensityCompletionMk
        (deningerMeyerFiniteXiZerothGraphNullAtom S rho n))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hrate : deningerMeyerHalfDensityXiHorizontalRate rho.1 ≠ 0 := by
    rw [deningerMeyerHalfDensityXiHorizontalRate]
    exact sub_ne_zero.mpr hrho
  have hrateSq : 0 < deningerMeyerHalfDensityXiHorizontalRate rho.1 ^ (2 : ℕ) :=
    sq_pos_of_ne_zero hrate
  have htop :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) * deningerMeyerHalfDensityXiHorizontalRate rho.1 ^ (2 : ℕ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hrateSq
  have hdecay :
      Tendsto
        (fun n : ℕ => Real.exp
          (-((n : ℝ) * deningerMeyerHalfDensityXiHorizontalRate rho.1 ^ (2 : ℕ))))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp htop)
  have hnorm :
      (fun n => ‖deningerMeyerHalfDensityCompletionMk
        (deningerMeyerFiniteXiZerothGraphNullAtom S rho n)‖) =
      (fun n : ℕ => Real.exp
          (-((n : ℝ) * deningerMeyerHalfDensityXiHorizontalRate rho.1 ^ (2 : ℕ))) *
        ‖deningerMeyerHalfDensityCompletionMk
          (deningerMeyerFiniteXiZerothBasisClass S rho)‖) := by
    funext n
    rw [deningerMeyerFiniteXiZerothGraphNullAtom, map_smul, norm_smul,
      deningerMeyerHalfDensityCompletionMk_norm,
      deningerMeyerHalfDensityCohomologySeminorm_centeredFlow,
      ← deningerMeyerHalfDensityCompletionMk_norm, Complex.norm_exp]
    congr 2
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.div_ofNat_re, Complex.one_re]
    rw [deningerMeyerHalfDensityXiGraphTime,
      deningerMeyerHalfDensityXiHorizontalRate]
    ring
  rw [hnorm]
  simpa [mul_comm] using hdecay.const_mul
    ‖deningerMeyerHalfDensityCompletionMk
      (deningerMeyerFiniteXiZerothBasisClass S rho)‖

/-- A finite packet of independently rescaled graph-null atoms. -/
def deningerMeyerFiniteXiZerothGraphNullSequence
    (S : Finset XiDivisorSupport) (y : ↥S → ℂ) (n : ℕ) :
    DeningerMeyerStrongLogCohomology :=
  ∑ rho : ↥S, y rho • deningerMeyerFiniteXiZerothGraphNullAtom S rho n

theorem deningerMeyerFiniteXiZerothGraphNullSequence_evaluation
    (S : Finset XiDivisorSupport) (y : ↥S → ℂ)
    (sigma : ↥S) (n : ℕ) :
    deningerMeyerHalfDensityXiEvaluationLM sigma.1
        (deningerMeyerFiniteXiZerothGraphNullSequence S y n) = y sigma := by
  simp only [deningerMeyerFiniteXiZerothGraphNullSequence, map_sum,
    map_smul, deningerMeyerFiniteXiZerothGraphNullAtom_evaluation,
    smul_eq_mul]
  rw [Finset.sum_eq_single sigma]
  · rw [Pi.single_eq_same, mul_one]
  · intro rho _ hrho
    rw [Pi.single_eq_of_ne (Ne.symm hrho)]
    simp
  · simp

theorem deningerMeyerFiniteXiZerothGraphNullSequence_tendsto_zero
    (S : Finset XiDivisorSupport)
    (hoffline : ∀ rho : ↥S, (rho.1 : ℂ).re ≠ 1 / 2)
    (y : ↥S → ℂ) :
    Tendsto
      (fun n => deningerMeyerHalfDensityCompletionMk
        (deningerMeyerFiniteXiZerothGraphNullSequence S y n))
      atTop (𝓝 0) := by
  have hsum := tendsto_finsetSum (Finset.univ : Finset ↥S)
    (fun rho _ =>
      (deningerMeyerFiniteXiZerothGraphNullAtom_tendsto_zero
        S rho (hoffline rho)).const_smul (y rho))
  simpa [deningerMeyerFiniteXiZerothGraphNullSequence, map_sum, map_smul] using hsum

/-- Joint graph of the finite zeroth Xi packet in the canonical half-density completion. -/
def deningerMeyerFiniteXiZerothGraph
    (S : Finset XiDivisorSupport) :
    Submodule ℂ (DeningerMeyerHalfDensityCompletion × (↥S → ℂ)) :=
  LinearMap.range
    (LinearMap.prod deningerMeyerHalfDensityCompletionMk
      (deningerMeyerFiniteXiZerothPacketLM S))

/-- Every finite packet of off-line Xi points becomes a full vertical defect space. -/
theorem deningerMeyerFiniteXiZerothGraph_fullVertical_of_offline
    (S : Finset XiDivisorSupport)
    (hoffline : ∀ rho : ↥S, (rho.1 : ℂ).re ≠ 1 / 2)
    (y : ↥S → ℂ) :
    ((0 : DeningerMeyerHalfDensityCompletion), y) ∈
      (deningerMeyerFiniteXiZerothGraph S).topologicalClosure := by
  change ((0 : DeningerMeyerHalfDensityCompletion), y) ∈
    closure (deningerMeyerFiniteXiZerothGraph S : Set
      (DeningerMeyerHalfDensityCompletion × (↥S → ℂ)))
  apply mem_closure_of_tendsto
    ((deningerMeyerFiniteXiZerothGraphNullSequence_tendsto_zero
      S hoffline y).prodMk_nhds
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)))
  filter_upwards with n
  refine ⟨deningerMeyerFiniteXiZerothGraphNullSequence S y n, ?_⟩
  apply Prod.ext
  · rfl
  · funext sigma
    exact deningerMeyerFiniteXiZerothGraphNullSequence_evaluation S y sigma n

/-- Vertical defect fibre of the closed finite Xi graph. -/
def deningerMeyerFiniteXiZerothGraphVertical
    (S : Finset XiDivisorSupport) : Submodule ℂ (↥S → ℂ) :=
  (deningerMeyerFiniteXiZerothGraph S).topologicalClosure.comap
    (LinearMap.inr ℂ DeningerMeyerHalfDensityCompletion (↥S → ℂ))

@[simp]
theorem mem_deningerMeyerFiniteXiZerothGraphVertical
    (S : Finset XiDivisorSupport) (y : ↥S → ℂ) :
    y ∈ deningerMeyerFiniteXiZerothGraphVertical S ↔
      ((0 : DeningerMeyerHalfDensityCompletion), y) ∈
        (deningerMeyerFiniteXiZerothGraph S).topologicalClosure :=
  Iff.rfl

/-- The vertical defect fibre is the full packet space when every selected point is off line. -/
theorem deningerMeyerFiniteXiZerothGraphVertical_eq_top_of_offline
    (S : Finset XiDivisorSupport)
    (hoffline : ∀ rho : ↥S, (rho.1 : ℂ).re ≠ 1 / 2) :
    deningerMeyerFiniteXiZerothGraphVertical S = ⊤ := by
  apply top_unique
  intro y _
  exact deningerMeyerFiniteXiZerothGraph_fullVertical_of_offline S hoffline y

/-- Exact finite defect index: one independent vertical direction per selected off-line zero. -/
theorem finrank_deningerMeyerFiniteXiZerothGraphVertical_of_offline
    (S : Finset XiDivisorSupport)
    (hoffline : ∀ rho : ↥S, (rho.1 : ℂ).re ≠ 1 / 2) :
    Module.finrank ℂ (deningerMeyerFiniteXiZerothGraphVertical S) = S.card := by
  rw [deningerMeyerFiniteXiZerothGraphVertical_eq_top_of_offline S hoffline]
  simp

end
end RHTower
