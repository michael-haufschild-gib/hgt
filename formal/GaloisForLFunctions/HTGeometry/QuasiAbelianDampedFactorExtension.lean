import GaloisForLFunctions.HTGeometry.QuasiAbelianPositiveFactorJetAmple
import GaloisForLFunctions.HTGeometry.QuasiAbelianFiniteJetPeeling

/-!
# Damped subgroup extensions preserve all-order jet ampleness

This file formalizes Abe's subgroup-rank induction.  An extension contains actual upper-lattice
forms, their literal complement-lattice remainder terms, a pointwise Poincare decomposition, and
the polynomial-Gaussian damping estimate.  The estimate proves local uniform convergence back to
the lower-lattice form.  Determinant continuity then transfers every finite jet packet.
-/

open Filter Function Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Packet-specific output of one normalized Abe damping construction.  The upper columns are
actual upper-factor forms.  Their finite mixed-jet matrix differs from the chosen lower columns by
the actual complement-lattice `tsum`, whose terms carry the quantitative damping majorant. -/
structure AbeDampedJetPacketLift
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (upper : AutomorphicFactor d Γ)
    {I : Type u} [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ) (m : I → ℕ)
    (lowerColumn : FiniteJetPacketIndex d I m → MultivariateEntire d) where
  complementRank : ℕ
  upperColumn : ℝ → FiniteJetPacketIndex d I m → upper.forms
  remainderTerm : ℝ → (Fin complementRank → ℤ) →
    FiniteJetPacketIndex d I m → FiniteJetPacketIndex d I m → ℂ
  jet_decomposition : ∀ (B : ℝ) (i j : FiniteJetPacketIndex d I m),
    multiIndexJetEvalCLM (w i.1) i.2.1 (upperColumn B j).1 =
      multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j) +
        ∑' z, remainderTerm B z i j
  remainderMajorant :
    ∃ (A : Fin complementRank → ℕ) (sigma : Fin complementRank → ℝ)
      (r : ℕ) (delta C : ℝ),
      (∀ i, 0 < sigma i) ∧ 0 < delta ∧ 0 ≤ C ∧
      ∀ B : ℝ, 0 ≤ B → ∀ z i j,
        ‖remainderTerm B z i j‖ ≤
          (C * (B ^ r * Real.exp (-(delta * B)))) *
            polynomialGaussianLatticeWeight (Fin complementRank) A sigma z

/-- Every scalar entry of the actual complement-lattice remainder tends to zero. -/
theorem AbeDampedJetPacketLift.remainder_tendsto_zero
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    {upper : AutomorphicFactor d Γ}
    {I : Type u} [Fintype I] [DecidableEq I]
    {w : I → Fin d → ℂ} {m : I → ℕ}
    {lowerColumn : FiniteJetPacketIndex d I m → MultivariateEntire d}
    (L : AbeDampedJetPacketLift upper w m lowerColumn)
    (i j : FiniteJetPacketIndex d I m) :
    Tendsto (fun B ↦ ∑' z, L.remainderTerm B z i j)
      Filter.atTop (nhds 0) := by
  obtain ⟨A, sigma, r, delta, C, hsigma, hdelta, hC, hbound⟩ :=
    L.remainderMajorant
  have hlocal : TendstoLocallyUniformly
      (fun B (_ : Unit) ↦ ∑' z, L.remainderTerm B z i j)
      (fun _ ↦ 0) Filter.atTop := by
    apply tendstoLocallyUniformly_tsum_zero_of_polynomialGaussian_damping_bound
      (fun B z (_ : Unit) ↦ L.remainderTerm B z i j)
      A sigma hsigma r delta hdelta
    intro K hK
    exact ⟨C, hC, fun B hB z x hx ↦ hbound B hB z i j⟩
  simpa using hlocal.tendstoLocallyUniformlyOn.tendsto_at
    (Set.mem_univ Unit.unit)

/-- One literal subgroup-rank extension step.  It lifts arbitrary lower packet columns to upper
Poincare columns together with the exact normalized complement remainder and its damping bound. -/
structure AbeDampedFactorExtension
    {d : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    (lower : AutomorphicFactor d ΓH) (upper : AutomorphicFactor d Γ) where
  subgroup_le : ΓH ≤ Γ
  liftPacket : ∀ (I : Type u) [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ) (m : I → ℕ)
    (lowerColumn : FiniteJetPacketIndex d I m → lower.forms),
    AbeDampedJetPacketLift upper w m (fun j ↦ (lowerColumn j).1)

/-- **Abe subgroup-rank induction step.**  All-order jet ampleness of the lower factor and the
literal damped packet lift imply all-order jet ampleness of the upper factor. -/
theorem AbeDampedFactorExtension.jetAmpleEveryFiniteOrder
    {d : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    {lower : AutomorphicFactor d ΓH} {upper : AutomorphicFactor d Γ}
    (E : AbeDampedFactorExtension.{u} lower upper)
    (hlower : AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} lower) :
    AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} upper := by
  intro I _ _ w m hdistinct hm
  classical
  let Q := FiniteJetPacketIndex d I m
  let basisTarget : Q → Q → ℂ := fun j i ↦ if i = j then 1 else 0
  have hlowerDistinct : PairwiseDistinctModulo ΓH w := by
    intro i j hij hmem
    exact hdistinct hij (E.subgroup_le hmem)
  have hexact (j : Q) : ∃ f : lower.forms,
      lower.jetPacketLinearMap w m f = basisTarget j :=
    hlower I w m hlowerDistinct hm (basisTarget j)
  let lowerColumn : Q → lower.forms := fun j ↦ Classical.choose (hexact j)
  have hlowerColumn (j : Q) :
      lower.jetPacketLinearMap w m (lowerColumn j) = basisTarget j :=
    Classical.choose_spec (hexact j)
  let L := E.liftPacket I w m lowerColumn
  let M : ℝ → Matrix Q Q ℂ := fun B ↦ Matrix.of fun i j ↦
    multiIndexJetEvalCLM (w i.1) i.2.1 (L.upperColumn B j).1
  have hmatrix : Tendsto M Filter.atTop (nhds (1 : Matrix Q Q ℂ)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have herr := L.remainder_tendsto_zero i j
    have hentry : Tendsto
        (fun B : ℝ ↦
          multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1 +
            ∑' z, L.remainderTerm B z i j)
        Filter.atTop
        (nhds (multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1 + 0)) :=
      (tendsto_const_nhds : Tendsto
        (fun _ : ℝ ↦ multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1)
        Filter.atTop
        (nhds (multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1))).add herr
    have hlowerEntry :
        multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1 =
          (1 : Matrix Q Q ℂ) i j := by
      have hij := congrFun (hlowerColumn j) i
      simpa [basisTarget, Matrix.one_apply] using hij
    rw [← hlowerEntry]
    simpa only [M, Matrix.of_apply, L.jet_decomposition, add_zero] using hentry
  have hdet : Tendsto (fun B ↦ (M B).det) Filter.atTop (nhds 1) := by
    change Tendsto ((fun X : Matrix Q Q ℂ ↦ X.det) ∘ M)
      Filter.atTop (nhds 1)
    simpa [Function.comp_def] using
      continuous_id.matrix_det.continuousAt.tendsto.comp hmatrix
  have heventually : ∀ᶠ B in Filter.atTop, (M B).det ≠ 0 :=
    hdet.eventually (eventually_ne_nhds one_ne_zero)
  obtain ⟨B, hB⟩ := heventually.exists
  letI : AddCommGroup upper.forms := Module.addCommMonoidToAddCommGroup ℂ
  exact linearMap_surjective_of_evaluationMatrix_det_ne_zero
    (upper.jetPacketLinearMap w m) (L.upperColumn B) (by
      simpa only [M, AutomorphicFactor.jetPacketLinearMap_apply] using hB)

/-- A finite positive-factor subgroup tower: explicit positive integer-lattice base followed by
finitely many literal damped Poincare extensions. -/
inductive AbePositiveFactorTower (d : ℕ) :
    {Γ : AddSubgroup (Fin d → ℂ)} → AutomorphicFactor d Γ → Type (u + 1)
  | base (P : AbePositiveFactorPresentation.{u} d) :
      AbePositiveFactorTower d P.factor
  | extension
      {ΓH Γ : AddSubgroup (Fin d → ℂ)}
      {lower : AutomorphicFactor d ΓH} {upper : AutomorphicFactor d Γ}
      (previous : AbePositiveFactorTower d lower)
      (step : AbeDampedFactorExtension.{u} lower upper) :
      AbePositiveFactorTower d upper

/-- Every factor reached by Abe's positive subgroup tower is jet ample at every finite order. -/
theorem AbePositiveFactorTower.jetAmpleEveryFiniteOrder
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    {ψ : AutomorphicFactor d Γ} (T : AbePositiveFactorTower.{u} d ψ) :
    AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} ψ := by
  induction T with
  | base P => exact P.jetAmpleEveryFiniteOrder
  | extension previous step ih =>
      exact step.jetAmpleEveryFiniteOrder ih

/-- Exact Lean predicate for a positive torusless quasi-Abelian automorphic factor: it has Abe's
finite positive base-and-damped-extension presentation. -/
def AutomorphicFactor.IsAbePositiveTorusless
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) : Prop :=
  Nonempty (AbePositiveFactorTower.{u} d ψ)

/-- **Torusless fixed-factor all-order jet ampleness.**  Every positive torusless factor in Abe's
literal base-and-extension presentation interpolates every finite mixed-jet packet. -/
theorem AutomorphicFactor.jetAmpleEveryFiniteOrder_of_isAbePositiveTorusless
    {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ)
    (hpositive : AutomorphicFactor.IsAbePositiveTorusless.{u} ψ) :
    AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} ψ :=
  hpositive.some.jetAmpleEveryFiniteOrder

end

end GaloisForLFunctions.HTGeometry
