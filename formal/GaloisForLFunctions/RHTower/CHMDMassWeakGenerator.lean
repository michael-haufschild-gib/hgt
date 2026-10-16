import GaloisForLFunctions.RHTower.CHMDMassSpectralAdmission

/-!
# Actual generator admission from the compact operator core

A mass-continuous representation of the signed generator pairing gives an
explicit preimage under the arithmetic resolvent. For a known graph source,
the same identity follows directly from the defining Riesz equation.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

theorem signed_generator_pair_of_compact {w b : MassSpace}
    (h : ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v),
      ⟪genImageL v hv hc, w⟫_ℝ = ⟪b, sourceMap (compactLift v hv hc)⟫_ℝ)
    (u : arithmeticGenerator.domain) :
    ⟪arithmeticGenerator u - (u : MassSpace), w⟫_ℝ = ⟪b, (u : MassSpace)⟫_ℝ := by
  have hcore : ∀ u : arithmeticGenerator.domain,
      (∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
        (u : MassSpace) =ᵐ[massMeasure] v) →
      ⟪arithmeticGenerator u - (u : MassSpace), w⟫_ℝ = ⟪b, (u : MassSpace)⟫_ℝ := by
    intro u hu
    obtain ⟨v, hv, hc, hs⟩ := hu
    have he : u = arithmeticCompactDomain v hv hc := by
      apply Subtype.ext
      exact Lp.ext (hs.trans (compactLift_source_ae v hv hc).symm)
    rw [he, arithmeticCompactDomain_signed_image]
    exact h v hv hc
  obtain ⟨v, hv, hs, hg⟩ := arithmeticGenerator_compact_smooth_core u
  have ht : Tendsto
      (fun n => ⟪arithmeticGenerator (v n) - (v n : MassSpace), w⟫_ℝ -
        ⟪b, (v n : MassSpace)⟫_ℝ) atTop
      (𝓝 (⟪arithmeticGenerator u - (u : MassSpace), w⟫_ℝ - ⟪b, (u : MassSpace)⟫_ℝ)) :=
    ((hg.sub hs).inner tendsto_const_nhds).sub (tendsto_const_nhds.inner hs)
  have hz : ∀ n, ⟪arithmeticGenerator (v n) - (v n : MassSpace), w⟫_ℝ -
      ⟪b, (v n : MassSpace)⟫_ℝ = 0 := fun n => sub_eq_zero.mpr (hcore (v n) (hv n))
  have he : ⟪arithmeticGenerator u - (u : MassSpace), w⟫_ℝ -
      ⟪b, (u : MassSpace)⟫_ℝ = 0 :=
    tendsto_nhds_unique ht (by simp only [hz]; exact tendsto_const_nhds)
  exact sub_eq_zero.mp he

/-- The compact-core weak equation yields a literal resolvent preimage. -/
theorem resolvent_preimage_of_compact_pair {w b : MassSpace}
    (h : ∀ (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v),
      ⟪genImageL v hv hc, w⟫_ℝ = ⟪b, sourceMap (compactLift v hv hc)⟫_ℝ) :
    resolvent ((2 : ℝ) • w + b) = w := by
  apply ext_inner_right ℝ
  intro z
  have he := signed_generator_pair_of_compact h ⟨resolvent z, ⟨z, rfl⟩⟩
  erw [arithmeticGenerator_resolvent, inner_sub_left, inner_sub_left] at he
  change ⟪z, w⟫_ℝ - ⟪resolvent z, w⟫_ℝ - ⟪resolvent z, w⟫_ℝ =
    ⟪b, resolvent z⟫_ℝ at he
  rw [real_inner_comm w z, resolvent_symm z w,
    real_inner_comm (resolvent w) z, ← resolvent_symm b z] at he
  rw [map_add, map_smul, inner_add_left, real_inner_smul_left]
  linarith

theorem mem_arithmetic_domain_of_resolvent_preimage {w b : MassSpace}
    (h : resolvent ((2 : ℝ) • w + b) = w) : w ∈ arithmeticGenerator.domain :=
  ⟨(2 : ℝ) • w + b, h⟩

theorem arithmeticGenerator_of_resolvent_preimage {w b : MassSpace}
    (h : resolvent ((2 : ℝ) • w + b) = w) :
    arithmeticGenerator ⟨w, mem_arithmetic_domain_of_resolvent_preimage h⟩ = w + b := by
  have he := resolvent_injective ((arithmeticGenerator_identity
    ⟨w, mem_arithmetic_domain_of_resolvent_preimage h⟩).trans h.symm)
  rw [two_smul] at he
  exact add_left_cancel (he.trans (add_assoc _ _ _))

theorem graph_lift_of_resolvent_preimage {w b : MassSpace}
    (h : resolvent ((2 : ℝ) • w + b) = w) :
    sourceMap (rieszLift ((2 : ℝ) • w + b)) = w := h

theorem sourcePair_rieszLift_of_resolvent_preimage {w b : MassSpace}
    (h : resolvent ((2 : ℝ) • w + b) = w) (q : SourceGraph) :
    sourcePair (rieszLift ((2 : ℝ) • w + b)) q = ⟪b, sourceMap q⟫_ℝ := by
  rw [sourcePair_eq_graph_inner, inner_rieszLift,
    graph_lift_of_resolvent_preimage h, inner_add_left, real_inner_smul_left]
  change 2 * ⟪w, sourceMap q⟫_ℝ + ⟪b, sourceMap q⟫_ℝ -
    2 * ⟪w, sourceMap q⟫_ℝ = ⟪b, sourceMap q⟫_ℝ
  ring

theorem sourceEnergy_rieszLift_of_resolvent_preimage {w b : MassSpace}
    (h : resolvent ((2 : ℝ) • w + b) = w) :
    sourceEnergy (rieszLift ((2 : ℝ) • w + b)) = ⟪b, w⟫_ℝ := by
  rw [← sourcePair_self, sourcePair_rieszLift_of_resolvent_preimage h,
    graph_lift_of_resolvent_preimage h]

/-- A universal mass pairing for an actual graph vector identifies its
arithmetic resolvent preimage, without assuming operator-domain membership. -/
theorem resolvent_preimage_of_sourcePair {p : SourceGraph} {b : MassSpace}
    (h : ∀ q : SourceGraph, sourcePair p q = ⟪b, sourceMap q⟫_ℝ) :
    resolvent ((2 : ℝ) • sourceMap p + b) = sourceMap p := by
  have hr : rieszLift ((2 : ℝ) • sourceMap p + b) = p := by
    apply rieszLift_unique
    intro q
    have he := h q
    rw [sourcePair_eq_graph_inner] at he
    rw [inner_add_left, real_inner_smul_left]
    change ⟪p, q⟫_ℝ = 2 * ⟪sourceMap p, sourceMap q⟫_ℝ + ⟪b, sourceMap q⟫_ℝ
    linarith
  change sourceMap (rieszLift ((2 : ℝ) • sourceMap p + b)) = sourceMap p
  rw [hr]

end RHTower.CHMDDoobGraph
