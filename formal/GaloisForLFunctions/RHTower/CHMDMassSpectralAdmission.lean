import GaloisForLFunctions.RHTower.CHMDMassMixedExplicitFormula
import GaloisForLFunctions.RHTower.CHMDFullSpectralNullspace
import GaloisForLFunctions.RHTower.CHMDCompactSmoothOperatorCore

/-!
# Spectral silence forces maximal-domain admission

The joint kernel of the literal Xi-zero and polar samples in the full mass
Hilbert space is exactly the one-half eigenspace of the arithmetic resolvent.
The nontrivial direction starts with no energy-domain regularity: the mixed
explicit formula and compact C2 operator core force the resolvent identity.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

def MassSpectrallySilent (w : MassSpace) : Prop :=
  (∀ z : ℂ, XiC z = 0 → massFourierReadout w z = 0) ∧
    massFourierReadout w (I/2) = 0 ∧ massFourierReadout w (-I/2) = 0

theorem compact_source_resolvent_preimage {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hc : HasCompactSupport v) :
    resolvent ((2 : ℝ) • (compactLift v hv hc).val.fst + genImageL v hv hc) =
      (compactLift v hv hc).val.fst := by
  rw [map_add, map_smul, resolvent_compactLift_source hv hc,
    smul_sub, smul_smul, smul_smul]
  norm_num

def arithmeticCompactDomain (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hc : HasCompactSupport v) : arithmeticGenerator.domain :=
  ⟨(compactLift v hv hc).val.fst,
    ⟨(2 : ℝ) • (compactLift v hv hc).val.fst + genImageL v hv hc,
      compact_source_resolvent_preimage hv hc⟩⟩

theorem arithmeticCompactDomain_signed_image (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hc : HasCompactSupport v) :
    arithmeticGenerator (arithmeticCompactDomain v hv hc) -
      (arithmeticCompactDomain v hv hc : MassSpace) = genImageL v hv hc := by
  have he := resolvent_injective ((arithmeticGenerator_identity
    (arithmeticCompactDomain v hv hc)).trans (compact_source_resolvent_preimage hv hc).symm)
  change (compactLift v hv hc).val.fst + arithmeticGenerator (arithmeticCompactDomain v hv hc) =
    (2 : ℝ) • (compactLift v hv hc).val.fst + genImageL v hv hc at he
  rw [two_smul] at he
  have he' : arithmeticGenerator (arithmeticCompactDomain v hv hc) =
      (compactLift v hv hc).val.fst + genImageL v hv hc :=
    add_left_cancel (he.trans (add_assoc _ _ _))
  change arithmeticGenerator (arithmeticCompactDomain v hv hc) -
    (compactLift v hv hc).val.fst = _
  rw [he']
  abel

theorem silent_inner_signed_generator_compact {w : MassSpace} (hw : MassSpectrallySilent w)
    (u : arithmeticGenerator.domain)
    (hu : ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧ (u : MassSpace) =ᵐ[massMeasure] v) :
    ⟪arithmeticGenerator u - (u : MassSpace), w⟫_ℝ = 0 := by
  obtain ⟨v, hv, hc, hs⟩ := hu
  have he : u = arithmeticCompactDomain v hv hc := by
    apply Subtype.ext
    exact Lp.ext (hs.trans (compactLift_source_ae v hv hc).symm)
  rw [he, arithmeticCompactDomain_signed_image]
  exact inner_genImage_eq_zero_of_samples hw.1 hw.2.1 hw.2.2 hv hc

/-- Operator-core density upgrades the weak compact-test equation to the full
maximal domain, without first admitting the silent mass vector to that domain. -/
theorem silent_inner_signed_generator {w : MassSpace} (hw : MassSpectrallySilent w)
    (u : arithmeticGenerator.domain) :
    ⟪arithmeticGenerator u - (u : MassSpace), w⟫_ℝ = 0 := by
  obtain ⟨v, hv, hs, hg⟩ := arithmeticGenerator_compact_smooth_core u
  have ht : Tendsto (fun n => ⟪arithmeticGenerator (v n) - (v n : MassSpace), w⟫_ℝ)
      atTop (𝓝 ⟪arithmeticGenerator u - (u : MassSpace), w⟫_ℝ) :=
    (hg.sub hs).inner tendsto_const_nhds
  have hz : ∀ n, ⟪arithmeticGenerator (v n) - (v n : MassSpace), w⟫_ℝ = 0 :=
    fun n => silent_inner_signed_generator_compact hw (v n) (hv n)
  exact tendsto_nhds_unique ht (by simp only [hz]; exact tendsto_const_nhds)

/-- The actual arithmetic resolvent halves every spectrally silent mass vector. -/
theorem resolvent_half_of_mass_silent {w : MassSpace} (hw : MassSpectrallySilent w) :
    resolvent w = (1/2 : ℝ) • w := by
  apply ext_inner_right ℝ
  intro z
  have h := silent_inner_signed_generator hw ⟨resolvent z, ⟨z, rfl⟩⟩
  erw [arithmeticGenerator_resolvent, inner_sub_left, inner_sub_left] at h
  change ⟪z, w⟫_ℝ - ⟪resolvent z, w⟫_ℝ - ⟪resolvent z, w⟫_ℝ = 0 at h
  rw [real_inner_comm w z, resolvent_symm z w, real_inner_comm (resolvent w) z] at h
  rw [real_inner_smul_left]
  linarith

theorem sourcePair_eq_graph_inner (p q : SourceGraph) :
    sourcePair p q = ⟪p, q⟫_ℝ - 2 * ⟪sourceMap p, sourceMap q⟫_ℝ := by
  rw [graph_inner]
  change ⟪p.val.snd, q.val.snd⟫_ℝ - ⟪p.val.fst, q.val.fst⟫_ℝ =
    (⟪p.val.fst, q.val.fst⟫_ℝ + ⟪p.val.snd, q.val.snd⟫_ℝ) - 2 * ⟪p.val.fst, q.val.fst⟫_ℝ
  ring

theorem critical_lift_source {w : MassSpace} (hw : resolvent w = (1/2 : ℝ) • w) :
    sourceMap ((2 : ℝ) • rieszLift w) = w := by
  change (2 : ℝ) • resolvent w = w
  rw [hw, smul_smul]
  norm_num

theorem critical_lift_mem_signedRadical {w : MassSpace}
    (hw : resolvent w = (1/2 : ℝ) • w) : (2 : ℝ) • rieszLift w ∈ signedRadical := by
  intro q
  rw [sourcePair_eq_graph_inner, inner_smul_graph, inner_rieszLift, critical_lift_source hw]
  exact sub_self _

theorem mass_silent_of_resolvent_half {w : MassSpace}
    (hw : resolvent w = (1/2 : ℝ) • w) : MassSpectrallySilent w := by
  have hp := critical_lift_mem_signedRadical hw
  have hs := critical_lift_source hw
  have hz := (full_radical_iff_samples_zero ((2 : ℝ) • rieszLift w)).mp hp
  refine ⟨fun z hzero => ?_, ?_, ?_⟩
  · rw [← hs, massFourierReadout_source _ (abs_im_lt_half_of_XiC_eq_zero hzero).le]
    exact hz.1 z hzero
  · rw [← hs, massFourierReadout_source _ (by norm_num : |(I/2 : ℂ).im| ≤ 1/2)]
    exact hz.2.1
  · rw [← hs, massFourierReadout_source _ (by norm_num : |(-I/2 : ℂ).im| ≤ 1/2)]
    exact hz.2.2

/-- Exact full-mass nullspace classification; no graph-admission hypothesis. -/
theorem mass_silent_iff_resolvent_half (w : MassSpace) :
    MassSpectrallySilent w ↔ resolvent w = (1/2 : ℝ) • w :=
  ⟨resolvent_half_of_mass_silent, mass_silent_of_resolvent_half⟩

/-- Spectral silence automatically supplies a unique literal graph source in
the signed radical. -/
theorem mass_silent_unique_radical_lift {w : MassSpace} (hw : MassSpectrallySilent w) :
    ∃! p : SourceGraph, p ∈ signedRadical ∧ sourceMap p = w := by
  have he := resolvent_half_of_mass_silent hw
  refine ⟨(2 : ℝ) • rieszLift w, ⟨critical_lift_mem_signedRadical he, critical_lift_source he⟩, ?_⟩
  intro q hq
  apply source_projection_injective
  exact hq.2.trans (critical_lift_source he).symm

theorem mass_silent_mem_arithmetic_domain {w : MassSpace} (hw : MassSpectrallySilent w) :
    w ∈ arithmeticGenerator.domain := by
  refine ⟨(2 : ℝ) • w, ?_⟩
  change resolvent ((2 : ℝ) • w) = w
  rw [map_smul, resolvent_half_of_mass_silent hw, smul_smul]
  norm_num

theorem arithmeticGenerator_silent {w : MassSpace} (hw : MassSpectrallySilent w) :
    arithmeticGenerator ⟨w, mass_silent_mem_arithmetic_domain hw⟩ = w := by
  have h1 := arithmeticGenerator_identity ⟨w, mass_silent_mem_arithmetic_domain hw⟩
  have h2 : resolvent (w+w) = w := by
    rw [map_add, resolvent_half_of_mass_silent hw, ← add_smul]
    norm_num
  exact add_left_cancel (resolvent_injective (h1.trans h2.symm))

end RHTower.CHMDDoobGraph
